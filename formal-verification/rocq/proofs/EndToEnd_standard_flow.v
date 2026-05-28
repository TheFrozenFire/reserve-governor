(** End-to-end standard-execution lifecycle (existence).

    Audit context. The Governor + Timelock pair is the protocol's
    governance kernel: an optimistic proposal escalates into a
    standard confirmation vote, the standard vote succeeds, the calls
    are queued through the Timelock with a mandatory delay, and after
    the delay elapses the Timelock dispatches them.

    The negative theorems already on the tree show that bad sequences
    don't compose:

      - [GovernorNoDoubleExecution.no_double_execution]: a single
        proposal can't be observed in both terminal-execution phases.
      - [IntegrationGovernorTimelock.execute_standard_blocked_before_maturity]:
        execute-before-maturity is rejected at the Timelock layer.
      - [TimelockSingleShot]: once executed, an op cannot be
        re-executed.

    This file delivers the positive complement: there *exists* a
    reachable sequence of valid transitions starting from a sane
    initial joint world (empty Governor, empty Timelock with a
    concrete minDelay, sane chain time) that lands in the joint
    terminal state ([PhaseStdExecuted], [OpDone]).

    The lifecycle is the long path:

      Step 1 : propose_optimistic              (PhaseSubmitted optimistic)
      Step 2 : transition_to_pessimistic       (parent -> Defeated,
                                                child -> StdPending)
      Step 3 : promote child to PhaseStdActive (bookkeeping oracle —
                                                see modeling note below)
      Step 4 : mark_std_succeeded              (StdActive -> StdSucceeded)
      Step 5 : queue                           (StdSucceeded -> StdQueued
                                                AND Timelock Unset -> Waiting)
      Step 6 : execute                         (StdQueued -> StdExecuted
                                                AND Timelock Ready -> Done)

    Modeling note on Step 3. The Governor simulation does not expose
    a [mark_std_active] transition — the contract's [state()] view
    reads [block.timestamp] against the snapshotted voteStart and
    flips PhaseStdPending into PhaseStdActive implicitly. The stored
    [phase] field of a freshly-spawned child carries
    [PhaseStdPending]; [mark_std_succeeded] requires the stored
    phase to be [PhaseStdActive]. We close this modeling gap with a
    single bookkeeping step [advance_to_std_active] that writes the
    phase field directly. This is the same kind of oracle move used
    elsewhere in the bridge (e.g. [proposal_to_opid] standing in for
    the keccak digest): the existence theorem captures path
    reachability, not the vote-tally arithmetic.

    Concrete calibration (used in the [vm_compute] cross-check):

      delay   = 86400  (one day, the OZ-recommended floor)
      t0      = 0      (propose)
      t1      = 100    (escalate)
      t2      = 200    (vote-window opens / active)
      t3      = 300    (succeeded + queue)
      t_exec  = 86700  (= t3 + delay, execute at maturity)

    Auxiliary calibration: vetoDelay = 0, vetoPeriod = 50,
    vetoThresholdTok = 1, then add_veto with delta = 1, so at
    [t1 = 100] the parent is past its voteStart (= 0) with
    againstVotes (= 1) >= vetoThresholdTok (= 1) — i.e.
    [observe parent t1 = PhaseDefeated]. votingDelay = 0,
    votingPeriod = 50, so the child has voteStart = 100,
    voteDuration = 50, deadline = 150; at [t3 = 300] the deadline
    is past so [mark_std_succeeded] is enabled.

    DONE_TIMESTAMP collision: DONE_TIMESTAMP = 1; t3 + delay = 86700
    is well above 1, so the magic-value collision noted in the OZ
    encoding (cf. task #122) cannot fire here.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.simulations.Timelock.
Require Import ReserveGovernor.proofs.Governor.
Require Import ReserveGovernor.proofs.Timelock.
Require Import ReserveGovernor.proofs.Integration_governor_timelock.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module EndToEndStandardFlow.

(** ===== Joint state =====

    The end-to-end lifecycle threads both a Governor proposal record
    and a Timelock state through six transitions. The [Joint] record
    pairs the two. *)
Record Joint : Set := {
  jp : Governor.Proposal.t;
  jt : Timelock.State.t;
}.

(** Bookkeeping oracle for Step 3. The contract observes the child
    in [PhaseStdActive] once [block.timestamp >= voteStart]; the
    simulation stores phase = PhaseStdPending until something writes
    the active tag. We expose that as a thin record-literal flip,
    documented above. The function is total — it doesn't gate — but
    the [JointReachable] inductive only fires it on a PhaseStdPending
    child, which is the audit-relevant transition. *)
Definition advance_to_std_active (p : Governor.Proposal.t)
    : Governor.Proposal.t :=
  {| Governor.Proposal.pid              := p.(Governor.Proposal.pid);
     Governor.Proposal.proposer         := p.(Governor.Proposal.proposer);
     Governor.Proposal.voteStart        := p.(Governor.Proposal.voteStart);
     Governor.Proposal.voteDuration     := p.(Governor.Proposal.voteDuration);
     Governor.Proposal.vetoThresholdTok := p.(Governor.Proposal.vetoThresholdTok);
     Governor.Proposal.againstVotes     := p.(Governor.Proposal.againstVotes);
     Governor.Proposal.phase            := Governor.PhaseStdActive;
     Governor.Proposal.isOptimistic     := p.(Governor.Proposal.isOptimistic);
     Governor.Proposal.parent           := p.(Governor.Proposal.parent);
  |}.

(** ===== Reachable joint sequences =====

    Six constructors, one per lifecycle step. The witness theorem
    builds a single chain; the inductive is here to make the
    reachability claim audit-legible. *)
Inductive JointReachable : Joint -> Prop :=
| jr_init :
    forall (s0 : Timelock.State.t) (p0 : Governor.Proposal.t),
    (* Step 1 produces a fresh optimistic proposal directly from
       propose_optimistic; we frame the initial joint world as the
       (post-propose, empty-Timelock) snapshot since the propose
       call does not touch the Timelock. *)
    JointReachable {| jp := p0; jt := s0 |}
| jr_add_veto :
    forall (j : Joint) (delta : U256.t),
    JointReachable j ->
    JointReachable {| jp := Governor.add_veto j.(jp) delta;
                      jt := j.(jt) |}
| jr_escalate :
    forall (j : Joint) (parent' child : Governor.Proposal.t)
           (new_pid votingDelay votingPeriod now : U256.t),
    JointReachable j ->
    Governor.transition_to_pessimistic
        j.(jp) new_pid votingDelay votingPeriod now
      = Governor.Result.Success (parent', child) ->
    (* The lifecycle threads on the *child*; the parent's terminal
       Defeated state is captured by the no-de-escalation theorem
       in [Governor_no_de_escalation.v]. *)
    JointReachable {| jp := child; jt := j.(jt) |}
| jr_advance_to_active :
    forall (j : Joint),
    JointReachable j ->
    j.(jp).(Governor.Proposal.phase) = Governor.PhaseStdPending ->
    j.(jp).(Governor.Proposal.isOptimistic) = false ->
    JointReachable {| jp := advance_to_std_active j.(jp);
                      jt := j.(jt) |}
| jr_mark_succeeded :
    forall (j : Joint) (p' : Governor.Proposal.t) (now : U256.t),
    JointReachable j ->
    Governor.mark_std_succeeded j.(jp) now = Governor.Result.Success p' ->
    JointReachable {| jp := p'; jt := j.(jt) |}
| jr_queue :
    forall (j : Joint) (delay now : U256.t) (hasProposer : bool)
           (p' : Governor.Proposal.t) (s' : Timelock.State.t),
    JointReachable j ->
    IntegrationGovernorTimelock.gov_queue_then_timelock_schedule
        j.(jp) j.(jt) delay now hasProposer
      = IntegrationGovernorTimelock.ChainSuccess p' s' ->
    JointReachable {| jp := p'; jt := s' |}
| jr_execute :
    forall (j : Joint) (now : U256.t) (hasExecutor : bool)
           (p' : Governor.Proposal.t) (s' : Timelock.State.t),
    JointReachable j ->
    IntegrationGovernorTimelock.gov_execute_then_timelock_execute
        j.(jp) j.(jt) now hasExecutor
      = IntegrationGovernorTimelock.ChainSuccess p' s' ->
    JointReachable {| jp := p'; jt := s' |}.

(** ===== Initial joint world =====

    A sane starting point: a fresh optimistic proposal, an empty
    Timelock with minDelay, sane veto/voting calibration. We package
    propose-optimistic as the first step (its arithmetic is exercised
    in [Integration_optimistic_propose.v] already); the existence
    theorem is parametric over the initial proposal record so it
    composes with any earlier-stage witness. *)

(** The constant calibration used in the [vm_compute] cross-check.
    Picked so that:
      - delay = 86400 (one day) > DONE_TIMESTAMP = 1
      - vetoDelay = 0, vetoPeriod = 50: parent active from t = 0
      - vetoThresholdTok = 1: a single 1-tok veto trips defeat
      - votingDelay = 0, votingPeriod = 50: child active from
        spawn time, deadline 50 seconds later
      - t0=0, t1=100, t2=200, t3=300, t_exec=86700: monotone, deep
        past all deadlines, well above DONE_TIMESTAMP. *)
Definition c_delay         : U256.t := 86400.
Definition c_t0            : U256.t := 0.
Definition c_t1            : U256.t := 100.
Definition c_t2            : U256.t := 200.
Definition c_t3            : U256.t := 300.
Definition c_t_exec        : U256.t := c_t3 + c_delay.

Definition c_vetoDelay     : U256.t := 0.
Definition c_vetoPeriod    : U256.t := 50.
Definition c_vetoThrTok    : U256.t := 1.
Definition c_votingDelay   : U256.t := 0.
Definition c_votingPeriod  : U256.t := 50.

Definition c_pid_parent    : U256.t := 4242.
Definition c_pid_child     : U256.t := 4343.
Definition c_proposer      : U256.t := 7777.

(** The proposal record produced by [propose_optimistic] under the
    above calibration. Exposed so the headline theorem can use it
    as the [p0] of the lifecycle. *)
Definition c_p0 : Governor.Proposal.t :=
  Governor.fresh_optimistic c_pid_parent c_proposer
    (c_t0 + c_vetoDelay) c_vetoPeriod c_vetoThrTok.

(** The empty Timelock with the calibrated minDelay. *)
Definition c_s0 : Timelock.State.t := Timelock.empty_state c_delay.

(** The initial joint world. *)
Definition c_j0 : Joint := {| jp := c_p0; jt := c_s0 |}.

(** ===== Time monotonicity preconditions =====

    Stated explicitly so the audit reader can verify by inspection
    that no step runs backwards in time. *)
Definition time_monotone (t0 t1 t2 t3 t_exec delay : U256.t) : Prop :=
  t0 <= t1 /\ t1 <= t2 /\ t2 <= t3 /\ t3 < t3 + delay /\ t3 + delay <= t_exec.

(** ===== Headline existence theorem =====

    From the initial joint world with a sane calibration, there
    exists a six-step Reachable sequence that lands in the joint
    terminal state.

    Concretely, we state the theorem parametrically over the
    initial proposal record (so it composes with the propose
    cross-check), the Timelock initial state, the times, and the
    delay; the conclusion is "there exist five intermediate
    joint states and a terminal joint state s.t. each transition
    fires successfully and the final state has
    [phase = PhaseStdExecuted] and [op_status = OpDone] at
    [t_exec]." *)
Theorem standard_lifecycle_exists
    (p0 : Governor.Proposal.t) (s0 : Timelock.State.t)
    (vetoDelay vetoPeriod vetoThrTok : U256.t)
    (votingDelay votingPeriod : U256.t)
    (new_pid : U256.t)
    (t0 t1 t2 t3 t_exec delay : U256.t) :
  (* propose-time calibration: p0 = fresh_optimistic at t0 *)
  p0 = Governor.fresh_optimistic
         p0.(Governor.Proposal.pid)
         p0.(Governor.Proposal.proposer)
         (t0 + vetoDelay) vetoPeriod vetoThrTok ->
  (* Timelock starts empty at the calibrated id *)
  Timelock.get_ts s0 (IntegrationGovernorTimelock.proposal_to_opid
                        new_pid) = 0 ->
  (* Timelock minDelay <= chosen delay *)
  delay >= s0.(Timelock.State.minDelay) ->
  (* Time monotone *)
  time_monotone t0 t1 t2 t3 t_exec delay ->
  (* Parent observable as Defeated at t1: in-window and threshold met *)
  t0 + vetoDelay <= t1 ->
  vetoThrTok >= 1 ->
  (* Standard vote-window calibration: voteStart + voteDuration <= t3 *)
  t1 + votingDelay + votingPeriod <= t3 ->
  (* Delay above DONE_TIMESTAMP collision (#122) *)
  Timelock.DONE_TIMESTAMP < t3 + delay ->
  exists (p1 p2 p3 p4 p5 : Governor.Proposal.t)
         (s4 s5 : Timelock.State.t)
         (parent' : Governor.Proposal.t),
    (* p1 = post-veto: enough againstVotes to trip the Defeated arm.
       We pick delta = vetoThrTok directly. *)
    p1 = Governor.add_veto p0 vetoThrTok /\
    (* p2 = child spawned by escalation. *)
    Governor.transition_to_pessimistic
        p1 new_pid votingDelay votingPeriod t1
      = Governor.Result.Success (parent', p2) /\
    p2.(Governor.Proposal.phase) = Governor.PhaseStdPending /\
    p2.(Governor.Proposal.isOptimistic) = false /\
    (* p3 = bookkeeping flip: PhaseStdPending -> PhaseStdActive. *)
    p3 = advance_to_std_active p2 /\
    p3.(Governor.Proposal.phase) = Governor.PhaseStdActive /\
    (* p4 = mark_std_succeeded. *)
    Governor.mark_std_succeeded p3 t3 = Governor.Result.Success p4 /\
    p4.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded /\
    (* (p5, s4) via the queue bridge. *)
    IntegrationGovernorTimelock.gov_queue_then_timelock_schedule
        p4 s0 delay t3 true
      = IntegrationGovernorTimelock.ChainSuccess p5 s4 /\
    p5.(Governor.Proposal.phase) = Governor.PhaseStdQueued /\
    p5.(Governor.Proposal.pid) = new_pid /\
    (* Final execute: bumps phase to StdExecuted and op to Done. *)
    (exists p6 s5',
      IntegrationGovernorTimelock.gov_execute_then_timelock_execute
          p5 s4 t_exec true
        = IntegrationGovernorTimelock.ChainSuccess p6 s5' /\
      p6.(Governor.Proposal.phase) = Governor.PhaseStdExecuted /\
      Timelock.op_status s5'
          (IntegrationGovernorTimelock.proposal_to_opid new_pid)
          t_exec
        = Timelock.OpDone /\
      (* Delay honored: scheduling happened at t3, execute at
         t_exec, t3 + delay <= t_exec. *)
      t3 + delay <= t_exec /\
      s5 = s5').
Proof.
  intros Hp0 Hunset HdelayGe Hmono HparAct HthrPos Hwin Hdone.
  destruct Hmono as (Hm01 & Hm12 & Hm23 & Hm3d & HmdE).
  (* ----- Step 1 -> 2: add_veto with delta = vetoThrTok. ----- *)
  set (p1 := Governor.add_veto p0 vetoThrTok).
  (* p1 inherits all fields from p0 except againstVotes = 0 + vetoThrTok. *)
  assert (Hp1opt : p1.(Governor.Proposal.isOptimistic) = true).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl.
    reflexivity. }
  assert (Hp1ph : p1.(Governor.Proposal.phase) = Governor.PhaseSubmitted).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl. reflexivity. }
  assert (Hp1vs : p1.(Governor.Proposal.voteStart) = t0 + vetoDelay).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl. reflexivity. }
  assert (Hp1vd : p1.(Governor.Proposal.voteDuration) = vetoPeriod).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl. reflexivity. }
  assert (Hp1vtt : p1.(Governor.Proposal.vetoThresholdTok) = vetoThrTok).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl. reflexivity. }
  assert (Hp1av : p1.(Governor.Proposal.againstVotes) = 0 + vetoThrTok).
  { unfold p1, Governor.add_veto. simpl. rewrite Hp0. simpl. reflexivity. }
  assert (Hp1pid : p1.(Governor.Proposal.pid) = p0.(Governor.Proposal.pid)).
  { unfold p1, Governor.add_veto. simpl. reflexivity. }
  (* ----- observe p1 t1 = PhaseDefeated ----- *)
  assert (Hobs1 : Governor.observe p1 t1 = Governor.PhaseDefeated).
  { unfold Governor.observe. rewrite Hp1ph. rewrite Hp1vs.
    rewrite Hp1opt.
    assert (Hpre : (t1 <? t0 + vetoDelay) = false)
      by (apply Z.ltb_ge; lia).
    rewrite Hpre.
    assert (Hge : (p1.(Governor.Proposal.againstVotes) >=?
                   p1.(Governor.Proposal.vetoThresholdTok)) = true).
    { rewrite Hp1av, Hp1vtt. apply Z.geb_le. lia. }
    rewrite Hge. reflexivity. }
  (* ----- Step 2: transition_to_pessimistic at t1 ----- *)
  set (parent' :=
        {| Governor.Proposal.pid              := p1.(Governor.Proposal.pid);
           Governor.Proposal.proposer         := p1.(Governor.Proposal.proposer);
           Governor.Proposal.voteStart        := p1.(Governor.Proposal.voteStart);
           Governor.Proposal.voteDuration     := p1.(Governor.Proposal.voteDuration);
           Governor.Proposal.vetoThresholdTok := p1.(Governor.Proposal.vetoThresholdTok);
           Governor.Proposal.againstVotes     := p1.(Governor.Proposal.againstVotes);
           Governor.Proposal.phase            := Governor.PhaseDefeated;
           Governor.Proposal.isOptimistic     := p1.(Governor.Proposal.isOptimistic);
           Governor.Proposal.parent           := p1.(Governor.Proposal.parent);
        |}).
  set (p2 := Governor.fresh_standard_child
               p1.(Governor.Proposal.pid)
               new_pid
               p1.(Governor.Proposal.proposer)
               (t1 + votingDelay)
               votingPeriod).
  assert (Hp2ph : p2.(Governor.Proposal.phase) = Governor.PhaseStdPending)
    by reflexivity.
  assert (Hp2opt : p2.(Governor.Proposal.isOptimistic) = false)
    by reflexivity.
  assert (Hp2vs : p2.(Governor.Proposal.voteStart) = t1 + votingDelay)
    by reflexivity.
  assert (Hp2vd : p2.(Governor.Proposal.voteDuration) = votingPeriod)
    by reflexivity.
  assert (Hp2pid : p2.(Governor.Proposal.pid) = new_pid)
    by reflexivity.
  (* ----- Step 3: advance_to_std_active ----- *)
  set (p3 := advance_to_std_active p2).
  assert (Hp3ph : p3.(Governor.Proposal.phase) = Governor.PhaseStdActive)
    by reflexivity.
  assert (Hp3opt : p3.(Governor.Proposal.isOptimistic) = false).
  { unfold p3, advance_to_std_active. simpl. exact Hp2opt. }
  assert (Hp3vs : p3.(Governor.Proposal.voteStart) = t1 + votingDelay).
  { unfold p3, advance_to_std_active. simpl. exact Hp2vs. }
  assert (Hp3vd : p3.(Governor.Proposal.voteDuration) = votingPeriod).
  { unfold p3, advance_to_std_active. simpl. exact Hp2vd. }
  assert (Hp3pid : p3.(Governor.Proposal.pid) = new_pid).
  { unfold p3, advance_to_std_active. simpl. exact Hp2pid. }
  (* ----- Step 4: mark_std_succeeded at t3 ----- *)
  set (p4 :=
        {| Governor.Proposal.pid              := p3.(Governor.Proposal.pid);
           Governor.Proposal.proposer         := p3.(Governor.Proposal.proposer);
           Governor.Proposal.voteStart        := p3.(Governor.Proposal.voteStart);
           Governor.Proposal.voteDuration     := p3.(Governor.Proposal.voteDuration);
           Governor.Proposal.vetoThresholdTok := p3.(Governor.Proposal.vetoThresholdTok);
           Governor.Proposal.againstVotes     := p3.(Governor.Proposal.againstVotes);
           Governor.Proposal.phase            := Governor.PhaseStdSucceeded;
           Governor.Proposal.isOptimistic     := p3.(Governor.Proposal.isOptimistic);
           Governor.Proposal.parent           := p3.(Governor.Proposal.parent);
        |}).
  assert (Hp4Eq : Governor.mark_std_succeeded p3 t3
                    = Governor.Result.Success p4).
  { unfold Governor.mark_std_succeeded.
    rewrite Hp3opt.
    rewrite Hp3ph. cbn [Governor.phase_eq negb].
    (* now <? voteStart + voteDuration must be false *)
    assert (Hdl : (t3 <? p3.(Governor.Proposal.voteStart) +
                            p3.(Governor.Proposal.voteDuration)) = false).
    { rewrite Hp3vs, Hp3vd. apply Z.ltb_ge. lia. }
    rewrite Hdl. unfold p4. reflexivity. }
  assert (Hp4ph : p4.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded)
    by reflexivity.
  assert (Hp4opt : p4.(Governor.Proposal.isOptimistic) = false).
  { unfold p4. simpl. exact Hp3opt. }
  assert (Hp4pid : p4.(Governor.Proposal.pid) = new_pid).
  { unfold p4. simpl. exact Hp3pid. }
  (* ----- Step 5: queue via the bridge at t3 ----- *)
  (* Use [escalate_then_queue_then_execute_chain] for steps 5+6. *)
  pose proof (IntegrationGovernorTimelock.escalate_then_queue_then_execute_chain
                p4 s0 delay t3 t_exec) as Hchain.
  assert (HdelayPos : 0 < delay) by lia.
  assert (HunsetP4 :
    Timelock.get_ts s0
      (IntegrationGovernorTimelock.proposal_to_opid
         p4.(Governor.Proposal.pid)) = 0).
  { rewrite Hp4pid. exact Hunset. }
  specialize (Hchain Hp4opt Hp4ph HunsetP4 HdelayGe HdelayPos Hdone HmdE).
  destruct Hchain as (p5 & s4 & p6 & s5 & HqEq & Hp5ph & _ & HeEq & Hp6ph & Hs5done).
  (* The queue call returns (p5, s4); the execute call returns (p6, s5). *)
  assert (Hp5pid : p5.(Governor.Proposal.pid) = new_pid).
  { (* Extract p5's pid from queue success: queue_operations preserves pid. *)
    unfold IntegrationGovernorTimelock.gov_queue_then_timelock_schedule in HqEq.
    destruct (Governor.queue_operations p4) eqn:Hgq; [|discriminate].
    destruct (Timelock.scheduleBatch s0 _ delay t3 true); [|discriminate].
    injection HqEq as Hp5eq Hs4eq.
    unfold Governor.queue_operations in Hgq.
    rewrite Hp4opt in Hgq. rewrite Hp4ph in Hgq. simpl in Hgq.
    injection Hgq as Hqop.
    rewrite <- Hp5eq, <- Hqop. simpl. exact Hp4pid. }
  (* ----- Assemble the existential. ----- *)
  exists p1, p2, p3, p4, p5, s4, s5, parent'.
  split; [reflexivity|].
  split.
  { (* transition_to_pessimistic p1 new_pid ... t1 = Success (parent', p2). *)
    unfold Governor.transition_to_pessimistic.
    rewrite Hobs1. unfold parent', p2. reflexivity. }
  split; [exact Hp2ph|].
  split; [exact Hp2opt|].
  split; [reflexivity|].
  split; [exact Hp3ph|].
  split; [exact Hp4Eq|].
  split; [exact Hp4ph|].
  split; [exact HqEq|].
  split; [exact Hp5ph|].
  split; [exact Hp5pid|].
  exists p6, s5.
  split; [exact HeEq|].
  split; [exact Hp6ph|].
  split.
  { (* op_status at new_pid = OpDone. Hs5done is at p4.(pid);
       p4.(pid) = new_pid via Hp4pid. *)
    rewrite <- Hp4pid. exact Hs5done. }
  split; [exact HmdE|].
  reflexivity.
Qed.

(** ===== JointReachable corollary =====

    The headline existence theorem implies that the terminal joint
    state is JointReachable from the initial joint world. This is
    the audit-facing framing: every step is one of the constructors
    of [JointReachable]. *)
Corollary standard_lifecycle_reachable
    (p0 : Governor.Proposal.t) (s0 : Timelock.State.t)
    (vetoDelay vetoPeriod vetoThrTok : U256.t)
    (votingDelay votingPeriod : U256.t)
    (new_pid : U256.t)
    (t0 t1 t2 t3 t_exec delay : U256.t) :
  p0 = Governor.fresh_optimistic
         p0.(Governor.Proposal.pid)
         p0.(Governor.Proposal.proposer)
         (t0 + vetoDelay) vetoPeriod vetoThrTok ->
  Timelock.get_ts s0 (IntegrationGovernorTimelock.proposal_to_opid
                        new_pid) = 0 ->
  delay >= s0.(Timelock.State.minDelay) ->
  time_monotone t0 t1 t2 t3 t_exec delay ->
  t0 + vetoDelay <= t1 ->
  vetoThrTok >= 1 ->
  t1 + votingDelay + votingPeriod <= t3 ->
  Timelock.DONE_TIMESTAMP < t3 + delay ->
  exists (p6 : Governor.Proposal.t) (s5 : Timelock.State.t),
    JointReachable {| jp := p6; jt := s5 |} /\
    p6.(Governor.Proposal.phase) = Governor.PhaseStdExecuted /\
    Timelock.op_status s5
        (IntegrationGovernorTimelock.proposal_to_opid new_pid) t_exec
      = Timelock.OpDone.
Proof.
  intros Hp0 Hunset HdelayGe Hmono HparAct HthrPos Hwin Hdone.
  pose proof (standard_lifecycle_exists
                p0 s0 vetoDelay vetoPeriod vetoThrTok
                votingDelay votingPeriod new_pid
                t0 t1 t2 t3 t_exec delay
                Hp0 Hunset HdelayGe Hmono HparAct HthrPos Hwin Hdone)
    as Hex.
  destruct Hex as (p1 & p2 & p3 & p4 & p5 & s4 & s5 & parent' &
                   Hp1eq & Htrans & Hp2ph & Hp2opt &
                   Hp3eq & Hp3ph & Hp4Eq & Hp4ph &
                   HqEq & Hp5ph & _Hp5pid &
                   p6 & s5' & HeEq & Hp6ph & Hs5done & _Hmat & Hs5eq).
  (* Build the JointReachable chain. *)
  pose (j0 := {| jp := p0; jt := s0 |}).
  assert (Hjr0 : JointReachable j0) by (apply jr_init).
  pose (j1 := {| jp := p1; jt := s0 |}).
  assert (Hjr1 : JointReachable j1).
  { unfold j1. rewrite Hp1eq.
    change ({| jp := Governor.add_veto p0 vetoThrTok; jt := s0 |})
      with {| jp := Governor.add_veto j0.(jp) vetoThrTok; jt := j0.(jt) |}.
    apply jr_add_veto. exact Hjr0. }
  pose (j2 := {| jp := p2; jt := s0 |}).
  assert (Hjr2 : JointReachable j2).
  { unfold j2.
    change ({| jp := p2; jt := s0 |})
      with {| jp := p2; jt := j1.(jt) |}.
    apply (jr_escalate j1 parent' p2 new_pid votingDelay votingPeriod t1).
    - exact Hjr1.
    - simpl. exact Htrans. }
  pose (j3 := {| jp := p3; jt := s0 |}).
  assert (Hjr3 : JointReachable j3).
  { unfold j3. rewrite Hp3eq.
    change ({| jp := advance_to_std_active p2; jt := s0 |})
      with {| jp := advance_to_std_active j2.(jp); jt := j2.(jt) |}.
    apply jr_advance_to_active.
    - exact Hjr2.
    - simpl. exact Hp2ph.
    - simpl. exact Hp2opt. }
  pose (j4 := {| jp := p4; jt := s0 |}).
  assert (Hjr4 : JointReachable j4).
  { unfold j4.
    change ({| jp := p4; jt := s0 |})
      with {| jp := p4; jt := j3.(jt) |}.
    apply (jr_mark_succeeded j3 p4 t3).
    - exact Hjr3.
    - simpl. exact Hp4Eq. }
  pose (j5 := {| jp := p5; jt := s4 |}).
  assert (Hjr5 : JointReachable j5).
  { unfold j5.
    change ({| jp := p5; jt := s4 |})
      with {| jp := p5; jt := s4 |}.
    apply (jr_queue j4 delay t3 true p5 s4).
    - exact Hjr4.
    - simpl. exact HqEq. }
  pose (j6 := {| jp := p6; jt := s5' |}).
  assert (Hjr6 : JointReachable j6).
  { unfold j6.
    apply (jr_execute j5 t_exec true p6 s5').
    - exact Hjr5.
    - simpl. exact HeEq. }
  exists p6, s5'.
  split; [exact Hjr6|].
  split; [exact Hp6ph|].
  (* op_status at new_pid t_exec = OpDone. Hs5done already uses
     [proposal_to_opid new_pid] after the headline-theorem update. *)
  exact Hs5done.
Qed.

(** ===== vm_compute cross-check =====

    The calibrated witnesses run end-to-end. Since
    [proposal_to_opid] is opaque, we cross-check the parts that
    evaluate concretely:

      - the Governor side (steps 1-4) evaluates entirely in
        [vm_compute].
      - the Timelock side (steps 5-6) is checked via the headline
        bridge lemma at the concrete values, abstracting over the
        opaque opid mapping.

    The wrapper [xcheck_concrete_lifecycle] composes the two. *)

(** Cross-check: time monotonicity holds at the calibrated values. *)
Lemma xcheck_time_monotone :
  time_monotone c_t0 c_t1 c_t2 c_t3 c_t_exec c_delay.
Proof.
  unfold time_monotone, c_t0, c_t1, c_t2, c_t3, c_t_exec, c_delay.
  vm_compute. repeat split; discriminate.
Qed.

(** Cross-check: parent transitions to Defeated at [c_t1] after a
    single 1-tok veto. *)
Lemma xcheck_parent_defeated :
  Governor.observe (Governor.add_veto c_p0 c_vetoThrTok) c_t1
    = Governor.PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

(** Cross-check: escalation at [c_t1] succeeds and produces a child
    in [PhaseStdPending]. *)
Lemma xcheck_escalate_success :
  exists parent' child,
    Governor.transition_to_pessimistic
        (Governor.add_veto c_p0 c_vetoThrTok)
        c_pid_child c_votingDelay c_votingPeriod c_t1
      = Governor.Result.Success (parent', child)
    /\ child.(Governor.Proposal.phase) = Governor.PhaseStdPending
    /\ child.(Governor.Proposal.isOptimistic) = false
    /\ parent'.(Governor.Proposal.phase) = Governor.PhaseDefeated.
Proof.
  vm_compute. eexists; eexists; repeat split; reflexivity.
Qed.

(** Cross-check: post-active child can be flipped to
    [PhaseStdSucceeded] at [c_t3]. *)
Lemma xcheck_mark_std_succeeded :
  let c_p1 := Governor.add_veto c_p0 c_vetoThrTok in
  match Governor.transition_to_pessimistic c_p1
          c_pid_child c_votingDelay c_votingPeriod c_t1 with
  | Governor.Result.Success (_, c_p2) =>
      let c_p3 := advance_to_std_active c_p2 in
      match Governor.mark_std_succeeded c_p3 c_t3 with
      | Governor.Result.Success c_p4 =>
          c_p4.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Cross-check: the full Governor side (steps 1-4) leaves the
    proposal in [PhaseStdSucceeded]. *)
Lemma xcheck_governor_side_to_succeeded :
  exists p4,
    let p1 := Governor.add_veto c_p0 c_vetoThrTok in
    match Governor.transition_to_pessimistic
            p1 c_pid_child c_votingDelay c_votingPeriod c_t1 with
    | Governor.Result.Success (_, p2) =>
        let p3 := advance_to_std_active p2 in
        Governor.mark_std_succeeded p3 c_t3 = Governor.Result.Success p4
    | _ => False
    end
    /\ p4.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded
    /\ p4.(Governor.Proposal.isOptimistic) = false
    /\ p4.(Governor.Proposal.pid) = c_pid_child.
Proof.
  vm_compute. eexists. repeat split; reflexivity.
Qed.

(** Cross-check: scheduling at [c_t3] writes [c_t_exec] into the
    Timelock; the op is Waiting at [c_t3 + 1] and Ready at
    [c_t_exec]. Abstracted over the opaque opid. *)
Lemma xcheck_schedule_at_t3 :
  forall id : Timelock.OpId,
    Timelock.get_ts c_s0 id = 0 ->
    exists s4,
      Timelock.scheduleBatch c_s0 id c_delay c_t3 true
        = Timelock.Result.Success s4
      /\ Timelock.get_ts s4 id = c_t_exec
      /\ Timelock.op_status s4 id c_t3 = Timelock.OpWaiting
      /\ Timelock.op_status s4 id c_t_exec = Timelock.OpReady.
Proof.
  intros id Hunset.
  unfold Timelock.scheduleBatch. rewrite Hunset. cbn [negb Z.eqb].
  (* delay <? minDelay is false at this calibration. *)
  unfold c_s0, Timelock.empty_state. cbn [Timelock.State.minDelay].
  change (c_delay <? c_delay) with false.
  eexists. split; [reflexivity|].
  split.
  - rewrite TimelockProofs.get_ts_set_same.
    unfold c_t_exec, c_t3, c_delay. reflexivity.
  - split.
    + unfold Timelock.op_status.
      rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity.
    + unfold Timelock.op_status.
      rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity.
Qed.

(** Cross-check: execute at [c_t_exec] turns the op to OpDone. *)
Lemma xcheck_execute_at_maturity :
  forall id : Timelock.OpId,
    Timelock.get_ts c_s0 id = 0 ->
    forall s4,
      Timelock.scheduleBatch c_s0 id c_delay c_t3 true
        = Timelock.Result.Success s4 ->
      exists s5,
        Timelock.executeBatch s4 id c_t_exec true
          = Timelock.Result.Success s5
        /\ Timelock.op_status s5 id c_t_exec = Timelock.OpDone.
Proof.
  intros id Hunset s4 HsOk.
  unfold Timelock.scheduleBatch in HsOk. rewrite Hunset in HsOk.
  cbn [negb Z.eqb] in HsOk.
  unfold c_s0, Timelock.empty_state in HsOk.
  cbn [Timelock.State.minDelay] in HsOk.
  change (c_delay <? c_delay) with false in HsOk.
  injection HsOk as Hs4.
  unfold Timelock.executeBatch.
  assert (Hready : Timelock.op_status s4 id c_t_exec = Timelock.OpReady).
  { rewrite <- Hs4. unfold Timelock.op_status.
    rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity. }
  rewrite Hready. eexists. split; [reflexivity|].
  unfold Timelock.op_status.
  rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity.
Qed.

(** Cross-check: the headline lemma fires at the calibrated values
    when applied to the initial joint world. This is the
    audit-visible existential at concrete numbers. *)
Lemma xcheck_concrete_calibration :
  Timelock.get_ts c_s0
    (IntegrationGovernorTimelock.proposal_to_opid c_pid_child) = 0 ->
  exists (p1 p2 p3 p4 p5 : Governor.Proposal.t)
         (s4 s5 : Timelock.State.t)
         (parent' : Governor.Proposal.t),
    p1 = Governor.add_veto c_p0 c_vetoThrTok /\
    Governor.transition_to_pessimistic
        p1 c_pid_child c_votingDelay c_votingPeriod c_t1
      = Governor.Result.Success (parent', p2) /\
    p2.(Governor.Proposal.phase) = Governor.PhaseStdPending /\
    p2.(Governor.Proposal.isOptimistic) = false /\
    p3 = advance_to_std_active p2 /\
    p3.(Governor.Proposal.phase) = Governor.PhaseStdActive /\
    Governor.mark_std_succeeded p3 c_t3 = Governor.Result.Success p4 /\
    p4.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded /\
    IntegrationGovernorTimelock.gov_queue_then_timelock_schedule
        p4 c_s0 c_delay c_t3 true
      = IntegrationGovernorTimelock.ChainSuccess p5 s4 /\
    p5.(Governor.Proposal.phase) = Governor.PhaseStdQueued /\
    p5.(Governor.Proposal.pid) = c_pid_child /\
    (exists p6 s5',
      IntegrationGovernorTimelock.gov_execute_then_timelock_execute
          p5 s4 c_t_exec true
        = IntegrationGovernorTimelock.ChainSuccess p6 s5' /\
      p6.(Governor.Proposal.phase) = Governor.PhaseStdExecuted /\
      Timelock.op_status s5'
          (IntegrationGovernorTimelock.proposal_to_opid c_pid_child)
          c_t_exec
        = Timelock.OpDone /\
      c_t3 + c_delay <= c_t_exec /\
      s5 = s5').
Proof.
  intros Hunset.
  apply (standard_lifecycle_exists
           c_p0 c_s0 c_vetoDelay c_vetoPeriod c_vetoThrTok
           c_votingDelay c_votingPeriod c_pid_child
           c_t0 c_t1 c_t2 c_t3 c_t_exec c_delay).
  - vm_compute. reflexivity.
  - exact Hunset.
  - unfold c_s0, Timelock.empty_state, c_delay. simpl. vm_compute. discriminate.
  - exact xcheck_time_monotone.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - vm_compute. reflexivity.
Qed.

End EndToEndStandardFlow.
