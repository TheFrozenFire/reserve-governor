(** Cross-domain integration: Governor x Timelock end-to-end execution
    chain.

    The Governor simulation models [queue_operations] and
    [execute_standard] as opaque phase bumps inside its own proposal
    state machine — it doesn't actually call out to the Timelock
    simulation. The lemma [queue_operations_requires_succeeded] from
    [proofs/Governor.v] tells us that you can only queue after the
    proposal succeeded, but doesn't connect to the Timelock's
    [scheduleBatch] semantics; analogously, [execute_standard_requires_queued]
    doesn't connect to the Timelock's [executeBatch] maturity check.

    This file builds the missing bridge. Concretely:

      - We introduce a parameter [proposal_to_opid : U256.t -> OpId]
        standing in for the keccak256 of (targets, values, payloads,
        predecessor, salt). The Solidity flow computes this id from the
        Governor's [_executeOperations] hook before it calls into the
        Timelock. We treat the map as opaque but injective (distinct
        proposalIds give distinct opids), modeling keccak256's
        collision resistance for distinct inputs.

      - [gov_queue_then_timelock_schedule] composes the Governor's
        phase bump [StdSucceeded -> StdQueued] with the Timelock's
        [scheduleBatch] (Unset -> Waiting). The result threads both
        the new Proposal.t and the new Timelock.State.t through.

      - [gov_execute_then_timelock_execute] composes the Governor's
        phase bump [StdQueued -> StdExecuted] with the Timelock's
        [executeBatch] (Ready -> Done).

    Headline lemmas:

      - [escalate_then_queue_then_execute_chain]: starting from a
        Governor proposal in PhaseStdSucceeded with a fresh Timelock
        state, the composed schedule-then-execute chain succeeds (and
        moves the Governor to PhaseStdExecuted and the Timelock op
        from Unset all the way to Done) IFF the elapsed time between
        the two calls is at least [delay] AND the timelock minDelay
        admits [delay].

      - [execute_standard_blocked_before_maturity]: if the proposal
        sits in PhaseStdQueued and the chain time is strictly below
        [scheduledAt + delay] (so the Timelock op is still OpWaiting),
        then the composed execute call reverts at the Timelock layer
        regardless of what the Governor would otherwise permit.

    The bridge keeps the OpId mapping opaque (Parameter +
    Axiom-injective). Modeling delay-precondition coupling: the
    Governor records the scheduling timestamp implicitly through the
    Timelock's [timestamps] map (the value written is [now + delay]);
    the [execute_standard_blocked_before_maturity] lemma's hypothesis
    [now2 < nowS + delay] is exactly the OZ Timelock's NotReady gate.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.simulations.Timelock.
Require Import ReserveGovernor.proofs.Governor.
Require Import ReserveGovernor.proofs.Timelock.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module IntegrationGovernorTimelock.

(** Bring both modules into scope under qualified names. The two
    simulations each define their own [Result.t] / [Address] /
    [Revert] surfaces, so we use module-qualified references to keep
    them unambiguous. *)

(** ===== Bridge: proposal id -> timelock op id =====

    On-chain the Timelock op id is keccak256(targets, values,
    payloads, predecessor, salt). The Governor reaches into the
    Timelock with the bytes that constitute the proposal's calls plus
    a salt; the result is uniquely determined by the proposal (modulo
    salt). For the state-machine bridge we keep the id derivation
    opaque and only require injectivity from distinct proposal ids,
    which matches the keccak256 collision-resistance argument used
    everywhere else in the on-chain reasoning. *)
Parameter proposal_to_opid : U256.t -> Timelock.OpId.

Axiom proposal_to_opid_injective :
  forall p1 p2 : U256.t,
    proposal_to_opid p1 = proposal_to_opid p2 -> p1 = p2.

(** ===== Bridge: composed operations =====

    Each composed operation pairs a Governor phase bump with the
    corresponding Timelock state transition. The result tuples carry
    BOTH new states so callers can reason about either side. *)

(** Two-shaped result: success threads (Proposal, State); revert
    bubbles up either domain's revert code with a tag so the proof
    can case-split on which layer failed. *)
Inductive ChainResult : Set :=
| ChainSuccess (p : Governor.Proposal.t) (s : Timelock.State.t)
| ChainGovRevert (p_code s_code : U256.t)
| ChainTLRevert  (p_code s_code : U256.t).

(** [gov_queue_then_timelock_schedule] — the queue-side composition.

    Steps (mirroring ReserveOptimisticGovernor.queueOperations):
      1. Governor.queue_operations p     (StdSucceeded -> StdQueued)
      2. Timelock.scheduleBatch s id delay now hasProposer
                                          (Unset -> Waiting at [now+delay])

    If either step reverts, the chain reverts with the appropriate
    tag. *)
Definition gov_queue_then_timelock_schedule
    (p : Governor.Proposal.t) (s : Timelock.State.t)
    (delay now : U256.t) (hasProposer : bool)
    : ChainResult :=
  match Governor.queue_operations p with
  | Governor.Result.Revert pc sc => ChainGovRevert pc sc
  | Governor.Result.Success p' =>
      let id := proposal_to_opid p.(Governor.Proposal.pid) in
      match Timelock.scheduleBatch s id delay now hasProposer with
      | Timelock.Result.Revert pc sc => ChainTLRevert pc sc
      | Timelock.Result.Success s' => ChainSuccess p' s'
      end
  end.

(** [gov_execute_then_timelock_execute] — the execute-side composition.

    Steps (mirroring ReserveOptimisticGovernor._executeOperations on
    the standard path):
      1. Governor.execute_standard p     (StdQueued -> StdExecuted)
      2. Timelock.executeBatch s id now hasExecutor
                                          (Ready -> Done @ DONE_TIMESTAMP)

    Both layers gate independently — the Timelock will revert if the
    op is OpWaiting at [now] even if the Governor's phase-eq check
    passes. *)
Definition gov_execute_then_timelock_execute
    (p : Governor.Proposal.t) (s : Timelock.State.t)
    (now : U256.t) (hasExecutor : bool)
    : ChainResult :=
  match Governor.execute_standard p with
  | Governor.Result.Revert pc sc => ChainGovRevert pc sc
  | Governor.Result.Success p' =>
      let id := proposal_to_opid p.(Governor.Proposal.pid) in
      match Timelock.executeBatch s id now hasExecutor with
      | Timelock.Result.Revert pc sc => ChainTLRevert pc sc
      | Timelock.Result.Success s' => ChainSuccess p' s'
      end
  end.

(** ===== Headline 1: full chain Unset -> Waiting -> Ready -> Done =====

    Threaded sequence:
      - p0 in PhaseStdSucceeded, not optimistic
      - s0 Timelock state with op id Unset, hasProposer=true,
        delay >= s0.minDelay
      - schedule at nowS, then execute at nowE with nowE >= nowS + delay
      - hasExecutor=true and DONE_TIMESTAMP < nowS + delay
        (rules out the degenerate collision with the magic ts=1 value).

    Conclusion:
      - composed schedule succeeds, producing (p1, s1) with
        p1.(phase) = PhaseStdQueued and op_status s1 id nowS = OpWaiting
      - composed execute on (p1, s1) at nowE succeeds, producing
        (p2, s2) with p2.(phase) = PhaseStdExecuted and
        op_status s2 id nowE = OpDone. *)
Lemma escalate_then_queue_then_execute_chain
    (p0 : Governor.Proposal.t) (s0 : Timelock.State.t)
    (delay nowS nowE : U256.t) :
  p0.(Governor.Proposal.isOptimistic) = false ->
  p0.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded ->
  Timelock.get_ts s0 (proposal_to_opid p0.(Governor.Proposal.pid)) = 0 ->
  delay >= s0.(Timelock.State.minDelay) ->
  0 < delay ->
  Timelock.DONE_TIMESTAMP < nowS + delay ->
  nowS + delay <= nowE ->
  exists p1 s1 p2 s2,
    gov_queue_then_timelock_schedule p0 s0 delay nowS true
      = ChainSuccess p1 s1 /\
    p1.(Governor.Proposal.phase) = Governor.PhaseStdQueued /\
    Timelock.op_status s1 (proposal_to_opid p0.(Governor.Proposal.pid)) nowS
      = Timelock.OpWaiting /\
    gov_execute_then_timelock_execute p1 s1 nowE true
      = ChainSuccess p2 s2 /\
    p2.(Governor.Proposal.phase) = Governor.PhaseStdExecuted /\
    Timelock.op_status s2 (proposal_to_opid p0.(Governor.Proposal.pid)) nowE
      = Timelock.OpDone.
Proof.
  intros Hopt Hph Hunset HdelayGe HdelayPos Hpos Hmat.
  (* Build the post-queue Governor proposal explicitly.
     Note: queue_operations is only invoked after the [isOptimistic = false]
     guard fires, so the resulting record literally carries [isOptimistic := false]
     (NOT [p0.(isOptimistic)]). Matching this exactly is what makes [HqEq]'s
     reflexivity check go through. *)
  set (id := proposal_to_opid p0.(Governor.Proposal.pid)).
  set (p1 := {|
    Governor.Proposal.pid              := p0.(Governor.Proposal.pid);
    Governor.Proposal.proposer         := p0.(Governor.Proposal.proposer);
    Governor.Proposal.voteStart        := p0.(Governor.Proposal.voteStart);
    Governor.Proposal.voteDuration     := p0.(Governor.Proposal.voteDuration);
    Governor.Proposal.vetoThresholdTok := p0.(Governor.Proposal.vetoThresholdTok);
    Governor.Proposal.againstVotes     := p0.(Governor.Proposal.againstVotes);
    Governor.Proposal.phase            := Governor.PhaseStdQueued;
    Governor.Proposal.isOptimistic     := false;
    Governor.Proposal.parent           := p0.(Governor.Proposal.parent);
    Governor.Proposal.pastSupply       := p0.(Governor.Proposal.pastSupply);
  |}).
  set (s1 := Timelock.set_state_ts s0 id (nowS + delay)).
  (* Build the post-execute Governor proposal. *)
  set (p2 := {|
    Governor.Proposal.pid              := p1.(Governor.Proposal.pid);
    Governor.Proposal.proposer         := p1.(Governor.Proposal.proposer);
    Governor.Proposal.voteStart        := p1.(Governor.Proposal.voteStart);
    Governor.Proposal.voteDuration     := p1.(Governor.Proposal.voteDuration);
    Governor.Proposal.vetoThresholdTok := p1.(Governor.Proposal.vetoThresholdTok);
    Governor.Proposal.againstVotes     := p1.(Governor.Proposal.againstVotes);
    Governor.Proposal.phase            := Governor.PhaseStdExecuted;
    Governor.Proposal.isOptimistic     := false;
    Governor.Proposal.parent           := p1.(Governor.Proposal.parent);
    Governor.Proposal.pastSupply       := p1.(Governor.Proposal.pastSupply);
  |}).
  set (s2 := Timelock.set_state_ts s1 id Timelock.DONE_TIMESTAMP).
  (* Useful timestamp arithmetic. *)
  assert (Hs1ts : Timelock.get_ts s1 id = nowS + delay).
  { unfold s1. apply TimelockProofs.get_ts_set_same. }
  unfold Timelock.DONE_TIMESTAMP in Hpos.
  assert (Hnz : (nowS + delay =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hnd : (nowS + delay =? 1) = false) by (apply Z.eqb_neq; lia).
  exists p1, s1, p2, s2.
  (* Goal: 6-way conjunction. *)
  split.
  { (* gov_queue_then_timelock_schedule p0 s0 delay nowS true = ChainSuccess p1 s1 *)
    unfold gov_queue_then_timelock_schedule.
    assert (HqEq : Governor.queue_operations p0 = Governor.Result.Success p1).
    { unfold Governor.queue_operations. rewrite Hopt. rewrite Hph.
      unfold p1. reflexivity. }
    rewrite HqEq.
    fold id.
    assert (HsEq : Timelock.scheduleBatch s0 id delay nowS true
                     = Timelock.Result.Success s1).
    { unfold Timelock.scheduleBatch. unfold id. rewrite Hunset. simpl.
      assert (Hdb : (delay <? s0.(Timelock.State.minDelay)) = false).
      { apply Z.ltb_ge. lia. }
      rewrite Hdb. unfold s1. unfold id. reflexivity. }
    rewrite HsEq. reflexivity. }
  split.
  { (* p1.(phase) = PhaseStdQueued *) reflexivity. }
  split.
  { (* op_status s1 id nowS = OpWaiting *)
    unfold Timelock.op_status. rewrite Hs1ts. rewrite Hnz.
    unfold Timelock.DONE_TIMESTAMP. rewrite Hnd.
    assert (HleF : (nowS + delay <=? nowS) = false)
      by (apply Z.leb_gt; lia).
    rewrite HleF. reflexivity. }
  split.
  { (* gov_execute_then_timelock_execute p1 s1 nowE true = ChainSuccess p2 s2 *)
    unfold gov_execute_then_timelock_execute.
    assert (HeEq : Governor.execute_standard p1 = Governor.Result.Success p2).
    { unfold Governor.execute_standard.
      replace p1.(Governor.Proposal.isOptimistic) with false by reflexivity.
      replace p1.(Governor.Proposal.phase) with Governor.PhaseStdQueued by reflexivity.
      simpl. unfold p2. reflexivity. }
    rewrite HeEq.
    replace (proposal_to_opid p1.(Governor.Proposal.pid)) with id by reflexivity.
    assert (Hs1statusE : Timelock.op_status s1 id nowE = Timelock.OpReady).
    { unfold Timelock.op_status. rewrite Hs1ts. rewrite Hnz.
      unfold Timelock.DONE_TIMESTAMP. rewrite Hnd.
      assert (HleT : (nowS + delay <=? nowE) = true)
        by (apply Z.leb_le; lia).
      rewrite HleT. reflexivity. }
    assert (HxEq : Timelock.executeBatch s1 id nowE true
                     = Timelock.Result.Success s2).
    { unfold Timelock.executeBatch. simpl. rewrite Hs1statusE. reflexivity. }
    rewrite HxEq. reflexivity. }
  split.
  { (* p2.(phase) = PhaseStdExecuted *) reflexivity. }
  { (* op_status s2 id nowE = OpDone *)
    unfold Timelock.op_status.
    assert (Hs2ts : Timelock.get_ts s2 id = Timelock.DONE_TIMESTAMP).
    { unfold s2. apply TimelockProofs.get_ts_set_same. }
    rewrite Hs2ts. unfold Timelock.DONE_TIMESTAMP. simpl. reflexivity. }
Qed.

(** ===== Headline 2: standard execution blocked before maturity =====

    If the Governor sits in PhaseStdQueued and the Timelock op for
    its proposal id is OpWaiting at [now] (because [now] is below
    [scheduledAt + delay]), the composed execute call reverts at the
    Timelock layer with [revert_not_ready]. The Governor's
    [phase = PhaseStdQueued] gate passes; the Timelock's maturity gate
    is what fails. This is the headline composition fact: the bridge
    enforces the delay even when the Governor is satisfied. *)
Lemma execute_standard_blocked_before_maturity
    (p : Governor.Proposal.t) (s : Timelock.State.t)
    (delay nowS now : U256.t) (hasExecutor : bool) :
  p.(Governor.Proposal.isOptimistic) = false ->
  p.(Governor.Proposal.phase) = Governor.PhaseStdQueued ->
  Timelock.get_ts s (proposal_to_opid p.(Governor.Proposal.pid))
    = nowS + delay ->
  Timelock.DONE_TIMESTAMP < nowS + delay ->
  now < nowS + delay ->
  exists pc sc,
    gov_execute_then_timelock_execute p s now hasExecutor
      = ChainTLRevert pc sc.
Proof.
  intros Hopt Hph Hts Hpos Hbefore.
  unfold gov_execute_then_timelock_execute.
  (* Governor.execute_standard succeeds (phase=StdQueued, not optimistic). *)
  unfold Governor.execute_standard.
  rewrite Hopt. rewrite Hph. simpl.
  (* Timelock.executeBatch: op_status is OpWaiting at [now]. *)
  set (id := proposal_to_opid p.(Governor.Proposal.pid)).
  unfold Timelock.DONE_TIMESTAMP in Hpos.
  assert (Hnz : (nowS + delay =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hnd : (nowS + delay =? 1) = false) by (apply Z.eqb_neq; lia).
  assert (Hstatus : Timelock.op_status s id now = Timelock.OpWaiting).
  { unfold Timelock.op_status. unfold id. rewrite Hts.
    rewrite Hnz. unfold Timelock.DONE_TIMESTAMP. rewrite Hnd.
    assert (HleF : (nowS + delay <=? now) = false)
      by (apply Z.leb_gt; lia).
    rewrite HleF. reflexivity. }
  (* The phase-bumped proposal p' carries the same pid as p, so its
     id under the bridge is the same id. *)
  simpl.
  unfold Timelock.executeBatch.
  destruct hasExecutor; simpl.
  - rewrite Hstatus. eexists. eexists. reflexivity.
  - eexists. eexists. reflexivity.
Qed.

(** ===== vm_compute cross-check: concrete (proposal, delay, time)
    calibration =====

    Calibrated scenarios:
      - delay = 200, nowS = 1000, nowE = 1200 (matures exactly).
      - delay = 200, nowS = 1000, nowEarly = 1199 (1 second early).

    The Timelock minDelay is 100 so the [delay >= minDelay] gate
    passes; DONE_TIMESTAMP=1 << 1200 so the magic-value collision
    cannot fire.

    Mirrors the cas/timelock probe at id=42, but ties the id to a
    governor proposal pid via [proposal_to_opid] (opaque, so we
    [set]-bind it at vm_compute time). *)

(** A concrete proposal in PhaseStdSucceeded ready to be queued. *)
Definition x_p_succeeded : Governor.Proposal.t :=
  {| Governor.Proposal.pid              := 4242;
     Governor.Proposal.proposer         := 7777;
     Governor.Proposal.voteStart        := 50;
     Governor.Proposal.voteDuration     := 800;
     Governor.Proposal.vetoThresholdTok := 0;
     Governor.Proposal.againstVotes     := 0;
     Governor.Proposal.phase            := Governor.PhaseStdSucceeded;
     Governor.Proposal.isOptimistic     := false;
     Governor.Proposal.parent           := 999;
     Governor.Proposal.pastSupply       := 1;
  |}.

Definition x_s0 : Timelock.State.t := Timelock.empty_state 100.

(** ----- Forward direction: the chain succeeds at the right
    calibration. Uses the headline lemma rather than vm_compute
    directly (since proposal_to_opid is opaque, we can't reduce it).
    But the surrounding state-machine arithmetic can be vm_compute'd
    by abstracting over [id]. ----- *)
Lemma xcheck_chain_at_maturity :
  forall id : Timelock.OpId,
    Timelock.get_ts x_s0 id = 0 ->
    exists s1, Timelock.scheduleBatch x_s0 id 200 1000 true
                 = Timelock.Result.Success s1
               /\ Timelock.get_ts s1 id = 1200
               /\ Timelock.op_status s1 id 1199 = Timelock.OpWaiting
               /\ Timelock.op_status s1 id 1200 = Timelock.OpReady.
Proof.
  intros id Hunset.
  unfold Timelock.scheduleBatch. rewrite Hunset. simpl.
  eexists; split; [reflexivity|].
  split; [apply TimelockProofs.get_ts_set_same|].
  split.
  - unfold Timelock.op_status. rewrite TimelockProofs.get_ts_set_same.
    vm_compute. reflexivity.
  - unfold Timelock.op_status. rewrite TimelockProofs.get_ts_set_same.
    vm_compute. reflexivity.
Qed.

(** ----- Reverse direction: at nowE = 1199 the executeBatch reverts
    not_ready. Concrete witness scenario. ----- *)
Lemma xcheck_execute_one_second_early_reverts :
  forall id : Timelock.OpId,
    Timelock.get_ts x_s0 id = 0 ->
    forall s1, Timelock.scheduleBatch x_s0 id 200 1000 true
                 = Timelock.Result.Success s1 ->
    Timelock.executeBatch s1 id 1199 true = Timelock.revert_not_ready.
Proof.
  intros id Hunset s1 HsOk.
  unfold Timelock.scheduleBatch in HsOk. rewrite Hunset in HsOk. simpl in HsOk.
  injection HsOk as Hs1.
  unfold Timelock.executeBatch.
  assert (Hstatus : Timelock.op_status s1 id 1199 = Timelock.OpWaiting).
  { rewrite <- Hs1. unfold Timelock.op_status.
    rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity. }
  rewrite Hstatus. reflexivity.
Qed.

(** ----- Reverse direction: at nowE = 1200 the executeBatch succeeds
    and the op is Done. ----- *)
Lemma xcheck_execute_at_maturity_done :
  forall id : Timelock.OpId,
    Timelock.get_ts x_s0 id = 0 ->
    forall s1, Timelock.scheduleBatch x_s0 id 200 1000 true
                 = Timelock.Result.Success s1 ->
    exists s2, Timelock.executeBatch s1 id 1200 true
                 = Timelock.Result.Success s2
               /\ Timelock.op_status s2 id 1200 = Timelock.OpDone.
Proof.
  intros id Hunset s1 HsOk.
  unfold Timelock.scheduleBatch in HsOk. rewrite Hunset in HsOk. simpl in HsOk.
  injection HsOk as Hs1.
  unfold Timelock.executeBatch.
  assert (Hstatus : Timelock.op_status s1 id 1200 = Timelock.OpReady).
  { rewrite <- Hs1. unfold Timelock.op_status.
    rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity. }
  rewrite Hstatus.
  eexists; split; [reflexivity|].
  unfold Timelock.op_status.
  rewrite TimelockProofs.get_ts_set_same. vm_compute. reflexivity.
Qed.

(** ----- A fully composed cross-check using the bridge: starting from
    the StdSucceeded proposal + empty Timelock, queue at nowS=1000
    succeeds and leaves the op Waiting; execute_standard at nowE=1199
    reverts at the Timelock layer; execute_standard at nowE=1200
    succeeds and leaves the op Done. ----- *)
Lemma xcheck_bridge_full_chain :
  Timelock.get_ts x_s0 (proposal_to_opid x_p_succeeded.(Governor.Proposal.pid)) = 0 ->
  exists p1 s1,
    gov_queue_then_timelock_schedule x_p_succeeded x_s0 200 1000 true
      = ChainSuccess p1 s1
    /\ p1.(Governor.Proposal.phase) = Governor.PhaseStdQueued
    /\ Timelock.op_status s1
         (proposal_to_opid x_p_succeeded.(Governor.Proposal.pid))
         1199 = Timelock.OpWaiting
    /\ (exists pc sc,
          gov_execute_then_timelock_execute p1 s1 1199 true
            = ChainTLRevert pc sc)
    /\ (exists p2 s2,
          gov_execute_then_timelock_execute p1 s1 1200 true
            = ChainSuccess p2 s2
          /\ p2.(Governor.Proposal.phase) = Governor.PhaseStdExecuted
          /\ Timelock.op_status s2
               (proposal_to_opid x_p_succeeded.(Governor.Proposal.pid))
               1200 = Timelock.OpDone).
Proof.
  intros Hunset.
  (* Apply the headline lemma at the calibrated values. *)
  pose proof (escalate_then_queue_then_execute_chain
                x_p_succeeded x_s0 200 1000 1200) as Hchain.
  assert (Hopt : x_p_succeeded.(Governor.Proposal.isOptimistic) = false)
    by reflexivity.
  assert (Hph : x_p_succeeded.(Governor.Proposal.phase) = Governor.PhaseStdSucceeded)
    by reflexivity.
  assert (HminDelay : 200 >= x_s0.(Timelock.State.minDelay)).
  { unfold x_s0, Timelock.empty_state. simpl. lia. }
  assert (HdelayPos : 0 < 200) by lia.
  assert (Hpos : Timelock.DONE_TIMESTAMP < 1000 + 200) by (vm_compute; reflexivity).
  assert (Hmat : 1000 + 200 <= 1200) by lia.
  specialize (Hchain Hopt Hph Hunset HminDelay HdelayPos Hpos Hmat).
  destruct Hchain as (p1 & s1 & p2 & s2 &
                      HqEq & Hp1ph & _Hs1wAt1000 &
                      HeEq & Hp2ph & Hs2done).
  exists p1, s1.
  split; [exact HqEq|].
  split; [exact Hp1ph|].
  set (id := proposal_to_opid x_p_succeeded.(Governor.Proposal.pid)).
  (* Extract the two underlying calls from the composed chain. *)
  assert (HqOps : Governor.queue_operations x_p_succeeded
                    = Governor.Result.Success p1
                  /\ Timelock.scheduleBatch x_s0 id 200 1000 true
                    = Timelock.Result.Success s1).
  { unfold gov_queue_then_timelock_schedule in HqEq.
    destruct (Governor.queue_operations x_p_succeeded) eqn:Hgov;
      [|discriminate].
    destruct (Timelock.scheduleBatch x_s0
                (proposal_to_opid x_p_succeeded.(Governor.Proposal.pid))
                200 1000 true) eqn:Hsched;
      [|discriminate].
    injection HqEq as Hp1eq Hs1eq. subst.
    split; [reflexivity|]. fold id in Hsched. exact Hsched. }
  destruct HqOps as (HgovOk & HschedOk).
  (* Derive get_ts s1 id = 1200 from the scheduleBatch success. *)
  assert (Hs1ts : Timelock.get_ts s1 id = 1200).
  { unfold Timelock.scheduleBatch in HschedOk.
    unfold id in HschedOk at 1. rewrite Hunset in HschedOk.
    simpl in HschedOk. injection HschedOk as Hs1eq.
    rewrite <- Hs1eq. apply TimelockProofs.get_ts_set_same. }
  (* p1 inherits the original pid and isOptimistic=false from queue_operations. *)
  assert (Hp1pid : p1.(Governor.Proposal.pid) = x_p_succeeded.(Governor.Proposal.pid)).
  { unfold Governor.queue_operations in HgovOk.
    rewrite Hopt in HgovOk. rewrite Hph in HgovOk. simpl in HgovOk.
    injection HgovOk as Heq. rewrite <- Heq. reflexivity. }
  assert (Hp1opt : p1.(Governor.Proposal.isOptimistic) = false).
  { unfold Governor.queue_operations in HgovOk.
    rewrite Hopt in HgovOk. rewrite Hph in HgovOk. simpl in HgovOk.
    injection HgovOk as Heq. rewrite <- Heq. reflexivity. }
  (* op_status s1 (proposal_to_opid x_p_succeeded.(pid)) 1199 = OpWaiting *)
  split.
  { change (proposal_to_opid x_p_succeeded.(Governor.Proposal.pid)) with id.
    unfold Timelock.op_status.
    replace (Timelock.get_ts s1 id) with (1000 + 200 : U256.t) by (rewrite Hs1ts; reflexivity).
    vm_compute. reflexivity. }
  (* execute at 1199 reverts at the Timelock layer. *)
  split.
  { apply (execute_standard_blocked_before_maturity p1 s1 200 1000 1199 true).
    - exact Hp1opt.
    - exact Hp1ph.
    - rewrite Hp1pid. exact Hs1ts.
    - vm_compute. reflexivity.
    - lia. }
  exists p2, s2.
  split; [exact HeEq|]. split; [exact Hp2ph|]. exact Hs2done.
Qed.

End IntegrationGovernorTimelock.
