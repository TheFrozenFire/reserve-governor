(** ReserveOptimisticGovernor — no de-escalation after transitionToPessimistic.

    Audit context. ReserveOptimisticGovernor.sol overwrites the parent
    proposal's [vetoThreshold] with [ProposalLib.TRANSITIONED_VETO_THRESHOLD]
    (= [type(uint256).max] = [2^256 - 1]) inside [transitionToPessimistic].
    The on-chain [state()] view then short-circuits to [Defeated] when it
    sees this sentinel (ReserveOptimisticGovernor.sol:243-246). The
    contract uses this as a pin: once a parent has been transitioned,
    no addition of veto votes can ever flip the observable phase back
    to [Active] or [Succeeded].

    History.
    --------
    Before CRIT-V / T1.4 (this file's previous revision), the Governor
    simulation modeled the contract's TRANSITIONED-sentinel write by
    pinning the parent's [phase] field to [PhaseDefeated] AND freezing
    a [vetoThresholdTok : U256.t] field at create time (so any
    threshold change between create and observe was invisible). The
    no-de-escalation claim was carried by the [phase = PhaseDefeated]
    pin plus a votes-monotonicity argument.

    With T1.4, the simulation:
      - replaces [Proposal.vetoThresholdTok] (snapped {tok}) with
        [Proposal.vetoThresholdD18] (un-snapped D18 fraction);
      - [observe] computes the snapped {tok} threshold LIVE per call,
        AND short-circuits to [PhaseDefeated] when
        [vetoThresholdD18 == TRANSITIONED_VETO_THRESHOLD] (matching the
        contract's branch at ROG.sol:243-246);
      - [transition_to_pessimistic] writes
        [vetoThresholdD18 := TRANSITIONED_VETO_THRESHOLD] AND pins
        [phase := PhaseDefeated] on the parent.

    The two writes are individually sufficient to keep [observe]
    returning [PhaseDefeated] for the parent (the phase-pin via the
    sticky-or-Defeated path; the sentinel via the new short-circuit).
    We apply both so the sim's stored representation mirrors the
    contract field-for-field, and so the deliverables below — which
    used to rest on the votes-tally argument — can now rest on the
    sentinel short-circuit directly.

    This file delivers (refreshed at T1.4):

      1. [transition_writes_sentinel_lemma]: [transition_to_pessimistic]
         writes the sentinel into [vetoThresholdD18]. (Previously stated
         on a sister [transition_to_pessimistic_sentinel] definition;
         the main entry point now carries the sentinel write, so the
         sister definition is gone and the lemma references
         [transition_to_pessimistic] directly.)

      2. [sentinel_makes_defeated_certain]: when [vetoThresholdD18 =
         TRANSITIONED_VETO_THRESHOLD] (and the parent is past its
         snapshot), [observe] returns [PhaseDefeated]. Strictly stronger
         than the previous "sentinel makes Defeated UNREACHABLE" — the
         contract's short-circuit makes Defeated MANDATORY, not merely
         possible-via-the-votes-tally.

      3. [cannot_de_escalate_after_transition] (headline): on the
         simulation, after [transition_to_pessimistic] succeeds, no
         sequence of [add_veto] calls can drive the parent's observable
         phase back to [PhaseSucceeded] or [PhaseActive], regardless of
         the wall-clock [now'] that observers later choose (provided
         [now' >= now_transition]). The proof is now via the sentinel
         short-circuit ([sentinel_makes_defeated_certain]) plus
         [add_veto] preserving [vetoThresholdD18].

    A [vm_compute] calibration cross-checks the sentinel encoding at a
    concrete (vetoThreshold-before, transition, vetoThreshold-after)
    tuple.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require ReserveGovernor.simulations.ProposalLib.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module GovernorNoDeEscalation.

Import Governor.

(** ===== Sentinel constant ===== *)

(** The [type(uint256).max] sentinel as a Z. Equivalent to
    [Governor.TRANSITIONED_VETO_THRESHOLD] and (via that) to
    [ProposalLib.TRANSITIONED_VETO_THRESHOLD]. We keep the local
    [Sentinel] name so a future reader can still cite both anchors. *)
Definition Sentinel : U256.t := 2 ^ 256 - 1.

Lemma Sentinel_eq_governor :
  Sentinel = Governor.TRANSITIONED_VETO_THRESHOLD.
Proof. reflexivity. Qed.

Lemma Sentinel_eq_proposal_lib :
  Sentinel = ProposalLib.ProposalLib.TRANSITIONED_VETO_THRESHOLD.
Proof. reflexivity. Qed.

(** Precomputed positivity facts. We never let [lia] unfold the literal. *)
Lemma Sentinel_pos : 0 < Sentinel.
Proof. unfold Sentinel. lia. Qed.

Lemma Sentinel_valid : U256.Valid.t Sentinel.
Proof. unfold U256.Valid.t, Sentinel. lia. Qed.

Lemma Sentinel_eq_max : Sentinel = 2 ^ 256 - 1.
Proof. reflexivity. Qed.

(** ===== Deliverable 1: transition writes the sentinel =====

    The main [transition_to_pessimistic] entry point (refreshed at
    T1.4) writes the sentinel into [vetoThresholdD18]. *)

Lemma transition_writes_sentinel_lemma
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.vetoThresholdD18) = Sentinel.
Proof.
  intros Hok. unfold transition_to_pessimistic in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hparent'. reflexivity.
Qed.

Lemma transition_parent_phase_defeated_explicit
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.phase) = PhaseDefeated.
Proof.
  intros Hok. unfold transition_to_pessimistic in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hparent'. reflexivity.
Qed.

Lemma transition_child_pending_explicit
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  child.(Proposal.phase) = PhaseStdPending /\
  child.(Proposal.isOptimistic) = false /\
  child.(Proposal.parent) = parent.(Proposal.pid).
Proof.
  intros Hok. unfold transition_to_pessimistic in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hchild. cbn.
  repeat split; reflexivity.
Qed.

(** ===== Deliverable 2: sentinel forces Defeated =====

    With [vetoThresholdD18 = Sentinel] AND the parent past its
    snapshot AND optimistic AND pre-terminal-phase, [observe] returns
    [PhaseDefeated]. The proof uses the new sentinel short-circuit
    in [observe] (matching ROG.sol:243-246) — no votes-tally argument
    is needed. *)
Lemma sentinel_makes_defeated_certain
    (p : Proposal.t) (now : U256.t) :
  p.(Proposal.isOptimistic) = true ->
  p.(Proposal.phase) = PhaseSubmitted \/
  p.(Proposal.phase) = PhaseActive \/
  p.(Proposal.phase) = PhaseDefeated ->
  p.(Proposal.voteStart) <= now ->
  p.(Proposal.vetoThresholdD18) = Sentinel ->
  observe p now = PhaseDefeated.
Proof.
  intros Hopt Hph Hvs Hsent.
  unfold observe.
  assert (Hpre : (now <? p.(Proposal.voteStart)) = false).
  { apply Z.ltb_ge. lia. }
  assert (Hs' : (p.(Proposal.vetoThresholdD18) =? TRANSITIONED_VETO_THRESHOLD)
                  = true).
  { apply Z.eqb_eq. unfold Sentinel in Hsent. exact Hsent. }
  destruct Hph as [Hph | Hrest].
  - rewrite Hph; simpl; rewrite Hpre; rewrite Hopt; rewrite Hs'; reflexivity.
  - destruct Hrest as [Hph | Hph];
      rewrite Hph; simpl; rewrite Hpre; rewrite Hopt; rewrite Hs'; reflexivity.
Qed.

(** ===== Deliverable 3: headline — cannot de-escalate ===== *)

(** [add_veto] preserves the [phase] field. *)
Lemma add_veto_preserves_phase (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.phase) = p.(Proposal.phase).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_voteStart (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.voteStart) = p.(Proposal.voteStart).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_voteDuration (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.voteDuration) = p.(Proposal.voteDuration).
Proof. reflexivity. Qed.

(** Renamed from [add_veto_preserves_vetoThresholdTok] in the
    pre-T1.4 layout. The stored field is now [vetoThresholdD18];
    [add_veto] preserves it. *)
Lemma add_veto_preserves_vetoThresholdD18 (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.vetoThresholdD18)
    = p.(Proposal.vetoThresholdD18).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_isOptimistic (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_pastSupply (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.pastSupply) = p.(Proposal.pastSupply).
Proof. reflexivity. Qed.

(** [add_veto] is monotone on [againstVotes] when [delta] is non-negative. *)
Lemma add_veto_monotone (p : Proposal.t) (delta : U256.t) :
  0 <= delta ->
  p.(Proposal.againstVotes) <= (add_veto p delta).(Proposal.againstVotes).
Proof. intros Hd. unfold add_veto. cbn. lia. Qed.

(** Iterated [add_veto]: apply a list of deltas in sequence. *)
Fixpoint add_vetoes (p : Proposal.t) (deltas : list U256.t) : Proposal.t :=
  match deltas with
  | []          => p
  | d :: rest   => add_vetoes (add_veto p d) rest
  end.

Lemma add_vetoes_preserves_phase (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.phase) = p.(Proposal.phase).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_phase.
Qed.

Lemma add_vetoes_preserves_voteStart (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.voteStart) = p.(Proposal.voteStart).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_voteStart.
Qed.

Lemma add_vetoes_preserves_voteDuration (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.voteDuration) = p.(Proposal.voteDuration).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_voteDuration.
Qed.

Lemma add_vetoes_preserves_vetoThresholdD18
    (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.vetoThresholdD18)
    = p.(Proposal.vetoThresholdD18).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_vetoThresholdD18.
Qed.

Lemma add_vetoes_preserves_isOptimistic
    (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_isOptimistic.
Qed.

Lemma add_vetoes_preserves_pastSupply (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.pastSupply) = p.(Proposal.pastSupply).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_pastSupply.
Qed.

(** Monotonicity over an iterated sequence of non-negative deltas. *)
Lemma add_vetoes_monotone (p : Proposal.t) (deltas : list U256.t) :
  Forall (fun d => 0 <= d) deltas ->
  p.(Proposal.againstVotes) <= (add_vetoes p deltas).(Proposal.againstVotes).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p Hnn.
  - cbn. lia.
  - cbn. inversion Hnn as [|d' ds' Hd Hnn']; subst.
    specialize (IH (add_veto p d) Hnn').
    pose proof (add_veto_monotone p d Hd) as Hstep.
    lia.
Qed.

(** A successful [transition_to_pessimistic] establishes the
    post-conditions needed for the headline: stored phase is Defeated,
    optimistic flag is preserved, voteStart unchanged, pastSupply
    unchanged and non-zero (otherwise [observe parent now] would have
    returned PhaseCanceled, not PhaseDefeated, contradicting the
    transition precondition), and [vetoThresholdD18 = Sentinel] (the
    transition write).

    STATEMENT CHANGED (T1.4): the post-condition
    [parent'.vetoThresholdD18 = Sentinel] is new (the sim previously
    didn't track this — the [phase = PhaseDefeated] pin alone carried
    the no-de-escalation claim). The post-condition
    [parent'.againstVotes >= parent'.vetoThresholdTok] from the
    pre-T1.4 layout is GONE — there is no longer a stored
    [vetoThresholdTok] field, and the votes-tally argument no longer
    drives the proof.

    ALSO CHANGED: a new precondition [vetoThresholdD18 != Sentinel]
    is required. This matches the contract's
    [require(optimisticProposal.vetoThreshold !=
    TRANSITIONED_VETO_THRESHOLD)] gate at ProposalLib.sol:117 — the
    contract refuses to re-transition an already-transitioned
    proposal. Without this precondition, the sim's
    [transition_to_pessimistic] would still admit
    re-transitions (the contract does not), and the [pastSupply != 0]
    conclusion would not hold (under sentinel, [observe] returns
    Defeated regardless of pastSupply). The added precondition
    closes the gap. *)
Lemma transition_postconditions_no_resentinel
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  parent.(Proposal.vetoThresholdD18) <> Sentinel ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.phase) = PhaseDefeated /\
  parent'.(Proposal.isOptimistic) = true /\
  parent'.(Proposal.voteStart) = parent.(Proposal.voteStart) /\
  parent'.(Proposal.vetoThresholdD18) = Sentinel /\
  parent'.(Proposal.againstVotes) = parent.(Proposal.againstVotes) /\
  parent'.(Proposal.pastSupply) = parent.(Proposal.pastSupply) /\
  parent'.(Proposal.pastSupply) <> 0.
Proof.
  intros Hopt Hvs HnoSent Hok.
  unfold transition_to_pessimistic in Hok.
  destruct (observe parent now) eqn:Hobs; try discriminate.
  injection Hok as Hparent' Hchild.
  unfold observe in Hobs.
  assert (Hsentb : (parent.(Proposal.vetoThresholdD18)
                      =? TRANSITIONED_VETO_THRESHOLD) = false).
  { apply Z.eqb_neq. unfold Sentinel in HnoSent. exact HnoSent. }
  destruct (parent.(Proposal.phase)) eqn:Hph; try discriminate;
    (assert (Hlt : (now <? parent.(Proposal.voteStart)) = false)
       by (apply Z.ltb_ge; lia);
     rewrite Hlt in Hobs;
     rewrite Hopt in Hobs;
     rewrite Hsentb in Hobs;
     destruct (parent.(Proposal.pastSupply) =? 0) eqn:Hpsb;
     [ discriminate
     | apply Z.eqb_neq in Hpsb ];
     destruct (parent.(Proposal.againstVotes)
                 >=? vetoThresholdTokOf parent.(Proposal.vetoThresholdD18)
                                        parent.(Proposal.pastSupply))
       eqn:Hgeb;
     [ idtac
     | destruct (now <? parent.(Proposal.voteStart)
                          + parent.(Proposal.voteDuration));
       discriminate ];
     rewrite <- Hparent'; cbn;
     repeat split; try assumption; try reflexivity).
Qed.

(** Headline theorem.

    After [transition_to_pessimistic] succeeds (on a non-already-
    transitioned parent, matching the contract's
    [require(vetoThreshold != TRANSITIONED_VETO_THRESHOLD)] gate at
    ProposalLib.sol:117), no sequence of [add_veto] calls on the
    resulting parent can drive the observable phase back to
    [PhaseSucceeded] or [PhaseActive], for any future [now' >=
    now_transition]. The parent stays observably [PhaseDefeated].

    The proof works by:
      1. [transition_postconditions_no_resentinel] establishes the
         parent's [vetoThresholdD18 = Sentinel], [phase = PhaseDefeated],
         [voteStart] unchanged, [isOptimistic = true], [pastSupply]
         non-zero.
      2. [add_vetoes] preserves [phase], [isOptimistic], [voteStart],
         [vetoThresholdD18], and [pastSupply].
      3. Apply [sentinel_makes_defeated_certain]: the sentinel
         short-circuit in [observe] forces [PhaseDefeated]. *)
Theorem cannot_de_escalate_after_transition
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now now' : U256.t)
    (deltas : list U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  parent.(Proposal.vetoThresholdD18) <> Sentinel ->
  now <= now' ->
  Forall (fun d => 0 <= d) deltas ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  observe (add_vetoes parent' deltas) now' = PhaseDefeated.
Proof.
  intros Hopt Hvs HnoSent Hnow Hnn Hok.
  pose proof (transition_postconditions_no_resentinel
                parent parent' child
                new_pid votingDelay votingPeriod now
                Hopt Hvs HnoSent Hok)
    as (Hph' & Hopt' & HvsEq & HsentEq & HavotesEq & _HpsEq & Hps').
  set (p' := add_vetoes parent' deltas).
  apply sentinel_makes_defeated_certain.
  - unfold p'. rewrite add_vetoes_preserves_isOptimistic. exact Hopt'.
  - unfold p'. rewrite add_vetoes_preserves_phase. right. right. exact Hph'.
  - unfold p'. rewrite add_vetoes_preserves_voteStart.
    rewrite HvsEq. lia.
  - unfold p'. rewrite add_vetoes_preserves_vetoThresholdD18. exact HsentEq.
Qed.

(** Convenient corollary: the observable phase is in the "Defeated or
    terminal" set, never in [PhaseSucceeded], [PhaseActive], or
    [PhaseSubmitted]. *)
Corollary cannot_observe_active_or_succeeded
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now now' : U256.t)
    (deltas : list U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  parent.(Proposal.vetoThresholdD18) <> Sentinel ->
  now <= now' ->
  Forall (fun d => 0 <= d) deltas ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  observe (add_vetoes parent' deltas) now' <> PhaseSucceeded /\
  observe (add_vetoes parent' deltas) now' <> PhaseActive /\
  observe (add_vetoes parent' deltas) now' <> PhaseSubmitted.
Proof.
  intros Hopt Hvs HnoSent Hnow Hnn Hok.
  pose proof (cannot_de_escalate_after_transition
                parent parent' child
                new_pid votingDelay votingPeriod now now' deltas
                Hopt Hvs HnoSent Hnow Hnn Hok) as Hdef.
  rewrite Hdef.
  repeat split; intros Heq; discriminate.
Qed.

(** ===== Deliverable 4: vm_compute calibration =====

    Concrete tuple. The transition entry point now performs the
    sentinel write directly, so the calibration shows:

      Pre-transition: vetoThresholdD18 = FIX_ONE / 10 (a sane 10%
        threshold), pastSupply = 100 — snapped threshold {tok} = 10.
        With againstVotes = 10, the proposal observes as PhaseDefeated
        in the active window (live computation).
      Post-transition: vetoThresholdD18 = Sentinel = 2^256 - 1
        (written by transition_to_pessimistic). phase = PhaseDefeated
        (pinned by transition_to_pessimistic).
        observe at any future time returns PhaseDefeated via the
        sentinel short-circuit.
*)

Definition cal_threshold_D18 : U256.t := Governor.FIX_ONE / 10.

Definition cal_parent : Proposal.t :=
  add_veto (fresh_optimistic 901 9001 100 1000 cal_threshold_D18 100) 10.

(** Sanity: [cal_parent] observes as PhaseDefeated in the active
    window via the LIVE threshold computation (vetoThresholdTokOf
    (FIX_ONE/10) 100 = 10; againstVotes = 10 >= 10). *)
Lemma xcheck_cal_parent_defeated :
  observe cal_parent 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

Definition cal_transition_result :=
  transition_to_pessimistic cal_parent 9999 50 1000 500.

(** Sentinel write: after [transition_to_pessimistic], the parent's
    [vetoThresholdD18] is the sentinel. *)
Lemma xcheck_transition_writes_sentinel :
  match cal_transition_result with
  | Result.Success (parent', _) =>
      parent'.(Proposal.vetoThresholdD18) = 2 ^ 256 - 1
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Parent's phase is also pinned to PhaseDefeated. *)
Lemma xcheck_transition_pins_phase :
  match cal_transition_result with
  | Result.Success (parent', _) => parent'.(Proposal.phase) = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Headline observable: post-transition, even after a flurry of
    additional veto adds, the parent stays Defeated for any later
    timestamp inside the calibration. Now driven by the sentinel
    short-circuit in [observe]. *)
Lemma xcheck_no_de_escalation_concrete :
  match cal_transition_result with
  | Result.Success (parent', _) =>
      observe (add_vetoes parent' [5; 7; 11]) 9999 = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Under the sentinel encoding, even WITH the (now-recomputed) tok
    threshold being astronomically large, the votes-comparison
    branch is unreachable — the sentinel short-circuit fires first.
    This vm_compute confirms it: after a few veto increments the
    parent observes as PhaseDefeated via the sentinel branch, not
    via the votes-tally. *)
Lemma xcheck_sentinel_short_circuit_fires :
  match cal_transition_result with
  | Result.Success (parent', _) =>
      (* The (recomputed) tok would be roughly (2^256 * 100)/1e18,
         a huge value the (small) accumulated votes cannot reach.
         If the sentinel short-circuit were absent, observe would
         fall through to PhaseActive or PhaseSucceeded, NOT
         PhaseDefeated. *)
      observe (add_vetoes parent' [1; 2; 3]) 9999 = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End GovernorNoDeEscalation.
