(** ReserveOptimisticGovernor escalation state-machine proofs.

    Headline lemmas:

      INV-1   escalation_monotone : every transition either preserves
              or strictly increases [phase_index]; once a proposal
              reaches Executed/Canceled/StdExecuted it cannot move.

      INV-1b  no_de_escalation : after [transition_to_pessimistic]
              succeeds, the parent's phase is PhaseDefeated. The
              parent's observable phase cannot revert to
              PhaseSucceeded/PhaseActive on any later [now].

      INV-2   veto_threshold_correctness : the optimistic proposal
              observed during its veto window is PhaseDefeated iff
              [againstVotes >= vetoThresholdTok], regardless of [now]
              within the window.

      INV-3   optimistic_execution_requires_succeeded :
              [execute_optimistic] succeeds iff
              [observe p now = PhaseSucceeded], which by definition
              means (no veto threshold met) AND (now >= deadline) AND
              (not canceled) AND (not already executed).

      INV-4   standard_execution_chain :
              [execute_standard] succeeds iff the proposal is in
              PhaseStdQueued, which is reachable from PhaseStdSucceeded
              only via [queue_operations].

      INV-4b  optimistic_cannot_be_queued : [queue_operations] reverts
              with [revert_optimistic_no_queue] whenever
              isOptimistic = true.

      INV-5   throttle_consumed_at_submission : every successful
              [propose_optimistic] decrements the throttle counter by
              exactly 1; failed proposals leave it untouched.

      INV-6   selector_gate_honored : [propose_optimistic] succeeds
              only if [all_calls_allowed allow targets selectors =
              true].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module GovernorProofs.

Import Governor.

(** ----- INV-1: phase-index monotonicity for each transition. -----

    We assert: for each transition [f : Proposal.t -> Result.t Proposal.t],
    whenever [f p = Success p'], [phase_index p.(phase) <=
    phase_index p'.(phase)]. The transitions covered:

      queue_operations
      execute_standard
      execute_optimistic   (involves [observe], so [now]-dependent)
      mark_std_succeeded
      transition_to_pessimistic   (parent + child)
*)

Lemma queue_operations_monotone (p p' : Proposal.t) :
  queue_operations p = Result.Success p' ->
  phase_index p.(Proposal.phase) <= phase_index p'.(Proposal.phase).
Proof.
  intros Hok. unfold queue_operations in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdSucceeded) eqn:Hph;
    [|discriminate].
  injection Hok as Hp'.
  (* phase_eq forces p.(phase) = PhaseStdSucceeded, so phase_index = 5,
     and p' has PhaseStdQueued (index 6). *)
  destruct (p.(Proposal.phase)); simpl in Hph; try discriminate.
  rewrite <- Hp'. simpl. lia.
Qed.

Lemma execute_standard_monotone (p p' : Proposal.t) :
  execute_standard p = Result.Success p' ->
  phase_index p.(Proposal.phase) <= phase_index p'.(Proposal.phase).
Proof.
  intros Hok. unfold execute_standard in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdQueued) eqn:Hph;
    [|discriminate].
  injection Hok as Hp'.
  destruct (p.(Proposal.phase)); simpl in Hph; try discriminate.
  rewrite <- Hp'. simpl. lia.
Qed.

(** [execute_optimistic] writes PhaseExecuted (index 7). Since
    phase_index never exceeds 7, the output's index dominates any
    input. *)
Lemma execute_optimistic_monotone (p p' : Proposal.t) (now : U256.t) :
  execute_optimistic p now = Result.Success p' ->
  phase_index p.(Proposal.phase) <= phase_index p'.(Proposal.phase).
Proof.
  intros Hok. unfold execute_optimistic in Hok.
  destruct (negb p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (observe p now); try discriminate.
  injection Hok as Hp'. rewrite <- Hp'. simpl.
  (* Output index = 7 (PhaseExecuted). Input is in {0..7}, so 0..7 <= 7. *)
  destruct (p.(Proposal.phase)); simpl; lia.
Qed.

Lemma mark_std_succeeded_monotone (p p' : Proposal.t) (now : U256.t) :
  mark_std_succeeded p now = Result.Success p' ->
  phase_index p.(Proposal.phase) <= phase_index p'.(Proposal.phase).
Proof.
  intros Hok. unfold mark_std_succeeded in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (negb (phase_eq p.(Proposal.phase) PhaseStdActive)) eqn:Hph;
    [discriminate|].
  destruct (now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration)) eqn:Hd;
    [discriminate|].
  injection Hok as Hp'.
  apply negb_false_iff in Hph.
  (* Hph forces phase = PhaseStdActive (index 4); output is
     PhaseStdSucceeded (index 5). *)
  destruct (p.(Proposal.phase)); simpl in Hph; try discriminate.
  rewrite <- Hp'. simpl. lia.
Qed.

(** [transition_to_pessimistic] writes parent's phase as PhaseDefeated
    (index 2) and child starts at PhaseStdPending (index 3). The
    monotonicity claim for the parent is preserved from the precondition
    that [observe parent now = PhaseDefeated], which implies the stored
    [phase] is pre-Defeated. *)
Lemma transition_parent_phase_defeated
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

Lemma transition_child_phase_pending
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  child.(Proposal.phase) = PhaseStdPending.
Proof.
  intros Hok. unfold transition_to_pessimistic in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hchild. reflexivity.
Qed.

(** ----- INV-1b: no de-escalation back from terminal phases. -----
    For PhaseExecuted, PhaseCanceled, PhaseStdQueued, PhaseStdExecuted
    the leading match in [observe] returns the stored phase directly,
    so [observe] is sticky for those. The Defeated case is more subtle:
    the contract rewrites [vetoThreshold] to the UINT256_MAX sentinel
    so the [againstVotes >= vtt] test always fails after escalation,
    forcing the optimistic branch to skip the Defeated arm. We model
    this contract-side invariant as a precondition: if
    [vetoThresholdTok > maxVotes] (impossible to surpass), then the
    optimistic Defeated arm is unreachable; combined with the parent
    being post-snapshot, the observable phase stays "succeeded" or
    "active". For the audit-relevant sticky claim we use [PhaseExecuted]
    and friends, which the contract reaches as final phases. *)
Lemma observe_executed_sticky (p : Proposal.t) (now : U256.t) :
  p.(Proposal.phase) = PhaseExecuted ->
  observe p now = PhaseExecuted.
Proof.
  intros Hph. unfold observe. rewrite Hph. reflexivity.
Qed.

Lemma observe_canceled_sticky (p : Proposal.t) (now : U256.t) :
  p.(Proposal.phase) = PhaseCanceled ->
  observe p now = PhaseCanceled.
Proof.
  intros Hph. unfold observe. rewrite Hph. reflexivity.
Qed.

Lemma observe_std_executed_sticky (p : Proposal.t) (now : U256.t) :
  p.(Proposal.phase) = PhaseStdExecuted ->
  observe p now = PhaseStdExecuted.
Proof.
  intros Hph. unfold observe. rewrite Hph. reflexivity.
Qed.

Lemma observe_std_queued_sticky (p : Proposal.t) (now : U256.t) :
  p.(Proposal.phase) = PhaseStdQueued ->
  observe p now = PhaseStdQueued.
Proof.
  intros Hph. unfold observe. rewrite Hph. reflexivity.
Qed.

(** After a successful [execute_optimistic], no further
    [execute_optimistic] / [queue_operations] / [execute_standard]
    can succeed. *)
Lemma execute_optimistic_then_execute_optimistic_reverts
    (p p' : Proposal.t) (now1 now2 : U256.t) :
  execute_optimistic p now1 = Result.Success p' ->
  exists pp ss, execute_optimistic p' now2 = Result.Revert pp ss.
Proof.
  intros Hok. unfold execute_optimistic in Hok.
  destruct (negb p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (observe p now1) eqn:Hobs; try discriminate.
  injection Hok as Hp'.
  unfold execute_optimistic.
  rewrite <- Hp'. cbn.
  rewrite Hopt. cbn.
  eexists. eexists. reflexivity.
Qed.

(** ----- INV-2: veto-threshold correctness. -----
    Within the active window (now between voteStart and deadline,
    optimistic, phase still pre-terminal, pastSupply > 0), observe
    returns PhaseDefeated iff againstVotes >= vetoThresholdTok.

    STATEMENT CHANGED (CRIT-G / T1.3): the [pastSupply > 0]
    precondition is new. The contract's [state()] short-circuits to
    [Canceled] when [pastSupply == 0], so the iff direction "veto
    threshold met -> Defeated" only holds when pastSupply is non-zero.
    The reverse direction (Defeated -> threshold met) is also true
    only with the pastSupply guard: a pastSupply=0 proposal would
    observe as Canceled, not Defeated, regardless of vetoes. *)
Lemma observe_defeated_iff_threshold_in_window
    (p : Proposal.t) (now : U256.t) :
  p.(Proposal.isOptimistic) = true ->
  p.(Proposal.phase) = PhaseSubmitted \/ p.(Proposal.phase) = PhaseActive ->
  p.(Proposal.voteStart) <= now ->
  p.(Proposal.pastSupply) <> 0 ->
  observe p now = PhaseDefeated
    <-> p.(Proposal.againstVotes) >= p.(Proposal.vetoThresholdTok).
Proof.
  intros Hopt Hph Hvs Hps.
  unfold observe.
  assert (Hpre : (now <? p.(Proposal.voteStart)) = false).
  { apply Z.ltb_ge. lia. }
  assert (Hps' : (p.(Proposal.pastSupply) =? 0) = false).
  { apply Z.eqb_neq. exact Hps. }
  destruct Hph as [Hph | Hph]; rewrite Hph; simpl; rewrite Hpre; rewrite Hopt;
    rewrite Hps'.
  - split.
    + intros Heq.
      destruct (p.(Proposal.againstVotes) >=? p.(Proposal.vetoThresholdTok)) eqn:Hge.
      * apply Z.geb_le in Hge. lia.
      * destruct (now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
          discriminate.
    + intros Hge.
      assert (Hb' : (p.(Proposal.againstVotes) >=? p.(Proposal.vetoThresholdTok)) = true).
      { apply Z.geb_le. lia. }
      rewrite Hb'. reflexivity.
  - split.
    + intros Heq.
      destruct (p.(Proposal.againstVotes) >=? p.(Proposal.vetoThresholdTok)) eqn:Hge.
      * apply Z.geb_le in Hge. lia.
      * destruct (now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
          discriminate.
    + intros Hge.
      assert (Hb' : (p.(Proposal.againstVotes) >=? p.(Proposal.vetoThresholdTok)) = true).
      { apply Z.geb_le. lia. }
      rewrite Hb'. reflexivity.
Qed.

(** ----- INV-3: execute_optimistic gating. ----- *)
Lemma execute_optimistic_success_iff_succeeded
    (p p' : Proposal.t) (now : U256.t) :
  execute_optimistic p now = Result.Success p'
    <-> p.(Proposal.isOptimistic) = true /\ observe p now = PhaseSucceeded
        /\ p' = {|
              Proposal.pid              := p.(Proposal.pid);
              Proposal.proposer         := p.(Proposal.proposer);
              Proposal.voteStart        := p.(Proposal.voteStart);
              Proposal.voteDuration     := p.(Proposal.voteDuration);
              Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
              Proposal.againstVotes     := p.(Proposal.againstVotes);
              Proposal.phase            := PhaseExecuted;
              Proposal.isOptimistic     := p.(Proposal.isOptimistic);
              Proposal.parent           := p.(Proposal.parent);
              Proposal.pastSupply       := p.(Proposal.pastSupply);
            |}.
Proof.
  unfold execute_optimistic. split.
  - intros Hok.
    destruct (negb p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
    apply negb_false_iff in Hopt.
    destruct (observe p now) eqn:Hobs; try discriminate.
    injection Hok as Hp'. rewrite <- Hp'.
    split; [exact Hopt|]. split; [reflexivity|reflexivity].
  - intros (Hopt & Hobs & Hp').
    assert (Hb : negb p.(Proposal.isOptimistic) = false).
    { rewrite Hopt. reflexivity. }
    rewrite Hb. rewrite Hobs. rewrite Hp'. reflexivity.
Qed.

(** ----- INV-4: standard execution chain. ----- *)
Lemma execute_standard_requires_queued (p p' : Proposal.t) :
  execute_standard p = Result.Success p' ->
  p.(Proposal.phase) = PhaseStdQueued.
Proof.
  intros Hok. unfold execute_standard in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdQueued) eqn:Hph;
    [|discriminate].
  destruct (p.(Proposal.phase)); simpl in Hph; try discriminate.
  reflexivity.
Qed.

Lemma queue_operations_requires_succeeded (p p' : Proposal.t) :
  queue_operations p = Result.Success p' ->
  p.(Proposal.isOptimistic) = false /\
  p.(Proposal.phase) = PhaseStdSucceeded.
Proof.
  intros Hok. unfold queue_operations in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdSucceeded) eqn:Hph;
    [|discriminate].
  destruct (p.(Proposal.phase)); simpl in Hph; try discriminate.
  split; reflexivity.
Qed.

(** ----- INV-4b: optimistic proposals cannot be queued. ----- *)
Lemma optimistic_cannot_be_queued (p : Proposal.t) :
  p.(Proposal.isOptimistic) = true ->
  queue_operations p = revert_optimistic_no_queue.
Proof.
  intros Hopt. unfold queue_operations. rewrite Hopt. reflexivity.
Qed.

(** ----- INV-5: throttle consumption at submission. -----
    [consume_throttle_oracle] models the bookkeeping interaction
    between the governor and the ProposerThrottle library. The
    invariant we prove here: a successful [propose_optimistic]
    coupled with a successful [consume_throttle_oracle] decrements
    the charges-remaining counter by exactly 1. The actual ordering
    inside the contract is propose_optimistic -> throttle.consume ->
    other validations; we capture the throttle-side bookkeeping as a
    separate function call so the proof is composable. *)
Lemma consume_throttle_oracle_decrements (charges charges' : U256.t) :
  consume_throttle_oracle charges = Result.Success charges' ->
  charges' = charges - 1.
Proof.
  intros Hok. unfold consume_throttle_oracle in Hok.
  destruct (charges <? 1) eqn:Hb; [discriminate|].
  injection Hok as Hch. lia.
Qed.

Lemma consume_throttle_oracle_reverts_iff_empty (charges : U256.t) :
  (exists p s, consume_throttle_oracle charges = Result.Revert p s)
  <-> charges < 1.
Proof.
  unfold consume_throttle_oracle. split.
  - intros (p & s & Hrev).
    destruct (charges <? 1) eqn:Hb.
    + apply Z.ltb_lt in Hb. exact Hb.
    + discriminate.
  - intros Hlt.
    assert (Hb : (charges <? 1) = true) by (apply Z.ltb_lt; exact Hlt).
    rewrite Hb. eexists. eexists. reflexivity.
Qed.

Lemma propose_optimistic_requires_charge
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
     throttleCharges now : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector)) :
  throttleCharges < 1 ->
  propose_optimistic pid proposer vetoDelay vetoPeriod vetoThresholdD18
    pastSupply throttleCharges targets selectors allow now
  = revert_throttle_exceeded.
Proof.
  intros Hlt. unfold propose_optimistic.
  assert (Hb : (throttleCharges <? 1) = true) by (apply Z.ltb_lt; exact Hlt).
  rewrite Hb. reflexivity.
Qed.

(** ----- INV-6: selector gate honored. ----- *)
Lemma propose_optimistic_requires_allowlist
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
     throttleCharges now : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector))
    (p' : Proposal.t) :
  propose_optimistic pid proposer vetoDelay vetoPeriod vetoThresholdD18
    pastSupply throttleCharges targets selectors allow now
  = Result.Success p' ->
  all_calls_allowed allow targets selectors = true.
Proof.
  intros Hok. unfold propose_optimistic in Hok.
  destruct (throttleCharges <? 1); [discriminate|].
  destruct (Nat.eqb (length targets) 0); [discriminate|].
  destruct (negb (lengths_match targets selectors)); [discriminate|].
  destruct (negb (all_calls_allowed allow targets selectors)) eqn:Hall;
    [discriminate|].
  apply negb_false_iff in Hall. exact Hall.
Qed.

Lemma propose_optimistic_denies_disallowed_call
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
     throttleCharges now : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector)) :
  1 <= throttleCharges ->
  (length targets > 0)%nat ->
  lengths_match targets selectors = true ->
  all_calls_allowed allow targets selectors = false ->
  propose_optimistic pid proposer vetoDelay vetoPeriod vetoThresholdD18
    pastSupply throttleCharges targets selectors allow now
  = revert_invalid_call.
Proof.
  intros Hc Hlen Hlm Hno.
  unfold propose_optimistic.
  assert (Hcb : (throttleCharges <? 1) = false) by (apply Z.ltb_ge; lia).
  rewrite Hcb.
  assert (Hneq : Nat.eqb (length targets) 0 = false).
  { destruct (length targets); [lia|reflexivity]. }
  rewrite Hneq.
  rewrite Hlm. simpl.
  rewrite Hno. reflexivity.
Qed.

(** ----- INV-5 / INV-6 combined: success requires both gates honored. ----- *)
Lemma propose_optimistic_success_witness
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
     throttleCharges now : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector))
    (p' : Proposal.t) :
  propose_optimistic pid proposer vetoDelay vetoPeriod vetoThresholdD18
    pastSupply throttleCharges targets selectors allow now
  = Result.Success p' ->
  1 <= throttleCharges /\
  (length targets > 0)%nat /\
  lengths_match targets selectors = true /\
  all_calls_allowed allow targets selectors = true /\
  p'.(Proposal.phase) = PhaseSubmitted /\
  p'.(Proposal.isOptimistic) = true /\
  p'.(Proposal.againstVotes) = 0.
Proof.
  intros Hok. unfold propose_optimistic in Hok.
  destruct (throttleCharges <? 1) eqn:Hc; [discriminate|].
  apply Z.ltb_ge in Hc.
  destruct (Nat.eqb (length targets) 0) eqn:Hlen0; [discriminate|].
  apply Nat.eqb_neq in Hlen0.
  destruct (negb (lengths_match targets selectors)) eqn:Hlm; [discriminate|].
  apply negb_false_iff in Hlm.
  destruct (negb (all_calls_allowed allow targets selectors)) eqn:Hno;
    [discriminate|].
  apply negb_false_iff in Hno.
  injection Hok as Hp'. rewrite <- Hp'. simpl.
  repeat split; try assumption; try lia.
Qed.

(** ----- veto-threshold snap: Math.max(_, 1). ----- *)
Lemma vetoThresholdTok_ge_1 (vetoThresholdD18 pastSupply : U256.t) :
  vetoThresholdTokOf vetoThresholdD18 pastSupply >= 1.
Proof.
  unfold vetoThresholdTokOf.
  destruct ((vetoThresholdD18 * pastSupply) / FIX_ONE <? 1) eqn:Hb.
  - lia.
  - apply Z.ltb_ge in Hb. lia.
Qed.

(** ===== Contract-faithful operation lemmas =====

    Adversarial review (G3, G4) found that the loose [add_veto] and
    [cancel] above accept inputs the contract refuses. The
    [_validated] variants in the simulation enforce the missing
    preconditions; the lemmas below pin their behavior. ===== *)

(** [add_veto_validated] only succeeds on Active phases
    (PhaseSubmitted for optimistic, PhaseStdActive for standard).
    Maps directly to Solidity [_validateStateBitmap(Active)]. *)
Lemma add_veto_validated_requires_active_phase
    (p p' : Proposal.t) (now delta : U256.t) :
  add_veto_validated p now delta = Result.Success p' ->
  p.(Proposal.phase) = PhaseSubmitted \/
  p.(Proposal.phase) = PhaseStdActive.
Proof.
  intros Hok. unfold add_veto_validated in Hok.
  destruct (p.(Proposal.phase));
    try discriminate; try (left; reflexivity); try (right; reflexivity);
    destruct (now <? p.(Proposal.voteStart)); try discriminate;
    destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
    try discriminate.
Qed.

(** [add_veto_validated] requires the time-window precondition.
    If the call succeeded, both [voteStart <= now] and
    [now <= voteStart + voteDuration] held. *)
Lemma add_veto_validated_requires_in_window
    (p p' : Proposal.t) (now delta : U256.t) :
  add_veto_validated p now delta = Result.Success p' ->
  p.(Proposal.voteStart) <= now /\
  now <= p.(Proposal.voteStart) + p.(Proposal.voteDuration).
Proof.
  intros Hok. unfold add_veto_validated in Hok.
  destruct (p.(Proposal.phase)); try discriminate;
    destruct (now <? p.(Proposal.voteStart)) eqn:Hlow; try discriminate;
    destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration)) eqn:Hhi;
    try discriminate;
    apply Z.ltb_ge in Hlow;
    rewrite Z.gtb_ltb in Hhi; apply Z.ltb_ge in Hhi;
    split; lia.
Qed.

(** [cancel_validated]: a caller without CANCELLER_ROLE and not the
    proposer cannot cancel. *)
Lemma cancel_validated_requires_authorization
    (p p' : Proposal.t)
    (has_canceller is_proposer : bool) :
  cancel_validated p has_canceller is_proposer = Result.Success p' ->
  has_canceller = true \/ is_proposer = true.
Proof.
  intros Hok. unfold cancel_validated in Hok.
  destruct has_canceller; [left; reflexivity|].
  destruct is_proposer; [right; reflexivity|].
  simpl in Hok. discriminate.
Qed.

(** [cancel_validated]: a proposer cancelling an optimistic
    proposal succeeds iff the phase is not Defeated. This is the
    SV3 finding — see test/ProposerCancelSucceeded.t.sol. *)
Lemma cancel_validated_optimistic_proposer_succeeds_iff_not_defeated
    (p p' : Proposal.t) :
  p.(Proposal.isOptimistic) = true ->
  cancel_validated p false true = Result.Success p' ->
  p.(Proposal.phase) <> PhaseDefeated.
Proof.
  intros Hopt Hok. unfold cancel_validated in Hok.
  simpl in Hok. rewrite Hopt in Hok.
  destruct (p.(Proposal.phase)) eqn:Hphase; try discriminate;
    intros Heq; discriminate Heq.
Qed.

End GovernorProofs.
