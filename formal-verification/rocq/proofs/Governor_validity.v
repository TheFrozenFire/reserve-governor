(** ReserveOptimisticGovernor validity preservation.

    Each transition in the [Governor] simulation preserves the
    [Valid.proposal] storage invariant:
      - all numeric fields (pid, voteStart, voteDuration,
        vetoThresholdTok, againstVotes, parent) fit in uint256.

    [propose_optimistic] writes a fresh [Proposal.t] with derived
    numeric fields. [add_veto] increments [againstVotes]. The other
    transitions ([queue_operations], [execute_standard],
    [execute_optimistic], [cancel], [mark_std_succeeded]) only rewrite
    the [phase] field, so they preserve numeric validity trivially.

    This file proves the [add_veto] preservation as a worked example;
    the other phase-only transitions are observably trivial and
    captured via [Notation] aliases in the audit index.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module GovernorValidity.

Import Governor.
Import Governor.Valid.

(** ----- [add_veto] preserves validity when the bumped tally still
    fits in uint256. ----- *)
Lemma add_veto_preserves_validity (p : Proposal.t) (delta : U256.t) :
  Valid.proposal p ->
  U256.Valid.t (p.(Proposal.againstVotes) + delta) ->
  Valid.proposal (add_veto p delta).
Proof.
  intros Hv Hbound.
  destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent].
  constructor; simpl; auto.
Qed.

(** ----- Type-safe variant: [add_veto] preserves validity when
    [delta] is itself a valid uint256 AND the sum doesn't overflow.

    This is the production-faithful entry point: callers establish
    [Valid.delta delta] from the Solidity uint256 typing of the
    castVote input, then discharge the no-overflow precondition
    (typically from [pastSupply <= 1e18 * vetoThreshold] or a
    similar global bound). The [Valid.delta] form makes the
    "uint256 -> non-negative" implication visible in the lemma
    signature instead of buried in a [Forall (0 <=)] hypothesis. *)
Lemma add_veto_preserves_validity_typed
    (p : Proposal.t) (delta : U256.t) :
  Valid.proposal p ->
  Valid.delta delta ->
  U256.Valid.t (p.(Proposal.againstVotes) + delta) ->
  Valid.proposal (add_veto p delta).
Proof.
  intros Hv _ Hbound.
  apply add_veto_preserves_validity; assumption.
Qed.

(** ----- Citable convention: [Valid.delta] implies the
    non-negativity that downstream proofs hand-derive. ----- *)
Lemma valid_delta_nonneg (delta : U256.t) :
  Valid.delta delta -> 0 <= delta.
Proof. unfold Valid.delta, U256.Valid.t. lia. Qed.

(** ----- Phase-only transitions preserve validity. -----
    These are observably trivial: the rewritten record has the same
    numeric fields as the input. *)
Lemma queue_operations_preserves_validity (p p' : Proposal.t) :
  Valid.proposal p ->
  queue_operations p = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hv Hok. unfold queue_operations in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdSucceeded); [|discriminate].
  injection Hok as Hp'. rewrite <- Hp'.
  destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent].
  constructor; simpl; auto.
Qed.

Lemma execute_standard_preserves_validity (p p' : Proposal.t) :
  Valid.proposal p ->
  execute_standard p = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hv Hok. unfold execute_standard in Hok.
  destruct (p.(Proposal.isOptimistic)); [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdQueued); [|discriminate].
  injection Hok as Hp'. rewrite <- Hp'.
  destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent].
  constructor; simpl; auto.
Qed.

Lemma execute_optimistic_preserves_validity (p p' : Proposal.t) (now : U256.t) :
  Valid.proposal p ->
  execute_optimistic p now = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hv Hok. unfold execute_optimistic in Hok.
  destruct (negb p.(Proposal.isOptimistic)); [discriminate|].
  destruct (observe p now); try discriminate.
  injection Hok as Hp'. rewrite <- Hp'.
  destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent].
  constructor; simpl; auto.
Qed.

Lemma cancel_preserves_validity (p p' : Proposal.t) :
  Valid.proposal p ->
  cancel p = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hv Hok. unfold cancel in Hok.
  destruct (p.(Proposal.phase)); try discriminate;
    injection Hok as Hp'; rewrite <- Hp';
    destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent];
    constructor; simpl; auto.
Qed.

Lemma mark_std_succeeded_preserves_validity (p p' : Proposal.t) (now : U256.t) :
  Valid.proposal p ->
  mark_std_succeeded p now = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hv Hok. unfold mark_std_succeeded in Hok.
  destruct (p.(Proposal.isOptimistic)); [discriminate|].
  destruct (negb (phase_eq p.(Proposal.phase) PhaseStdActive)); [discriminate|].
  destruct (now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
    [discriminate|].
  injection Hok as Hp'. rewrite <- Hp'.
  destruct Hv as [Hpid Hvs Hvd Hvtt Havotes Hparent].
  constructor; simpl; auto.
Qed.

(** ----- propose_optimistic produces a valid proposal under sane inputs.
    Sane inputs: pid, proposer, the delay/period inputs, and the
    derived vetoThresholdTok all fit in uint256. The [now + vetoDelay]
    sum has to fit too. *)
Lemma vetoThresholdTokOf_u256 (vetoThresholdD18 pastSupply : U256.t) :
  0 <= vetoThresholdD18 -> 0 <= pastSupply ->
  vetoThresholdD18 * pastSupply < 2^256 ->
  U256.Valid.t (vetoThresholdTokOf vetoThresholdD18 pastSupply).
Proof.
  intros Hv Hs Hbound.
  unfold vetoThresholdTokOf.
  destruct ((vetoThresholdD18 * pastSupply) / FIX_ONE <? 1) eqn:Hb.
  - unfold U256.Valid.t. split; [lia|]. lia.
  - apply Z.ltb_ge in Hb.
    unfold U256.Valid.t. split.
    + lia.
    + assert (Hdiv : (vetoThresholdD18 * pastSupply) / FIX_ONE
                       <= vetoThresholdD18 * pastSupply).
      { apply Z.div_le_upper_bound; [unfold FIX_ONE; lia|].
        assert (0 <= vetoThresholdD18 * pastSupply).
        { apply Z.mul_nonneg_nonneg; lia. }
        nia. }
      lia.
Qed.

Lemma propose_optimistic_preserves_validity
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
     throttleCharges now : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector))
    (p' : Proposal.t) :
  U256.Valid.t pid ->
  U256.Valid.t (now + vetoDelay) ->
  U256.Valid.t vetoPeriod ->
  0 <= vetoThresholdD18 -> 0 <= pastSupply ->
  vetoThresholdD18 * pastSupply < 2^256 ->
  propose_optimistic pid proposer vetoDelay vetoPeriod vetoThresholdD18
    pastSupply throttleCharges targets selectors allow now
  = Result.Success p' ->
  Valid.proposal p'.
Proof.
  intros Hpid Hvs Hvd Hv Hs Hbound Hok.
  unfold propose_optimistic in Hok.
  destruct (throttleCharges <? 1); [discriminate|].
  destruct (Nat.eqb (length targets) 0); [discriminate|].
  destruct (negb (lengths_match targets selectors)); [discriminate|].
  destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
  injection Hok as Hp'. rewrite <- Hp'.
  constructor; simpl; auto.
  - apply vetoThresholdTokOf_u256; assumption.
  - unfold U256.Valid.t. lia.
  - unfold U256.Valid.t. lia.
Qed.

End GovernorValidity.
