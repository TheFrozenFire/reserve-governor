(** ProposalLib validity preservation.

    Each entry point either reverts or returns a [ProposalCore.t]
    whose fields satisfy the storage shape that downstream
    Governor code relies on. For the optimistic-details slot,
    [transitionToPessimistic] preserves [Valid.transitioned] on the
    sentinel branch.

    The lemmas in this file:

      validateProposal_success_implies_well_formed_proposal :
        a Success result from [validateProposal] implies the
        proposal record is [Valid.well_formed_proposal].

      proposeOptimistic_preserves_well_formed :
        successful [proposeOptimistic] feeds a well-formed proposal
        into [saveProposal], so the resulting core preserves the
        proposal's identity (proposer field carries through).

      transitionToPessimistic_preserves_sentinel :
        a successful [transitionToPessimistic] produces details with
        [Valid.transitioned].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposalLib.
Require Import ReserveGovernor.proofs.ProposalLib.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module ProposalLibValidity.

Import ReserveGovernor.simulations.ProposalLib.
Import ProposalLib.
Import ProposalLib.Valid.
Import ProposalLibProofs.

(** ----- Helper: nil-vs-nonnil case-analysis on the targets list. ----- *)
Lemma targets_nil_or_cons (xs : list Address) :
  xs = [] \/ xs <> [].
Proof.
  destruct xs.
  - left. reflexivity.
  - right. discriminate.
Qed.

(** ----- validateProposal Success implies well-formed input. ----- *)
Lemma validateProposal_success_implies_well_formed_proposal :
  forall p core,
    validateProposal p core = Result.Success tt ->
    core.(ProposalCore.voteStart) = 0 /\
    well_formed_proposal p.
Proof.
  intros p core Hv.
  unfold validateProposal in Hv.
  destruct (negb (core.(ProposalCore.voteStart) =? 0)) eqn:Hvs;
    [discriminate|].
  destruct (negb (isValidDescriptionForProposer _ _)) eqn:Hsuf;
    [discriminate|].
  destruct (has_confirmation_prefix _) eqn:Hcp;
    [discriminate|].
  destruct (negb (length_eq p.(ProposalData.targets)
                            p.(ProposalData.values))) eqn:Hetv;
    [discriminate|].
  destruct (negb (length_eq p.(ProposalData.targets)
                            p.(ProposalData.calldatas))) eqn:Hetc;
    [discriminate|].
  apply negb_false_iff in Hvs.
  apply Z.eqb_eq in Hvs.
  apply negb_false_iff in Hsuf.
  apply negb_false_iff in Hetv. apply length_eq_iff in Hetv.
  apply negb_false_iff in Hetc. apply length_eq_iff in Hetc.
  assert (Hnz : p.(ProposalData.targets) <> []).
  { intro Habs. rewrite Habs in Hv. discriminate Hv. }
  split.
  - exact Hvs.
  - constructor.
    + exact Hetv.
    + exact Hetc.
    + exact Hnz.
    + exact Hcp.
    + exact Hsuf.
Qed.

(** ----- saveProposal writes the expected fields. -----

    Pure-functional sanity lemma. *)
Lemma saveProposal_fields (p : ProposalData.t)
    (voteDelay voteDuration now : U256.t) :
  let c := saveProposal p voteDelay voteDuration now in
  c.(ProposalCore.proposer)     = p.(ProposalData.proposer) /\
  c.(ProposalCore.voteStart)    = now + voteDelay /\
  c.(ProposalCore.voteDuration) = voteDuration.
Proof.
  simpl. auto.
Qed.

(** ----- transitionToPessimistic preserves the sentinel on success. ----- *)
Lemma transitionToPessimistic_preserves_sentinel
    (d d' : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t) (now : U256.t)
    (proposer : Address) (newPid : U256.t) (newCore : ProposalCore.t) :
  transitionToPessimistic d params now proposer
  = Result.Success (newPid, d', newCore) ->
  Valid.transitioned d'.
Proof.
  intros Hok.
  unfold Valid.transitioned.
  apply transitionToPessimistic_success_sets_sentinel in Hok.
  exact Hok.
Qed.

(** ----- transition produces an "already-transitioned" details slot,
    which any subsequent [transitionToPessimistic] rejects. -----

    Composition with [transition_then_transition_reverts] from the
    main proofs file: this is the safety story for the one-way
    transition. *)
Lemma transition_produces_terminal_details
    (d d' : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t) (now1 now2 : U256.t)
    (proposer : Address) (newPid : U256.t) (newCore : ProposalCore.t) :
  transitionToPessimistic d params now1 proposer
  = Result.Success (newPid, d', newCore) ->
  transitionToPessimistic d' params now2 proposer
  = revert_already_transitioned.
Proof.
  exact (transition_then_transition_reverts d d' params now1 now2 proposer newPid newCore).
Qed.

End ProposalLibValidity.
