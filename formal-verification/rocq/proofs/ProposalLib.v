(** ProposalLib headline lemmas.

    Proves the load-bearing safety invariants for the [ProposalLib]
    simulation defined in
    [ReserveGovernor.simulations.ProposalLib]:

      INV-1   Hash determinism: proposalIdOf is a function — same key
              yields the same id. (Pure consequence of being a
              [Parameter].)

      INV-2   Hash injectivity: proposalIdOf id collision implies key
              equality. (Axiom of the model — recorded as a lemma for
              uniform citation.)

      INV-3   Optimistic vs prefixed-pessimistic discrimination: the
              proposalId derived from a description and from
              [Confirmation For: ] ++ description are always distinct.

      INV-4   Length-coupling: validateProposal rejects targets /
              values / calldatas length mismatch and zero-length
              proposals.

      INV-5   Confirmation-prefix gate: user-facing entries reject a
              description whose prefix-check returns true.

      INV-6   Already-proposed gate: validateProposal rejects a core
              whose voteStart != 0.

      INV-7   Restricted-proposer gate: validateProposal rejects when
              the description's [#proposer=] suffix is present and
              points at a different address than the proposer.

      INV-8   Optimistic proposer-role gate: proposeOptimistic reverts
              [NotOptimisticProposer] when the proposer lacks the
              role.

      INV-9   Optimistic call gate: proposeOptimistic reverts
              [InvalidCall] when any (target, selector) is missing
              from the registry, or when any calldata has no selector,
              or when any target is not a contract.

      INV-10  Pessimistic votes gate: proposePessimistic reverts
              [InsufficientProposerVotes] when the proposer's votes
              are below the proposalThreshold.

      INV-11  Transition sentinel idempotence: once
              transitionToPessimistic succeeds, the resulting details
              slot has vetoThreshold = TRANSITIONED, and a second call
              on it reverts [AlreadyTransitioned].

      INV-12  Save-proposal storage delta: after a successful
              propose*, the core slot has the expected
              (proposer, voteStart, voteDuration).

    Validity preservation is split into [ProposalLib_validity.v].
    The CAS cross-check sits in [ProposalLib_xcheck.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposalLib.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module ProposalLibProofs.

Import ProposalLib.

(** ----- INV-1: hash determinism. Trivial — proposalIdOf is a function. ----- *)
Lemma proposalIdOf_deterministic :
  forall k1 k2, k1 = k2 -> proposalIdOf k1 = proposalIdOf k2.
Proof. intros k1 k2 Heq. rewrite Heq. reflexivity. Qed.

(** ----- INV-2: hash injectivity, restated as a lemma. ----- *)
Lemma proposalIdOf_inj :
  forall k1 k2, proposalIdOf k1 = proposalIdOf k2 -> k1 = k2.
Proof. exact proposalIdOf_injective. Qed.

(** ----- INV-3: prefix always changes the proposalId. -----

    The argument: if [proposalIdOf(t, v, c, d) = proposalIdOf(t, v, c,
    prefix d)], then by injectivity the keys are equal, which forces
    [d = prefix d], which violates [prefix_sets_prefix] combined with
    a [wf_no_prefix] assumption on [d]. *)
Lemma transition_changes_pid :
  forall targets values calldatas (d : Desc),
    has_confirmation_prefix d = false ->
    proposalIdOf (targets, values, calldatas, d)
    <> proposalIdOf (targets, values, calldatas,
                     prefix_with_confirmation d).
Proof.
  intros targets values calldatas d Hnp Hcoll.
  apply proposalIdOf_injective in Hcoll.
  injection Hcoll as Heq.
  (* Heq : d = prefix_with_confirmation d *)
  pose proof (prefix_sets_prefix d) as Hp.
  rewrite <- Heq in Hp.
  rewrite Hnp in Hp. discriminate Hp.
Qed.

(** ----- INV-4: length-coupling and zero-length rejection. ----- *)

Lemma length_eq_iff {A B : Set} (xs : list A) (ys : list B) :
  length_eq xs ys = true <-> length xs = length ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl; split; intros H;
    try discriminate; try lia; try reflexivity.
  - apply IH in H. lia.
  - apply IH. lia.
Qed.

Lemma validateProposal_rejects_length_mismatch_tv :
  forall p core,
    core.(ProposalCore.voteStart) = 0 ->
    isValidDescriptionForProposer p.(ProposalData.proposer)
                                  p.(ProposalData.description) = true ->
    has_confirmation_prefix p.(ProposalData.description) = false ->
    length p.(ProposalData.targets) <> length p.(ProposalData.values) ->
    validateProposal p core = revert_length_mismatch.
Proof.
  intros p core Hvs Hsuf Hnp Hlen.
  unfold validateProposal.
  rewrite Hvs. simpl.
  rewrite Hsuf. simpl.
  rewrite Hnp.
  destruct (length_eq p.(ProposalData.targets) p.(ProposalData.values)) eqn:Heq.
  - apply length_eq_iff in Heq. contradiction.
  - simpl. reflexivity.
Qed.

Lemma validateProposal_rejects_length_mismatch_tc :
  forall p core,
    core.(ProposalCore.voteStart) = 0 ->
    isValidDescriptionForProposer p.(ProposalData.proposer)
                                  p.(ProposalData.description) = true ->
    has_confirmation_prefix p.(ProposalData.description) = false ->
    length p.(ProposalData.targets) = length p.(ProposalData.values) ->
    length p.(ProposalData.targets) <> length p.(ProposalData.calldatas) ->
    validateProposal p core = revert_length_mismatch.
Proof.
  intros p core Hvs Hsuf Hnp Htv Htc.
  unfold validateProposal.
  rewrite Hvs. simpl.
  rewrite Hsuf. simpl.
  rewrite Hnp.
  assert (Hetv : length_eq p.(ProposalData.targets) p.(ProposalData.values) = true)
    by (apply length_eq_iff; exact Htv).
  rewrite Hetv. simpl.
  destruct (length_eq p.(ProposalData.targets) p.(ProposalData.calldatas)) eqn:Heq.
  - apply length_eq_iff in Heq. contradiction.
  - simpl. reflexivity.
Qed.

Lemma validateProposal_rejects_zero_length :
  forall p core,
    core.(ProposalCore.voteStart) = 0 ->
    isValidDescriptionForProposer p.(ProposalData.proposer)
                                  p.(ProposalData.description) = true ->
    has_confirmation_prefix p.(ProposalData.description) = false ->
    p.(ProposalData.targets) = [] ->
    p.(ProposalData.values) = [] ->
    p.(ProposalData.calldatas) = [] ->
    validateProposal p core = revert_zero_length.
Proof.
  intros p core Hvs Hsuf Hnp Ht Hv Hc.
  unfold validateProposal.
  rewrite Hvs. simpl.
  rewrite Hsuf. simpl.
  rewrite Hnp.
  rewrite Ht, Hv, Hc. simpl. reflexivity.
Qed.

(** ----- INV-5: confirmation-prefix gate. ----- *)
Lemma validateProposal_rejects_confirmation_prefix :
  forall p core,
    core.(ProposalCore.voteStart) = 0 ->
    isValidDescriptionForProposer p.(ProposalData.proposer)
                                  p.(ProposalData.description) = true ->
    has_confirmation_prefix p.(ProposalData.description) = true ->
    validateProposal p core = revert_confirmation_prefix.
Proof.
  intros p core Hvs Hsuf Hcp.
  unfold validateProposal.
  rewrite Hvs. simpl.
  rewrite Hsuf. simpl.
  rewrite Hcp. reflexivity.
Qed.

(** ----- INV-6: already-proposed gate. ----- *)
Lemma validateProposal_rejects_already_proposed :
  forall p core,
    core.(ProposalCore.voteStart) <> 0 ->
    validateProposal p core = revert_already_proposed.
Proof.
  intros p core Hne.
  unfold validateProposal.
  assert (Hb : (core.(ProposalCore.voteStart) =? 0) = false)
    by (apply Z.eqb_neq; exact Hne).
  rewrite Hb. simpl. reflexivity.
Qed.

(** ----- INV-7: restricted-proposer suffix gate. ----- *)
Lemma validateProposal_rejects_restricted_proposer :
  forall p core a,
    core.(ProposalCore.voteStart) = 0 ->
    description_proposer p.(ProposalData.description) = Some a ->
    a <> p.(ProposalData.proposer) ->
    validateProposal p core = revert_restricted_proposer.
Proof.
  intros p core a Hvs Hsuf Hne.
  unfold validateProposal.
  rewrite Hvs. simpl.
  unfold isValidDescriptionForProposer.
  rewrite Hsuf.
  assert (Hb : (a =? p.(ProposalData.proposer)) = false)
    by (apply Z.eqb_neq; exact Hne).
  rewrite Hb. simpl. reflexivity.
Qed.

(** ----- INV-8: optimistic proposer-role gate. ----- *)
Lemma proposeOptimistic_rejects_non_role
    (p : ProposalData.t) (core : ProposalCore.t)
    (params : OptimisticGovernanceParams.t)
    (roles : RoleSet) (reg : SelectorRegistry)
    (is_contract : Address -> bool) (now : U256.t) :
  validateProposal p core = Result.Success tt ->
  roles p.(ProposalData.proposer) = false ->
  proposeOptimistic p core params roles reg is_contract now
  = revert_not_optimistic_proposer.
Proof.
  intros Hv Hr.
  unfold proposeOptimistic.
  rewrite Hv.
  rewrite Hr. simpl. reflexivity.
Qed.

(** ----- INV-9: optimistic call gate -----

    Three failure modes are all collapsed into [revert_invalid_call]:
      a) any calldata is empty (selector_of = None)
      b) any (target, selector) not in the registry
      c) any target is not a contract
*)
Lemma proposeOptimistic_rejects_invalid_call
    (p : ProposalData.t) (core : ProposalCore.t)
    (params : OptimisticGovernanceParams.t)
    (roles : RoleSet) (reg : SelectorRegistry)
    (is_contract : Address -> bool) (now : U256.t) :
  validateProposal p core = Result.Success tt ->
  roles p.(ProposalData.proposer) = true ->
  validate_optimistic_calls reg is_contract
    p.(ProposalData.targets) p.(ProposalData.calldatas) = false ->
  proposeOptimistic p core params roles reg is_contract now
  = revert_invalid_call.
Proof.
  intros Hv Hr Hc.
  unfold proposeOptimistic.
  rewrite Hv. rewrite Hr. simpl.
  rewrite Hc. simpl. reflexivity.
Qed.

(** Concrete: an empty calldata in the list trips the gate. *)
Lemma validate_optimistic_calls_rejects_empty_calldata :
  forall reg ic ts cs t,
    validate_optimistic_calls reg ic (t :: ts) ([] :: cs) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Concrete: an entry whose selector is not allowed trips the gate. *)
Lemma validate_optimistic_calls_rejects_disallowed
    (reg : SelectorRegistry) (ic : Address -> bool)
    (t : Address) (sel : Selector) (rest_t : list Address)
    (rest_c : list Calldata) (tail : list U256.t) :
  ic t = true ->
  reg t sel = false ->
  validate_optimistic_calls reg ic
    (t :: rest_t) ((sel :: tail) :: rest_c) = false.
Proof.
  intros Hic Hreg. simpl. rewrite Hic. rewrite Hreg.
  simpl. reflexivity.
Qed.

(** Concrete: a non-contract target trips the gate. *)
Lemma validate_optimistic_calls_rejects_non_contract
    (reg : SelectorRegistry) (ic : Address -> bool)
    (t : Address) (sel : Selector) (rest_t : list Address)
    (rest_c : list Calldata) (tail : list U256.t) :
  ic t = false ->
  validate_optimistic_calls reg ic
    (t :: rest_t) ((sel :: tail) :: rest_c) = false.
Proof.
  intros Hic. simpl. rewrite Hic. simpl. reflexivity.
Qed.

(** ----- INV-10: pessimistic votes gate. ----- *)
Lemma proposePessimistic_rejects_insufficient_votes
    (p : ProposalData.t) (core : ProposalCore.t)
    (params : StandardGovernanceParams.t)
    (votes : Address -> U256.t)
    (is_contract : Address -> bool) (now : U256.t) :
  validateProposal p core = Result.Success tt ->
  votes p.(ProposalData.proposer)
    < params.(StandardGovernanceParams.proposalThreshold) ->
  proposePessimistic p core params votes is_contract now
  = revert_insufficient_votes.
Proof.
  intros Hv Hlt.
  unfold proposePessimistic.
  rewrite Hv.
  assert (Hb : votes p.(ProposalData.proposer)
                 <? params.(StandardGovernanceParams.proposalThreshold) = true)
    by (apply Z.ltb_lt; exact Hlt).
  rewrite Hb. simpl. reflexivity.
Qed.

(** ----- INV-11: transition sentinel idempotence. ----- *)

Lemma transitionToPessimistic_rejects_sentinel
    (d : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t) (now : U256.t)
    (proposer : Address) :
  d.(OptimisticProposalDetails.vetoThreshold)
    = TRANSITIONED_VETO_THRESHOLD ->
  transitionToPessimistic d params now proposer
  = revert_already_transitioned.
Proof.
  intros Hs.
  unfold transitionToPessimistic.
  rewrite Hs.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma transitionToPessimistic_success_sets_sentinel
    (d d' : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t) (now : U256.t)
    (proposer : Address) (newPid : U256.t) (newCore : ProposalCore.t) :
  transitionToPessimistic d params now proposer
  = Result.Success (newPid, d', newCore) ->
  d'.(OptimisticProposalDetails.vetoThreshold) = TRANSITIONED_VETO_THRESHOLD.
Proof.
  intros Hok.
  unfold transitionToPessimistic in Hok.
  destruct (d.(OptimisticProposalDetails.vetoThreshold)
              =? TRANSITIONED_VETO_THRESHOLD) eqn:Hb.
  - discriminate Hok.
  - injection Hok as Hpid Hd' Hc'. rewrite <- Hd'. simpl. reflexivity.
Qed.

Lemma transition_then_transition_reverts
    (d d' : OptimisticProposalDetails.t)
    (params : StandardGovernanceParams.t) (now1 now2 : U256.t)
    (proposer : Address) (newPid : U256.t) (newCore : ProposalCore.t) :
  transitionToPessimistic d params now1 proposer
  = Result.Success (newPid, d', newCore) ->
  transitionToPessimistic d' params now2 proposer
  = revert_already_transitioned.
Proof.
  intros Hok.
  apply transitionToPessimistic_success_sets_sentinel in Hok.
  apply transitionToPessimistic_rejects_sentinel. exact Hok.
Qed.

(** ----- INV-12: save-proposal storage delta. -----

    After a successful propose, the new core has the expected fields. *)

Lemma proposeOptimistic_success_core
    (p : ProposalData.t) (core core' : ProposalCore.t)
    (params : OptimisticGovernanceParams.t)
    (roles : RoleSet) (reg : SelectorRegistry)
    (is_contract : Address -> bool) (now : U256.t) :
  proposeOptimistic p core params roles reg is_contract now
  = Result.Success core' ->
  core'.(ProposalCore.proposer)     = p.(ProposalData.proposer) /\
  core'.(ProposalCore.voteStart)    = now + params.(OptimisticGovernanceParams.vetoDelay) /\
  core'.(ProposalCore.voteDuration) = params.(OptimisticGovernanceParams.vetoPeriod).
Proof.
  intros Hok.
  unfold proposeOptimistic in Hok.
  destruct (validateProposal p core) as [u | pp ss]; [|discriminate].
  destruct (negb (roles p.(ProposalData.proposer))); [discriminate|].
  destruct (negb (validate_optimistic_calls _ _ _ _)); [discriminate|].
  injection Hok as Hc'. rewrite <- Hc'. simpl. auto.
Qed.

Lemma proposePessimistic_success_core
    (p : ProposalData.t) (core core' : ProposalCore.t)
    (params : StandardGovernanceParams.t)
    (votes : Address -> U256.t)
    (is_contract : Address -> bool) (now : U256.t) :
  proposePessimistic p core params votes is_contract now
  = Result.Success core' ->
  core'.(ProposalCore.proposer)     = p.(ProposalData.proposer) /\
  core'.(ProposalCore.voteStart)    = now + params.(StandardGovernanceParams.votingDelay) /\
  core'.(ProposalCore.voteDuration) = params.(StandardGovernanceParams.votingPeriod).
Proof.
  intros Hok.
  unfold proposePessimistic in Hok.
  destruct (validateProposal p core) as [u | pp ss]; [|discriminate].
  destruct (votes p.(ProposalData.proposer) <?
            params.(StandardGovernanceParams.proposalThreshold)); [discriminate|].
  destruct (negb (validate_pessimistic_calls _ _ _)); [discriminate|].
  injection Hok as Hc'. rewrite <- Hc'. simpl. auto.
Qed.

End ProposalLibProofs.
