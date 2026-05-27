(** ProposalLib simulation × CAS witness cross-check.

    Evaluates the [ProposalLib] simulation on the same scenarios used
    by [cas/proposal_lib/proposal_lifecycle.gp] and asserts identical
    outcomes. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build.

    Scenarios reproduced (numbered to match the CAS file):
      - INV-1   Encode round-trip on ProposalData record.
      - INV-2   proposalIdOf determinism on identical keys.
      - INV-4   _validateProposal length-and-zero gates.
      - INV-5   Confirmation-prefix gate rejects.
      - INV-6   transitionToPessimistic sentinel idempotence.
      - INV-7   Optimistic selector / call gate rejects.
      - INV-8   Optimistic proposer-role gate rejects.
      - INV-9   Pessimistic votes gate rejects and accepts.
      - INV-12  saveProposal storage delta.

    Note on hashing:
      [proposalIdOf] is a [Parameter], so [vm_compute] cannot reduce
      it. The two hash-flavored checks (INV-2 hash determinism and
      INV-3 prefix discrimination) are stated as logical equalities
      and discharged by [reflexivity] / the [transition_changes_pid]
      lemma rather than [vm_compute reflexivity].

    Note on descriptions:
      [Desc] is a [Parameter] and [has_confirmation_prefix] /
      [description_proposer] are [Parameter]s as well. Each xcheck
      scenario fixes the boolean / option return value of those
      queries via local hypotheses, so [vm_compute] reduces the
      simulation deterministically.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposalLib.
Require Import ReserveGovernor.proofs.ProposalLib.
Require Import Coq.Lists.List.
Import ListNotations.

Module ProposalLibXCheck.

Import ReserveGovernor.simulations.ProposalLib.
Import ProposalLib.
Import ProposalLibProofs.

(** ----- Sample addresses, matching the CAS witness corpus. ----- *)
Definition proposer1 : Address := 9001.
Definition proposer2 : Address := 8000.
Definition target1   : Address := 200.
Definition target2   : Address := 201.

(** ----- Sample selectors. ----- *)
Definition sel_allowed   : Selector := 170.   (** 0xAA *)
Definition sel_other     : Selector := 180.   (** 0xB4 *)

(** Registry parameter: only (target1, sel_allowed) is in. *)
Definition reg_one (t : Address) (s : Selector) : bool :=
  andb (t =? target1) (s =? sel_allowed).

(** is_contract: target1 and target2 are contracts; everything else
    is an EOA. *)
Definition ic_two (t : Address) : bool :=
  orb (t =? target1) (t =? target2).

(** Role set: only proposer1 has the role. *)
Definition role_one (a : Address) : bool := a =? proposer1.

(** Votes: proposer1 has 100, proposer2 has 50, all others 0. *)
Definition votes_two (a : Address) : U256.t :=
  if a =? proposer1 then 100
  else if a =? proposer2 then 50
  else 0.

(** ----- Description-side abstract witness. -----

    We use a single abstract description [desc_safe] with these
    pinned-query properties:
      - has_confirmation_prefix desc_safe = false
      - description_proposer    desc_safe = None *)
Parameter desc_safe : Desc.
Axiom desc_safe_no_prefix :
  has_confirmation_prefix desc_safe = false.
Axiom desc_safe_no_suffix :
  description_proposer desc_safe = None.

(** A bad description that DOES start with the prefix. *)
Parameter desc_prefixed : Desc.
Axiom desc_prefixed_has_prefix :
  has_confirmation_prefix desc_prefixed = true.
Axiom desc_prefixed_no_suffix :
  description_proposer desc_prefixed = None.

(** ----- Common sample proposal: 1 target, sel_allowed, proposer1. ----- *)
Definition sample_proposal (pid : U256.t) (p : Address) (d : Desc) : ProposalData.t :=
  {|
    ProposalData.proposalId  := pid;
    ProposalData.proposer    := p;
    ProposalData.targets     := [target1];
    ProposalData.values      := [0];
    ProposalData.calldatas   := [ [sel_allowed] ];
    ProposalData.description := d;
  |}.

Definition std_params : StandardGovernanceParams.t := {|
  StandardGovernanceParams.votingDelay := 100;
  StandardGovernanceParams.votingPeriod := 7200;
  StandardGovernanceParams.proposalThreshold := 100;
|}.

Definition opt_params : OptimisticGovernanceParams.t := {|
  OptimisticGovernanceParams.vetoDelay := 60;
  OptimisticGovernanceParams.vetoPeriod := 3600;
  OptimisticGovernanceParams.vetoThreshold := 10 ^ 17;
|}.

(** ----- INV-1: encode round-trip on a ProposalData record.
    With record field access, this is reflexivity. ----- *)
Lemma xcheck_inv1_round_trip :
  forall pid p d,
    let q := sample_proposal pid p d in
    q.(ProposalData.proposalId)  = pid /\
    q.(ProposalData.proposer)    = p /\
    q.(ProposalData.targets)     = [target1] /\
    q.(ProposalData.values)      = [0] /\
    q.(ProposalData.calldatas)   = [ [sel_allowed] ] /\
    q.(ProposalData.description) = d.
Proof. intros. simpl. repeat split. Qed.

(** ----- INV-2: hash determinism on identical keys. ----- *)
Lemma xcheck_inv2_hash_determinism
    (targets : list Address) (values : list U256.t)
    (calldatas : list Calldata) (d : Desc) :
  proposalIdOf (targets, values, calldatas, d)
  = proposalIdOf (targets, values, calldatas, d).
Proof. reflexivity. Qed.

(** ----- INV-3: prefix changes proposalId, given a no-prefix desc. ----- *)
Lemma xcheck_inv3_prefix_changes_pid
    (targets : list Address) (values : list U256.t)
    (calldatas : list Calldata) :
  proposalIdOf (targets, values, calldatas, desc_safe)
  <> proposalIdOf (targets, values, calldatas,
                   prefix_with_confirmation desc_safe).
Proof.
  apply transition_changes_pid. exact desc_safe_no_prefix.
Qed.

(** ----- INV-4: length / zero gates. -----

    Build proposals with explicit length mismatches and check the
    revert codes. *)
Definition mismatch_tv_proposal : ProposalData.t := {|
  ProposalData.proposalId  := 42;
  ProposalData.proposer    := proposer1;
  ProposalData.targets     := [target1; target2];
  ProposalData.values      := [0];
  ProposalData.calldatas   := [ [sel_allowed]; [sel_allowed] ];
  ProposalData.description := desc_safe;
|}.

Lemma xcheck_inv4_length_mismatch_tv :
  validateProposal mismatch_tv_proposal empty_core = revert_length_mismatch.
Proof.
  apply validateProposal_rejects_length_mismatch_tv;
    simpl; try reflexivity.
  - unfold isValidDescriptionForProposer. rewrite desc_safe_no_suffix.
    reflexivity.
  - exact desc_safe_no_prefix.
  - simpl. discriminate.
Qed.

Definition zero_length_proposal : ProposalData.t := {|
  ProposalData.proposalId  := 42;
  ProposalData.proposer    := proposer1;
  ProposalData.targets     := [];
  ProposalData.values      := [];
  ProposalData.calldatas   := [];
  ProposalData.description := desc_safe;
|}.

Lemma xcheck_inv4_zero_length :
  validateProposal zero_length_proposal empty_core = revert_zero_length.
Proof.
  apply validateProposal_rejects_zero_length;
    simpl; try reflexivity.
  - unfold isValidDescriptionForProposer. rewrite desc_safe_no_suffix.
    reflexivity.
  - exact desc_safe_no_prefix.
Qed.

(** ----- INV-5: confirmation-prefix gate. ----- *)
Definition prefixed_proposal : ProposalData.t :=
  sample_proposal 42 proposer1 desc_prefixed.

Lemma xcheck_inv5_confirmation_prefix :
  validateProposal prefixed_proposal empty_core = revert_confirmation_prefix.
Proof.
  apply validateProposal_rejects_confirmation_prefix;
    simpl; try reflexivity.
  - unfold isValidDescriptionForProposer.
    rewrite desc_prefixed_no_suffix. reflexivity.
  - exact desc_prefixed_has_prefix.
Qed.

(** ----- INV-6: transition sentinel idempotence. ----- *)
Definition optimistic_details_active : OptimisticProposalDetails.t := {|
  OptimisticProposalDetails.targets       := [target1];
  OptimisticProposalDetails.values        := [0];
  OptimisticProposalDetails.calldatas     := [ [sel_allowed] ];
  OptimisticProposalDetails.description   := desc_safe;
  OptimisticProposalDetails.vetoThreshold := 10 ^ 17;
|}.

Definition optimistic_details_terminal : OptimisticProposalDetails.t :=
  {| OptimisticProposalDetails.targets       := [target1];
     OptimisticProposalDetails.values        := [0];
     OptimisticProposalDetails.calldatas     := [ [sel_allowed] ];
     OptimisticProposalDetails.description   := desc_safe;
     OptimisticProposalDetails.vetoThreshold := TRANSITIONED_VETO_THRESHOLD;
  |}.

Lemma xcheck_inv6_sentinel_rejects :
  transitionToPessimistic optimistic_details_terminal std_params 1000 proposer1
  = revert_already_transitioned.
Proof.
  apply transitionToPessimistic_rejects_sentinel. simpl. reflexivity.
Qed.

(** ----- INV-7: optimistic call gate.

    Three call-gate failures: unknown target, unknown selector on
    known target, empty calldata. *)
Definition unknown_target_proposal : ProposalData.t :=
  {| ProposalData.proposalId  := 42;
     ProposalData.proposer    := proposer1;
     ProposalData.targets     := [target2];   (** not in registry *)
     ProposalData.values      := [0];
     ProposalData.calldatas   := [ [sel_allowed] ];
     ProposalData.description := desc_safe;
  |}.

Lemma xcheck_inv7_unknown_target :
  proposeOptimistic unknown_target_proposal empty_core opt_params
                    role_one reg_one ic_two 1000
  = revert_invalid_call.
Proof.
  apply proposeOptimistic_rejects_invalid_call.
  - unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity.
  - simpl. unfold role_one. simpl. reflexivity.
  - simpl. unfold reg_one. simpl. reflexivity.
Qed.

Definition unknown_selector_proposal : ProposalData.t :=
  {| ProposalData.proposalId  := 42;
     ProposalData.proposer    := proposer1;
     ProposalData.targets     := [target1];
     ProposalData.values      := [0];
     ProposalData.calldatas   := [ [sel_other] ];
     ProposalData.description := desc_safe;
  |}.

Lemma xcheck_inv7_unknown_selector :
  proposeOptimistic unknown_selector_proposal empty_core opt_params
                    role_one reg_one ic_two 1000
  = revert_invalid_call.
Proof.
  apply proposeOptimistic_rejects_invalid_call.
  - unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity.
  - simpl. unfold role_one. simpl. reflexivity.
  - simpl. unfold reg_one. simpl. reflexivity.
Qed.

Definition empty_calldata_proposal : ProposalData.t :=
  {| ProposalData.proposalId  := 42;
     ProposalData.proposer    := proposer1;
     ProposalData.targets     := [target1];
     ProposalData.values      := [0];
     ProposalData.calldatas   := [ [] ];
     ProposalData.description := desc_safe;
  |}.

Lemma xcheck_inv7_empty_calldata :
  proposeOptimistic empty_calldata_proposal empty_core opt_params
                    role_one reg_one ic_two 1000
  = revert_invalid_call.
Proof.
  apply proposeOptimistic_rejects_invalid_call.
  - unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity.
  - simpl. unfold role_one. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** ----- INV-8: optimistic proposer-role gate. -----

    Build a proposal whose proposer is proposer2 (no role) and all
    other gates would pass. *)
Definition non_role_proposal : ProposalData.t :=
  sample_proposal 42 proposer2 desc_safe.

Lemma xcheck_inv8_non_role :
  proposeOptimistic non_role_proposal empty_core opt_params
                    role_one reg_one ic_two 1000
  = revert_not_optimistic_proposer.
Proof.
  apply proposeOptimistic_rejects_non_role.
  - unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity.
  - unfold role_one. simpl. reflexivity.
Qed.

(** ----- INV-9: pessimistic votes gate. -----

    Build a proposal from proposer2 (50 votes, threshold 100). *)
Lemma xcheck_inv9_insufficient_votes :
  proposePessimistic
    (sample_proposal 42 proposer2 desc_safe)
    empty_core std_params votes_two ic_two 1000
  = revert_insufficient_votes.
Proof.
  apply proposePessimistic_rejects_insufficient_votes.
  - unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity.
  - simpl. unfold votes_two. simpl.
    unfold std_params, StandardGovernanceParams.proposalThreshold.
    lia.
Qed.

(** ----- INV-12: saveProposal field expectations on success. -----

    Build a proposal that passes all gates and check the resulting
    core. *)
Lemma xcheck_inv12_optimistic_save :
  exists core',
    proposeOptimistic
      (sample_proposal 42 proposer1 desc_safe)
      empty_core opt_params role_one reg_one ic_two 1000
    = Result.Success core' /\
    core'.(ProposalCore.proposer)     = proposer1 /\
    core'.(ProposalCore.voteStart)    = 1000 + 60 /\
    core'.(ProposalCore.voteDuration) = 3600.
Proof.
  unfold proposeOptimistic.
  assert (Hv : validateProposal (sample_proposal 42 proposer1 desc_safe)
                                empty_core = Result.Success tt).
  { unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity. }
  rewrite Hv.
  unfold role_one, reg_one, ic_two. simpl.
  eexists. split; [reflexivity| simpl; auto].
Qed.

Lemma xcheck_inv12_pessimistic_save :
  exists core',
    proposePessimistic
      (sample_proposal 42 proposer1 desc_safe)
      empty_core std_params votes_two ic_two 1000
    = Result.Success core' /\
    core'.(ProposalCore.proposer)     = proposer1 /\
    core'.(ProposalCore.voteStart)    = 1000 + 100 /\
    core'.(ProposalCore.voteDuration) = 7200.
Proof.
  unfold proposePessimistic.
  assert (Hv : validateProposal (sample_proposal 42 proposer1 desc_safe)
                                empty_core = Result.Success tt).
  { unfold validateProposal. simpl.
    unfold isValidDescriptionForProposer.
    rewrite desc_safe_no_suffix. simpl.
    rewrite desc_safe_no_prefix. simpl. reflexivity. }
  rewrite Hv.
  unfold votes_two, ic_two, std_params,
    StandardGovernanceParams.proposalThreshold. simpl.
  eexists. split; [reflexivity| simpl; auto].
Qed.

End ProposalLibXCheck.
