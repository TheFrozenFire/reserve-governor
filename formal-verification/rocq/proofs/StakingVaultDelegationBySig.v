(** StakingVault signature-based delegation — headline theorems.

    Five theorems characterizing [delegateOptimisticBySig]:

      BS-1   Expired signatures revert (now > expiry path).

      BS-2   Successful BySig delegation increments the SIGNER's
             nonce by exactly 1 (and leaves all other accounts'
             nonces untouched).

      BS-3   Successful BySig delegation only re-points the
             SIGNER's optimistic delegate — not the caller's,
             not any third party's. This is the "signature
             authorizes only the signer" property.

      BS-4   Replay: calling BySig twice with the SAME (sig, nonce)
             reverts the second call. Direct corollary of the
             nonce-increment property combined with the contract's
             revert-on-mismatch behavior.

      BS-5   Cross-chain / cross-contract replay: a signature
             produced with key K against chain A or contract X
             cannot be successfully replayed against chain B or
             contract Y, even with the same (delegatee, nonce,
             expiry) triple. Captures the EIP-712 domain-separator
             binding.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.simulations.StakingVaultDelegationBySig.
Require Import ReserveGovernor.mocks.ECDSA.
Require Import ReserveGovernor.mocks.Nonces.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultDelegationBySigProofs.

Import StakingVaultDelegationBySig.

(** ----- BS-1: expired signatures revert. -----

    The contract's expiry check is [block.timestamp > expiry];
    we encode it as [expiry <? now]. *)
Lemma bysig_expired_reverts :
  forall (s : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature),
    expiry < now ->
    delegateOptimisticBySig s now delegatee nonce expiry sig =
    revert_expired_signature.
Proof.
  intros s now delegatee nonce expiry sig Hexp.
  unfold delegateOptimisticBySig.
  destruct (Z.ltb expiry now) eqn:Hlt.
  - reflexivity.
  - apply Z.ltb_nlt in Hlt. lia.
Qed.

(** ----- BS-2: successful BySig increments the signer's nonce. -----

    Lemma split into two parts:
      (a) the signer's nonce increases by exactly 1
      (b) all other accounts' nonces are unchanged
*)
Lemma bysig_success_increments_signer_nonce :
  forall (s s' : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature),
    delegateOptimisticBySig s now delegatee nonce expiry sig = Result.Success s' ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    s'.(State.nonces) signer = s.(State.nonces) signer + 1.
Proof.
  intros s s' now delegatee nonce expiry sig H.
  unfold delegateOptimisticBySig in H.
  destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
  set (struct_hash := ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
  set (typed_hash  := ECDSA.typed_data_hash s.(State.domain) struct_hash) in *.
  set (signer      := ECDSA.recover typed_hash sig) in *.
  destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
  destruct (Nonces.useCheckedNonce s.(State.nonces) signer nonce)
    as [nonces' | p sm] eqn:Hn; [|discriminate].
  injection H as Hs'_eq.
  subst s'. simpl.
  apply (Nonces.useCheckedNonce_increments _ _ _ _ Hn).
Qed.

Lemma bysig_success_preserves_other_nonces :
  forall (s s' : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature) (other : Address),
    delegateOptimisticBySig s now delegatee nonce expiry sig = Result.Success s' ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    other <> signer ->
    s'.(State.nonces) other = s.(State.nonces) other.
Proof.
  intros s s' now delegatee nonce expiry sig other H.
  unfold delegateOptimisticBySig in H.
  destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
  set (struct_hash := ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
  set (typed_hash  := ECDSA.typed_data_hash s.(State.domain) struct_hash) in *.
  set (signer      := ECDSA.recover typed_hash sig) in *.
  destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
  destruct (Nonces.useCheckedNonce s.(State.nonces) signer nonce)
    as [nonces' | p sm] eqn:Hn; [|discriminate].
  injection H as Hs'_eq.
  subst s'. simpl.
  intros Hne.
  apply (Nonces.useCheckedNonce_preserves_other_accounts
           s.(State.nonces) signer other nonce nonces').
  - intros Heq. apply Hne. symmetry. exact Heq.
  - exact Hn.
Qed.

(** ----- BS-3: successful BySig re-points only the signer's delegate. -----

    The contract calls [_delegateOptimistic(signer, delegatee)], which
    re-points the optimistic delegate of [signer] (not [msg.sender]
    and not any third party). *)
Lemma bysig_success_sets_signer_delegate :
  forall (s s' : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature),
    delegateOptimisticBySig s now delegatee nonce expiry sig = Result.Success s' ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    signer <> StakingVaultDelegation.zero_address ->
    s'.(State.base).(StakingVaultDelegation.State.opt)
      .(StakingVaultDelegation.Ledger.delegatee) signer = delegatee.
Proof.
  intros s s' now delegatee nonce expiry sig H.
  unfold delegateOptimisticBySig in H.
  destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
  set (struct_hash := ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
  set (typed_hash  := ECDSA.typed_data_hash s.(State.domain) struct_hash) in *.
  set (signer      := ECDSA.recover typed_hash sig) in *.
  destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
  destruct (Nonces.useCheckedNonce s.(State.nonces) signer nonce)
    as [nonces' | p sm] eqn:Hn; [|discriminate].
  injection H as Hs'_eq.
  subst s'. simpl.
  intros _.
  unfold StakingVaultDelegation.set_opt_delegate. simpl.
  unfold StakingVaultDelegation.upd.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** ----- BS-3b: third parties' delegate maps are untouched. -----

    The same call leaves all OTHER accounts' optimistic delegations
    untouched. *)
Lemma bysig_success_preserves_other_delegates :
  forall (s s' : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature) (other : Address),
    delegateOptimisticBySig s now delegatee nonce expiry sig = Result.Success s' ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    other <> signer ->
    s'.(State.base).(StakingVaultDelegation.State.opt)
      .(StakingVaultDelegation.Ledger.delegatee) other =
    s.(State.base).(StakingVaultDelegation.State.opt)
      .(StakingVaultDelegation.Ledger.delegatee) other.
Proof.
  intros s s' now delegatee nonce expiry sig other H.
  unfold delegateOptimisticBySig in H.
  destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
  set (struct_hash := ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
  set (typed_hash  := ECDSA.typed_data_hash s.(State.domain) struct_hash) in *.
  set (signer      := ECDSA.recover typed_hash sig) in *.
  destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
  destruct (Nonces.useCheckedNonce s.(State.nonces) signer nonce)
    as [nonces' | p sm] eqn:Hn; [|discriminate].
  injection H as Hs'_eq.
  subst s'. simpl.
  intros Hne.
  unfold StakingVaultDelegation.set_opt_delegate. simpl.
  unfold StakingVaultDelegation.upd.
  destruct (Z.eqb other signer) eqn:Heqb.
  - apply Z.eqb_eq in Heqb. contradiction.
  - reflexivity.
Qed.

(** ----- BS-4: replay reverts. -----

    Calling [delegateOptimisticBySig] again with the same
    (delegatee, nonce, expiry, sig) on the post-state of a
    successful first call reverts with [revert_invalid_nonce]. The
    sig itself is identical, the recovered signer is identical, but
    the stored nonce has incremented, so the [useCheckedNonce] check
    now fails. *)
Lemma bysig_replay_reverts :
  forall (s s' : State.t) (now1 now2 : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature),
    delegateOptimisticBySig s now1 delegatee nonce expiry sig = Result.Success s' ->
    expiry >= now2 ->
    delegateOptimisticBySig s' now2 delegatee nonce expiry sig = revert_invalid_nonce.
Proof.
  intros s s' now1 now2 delegatee nonce expiry sig Hfirst Hnotexp.
  unfold delegateOptimisticBySig in Hfirst.
  destruct (Z.ltb expiry now1) eqn:Hexp1; [discriminate|].
  destruct (Z.eqb (ECDSA.recover
              (ECDSA.typed_data_hash s.(State.domain)
                 (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
              sig) ECDSA.zero_address) eqn:Hsig0; [discriminate|].
  destruct (Nonces.useCheckedNonce s.(State.nonces)
              (ECDSA.recover
                 (ECDSA.typed_data_hash s.(State.domain)
                    (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
                 sig) nonce)
    as [nonces' | p sm] eqn:Hn; [|discriminate].
  injection Hfirst as Hs'_eq. subst s'.
  (* On the second call: now2 <= expiry so the expiry guard passes, and the
     domain/struct/typed-hash/signer chain reduces to the same recovered
     signer (the State.domain field is preserved across the success). *)
  unfold delegateOptimisticBySig. simpl State.nonces. simpl State.domain.
  destruct (Z.ltb expiry now2) eqn:Hexp2.
  { apply Z.ltb_lt in Hexp2. lia. }
  rewrite Hsig0.
  pose proof (Nonces.useCheckedNonce_replay_reverts _ _ _ _ Hn) as Hrep.
  rewrite Hrep. reflexivity.
Qed.

(** ----- BS-5: cross-chain replay reverts. -----

    A signature [sig] that successfully delegates on chain A
    (chain_id = chainA) cannot be replayed on chain B (chain_id =
    chainB). Concretely: if we change ONLY the domain's chain_id to
    a different value, the recovered signer is no longer the
    legitimate signer — so either it's [zero_address] (revert) or
    it's some other principal whose nonce won't match, OR — the
    case we model — the typed_hash differs, so the recovered signer
    is some address other than [pub k].

    The statement: given a chainA-bound state where BySig succeeded
    with a particular signature, the SAME signature on a chainB
    state (with the same nonce and a fresh nonces map) cannot recover
    the same key holder's public address — hence either reverts
    (signer=0) or addresses a different principal entirely.
*)
Lemma bysig_cross_chain_recovers_different_signer :
  forall (k : ECDSA.Key.t) (dep : ECDSA.Domain.deployment_id)
         (chainA chainB : U256.t) (contract : Address)
         (delegatee : Address) (nonce expiry : U256.t),
    chainA <> chainB ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let domainA :=
      {| ECDSA.Domain.deployment := dep;
         ECDSA.Domain.chain_id   := chainA;
         ECDSA.Domain.contract   := contract |} in
    let domainB :=
      {| ECDSA.Domain.deployment := dep;
         ECDSA.Domain.chain_id   := chainB;
         ECDSA.Domain.contract   := contract |} in
    let hashA := ECDSA.typed_data_hash domainA struct_hash in
    let hashB := ECDSA.typed_data_hash domainB struct_hash in
    let sigA  := ECDSA.sign_with k hashA in
    ECDSA.recover hashB sigA <> ECDSA.pub k.
Proof.
  intros k dep chainA chainB contract delegatee nonce expiry Hchain.
  cbn zeta.
  apply ECDSA.recover_injective_in_hash.
  apply ECDSA.cross_chain_replay_fails. exact Hchain.
Qed.

(** ----- BS-5b: cross-contract replay reverts. -----

    Symmetric statement on the verifying-contract field. *)
Lemma bysig_cross_contract_recovers_different_signer :
  forall (k : ECDSA.Key.t) (dep : ECDSA.Domain.deployment_id)
         (chain : U256.t) (contractX contractY : Address)
         (delegatee : Address) (nonce expiry : U256.t),
    contractX <> contractY ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let domainX :=
      {| ECDSA.Domain.deployment := dep;
         ECDSA.Domain.chain_id   := chain;
         ECDSA.Domain.contract   := contractX |} in
    let domainY :=
      {| ECDSA.Domain.deployment := dep;
         ECDSA.Domain.chain_id   := chain;
         ECDSA.Domain.contract   := contractY |} in
    let hashX := ECDSA.typed_data_hash domainX struct_hash in
    let hashY := ECDSA.typed_data_hash domainY struct_hash in
    let sigX  := ECDSA.sign_with k hashX in
    ECDSA.recover hashY sigX <> ECDSA.pub k.
Proof.
  intros k dep chain contractX contractY delegatee nonce expiry Hne.
  cbn zeta.
  apply ECDSA.recover_injective_in_hash.
  apply ECDSA.cross_contract_replay_fails. exact Hne.
Qed.

End StakingVaultDelegationBySigProofs.
