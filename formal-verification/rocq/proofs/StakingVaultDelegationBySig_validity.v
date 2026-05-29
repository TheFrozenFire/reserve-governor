(** StakingVaultDelegationBySig — validity preservation.

    Shows that [delegateOptimisticBySig] preserves the extended
    [Valid.state] predicate (base delegation invariants plus
    nonce-map non-negativity) on the success branch.

    The base sim's [set_opt_delegate_preserves_validity] requires
    a conservation precondition on the from-side delegate:

      old_d = zero_address \/ balance(signer) <= votes(old_d)

    We surface this as an explicit hypothesis on the BySig operator
    rather than discharging it here. The hypothesis is true on any
    reachable state of the contract (proved transitively from the
    OZ ERC20Votes accounting + dual-delegation overlay), and any
    integration proof composing BySig with other operators should
    discharge it from the inductive invariant.

    Outside the success branch, validity is preserved trivially:
    all three revert paths leave state unchanged.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.simulations.StakingVaultDelegationBySig.
Require Import ReserveGovernor.proofs.StakingVaultDelegation_validity.
Require Import ReserveGovernor.mocks.ECDSA.
Require Import ReserveGovernor.mocks.Nonces.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultDelegationBySigValidity.

Import StakingVaultDelegationBySig.

(** The conservation precondition the base sim demands of any
    [set_opt_delegate] call. We surface this on the BySig signer
    as the cleanest hand-off: when an integration proof reaches
    BySig, it must show that the signer's prior delegate's vote
    pile is at least the signer's balance. *)
Definition signer_conservation_pre
    (s : State.t) (signer : Address) : Prop :=
  let opt := s.(State.base).(StakingVaultDelegation.State.opt) in
  let old_d := StakingVaultDelegation.delegate_of opt signer in
  let bal := s.(State.base).(StakingVaultDelegation.State.balances) signer in
  old_d = StakingVaultDelegation.zero_address \/
  bal <= opt.(StakingVaultDelegation.Ledger.votes) old_d.

(** Validity preservation across the BySig operator.

    Given:
      - prior [Valid.state s]
      - the conservation precondition on the recovered signer

    the success branch lands in [Valid.state s']. *)
Theorem delegateOptimisticBySig_preserves_validity :
  forall (s s' : State.t) (now : U256.t)
         (delegatee : Address) (nonce expiry : U256.t)
         (sig : ECDSA.Signature),
    Valid.state s ->
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    signer_conservation_pre s signer ->
    delegateOptimisticBySig s now delegatee nonce expiry sig = Result.Success s' ->
    Valid.state s'.
Proof.
  intros s s' now delegatee nonce expiry sig Hvalid.
  cbv zeta. (* unfold the three [let] bindings in the goal so [intros]
                gets straight to the two [->] hypotheses. *)
  intros Hcons Hsucc.
  unfold delegateOptimisticBySig in Hsucc.
  destruct (Z.ltb expiry now) eqn:Hexp.
  - (* expired branch — Hsucc is a contradiction. *)
    unfold revert_expired_signature in Hsucc. discriminate Hsucc.
  - (* not expired. *)
    set (signer :=
         ECDSA.recover
           (ECDSA.typed_data_hash s.(State.domain)
              (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
           sig) in *.
    destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0.
    + (* invalid sig — contradiction. *)
      unfold revert_invalid_signature in Hsucc. discriminate Hsucc.
    + (* valid sig. *)
      destruct (Nonces.useCheckedNonce s.(State.nonces) signer nonce)
        as [nonces' | p sm] eqn:Hn.
      2: { unfold revert_invalid_nonce in Hsucc. discriminate Hsucc. }
      (* success branch — extract s'. *)
      cbn zeta in Hsucc.
      injection Hsucc as Hs'_eq. subst s'.
      destruct Hvalid as [Hbase Hnon_neg].
      constructor; simpl.
      * (* base_valid — delegate to the existing lemma using Hcons. *)
        apply StakingVaultDelegationValidity.set_opt_delegate_preserves_validity.
        -- exact Hbase.
        -- exact Hcons.
      * (* nonces non-negativity — preserved by useCheckedNonce. *)
        intros a.
        destruct (Z.eq_dec a signer) as [Heq | Hne].
        -- subst a.
           pose proof (Nonces.useCheckedNonce_increments _ _ _ _ Hn) as Hinc.
           rewrite Hinc.
           specialize (Hnon_neg signer). lia.
        -- assert (Hne' : signer <> a) by (intros Heq; apply Hne; symmetry; exact Heq).
           rewrite (Nonces.useCheckedNonce_preserves_other_accounts
                      s.(State.nonces) signer a nonce nonces' Hne' Hn).
           apply Hnon_neg.
Qed.

End StakingVaultDelegationBySigValidity.
