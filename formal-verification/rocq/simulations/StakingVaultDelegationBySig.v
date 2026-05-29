(** StakingVault — signature-based optimistic delegation simulation.

    Mirrors [delegateOptimisticBySig] (StakingVault.sol:202-214):

      function delegateOptimisticBySig(
        address delegatee, uint256 nonce, uint256 expiry,
        uint8 v, bytes32 r, bytes32 s
      ) external {
        if (block.timestamp > expiry) {
          revert IVotes.VotesExpiredSignature(expiry);
        }
        address signer = ECDSA.recover(
          _hashTypedDataV4(keccak256(abi.encode(
            OPTIMISTIC_DELEGATION_TYPEHASH, delegatee, nonce, expiry))),
          v, r, s
        );
        _useCheckedNonce(signer, nonce);
        _delegateOptimistic(signer, delegatee);
      }

    Layered on top of [simulations/StakingVaultDelegation.v]:
      - Reuses [State.t] for balances + delegate ledgers.
      - Adds a [Nonces.Map] field for the OZ Nonces book.
      - Adds an [ECDSA.Domain.t] field for the EIP-712 domain
        (chainid + verifying contract address + deployment id).

    The headline correctness theorems live in
    [proofs/StakingVaultDelegationBySig.v]. This file defines the
    state shape and the [delegateOptimisticBySig] operator with
    correct revert discipline for the three failure paths
    (expired, invalid sig, wrong nonce).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.mocks.ECDSA.
Require Import ReserveGovernor.mocks.Nonces.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultDelegationBySig.

(** ---- Reused carriers ---- *)
Definition Address : Set := U256.t.

(** ---- Extended state ---- *)

(** The contract's full BySig-relevant storage: the dual-delegation
    ledger from [StakingVaultDelegation], OZ's Nonces book, and the
    EIP-712 domain pinning chain id / verifying contract address. *)
Module State.
  Record t : Set := {
    base    : StakingVaultDelegation.State.t;
    nonces  : Nonces.Map;
    domain  : ECDSA.Domain.t;
  }.
End State.

(** A blank state with the StakingVault EIP-712 deployment id, a
    designated chain id and contract address. Used in example
    traces. *)
Definition init_state
    (chain_id : U256.t) (contract : Address) : State.t :=
  {|
    State.base   := StakingVaultDelegation.empty_state;
    State.nonces := Nonces.empty;
    State.domain := {|
      ECDSA.Domain.deployment := ECDSA.Domain.staking_vault_id;
      ECDSA.Domain.chain_id   := chain_id;
      ECDSA.Domain.contract   := contract;
    |};
  |}.

(** ---- Result-monad envelope ---- *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Revert sentinels. We don't model selectors precisely; distinct
    [(p, s)] pairs let proofs distinguish revert kinds. *)
Definition revert_expired_signature  {A : Set} : Result.t A := Result.Revert 0  64.
Definition revert_invalid_signature  {A : Set} : Result.t A := Result.Revert 32 64.
Definition revert_invalid_nonce      {A : Set} : Result.t A := Result.Revert 64 64.

(** ---- The BySig delegation operator ---- *)

(** [delegateOptimisticBySig s now delegatee nonce expiry sig]:
    threads the three contract-side checks in order:
      1. [now > expiry] -> revert (expired)
      2. signer := recover(typed_data_hash(domain, struct_hash), sig)
         if signer = 0 -> revert (invalid sig)
      3. useCheckedNonce(signer, nonce); revert if mismatch
      4. set optimistic delegate(signer, delegatee)

    The [now : U256.t] argument stands in for [block.timestamp];
    the contract reads it from the EVM, our simulation takes it as
    an explicit parameter following the project convention
    (Conventions.v / "block.timestamp monotonicity"). *)
Definition delegateOptimisticBySig
    (s : State.t) (now : U256.t)
    (delegatee : Address) (nonce expiry : U256.t)
    (sig : ECDSA.Signature)
    : Result.t State.t :=
  if Z.ltb expiry now then
    revert_expired_signature
  else
    let struct_hash :=
      ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
    let typed_hash :=
      ECDSA.typed_data_hash s.(State.domain) struct_hash in
    let signer := ECDSA.recover typed_hash sig in
    if Z.eqb signer ECDSA.zero_address then
      revert_invalid_signature
    else
      match Nonces.useCheckedNonce s.(State.nonces) signer nonce with
      | Nonces.Result.Revert _ _ => revert_invalid_nonce
      | Nonces.Result.Success nonces' =>
          let base' :=
            StakingVaultDelegation.set_opt_delegate s.(State.base) signer delegatee in
          Result.Success {|
            State.base   := base';
            State.nonces := nonces';
            State.domain := s.(State.domain);
          |}
      end.

(** ---- Validity ---- *)

(** State validity bundles the base sim's validity plus nonce
    non-negativity. Domain is opaque so it has no shape invariant. *)
Module Valid.
  Record state (s : State.t) : Prop := {
    base_valid    : StakingVaultDelegation.Valid.state s.(State.base);
    nonces_nonneg : forall a, 0 <= s.(State.nonces) a;
  }.
End Valid.

End StakingVaultDelegationBySig.
