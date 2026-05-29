(** ECDSA + EIP-712 mock — axiomatic interface for OZ's
    [ECDSA.recover] together with [EIP712._hashTypedDataV4].

    Captures the surface of
      @openzeppelin/contracts/utils/cryptography/ECDSA.sol
      @openzeppelin/contracts-upgradeable/utils/cryptography/EIP712Upgradeable.sol
    that StakingVault's [delegateOptimisticBySig] depends on
    (StakingVault.sol:209-211):

      address signer = ECDSA.recover(
        _hashTypedDataV4(keccak256(abi.encode(
          OPTIMISTIC_DELEGATION_TYPEHASH, delegatee, nonce, expiry))),
        v, r, s
      );

    Why axiomatic instead of a full simulation:
      - The secp256k1 group law and Keccak256 round function are
        large, well-audited primitives whose formalization is a
        research program in its own right. Replicating them in Rocq
        would consume effort vastly exceeding the marginal risk
        reduction.
      - The downstream proof only needs THREE properties: signature
        recovery is injective on the (keypair, hash) pair; signing
        with a different key cannot recover the original public
        address; and EIP-712 typed-data hashing binds chain id and
        verifying contract address into the hash so a signature on
        chain A or contract A cannot be replayed on chain/contract
        B. Axiomatizing exactly those keeps the trust surface
        minimal and observable.

    Trust surface: every proof that depends on a signature being
    "the right signature for the right principal" must explicitly
    cite either [recover_of_sign] or one of the [typed_data_hash_*]
    axioms. The Foundry differential tests in
    [test/DelegateOptimisticBySig.t.sol] exercise the same shape
    against OZ's real ECDSA implementation.

    Used by:
      - [simulations/StakingVaultDelegationBySig.v]
      - [proofs/StakingVaultDelegationBySig.v]
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module ECDSA.

(** ---- Address / Hash / Signature carriers ---- *)

(** An address is a 160-bit number in [0, 2^160 - 1]. We use [U256.t]
    for compatibility with the existing simulation convention; the
    [< 2^160] bound is asserted at boundaries. *)
Definition Address : Set := U256.t.

(** The zero address — what [recover] returns on invalid input in
    the *pre-v5* code path. OZ v5 reverts instead; we model the
    revert via the dedicated [Result.Revert] constructor in callers,
    so [recover] in this mock is total. *)
Definition zero_address : Address := 0.

(** A 256-bit hash — output of [keccak256] or [_hashTypedDataV4]. *)
Definition Hash : Set := U256.t.

(** A 65-byte ECDSA signature, modeled as an opaque integer triple
    [(v, r, s)] in [U256.t * U256.t * U256.t]. The actual byte layout
    is irrelevant to the recovery axioms; only the identity of the
    triple matters. *)
Definition Signature : Set := (U256.t * U256.t * U256.t)%type.

(** Keypair handles — used to thread a "who's signing what" identity
    through the axioms without committing to the field representation.
    A [Key.t] is an opaque token; [pub] projects it to its public
    address. Sign/recover round-trip via [recover_of_sign]. *)
Module Key.
  Parameter t : Set.
End Key.

Parameter pub : Key.t -> Address.

(** ---- EIP-712 domain separator ---- *)

(** The EIP-712 domain binds: name, version, chainId, verifyingContract.
    OZ's [EIP712Upgradeable] computes this as
      keccak256(abi.encode(
        TYPE_HASH, hashedName, hashedVersion, chainid, address(this)))
    All four fields enter the domain separator; here we expose only
    the two that vary at runtime (the others are constant per
    deployment). The fixed parts are captured by an opaque
    [Domain.deployment_id] handle.

    Concretely for StakingVault: the [deployment_id] encodes the
    deployment-time-bound (name="ReserveOptimisticStakingVault",
    version="1"); [chain_id] and [contract] vary per environment.
*)
Module Domain.
  Parameter deployment_id : Set.

  (** The constant (name, version) part of the domain for any
      StakingVault deployment. *)
  Parameter staking_vault_id : deployment_id.

  Record t : Set := {
    deployment : deployment_id;
    chain_id   : U256.t;
    contract   : Address;
  }.
End Domain.

(** ---- Primitive operations ---- *)

(** [sign key hash signature] — non-injective shape: we don't model
    randomness (ECDSA's k value), so multiple signatures may exist
    for the same (key, hash). The recovery axiom uses *some* signature
    that round-trips, named via [sign_with]. *)
Parameter sign_with : Key.t -> Hash -> Signature.

(** [recover hash sig] — given a hash and a signature triple,
    returns the recovered signer address. Total function; callers
    handle the "zero address means invalid" or "reverts on malformed"
    paths in their own [Result] discipline. *)
Parameter recover : Hash -> Signature -> Address.

(** [typed_data_hash domain struct_hash] — computes the EIP-712 v4
    digest:
      keccak256(0x1901 || domain_separator(domain) || struct_hash)
    OZ implements this as [MessageHashUtils.toTypedDataHash] applied
    to the domain separator and the struct hash. *)
Parameter typed_data_hash : Domain.t -> Hash -> Hash.

(** [optimistic_delegation_struct_hash delegatee nonce expiry] —
    [keccak256(abi.encode(OPTIMISTIC_DELEGATION_TYPEHASH, delegatee,
    nonce, expiry))]. The typed-struct hash for the BySig delegation
    message; the input to [typed_data_hash] in the caller. *)
Parameter optimistic_delegation_struct_hash :
  Address -> U256.t -> U256.t -> Hash.

(** ---- Axioms ---- *)

(** Axiom 1: [recover_of_sign].
    Round-trip: signing with key [k] for hash [h] produces a
    signature that recovers [pub k]. This is the soundness side
    of ECDSA: a valid signature from key [k] cannot be misattributed
    to a different public address.

    Used to prove: in a successful BySig delegation, the recovered
    signer is exactly [pub key] for the key that produced the
    signature. *)
Axiom recover_of_sign :
  forall (k : Key.t) (h : Hash),
    recover h (sign_with k h) = pub k.

(** Axiom 2: [recover_injective_in_hash].
    Two different hashes signed by the SAME key produce signatures
    that, when each is recovered against the wrong hash, do not
    yield [pub k].

    More formally: if [h1 != h2], then recovering [sign_with k h1]
    against [h2] yields some address != [pub k]. This captures
    "you cannot replay a signature for hash h1 to assert authority
    over the message with hash h2". *)
Axiom recover_injective_in_hash :
  forall (k : Key.t) (h1 h2 : Hash),
    h1 <> h2 ->
    recover h2 (sign_with k h1) <> pub k.

(** Axiom 3: [pub_nonzero].
    Public addresses of keypairs are never the zero address —
    the secp256k1 group has no element mapping to [0x0..0]. The
    contract uses this implicitly when it treats [signer != 0] as
    "the signature is valid".

    Without this axiom, a malformed signature recovering to 0x0
    could be confused with a legitimate signature from the (non-
    existent) zero-address principal. *)
Axiom pub_nonzero :
  forall (k : Key.t), pub k <> zero_address.

(** Axiom 4: [typed_data_hash_injective].
    [typed_data_hash] is injective in all three of its inputs
    (domain, struct_hash), and the domain in turn is injective in
    (deployment, chain_id, contract). This captures the property
    that EIP-712 digests bind the chain id and verifying contract:
    a signature for chain A cannot be replayed on chain B, and a
    signature for contract X cannot be replayed on contract Y.

    The injectivity here is at the digest level, not the byte level;
    the underlying Keccak256 is assumed collision-resistant. *)
Axiom typed_data_hash_injective :
  forall (d1 d2 : Domain.t) (s1 s2 : Hash),
    typed_data_hash d1 s1 = typed_data_hash d2 s2 ->
    d1 = d2 /\ s1 = s2.

(** Axiom 5: [struct_hash_injective].
    The struct hash for the optimistic-delegation message is
    injective in all three of its inputs. Captures collision-
    resistance of Keccak256 against the [abi.encode] of the typed
    fields. Without this, a signature on (delegatee=A, nonce=N,
    expiry=E1) could be replayed as (delegatee=A, nonce=N,
    expiry=E2), defeating the expiry guard. *)
Axiom struct_hash_injective :
  forall (d1 d2 : Address) (n1 n2 e1 e2 : U256.t),
    optimistic_delegation_struct_hash d1 n1 e1 =
    optimistic_delegation_struct_hash d2 n2 e2 ->
    d1 = d2 /\ n1 = n2 /\ e1 = e2.

(** ---- Derived lemmas ---- *)

(** [recover_signs_only_pub_k]: if a signature [sig] was produced
    by [sign_with k h] for some [k], [h], then recovering it against
    [h] returns exactly [pub k] — no other key's signature
    coincidentally recovers to [pub k] against the same hash. *)
Lemma recover_signs_only_pub_k :
  forall (k1 k2 : Key.t) (h : Hash),
    sign_with k1 h = sign_with k2 h ->
    pub k1 = pub k2.
Proof.
  intros k1 k2 h Hsig_eq.
  rewrite <- (recover_of_sign k1 h).
  rewrite Hsig_eq.
  apply recover_of_sign.
Qed.

(** [cross_chain_replay_fails]: a signature valid on chain A is
    not valid on chain B against the same struct hash. Direct
    corollary of [typed_data_hash_injective]. *)
Lemma cross_chain_replay_fails :
  forall (dep : Domain.deployment_id)
         (chainA chainB : U256.t) (addr : Address)
         (struct_hash : Hash),
    chainA <> chainB ->
    typed_data_hash {| Domain.deployment := dep;
                       Domain.chain_id := chainA;
                       Domain.contract := addr |}
                    struct_hash
    <>
    typed_data_hash {| Domain.deployment := dep;
                       Domain.chain_id := chainB;
                       Domain.contract := addr |}
                    struct_hash.
Proof.
  intros dep chainA chainB addr struct_hash Hne Heq.
  apply typed_data_hash_injective in Heq.
  destruct Heq as [Hd _].
  inversion Hd.
  contradiction.
Qed.

(** [cross_contract_replay_fails]: a signature valid against
    verifying contract X cannot be replayed against a different
    contract Y. Same shape as the chain-id case. *)
Lemma cross_contract_replay_fails :
  forall (dep : Domain.deployment_id)
         (chain : U256.t) (addrX addrY : Address)
         (struct_hash : Hash),
    addrX <> addrY ->
    typed_data_hash {| Domain.deployment := dep;
                       Domain.chain_id := chain;
                       Domain.contract := addrX |}
                    struct_hash
    <>
    typed_data_hash {| Domain.deployment := dep;
                       Domain.chain_id := chain;
                       Domain.contract := addrY |}
                    struct_hash.
Proof.
  intros dep chain addrX addrY struct_hash Hne Heq.
  apply typed_data_hash_injective in Heq.
  destruct Heq as [Hd _].
  inversion Hd.
  contradiction.
Qed.

(** [different_expiry_yields_different_hash]: prevents replay of
    a signature with a different expiry value. Corollary of
    [struct_hash_injective]. *)
Lemma different_expiry_yields_different_hash :
  forall (delegatee : Address) (nonce expiry1 expiry2 : U256.t),
    expiry1 <> expiry2 ->
    optimistic_delegation_struct_hash delegatee nonce expiry1
    <>
    optimistic_delegation_struct_hash delegatee nonce expiry2.
Proof.
  intros delegatee nonce expiry1 expiry2 Hne Heq.
  apply struct_hash_injective in Heq.
  destruct Heq as (_ & _ & Heq_expiry).
  contradiction.
Qed.

(** [different_nonce_yields_different_hash]: same shape, on the
    nonce field. Prevents replay across nonces. *)
Lemma different_nonce_yields_different_hash :
  forall (delegatee : Address) (nonce1 nonce2 expiry : U256.t),
    nonce1 <> nonce2 ->
    optimistic_delegation_struct_hash delegatee nonce1 expiry
    <>
    optimistic_delegation_struct_hash delegatee nonce2 expiry.
Proof.
  intros delegatee nonce1 nonce2 expiry Hne Heq.
  apply struct_hash_injective in Heq.
  destruct Heq as (_ & Heq_nonce & _).
  contradiction.
Qed.

End ECDSA.
