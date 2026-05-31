(** Task #237 — OpenZeppelin ECDSA equivalence (foundation tier).

    Standalone sanity-check proof against the mock at
    [mocks/ECDSA.v]. The natural target — binding the [recover] /
    [tryRecover] entries of OZ's [ECDSA] library to a shallow form
    derived from any consumer (e.g. [StakingVault.delegateOptimisticBySig]
    or the Governor's [castVoteBySig] / [castVoteWithReasonAndParamsBySig]
    paths, both of which call [ECDSA.recover(hash, v, r, s)] on a
    typed-data digest) — is blocked by two upstream items:

      * Per [notes/shallow_embed_oz_gaps.md], OZ libraries compiled in
        isolation emit only the deploy scaffold (~80 lines of
        [allocate_unbounded] / [constructor_X] / [body] /
        [X_deployed.body]); the actual [recover] / [tryRecover]
        function bodies appear ONLY inlined in concrete consumers'
        Yul output. Equivalence therefore requires a consumer-side
        shallow form to exist.
      * R046 — [shallow_embed.py] drops critical bodies in the
        success arm of certain mutators; consumer-side equivalence
        files (StakingVault.delegateBySig, Governor.castVoteBySig)
        depend on its resolution.
      * R035 — neither StakingVault nor ReserveOptimisticGovernor
        has a usable shallow form yet (switch-binding bug + the
        contracts are heavy enough that the generator hits
        independent issues even after R046).

    Until both land, no equivalence-tier binding for the ECDSA
    primitives at the call site is feasible.

    R048 — pure-function library variant of R045
    --------------------------------------------

    R045 captures the [with_X body] symbolic-expansion pattern for OZ
    *modifiers* and *precondition-shape* helpers. R048 (established
    by [proofs/equivalence/EnumerableSet.v] and adopted by
    [proofs/equivalence/Checkpoints.v]) documents a third shape:
    *pure-function libraries* (Solidity `library` keyword, every
    entry takes its inputs explicitly and returns either a value or
    a new state). At the Yul / shallow-form level, an [ECDSA.recover]
    call at a consumer expands as a single value-producing
    sub-expression:

      let digest = _hashTypedDataV4(struct_hash);
      let signer = ECDSA_recover(digest, v, r, s);
      // ... use `signer` (e.g. equality check vs `owner`) ...

    There is no surrounding body to bracket and no per-call storage
    side effect — ECDSA is the *most stateless* member of the
    R048 family. The "sanity check" for ECDSA is therefore a set of
    standalone consistency theorems lifting the mock's axiomatic
    semantics to the domain-flavored properties callers rely on:
    round-trip recovery, replay protection across (chain, contract,
    nonce, expiry), and the non-zero-address guarantee that lets
    callers treat `signer != 0` as "this signature is valid".

    Each lemma below cross-references the mock's primitive lemma or
    axiom; we do not re-prove from scratch. Once a consumer-side
    shallow form lands, the natural binding will pose
    [signer = recover (typed_data_hash dom (struct_hash ...)) (v,r,s)]
    against the shallow recovery sequence and discharge the
    `signer == owner` equality via [recover_of_sign]. The lemmas
    here characterise the abstract semantics that binding will
    preserve. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.ECDSA.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module ECDSAEquivalence.

  Import ECDSA.

  (** ----- 1. round-trip: recovering a signature produced by [sign_with k]
                returns [pub k] -----

      OZ surface: when a wallet signs a typed-data digest with key [k],
      the on-chain [ECDSA.recover(digest, sig)] call returns exactly
      that wallet's address — the soundness side of ECDSA. Consumers
      rely on this to identify the signer in BySig flows
      ([StakingVault.delegateOptimisticBySig:209-211],
      [Governor.castVoteBySig]).

      Direct re-export of the mock's [recover_of_sign] axiom. *)
  Lemma recover_round_trip :
    forall (k : Key.t) (h : Hash),
      recover h (sign_with k h) = pub k.
  Proof. exact recover_of_sign. Qed.

  (** ----- 2. recovered signer is never the zero address when the
                signature came from a real keypair -----

      OZ surface: the post-recovery check [signer != address(0)] is
      what callers use to distinguish a valid signature from a
      malformed/garbage one. This lemma certifies that any signature
      produced by [sign_with] recovers to a non-zero address, so the
      "valid signature" branch in the consumer is actually reachable
      and not a no-op.

      Composes [recover_of_sign] with [pub_nonzero]. *)
  Lemma valid_sig_recovery_non_zero :
    forall (k : Key.t) (h : Hash),
      recover h (sign_with k h) <> zero_address.
  Proof.
    intros k h.
    rewrite recover_of_sign.
    apply pub_nonzero.
  Qed.

  (** ----- 3. cross-hash replay protection: a signature for hash [h1]
                cannot be replayed against hash [h2 != h1] -----

      OZ surface: the [hash] argument to [recover] enters the
      [ecrecover] precompile directly; changing it changes the recovered
      address. Consumers exploit this to bind each signature to a
      *specific* message — the typed-data digest includes nonce, expiry,
      and the verifying contract, so the same (v, r, s) tuple cannot be
      lifted to a different message. This is the abstract version of
      that property at the [recover] surface.

      Direct re-export of the mock's [recover_injective_in_hash]. *)
  Lemma recover_rejects_hash_replay :
    forall (k : Key.t) (h1 h2 : Hash),
      h1 <> h2 ->
      recover h2 (sign_with k h1) <> pub k.
  Proof. exact recover_injective_in_hash. Qed.

  (** ----- 4. signatures coincide only if their public keys coincide -----

      OZ surface: two different keypairs cannot produce the same
      signature on the same hash. This is the counter-positive of the
      ECDSA forging hardness: if [sign_with k1 h = sign_with k2 h],
      then [pub k1 = pub k2] (they must have been the same key, modulo
      our opaque key-token representation).

      Direct re-export of the mock's [recover_signs_only_pub_k]
      derived lemma. *)
  Lemma sig_collision_implies_pub_equal :
    forall (k1 k2 : Key.t) (h : Hash),
      sign_with k1 h = sign_with k2 h ->
      pub k1 = pub k2.
  Proof. exact recover_signs_only_pub_k. Qed.

  (** ----- 5. cross-chain replay protection at the typed-data layer -----

      OZ surface: EIP-712's [_hashTypedDataV4] folds [chain_id] into
      the domain separator, so the same struct hash produces a
      different digest on chain A vs chain B. A signature collected
      on Ethereum mainnet cannot be relayed to Optimism (or vice
      versa) even against the same contract address. This is the
      defining feature of EIP-712 vs personal_sign.

      Direct re-export of the mock's [cross_chain_replay_fails]. *)
  Lemma typed_data_binds_chain_id :
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
  Proof. exact cross_chain_replay_fails. Qed.

  (** ----- 6. cross-contract replay protection at the typed-data layer -----

      OZ surface: [_hashTypedDataV4] also folds the verifying contract
      address into the domain separator, so a signature for
      StakingVault A cannot be replayed against StakingVault B (or
      against a Governor) even on the same chain. Together with R5,
      this fully constrains "where" a signature is valid.

      Direct re-export of the mock's [cross_contract_replay_fails]. *)
  Lemma typed_data_binds_verifying_contract :
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
  Proof. exact cross_contract_replay_fails. Qed.

  (** ----- 7. nonce/expiry replay protection at the struct-hash layer -----

      OZ surface: the optimistic-delegation struct hash binds nonce
      and expiry. A signature collected with [(nonce=N, expiry=E1)]
      cannot be lifted to [(nonce=N, expiry=E2)] — neither the
      consumer's [_useCheckedNonce] guard alone nor the expiry
      timestamp check could catch the swap if the digest were the
      same. The struct-hash injectivity is what makes the two guards
      complementary.

      Combines the mock's two derived lemmas
      [different_nonce_yields_different_hash] and
      [different_expiry_yields_different_hash] into a single
      headline statement: any change in either nonce OR expiry
      yields a different struct hash. *)
  Lemma struct_hash_binds_nonce_and_expiry :
    forall (delegatee : Address) (n1 n2 e1 e2 : U256.t),
      (n1 <> n2 \/ e1 <> e2) ->
      optimistic_delegation_struct_hash delegatee n1 e1
      <>
      optimistic_delegation_struct_hash delegatee n2 e2.
  Proof.
    intros delegatee n1 n2 e1 e2 Hne Heq.
    apply struct_hash_injective in Heq.
    destruct Heq as (_ & Hn & He).
    destruct Hne as [Hne_n | Hne_e]; contradiction.
  Qed.

End ECDSAEquivalence.
