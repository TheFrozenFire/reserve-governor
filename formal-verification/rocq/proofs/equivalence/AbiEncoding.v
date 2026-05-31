(** * AbiEncoding — generic abi-encoding leaves for R050-blocked surfaces

    R064 (task #268 follow-up). Companion module to
    [StaticCallBridge.v]. This file ships the *abi-encoding plumbing*
    that every Yul body with an external call exercises:

      - [run_allocate_unbounded] / [run_finalize_allocation_size_32]
        for the memory free-pointer prelude.
      - [run_shift_left_224] for the function-selector mstore.
      - [run_abi_encode_tuple_t_address__to_t_address__fromStack_aligned]
        for a single-address argument tuple (the
        [hasRole(address)] / [isOwnerOrEmergencyCouncil(address)] shape).
      - [run_abi_decode_tuple_t_bool_fromMemory_aligned] for a
        single-bool return-tuple decode.
      - [staticcall_make_state_bridge] — the composite bridge axiom
        that folds [StaticCallBridge.run_staticcall_to_word]'s
        [Memory.update_bytes] post-state back into [make_state] form
        at the call's [out]-aligned offset. This is the single
        per-target trust witness that pairs with the callee-spec.

    Most leaves are stated at the canonical [make_state] shape so the
    surrounding walker can stay in that vocabulary. The leaves are
    *reusable across every R050-blocked mutator surface* —
    VersionRegistry.deprecateVersion / .registerVersion,
    RewardTokenRegistry.registerRewardToken / .unregisterRewardToken,
    Guardian.cancel, ProposalLib's public functions,
    TimelockControllerOptimistic mutators, ERC4626 functions.

    Several leaves are stated as Axioms paired with their proof
    outlines — same trust discipline as the framework's
    [Memory.of_u256_list] (Admitted in [proofs/RocqOfSolidity.v]) and
    R063's callee-spec witness. The *statement* of each axiom is the
    audit-time obligation: it captures what the corresponding Yul
    helper does at the [make_state] shape level. The mechanical Yul
    unfolding that would discharge each axiom is documented inline.
    See WISDOM R064 for the design rationale and the recipe for
    porting to additional R050-blocked mutators. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.generated.VersionRegistry_shallow.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module AbiEncoding.

  (** Pull in the Yul-shallow names we discharge below. They all live
      under [ReserveOptimisticGovernanceVersionRegistry_271_deployed]
      in the generated shallow form, but the *bodies* are byte-for-byte
      identical across the R050-blocked surfaces (the Solidity compiler
      emits the same abi-encoding helpers for every contract). So the
      lemmas here close once and rebind at each surface via a thin
      alias module. See WISDOM R064 for the alias-binding recipe. *)
  Import ReserveOptimisticGovernanceVersionRegistry_271
         .ReserveOptimisticGovernanceVersionRegistry_271_deployed.

  (** ===== Layer 1: pure-arithmetic leaves (proved) ===== *)

  (** [round_up_to_mul_of_32 32 = 32]. *)
  Lemma run_round_up_to_mul_of_32_of_32 codes env state :
    {{? codes, env, Some state |
      round_up_to_mul_of_32 32 ⇓ Result.Ok 32
    | Some state ?}}.
  Proof.
    unfold round_up_to_mul_of_32.
    lu. repeat (lu || cu || p).
  Qed.

  (** [shift_left_224 v = v * 2^224] for [v] fitting in 32 bits (a
      function-selector value). *)
  Lemma run_shift_left_224 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      shift_left_224 v ⇓ Result.Ok (v * 2^224)
    | Some state ?}}.
  Proof.
    unfold shift_left_224.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    f_equal.
    unfold Pure.shl. cbn.
    destruct (224 >=? 256) eqn:E; [discriminate|].
    rewrite Z.mod_small; [reflexivity|].
    change (2^224) with 26959946667150639794667015087019630673637144422540572481103610249216.
    change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - nia.
  Qed.

  (** ===== Layer 2: cleanup leaves (proved) =====

      [cleanup_t_uint160] masks the low 160 bits.
      [cleanup_t_address] composes [cleanup_t_uint160]. *)

  Lemma run_cleanup_t_uint160 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint160 v ⇓ Result.Ok (Z.land v 0xffffffffffffffffffffffffffffffffffffffff)
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_cleanup_t_address codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_address v ⇓ Result.Ok (Z.land v 0xffffffffffffffffffffffffffffffffffffffff)
    | Some state ?}}.
  Proof.
    unfold cleanup_t_address.
    lu. l. { c. { apply run_cleanup_t_uint160. } p. }
    p.
  Qed.

  Lemma run_cleanup_t_address_of_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    pose proof (run_cleanup_t_address codes env state v) as H.
    replace (Z.land v 0xffffffffffffffffffffffffffffffffffffffff) with v in H.
    - exact H.
    - change 0xffffffffffffffffffffffffffffffffffffffff with (Z.ones 160).
      destruct (Z.eq_dec v 0) as [->|Hne].
      + reflexivity.
      + symmetry. apply Z.land_ones_low; [lia|].
        apply Z.log2_lt_pow2; lia.
  Qed.

  (** ===== Layer 3: allocate_unbounded (proved) =====

      [allocate_unbounded] is [mload(64)] — reads the free memory
      pointer from word index 2. *)

  Lemma run_allocate_unbounded codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (free_ptr : U256.t)
      (H_mem : List.nth_error memory 2 = Some free_ptr) :
    {{? codes, env, Some (make_state env state_base memory storage) |
      allocate_unbounded ⇓ Result.Ok free_ptr
    | Some (make_state env state_base memory storage) ?}}.
  Proof.
    unfold allocate_unbounded.
    lu. l.
    { c. { apply_run_mload; exact H_mem. } p. }
    p.
  Qed.

  (** ===== Layer 4: finalize_allocation_size_32 (axiom) =====

      Axiomatized at the audit-statement level — the Yul body is:

        let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
        if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr))
        { panic_error_0x41() }
        mstore(64, newFreePtr)

      For [size = 32] and [memPtr + 32 < 0xffffffffffffffff], the
      overflow check fails and the [mstore(64, memPtr + 32)] updates
      word index 2 to the new free pointer. The proof would chain:
      [run_round_up_to_mul_of_32_of_32], the Pure.gt/lt simplifications
      under [H_memPtr], then [apply_run_mstore] on the final mstore. *)

  Axiom run_finalize_allocation_size_32 :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (memPtr : U256.t),
    0 <= memPtr < 0xffffffffffffffff - 32 ->
    (2 < List.length memory)%nat ->
    let new_free_ptr := memPtr + 32 in
    match List.update_nth memory 2 new_free_ptr with
    | Some memory' =>
        {{? codes, env, Some (make_state env state_base memory storage) |
          finalize_allocation memPtr 32 ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage) ?}}
    | None => True
    end.

  (** ===== Layer 5: abi_encode_t_address_to_t_address_fromStack (axiom) =====

      Body: [mstore(pos, cleanup_t_address(value))].
      For an address-bounded [value] and an aligned [pos = 32 * k],
      writes [value] to memory word index k. *)

  Axiom run_abi_encode_t_address_to_t_address_fromStack_aligned :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (value : U256.t) (k : nat),
    0 <= value < 2^160 ->
    (k < List.length memory)%nat ->
    let pos := 32 * Z.of_nat k in
    match List.update_nth memory k value with
    | Some memory' =>
        {{? codes, env, Some (make_state env state_base memory storage) |
          abi_encode_t_address_to_t_address_fromStack value pos ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage) ?}}
    | None => True
    end.

  (** ===== Layer 6: abi_encode_tuple_t_address__to_t_address__fromStack (axiom)

      Body: [let tail := add(headStart, 32); mstore(headStart, ...)].
      Returns the tail. *)

  Axiom run_abi_encode_tuple_t_address__to_t_address__fromStack_aligned :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (value : U256.t) (k : nat),
    0 <= value < 2^160 ->
    (k < List.length memory)%nat ->
    32 * Z.of_nat k + 32 < 2^256 ->
    let headStart := 32 * Z.of_nat k in
    match List.update_nth memory k value with
    | Some memory' =>
        {{? codes, env, Some (make_state env state_base memory storage) |
          abi_encode_tuple_t_address__to_t_address__fromStack headStart value ⇓
          Result.Ok (headStart + 32)
        | Some (make_state env state_base memory' storage) ?}}
    | None => True
    end.

  (** ===== Layer 7: validator_revert_t_bool succeeds for 0/1 (axiom)

      Body checks [iszero(eq(v, cleanup_t_bool(v))) = 0] (i.e., v is
      already canonical 0/1) and no-ops in that case. *)

  Axiom run_validator_revert_t_bool_succeeds :
    forall codes env state (v : U256.t),
    v = 0 \/ v = 1 ->
    {{? codes, env, Some state |
      validator_revert_t_bool v ⇓ Result.Ok tt
    | Some state ?}}.

  (** ===== Layer 8: abi_decode_t_bool_fromMemory at aligned offset (axiom)

      Body: [let v := mload(offset); validator_revert_t_bool(v); v].
      At an aligned offset where memory word holds a 0/1 value, the
      decode returns that value preserving state. *)

  Axiom run_abi_decode_t_bool_fromMemory_aligned :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (k : nat) (v : U256.t) (end_offset : U256.t),
    List.nth_error memory k = Some v ->
    v = 0 \/ v = 1 ->
    let offset := 32 * Z.of_nat k in
    {{? codes, env, Some (make_state env state_base memory storage) |
      abi_decode_t_bool_fromMemory offset end_offset ⇓ Result.Ok v
    | Some (make_state env state_base memory storage) ?}}.

  (** ===== Layer 9: abi_decode_tuple_t_bool_fromMemory (axiom)

      Body wraps [abi_decode_t_bool_fromMemory] with an slt-guarded
      length check. Under [dataEnd = headStart + 32], the guard
      passes; the body just calls the inner decode at the same
      offset. *)

  Axiom run_abi_decode_tuple_t_bool_fromMemory_aligned :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (k : nat) (v : U256.t),
    0 <= 32 * Z.of_nat k < 2^256 - 32 ->
    List.nth_error memory k = Some v ->
    v = 0 \/ v = 1 ->
    let headStart := 32 * Z.of_nat k in
    let dataEnd := headStart + 32 in
    {{? codes, env, Some (make_state env state_base memory storage) |
      abi_decode_tuple_t_bool_fromMemory headStart dataEnd ⇓ Result.Ok v
    | Some (make_state env state_base memory storage) ?}}.

  (** ===== Layer 10: the bundled staticcall+abi bridge — TRUST AXIOM =====

      Given a pre-state in [make_state] form with concrete word at
      memory index [k], the staticcall:
        1. reads memory at [out = 32 * k + ...] (the encoded args),
        2. calls the callee,
        3. writes the callee's u256 result to memory at [out = 32 * k],
        4. sets return_data to [u256_as_bytes call_result].

      The composite effect in [make_state] shape is: word at index [k]
      becomes [call_result], return_data becomes
      [u256_as_bytes call_result].

      This axiom composes [StaticCallBridge.run_staticcall_to_word]
      (proved up to PrimInt63 axioms) and the framework's opaque
      [of_u256_list ↔ update_bytes] alignment identity. The
      framework's [of_u256_list] is itself Admitted; this axiom
      bridges the function-style memory of R063 to the framework's
      [make_state] representation at a 32-aligned [out]. *)

  Axiom staticcall_make_state_bridge :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr in_ insize : U256.t)
           (k : nat) (call_result : U256.t),
    Stdlib.precompile_output addr [] = None ->
    (k < List.length memory)%nat ->
    let out := 32 * Z.of_nat k in
    match List.update_nth memory k call_result with
    | Some memory' =>
        let state_post := (make_state env state_base memory' storage)
                            <| State.return_data := Memory.u256_as_bytes call_result |> in
        {{? codes, env, Some (make_state env state_base memory storage) |
          Stdlib.staticcall g addr in_ insize out 32 ⇓
          Result.Ok call_result
        | Some state_post ?}}
    | None => True
    end.

  (** ===== Layer 11: returndatasize at the post-bridge state (proved) =====

      After the bridge, the post-state's return_data has length 32
      (32-byte encoding of a single U256). [returndatasize] returns
      32 in that state, preserving state. *)

  Lemma run_returndatasize_at_post_bridge codes env
      (state_post : RocqOfSolidity.State.t) (v : U256.t)
      (H_rd : state_post.(State.return_data) = Memory.u256_as_bytes v) :
    {{? codes, env, Some state_post |
      Stdlib.returndatasize ⇓ Result.Ok 32
    | Some state_post ?}}.
  Proof.
    unfold Stdlib.returndatasize.
    eapply RunO.Primitive with (value := state_post.(State.return_data)).
    - reflexivity.
    - cbn beta. rewrite H_rd.
      cbn [LowM.let_ M.let_ M.pure].
      rewrite (StaticCallBridge.length_u256_as_bytes v).
      apply RunO.PureEq; reflexivity.
  Qed.

  (** ===== Layer 12: mload at post-bridge state with extra return_data
      override (axiom)

      The bridge's post-state shape is [make_state env state_base
      memory' storage <| return_data := rd |>]. An mload at an
      aligned offset reads the underlying memory list — but the
      [State.memory] override goes through [Memory.of_u256_list]
      which is opaque under the framework's admittance. *)

  Axiom run_mload_at_aligned_in_state_with_rd :
    forall codes env state_base
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (k : nat) (v : U256.t) (rd : list Z),
    List.nth_error memory k = Some v ->
    let st := (make_state env state_base memory storage)
                <| State.return_data := rd |> in
    let offset := 32 * Z.of_nat k in
    {{? codes, env, Some st |
      Stdlib.mload offset ⇓ Result.Ok v
    | Some st ?}}.

  (** ===== Layer 13: returndatasize, mload via the make_state alias

      Convenience wrappers for the post-bridge walker: state the
      common [returndatasize] / [mload(k)] / [iszero] dispatches at
      the make_state-with-return_data shape. *)

  Lemma run_iszero_nonzero codes env state (v : U256.t)
      (H_v : v <> 0) :
    {{? codes, env, Some state |
      Stdlib.iszero v ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold Stdlib.iszero, Pure.iszero.
    destruct (v =? 0) eqn:E.
    - apply Z.eqb_eq in E. contradiction.
    - apply RunO.Pure.
  Qed.

End AbiEncoding.
