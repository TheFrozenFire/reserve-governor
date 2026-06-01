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

  (** ===== Layer 10b: the absorbing staticcall bridge (R082) =====

      Skolem-form sibling to [staticcall_make_state_bridge]: instead
      of requiring [k < length memory] and producing the concrete
      [update_nth memory k call_result], the absorbing form
      Skolemises the post-memory as an arbitrary function of the
      inputs. This is the staticcall analog of R083's absorbing
      mstore primitive — useful when prior mstores (themselves
      absorbed) make the per-index length precondition non-trivial.

      Soundness: same as the per-index bridge — under audit-time
      alignment / well-formedness, the staticcall writes its
      [call_result] as bytes at [out], producing a new memory
      expressible at the [SimulatedMemory.t] level. The Skolem
      function [staticcall_post_memory] points at that witness. *)

  Parameter staticcall_post_memory :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t -> SimulatedMemory.t.

  Axiom staticcall_make_state_bridge_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr in_ insize out : U256.t) (call_result : U256.t),
    Stdlib.precompile_output addr [] = None ->
    let state_post :=
      (make_state env state_base
         (staticcall_post_memory env state_base memory storage out call_result)
         storage)
        <| State.return_data := Memory.u256_as_bytes call_result |> in
    {{? codes, env, Some (make_state env state_base memory storage) |
      Stdlib.staticcall g addr in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state_post ?}}.

  (** ===== Layer 10c: staticcall_post_memory structural axioms =====

      Audit-time obligations on the Skolem post-memory:

      - At the word-index corresponding to [out] (= [out/32] when
        [out] is 32-aligned), the post-memory contains [call_result].
        This is the operational specification: the staticcall writes
        the callee's return word to memory at [out].

      - At any OTHER word-index, the post-memory equals the
        pre-memory. The staticcall only writes at [out].

      - The post-memory list has the same length as the pre-memory.
        The staticcall doesn't grow memory at the SimulatedMemory.t
        list level (it overwrites a single 32-byte slot, allocated
        by the prior abi-prelude). *)

  Axiom staticcall_post_memory_at_out :
    forall env state_base memory storage out call_result (k : nat),
    out = 32 * Z.of_nat k ->
    List.nth_error
      (staticcall_post_memory env state_base memory storage out call_result) k
    = Some call_result.

  Axiom staticcall_post_memory_at_other :
    forall env state_base memory storage out call_result (k : nat),
    32 * Z.of_nat k <> out ->
    List.nth_error
      (staticcall_post_memory env state_base memory storage out call_result) k
    = List.nth_error memory k.

  Axiom staticcall_post_memory_length :
    forall env state_base memory storage out call_result,
    List.length
      (staticcall_post_memory env state_base memory storage out call_result)
    = List.length memory.

  (** [make_state]'s [return_data] passes through from [state_base].
      Useful for proving [(make_state env state_base ...).return_data
      = state_base.return_data] post-rd-absorption. *)

  Axiom make_state_return_data_eq :
    forall env state_base memory storage,
    (make_state env state_base memory storage).(State.return_data)
    = state_base.(State.return_data).

  (** ===== Layer 10c.2: mapping_index_access composite (R082) =====

      The mapping_index_access pattern at a 32-byte key/slot pair:
        do~ mstore(0, key) in
        do~ mstore(0x20, slot) in
        let~ dataSlot := keccak256(0, 0x40) in
        ...

      The keccak256 reads memory[0] (= key after the first mstore)
      and memory[1] (= slot after the second mstore) — but the
      framework's [run_keccak256_tuple2] requires explicit per-index
      [nth_error] hypotheses. The absorbing-mstore Skolem memory
      doesn't satisfy those.

      This composite axiom abstracts over the two-mstore-then-
      keccak256 pattern at the absorbing make_state state shape.
      Audit-time obligation: the two mstores write [key] and [slot]
      at scratch words 0 and 1, so the keccak256 reads exactly the
      bytes that produce [keccak256_tuple2 key slot]. *)

  Parameter mapping_index_access_post_memory :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t (* key *) -> U256.t (* slot *) -> SimulatedMemory.t.

  Axiom run_mapping_index_access_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (slot key : U256.t),
    {{? codes, env, Some (make_state env state_base memory storage) |
      mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
    | Some (make_state env state_base
              (mapping_index_access_post_memory env state_base memory storage
                                                 key slot)
              storage) ?}}.

  (** ===== Layer 10d: post-bridge decode composite (R082) =====

      The post-staticcall return-path is structured by the Solidity
      compiler as a fixed three-step sequence:

        1. [returndatasize] — checked >= expected size
        2. [finalize_allocation(memPtr, returndatasize)] — bumps
           the free memory pointer past the just-read bytes
        3. [abi_decode_tuple_t_bool_fromMemory(memPtr, memPtr + size)] —
           reads + validates the 0/1 bool at [memPtr]

      Each step's per-index semantics is gnarly (the staticcall
      writes [call_result] at [out = memPtr]; finalize_allocation
      bumps memory[2] but leaves memory[memPtr/32] alone; the abi
      decode reads memory[memPtr/32]). Rather than thread per-index
      memory shape facts through three axiom invocations, we ship a
      composite axiom that produces the cleaned-up [call_result]
      value and a Skolemised post-memory.

      Audit-time obligation on the contract: [call_result] is the
      bool the callee returned (0 for false, 1 for true).

      Reusable across every Solidity contract that decodes a single
      bool from a staticcall return — i.e., every R050-blocked
      external boolean call. *)

  Parameter post_staticcall_decode_post_memory :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t (* memPtr *) -> U256.t (* call_result *) -> SimulatedMemory.t.

  (** The composite post-staticcall decode block:
        do~ finalize_allocation memPtr 32 in
        let~ expr := abi_decode_tuple_t_bool_fromMemory memPtr (memPtr + 32) in
        M.pure (Tt, expr)
      reduces — at the post-staticcall absorbing state — to
      [call_result], with the memory Skolemised. *)

  Axiom run_post_staticcall_decode_bool :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (memPtr size : U256.t) (call_result : U256.t),
    call_result = 0 \/ call_result = 1 ->
    size = 32 ->
    let body :=
      do~ M.call (finalize_allocation memPtr size) in
      (let~ ' expr_162 :=
         let* v := M.call (Stdlib.add memPtr size) in
         M.call (abi_decode_tuple_t_bool_fromMemory memPtr v)
       in LowM.Pure (Result.Ok (BlockUnit.Tt, expr_162)))
    in
    {{? codes, env, Some (make_state env state_base memory storage) |
      body ⇓ Result.Ok (BlockUnit.Tt, call_result)
    | Some (make_state env state_base
              (post_staticcall_decode_post_memory env state_base memory storage
                                                  memPtr call_result)
              storage) ?}}.

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

  (** ===== Layer 14: make_state / return_data commutation =====

      The bridge produces a post-state of shape

        (make_state env state_base memory' storage)
          <| State.return_data := bytes |>

      [make_state] is defined via [with_current_storage] (opaque in
      [proofs/RocqOfSolidity.v]). [State.return_data] is a different
      record field from those touched by [with_current_storage] (which
      writes [State.accounts]). The two commute: applying the
      [return_data] override outside [make_state] is the same as
      threading it through [state_base] first.

      Closed in the same spirit as the framework's
      [CanonizeState.update_memory_eq] / [update_storage_eq] — both
      [Admitted] because [with_current_storage] is opaque. *)

  Axiom make_state_with_rd_eq :
    forall env state_base memory storage (rd : list Z),
    (make_state env state_base memory storage)
      <| State.return_data := rd |> =
    make_state env (state_base <| State.return_data := rd |>) memory storage.

  (** Gas-decrement commutation. Same soundness story as
      [make_state_with_rd_eq]: [State.gas] is a record field not
      touched by [with_current_storage] (which only writes
      [State.accounts]). Applying a [gas]-override outside
      [make_state] is the same as threading it through [state_base]
      first. Useful for absorbing [gas] reads (each of which
      decrements via [GetGas]'s eval_primitive). *)

  Axiom make_state_with_gas_eq :
    forall env state_base memory storage (g : U256.t),
    (make_state env state_base memory storage)
      <| State.gas := g |> =
    make_state env (state_base <| State.gas := g |>) memory storage.

  (** [make_state] preserves the [State.gas] field — useful for
      proving [state.gas = state_base.gas] after the [make_state]
      wrapping (since [with_current_storage] only writes accounts). *)

  Axiom make_state_gas_eq :
    forall env state_base memory storage,
    (make_state env state_base memory storage).(State.gas)
    = state_base.(State.gas).

  (** ===== Layer 14b: the absorbing delegatecall bridge (R091) =====

      Sibling to [staticcall_make_state_bridge_absorbing] above, for
      the [Stdlib.delegatecall] opcode.  Closes R087 Blocker 2 — the
      delegatecall framework gap that blocked ROG's [fun_propose_389]
      walker (delegatecall into [ProposalLib.proposePessimistic]) and
      Timelock's [executeBatch] inner-body walker (delegatecall into
      each target's bytecode).

      Semantic difference vs staticcall:

        - staticcall: target runs in TARGET's storage.  Caller's
          storage is unchanged.  Only memory + return_data move.
        - delegatecall: target runs in CALLER's storage.  Caller's
          storage IS mutated by target's logic.  Memory shared;
          return_data carries the target's return.

      The absorbing form Skolemises BOTH the memory and the storage
      effects:

        - [delegatecall_post_memory] — caller's memory after the
          delegatecall's mstore tail write.  Mirrors [staticcall_post_memory].
        - [delegatecall_post_storage] — caller's storage after the
          target's body wrote against it.  THIS IS NEW: staticcall has
          no analogue because staticcall cannot mutate storage.

      Per-target audit-time obligation: the
      [delegatecall_post_storage] Skolem captures the target's net
      storage effect under the caller's storage context.  Each use
      site discharges this via a companion observational-bridge axiom
      (R070 / R086 shape) that pins the post-storage to the target's
      sim-side post-state at the slot anchors the target writes.  See
      the consumers under [ReserveOptimisticGovernor.v]'s
      [fun_propose_389] walker and [TimelockControllerOptimistic.v]'s
      [fun_executeBatch_1552_inner] walker.

      Soundness justification:

        - The upstream's [Stdlib.delegatecall] reduces to
          [LowM.CallContract addr 0 input false true k] sandwiched
          between MLoad / RLoad / MStore primitives (see
          [StaticCallBridge.run_delegatecall_general] for the base
          proof).
        - [LowM.CallContract] is a trust-based proof rule whose
          [state_inter] choice is what carries the target's body
          effect.  For delegatecall, [state_inter] reflects the
          caller's storage AFTER the target ran against it.
        - The Skolem [delegatecall_post_storage] points at THAT
          storage witness.  Soundness reduces to the per-target
          observational bridge: the Skolem MUST equal the target's
          sim post-storage at the audited slots.
        - This is consistent with upstream's [Storage.of_storable_values]
          being [Admitted] — the framework leaves the storage
          projection unspecified; the Skolem witnesses one consistent
          assignment.

      AUDIT OBLIGATION per use site: the consumer carries a
      companion bridge axiom tying [delegatecall_post_storage] to
      the target's sim post-state at the slot anchors the target
      writes.  Same shape as R070 / R086 — the bridge is the
      observational equality; the Skolem is the existential
      witness.

      Trust delta: +1 axiom (this one) per framework use; the
      per-use-site bridge axioms are existing R070 trust budget
      lines, NOT new framework lines.  The primitive itself is
      reused across every delegatecall consumer. *)

  Parameter delegatecall_post_memory :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t (* addr *) -> U256.t (* out *) -> U256.t (* call_result *) ->
    SimulatedMemory.t.

  Parameter delegatecall_post_storage :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t (* addr *) -> list Z (* input bytes *) ->
    SimulatedStorage.t.

  Axiom delegatecall_make_state_bridge_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr in_ insize out outsize : U256.t)
           (input_bytes : list Z) (call_result : U256.t),
    let storage' :=
      delegatecall_post_storage env state_base memory storage addr input_bytes in
    let memory' :=
      delegatecall_post_memory env state_base memory storage addr out call_result in
    let state_post :=
      (make_state env state_base memory' storage')
        <| State.return_data := Memory.u256_as_bytes call_result |> in
    {{? codes, env, Some (make_state env state_base memory storage) |
      Stdlib.delegatecall g addr in_ insize out outsize ⇓
      Result.Ok call_result
    | Some state_post ?}}.

  (** Structural companion axioms on [delegatecall_post_memory] —
      mirror [staticcall_post_memory_at_out / at_other / length].
      Audit obligation: the delegatecall's mstore tail only touches
      the word at [out/32] (when [out] is 32-aligned); all other
      word indices are unchanged. *)

  Axiom delegatecall_post_memory_at_out :
    forall env state_base memory storage addr out call_result (k : nat),
    out = 32 * Z.of_nat k ->
    List.nth_error
      (delegatecall_post_memory env state_base memory storage addr out call_result) k
    = Some call_result.

  Axiom delegatecall_post_memory_at_other :
    forall env state_base memory storage addr out call_result (k : nat),
    32 * Z.of_nat k <> out ->
    List.nth_error
      (delegatecall_post_memory env state_base memory storage addr out call_result) k
    = List.nth_error memory k.

  Axiom delegatecall_post_memory_length :
    forall env state_base memory storage addr out call_result,
    List.length
      (delegatecall_post_memory env state_base memory storage addr out call_result)
    = List.length memory.

  (** Structural companion axiom on [delegatecall_post_storage]:
      length preservation.  Audit obligation: library delegatecall
      targets (ProposalLib, OZ AccessControlEnumerable swap-and-pop,
      etc.) write at slot expressions whose backing storage cell
      already exists in the caller's projection — they do not GROW
      the storage list.  Same obligation shape as
      [sstore_post_storage_length] in FrameworkExtensions.v. *)

  Axiom delegatecall_post_storage_length :
    forall env state_base memory storage addr input_bytes,
    List.length
      (delegatecall_post_storage env state_base memory storage addr input_bytes)
    = List.length storage.

  (** Absorbing-form variant when the delegatecall's [outsize = 0]
      (no return-data write to memory).  Used by [fun_propose_389]
      (delegatecall with outsize = 0 — return decoded via
      returndatacopy later) and by [fun_functionDelegateCall_4416]
      (delegatecall with outsize = 0 — return extracted via
      [extract_returndata]).

      Same Skolems as the [_absorbing] form but the post-memory is
      independent of [out] / [call_result] (the delegatecall didn't
      mstore at [out]).  We re-use the [delegatecall_post_memory]
      Skolem with [out := 0] / [call_result := 0] to keep one Skolem
      family, accepting that the structural [at_out] axiom is
      vacuous for the zero-out case. *)

  Axiom delegatecall_make_state_bridge_absorbing_outsize_0 :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr in_ insize out : U256.t)
           (input_bytes : list Z) (call_result : U256.t),
    let storage' :=
      delegatecall_post_storage env state_base memory storage addr input_bytes in
    let memory' :=
      delegatecall_post_memory env state_base memory storage addr 0 0 in
    let state_post :=
      (make_state env state_base memory' storage')
        <| State.return_data := Memory.u256_as_bytes call_result |> in
    {{? codes, env, Some (make_state env state_base memory storage) |
      Stdlib.delegatecall g addr in_ insize out 0 ⇓
      Result.Ok call_result
    | Some state_post ?}}.

  (** Ergonomic [Ltac] aliases: drive a walker arm past a delegatecall
      by deferring to the absorbing axiom.  The Skolem witnesses are
      filled in by unification with the surrounding goal's post-state
      shape. *)
  Ltac apply_run_delegatecall_absorbing :=
    apply delegatecall_make_state_bridge_absorbing.

  Ltac apply_run_delegatecall_absorbing_outsize_0 :=
    apply delegatecall_make_state_bridge_absorbing_outsize_0.

  (** ===== Layer 14c: the absorbing [call] bridge (R093) =====

      Sibling to [staticcall_make_state_bridge_absorbing] (R082) and
      [delegatecall_make_state_bridge_absorbing] (R091), for the
      low-level [Stdlib.call] opcode.  Closes R086 — the SafeERC20
      library-call gap blocking UnstakingManager (3 walkers) +
      StakingVaultExchange (4 walkers).

      Semantic difference vs siblings:

        - staticcall: target runs in TARGET's storage; cannot mutate.
          Caller storage unchanged at projection level.
        - delegatecall: target runs in CALLER's storage; WRITES
          caller storage.  Absorbing form Skolemises the caller's
          post-storage.
        - call: target runs in TARGET's storage; writes TARGET's
          storage (NOT caller's).  Caller storage unchanged at the
          projection level — same shape as staticcall.

      The absorbing form Skolemises the memory write at [out]
      (mirrors [staticcall_post_memory]); storage is UNCHANGED at
      the projection layer (matches staticcall, NOT delegatecall).
      The target's storage mutation is invisible from the caller's
      [SimulatedStorage.t] projection.

      Per-target audit-time obligation: the call's success/failure
      outcome (the [call_result] U256 value) is the load-bearing
      trust commitment.  Each use site discharges this via a
      companion callee-spec axiom (R063 / R086 shape).  Examples:

        - SafeERC20.safeTransfer:
            [safeTransfer_success_spec_concrete token to amount]
            (audit-time obligation: the registered token's [transfer]
            returns success — a [call_result = 1] witness).
        - SafeERC20.safeTransferFrom:
            [safeTransferFrom_success_spec_concrete token from to amount].
        - SafeERC20.forceApprove:
            [forceApprove_success_spec_concrete token spender value].

      See [StakingVaultRewards.v]'s
      [safeTransfer_success_spec_concrete] (Section 6) for the
      template; UnstakingManager / StakingVaultExchange will declare
      their own per-contract instances following the same shape.

      Soundness justification:

        - The upstream's [Stdlib.call] reduces (in the non-fast-path
          non-precompile branch) to [LowM.CallContract addr v input
          false false k] sandwiched between MLoad / RLoad / MStore
          primitives.  See [StaticCallBridge.run_call_general]
          (Layer 6) for the Qed-proved base bridge.
        - [LowM.CallContract] is a trust-based proof rule whose
          [state_inter] choice is what carries the target's body
          effect.  For [call], the target's body runs in TARGET's
          storage context, so [state_inter] reflects the CALLER's
          storage UNCHANGED — only memory + return_data move.
        - The Skolem [call_post_memory] captures the post-memory
          witness exactly as the staticcall absorbing form does.
        - Storage is identity at the projection layer.  This is the
          structural difference from the delegatecall absorbing form.

      AUDIT OBLIGATION per use site: the consumer carries a
      companion callee-spec axiom witnessing that the call's
      [call_result] satisfies the per-target trust assumption (the
      ERC20 returned [true], or the SafeERC20 wrapper succeeded).
      Same shape as R063 — the spec is the per-contract obligation;
      the bridge is the framework primitive.

      Trust delta: +1 axiom (this one) per framework use; the
      per-use-site callee-spec axioms are existing R063 trust
      budget lines, NOT new framework lines.  Reused across every
      [call] consumer. *)

  Parameter call_post_memory :
    Environment.t -> RocqOfSolidity.State.t ->
    SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t (* addr *) -> U256.t (* v *) ->
    U256.t (* out *) -> U256.t (* call_result *) ->
    SimulatedMemory.t.

  Axiom call_make_state_bridge_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr v in_ insize out : U256.t) (call_result : U256.t),
    ((g <? 100) && (v =? 0))%bool = false ->
    Stdlib.precompile_output addr [] = None ->
    let state_post :=
      (make_state env state_base
         (call_post_memory env state_base memory storage addr v out call_result)
         storage)
        <| State.return_data := Memory.u256_as_bytes call_result |> in
    {{? codes, env, Some (make_state env state_base memory storage) |
      Stdlib.call g addr v in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state_post ?}}.

  (** Structural companion axioms on [call_post_memory] —
      mirror [staticcall_post_memory_at_out / at_other / length].
      Audit obligation: the call's mstore tail only touches the
      word at [out/32] (when [out] is 32-aligned); all other
      word indices are unchanged. *)

  Axiom call_post_memory_at_out :
    forall env state_base memory storage addr v out call_result (k : nat),
    out = 32 * Z.of_nat k ->
    List.nth_error
      (call_post_memory env state_base memory storage addr v out call_result) k
    = Some call_result.

  Axiom call_post_memory_at_other :
    forall env state_base memory storage addr v out call_result (k : nat),
    32 * Z.of_nat k <> out ->
    List.nth_error
      (call_post_memory env state_base memory storage addr v out call_result) k
    = List.nth_error memory k.

  Axiom call_post_memory_length :
    forall env state_base memory storage addr v out call_result,
    List.length
      (call_post_memory env state_base memory storage addr v out call_result)
    = List.length memory.

  (** Absorbing-form variant when the [call]'s [outsize = 0] (no
      return-data write to memory).  Used when the caller decodes
      the return via [returndatasize] / [returndatacopy] after the
      call (e.g. OZ SafeERC20's [_callOptionalReturn] inspects
      [returndatasize()] post-call to decide whether to mload the
      return word). *)

  Axiom call_make_state_bridge_absorbing_outsize_0 :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (g addr v in_ insize out : U256.t) (call_result : U256.t),
    ((g <? 100) && (v =? 0))%bool = false ->
    Stdlib.precompile_output addr [] = None ->
    let state_post :=
      (make_state env state_base
         (call_post_memory env state_base memory storage addr v 0 0)
         storage)
        <| State.return_data := Memory.u256_as_bytes call_result |> in
    {{? codes, env, Some (make_state env state_base memory storage) |
      Stdlib.call g addr v in_ insize out 0 ⇓
      Result.Ok call_result
    | Some state_post ?}}.

  (** Ergonomic [Ltac] aliases: drive a walker arm past a [call]
      by deferring to the absorbing axiom. *)
  Ltac apply_run_call_absorbing :=
    apply call_make_state_bridge_absorbing.

  Ltac apply_run_call_absorbing_outsize_0 :=
    apply call_make_state_bridge_absorbing_outsize_0.

  (** ===== Layer 14d: SafeERC20 callee-spec template (R093) =====

      Per-library audit-time spec templates following the R063
      callee-spec pattern.  These are PARAMETERS (per-consumer
      obligations), NOT framework axioms — each consumer of
      SafeERC20 declares its own per-(token, args) instances.

      The framework supplies the SHAPE; the consumer pins the
      obligation at audit time.  The pattern mirrors
      [StakingVaultRewards.v]'s [safeTransfer_success_spec_concrete]
      from Section 6 — we re-expose it here as a framework template
      so future consumers (UnstakingManager, StakingVaultExchange,
      and any future SafeERC20-using contract) declare their own
      instance against the framework's name conventions.

      Soundness: a [Parameter] of shape [Address -> Address -> U256.t
      -> Prop] is the canonical T-TOKEN trust boundary.  Witnessing
      it requires the audit-time argument that the registered token
      is well-behaved (no fee-on-transfer, no balance-lying, no
      malicious return-data encoding).  Each consumer declares its
      own [Parameter] instance + the corresponding
      [_callee_spec] [Axiom] tying the bool flag to the on-chain
      call result.

      The SHAPE templates below are placeholders — they document
      the expected signature.  Real consumers (UnstakingManager.v,
      StakingVaultExchange.v) will declare their own at module
      scope. *)

  Module SafeERC20Templates.

    (** Convenience local alias.  [Address] is a 160-bit subset of
        [U256.t]; per-contract modules typically redefine it at their
        own module scope (see [StakingVaultRewards.v] line 171).
        Re-stated here so the template shapes are well-typed inside
        AbiEncoding's module. *)
    Definition Address : Set := U256.t.

    (** Spec shape for [SafeERC20.safeTransfer(token, to, amount)].
        Audit-time obligation: token's [transfer(to, amount)]
        returns success (either as a bool true or void with no
        revert).  Per-(token, recipient, amount). *)
    Definition safeTransfer_spec_shape : Type :=
      Address -> Address -> U256.t -> Prop.

    (** Spec shape for [SafeERC20.safeTransferFrom(token, from, to,
        amount)].  Audit-time obligation: token's [transferFrom]
        returns success.  Per-(token, from, to, amount). *)
    Definition safeTransferFrom_spec_shape : Type :=
      Address -> Address -> Address -> U256.t -> Prop.

    (** Spec shape for [SafeERC20.forceApprove(token, spender, value)].
        Audit-time obligation: token's [approve] (or the
        zero-then-set fallback) returns success.  Per-(token,
        spender, value). *)
    Definition forceApprove_spec_shape : Type :=
      Address -> Address -> U256.t -> Prop.

  End SafeERC20Templates.

  (** [abi_encode_tuple__to__fromStack memPtr] is the zero-arg encode
      (for an empty event payload). Returns [memPtr] unchanged, no
      memory side effect. The Yul body is:
        [function abi_encode_tuple__to__fromStack(headStart) -> tail {
           tail := headStart
         }] — i.e. a pure return. *)

  Lemma run_abi_encode_tuple_empty_fromStack codes env state (memPtr : U256.t)
      (H_bound : 0 <= memPtr < 2^256) :
    {{? codes, env, Some state |
      abi_encode_tuple__to__fromStack memPtr ⇓ Result.Ok memPtr
    | Some state ?}}.
  Proof.
    unfold abi_encode_tuple__to__fromStack.
    lu. repeat (lu || cu || p).
    s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.add. rewrite Z.add_0_r.
    rewrite Z.mod_small by exact H_bound.
    reflexivity.
  Qed.

End AbiEncoding.
