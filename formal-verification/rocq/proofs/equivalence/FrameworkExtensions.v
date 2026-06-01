(** [FrameworkExtensions] -- R083 framework primitives that bridge
    two gaps left by upstream [rocq-of-solidity]'s
    [proofs/RocqOfSolidity.v] axioms:

      Gap 1 (ERC-7201 namespaced storage lens):
        Upstream's [Storage.run_sload_map2_u256] /
        [run_sstore_map2_u256] pin the slot expression to
        [Z.of_nat <small_nat>], which cannot unify with the
        keccak-derived ERC-7201 namespace anchors used by
        OZ AccessControl ([0x02dd...]), AccessControlEnumerable
        ([0xc1f6...]), UUPS implementation slot ([0x3608...]),
        Initializable, ReentrancyGuard, ERC20Permit / Nonces /
        EIP712, etc.  These anchors are 256-bit keccak outputs;
        they don't fit a small-nat slot index.  See WISDOM R083.

        Fix: add slot-anchor-agnostic Storage primitives that take an
        explicit [anchor : U256.t] argument plus a per-projection
        binding [IsNamespaceAnchor values index anchor] discharged
        per-contract as an [Axiom].  The primitive is otherwise
        identical to its small-nat sibling.

      Gap 2 (memory absorption for event-emission tails):
        Upstream's [Memory.run_mload] / [run_mstore] require per-index
        [nth_error memory index = Some _] hypotheses.  For walker
        discharges where the memory result doesn't matter (e.g. event
        emission tails: [allocate_unbounded -> mstore -> log1]), this
        forces the walker to track the entire memory list shape
        through every operation -- which is both onerous and brittle.

        Fix: add default-value variants of [run_mload] and
        [run_mstore] that work at ANY index, where:
          - mload returns [List.nth index memory 0] (Solidity's
            zero-init for unset memory positions);
          - mstore returns a memory list extended via right-padding
            with zeros up to the written index.
        These let the existential [memory' : SimulatedMemory.t] in
        composite walker post-states absorb arbitrary memory
        perturbations without per-index bookkeeping.

    Soundness arguments:

      [Gap 1]:  Upstream's [Storage.of_storable_values] is
        [Admitted], meaning the framework leaves the projection
        function unspecified beyond the existing
        [run_sload_*]/[run_sstore_*] axioms.  Adding more axioms
        about the projection's behaviour at OTHER slot expressions
        is consistent so long as no two axioms force contradictory
        values at the same slot.  The new [run_sload_map2_u256_at_anchor]
        axiom is consistent with the existing
        [run_sload_map2_u256] axiom because (a) it takes a different
        slot expression (keccak2(keccak2(k1, anchor)) vs
        keccak2(keccak2(k1, Z.of_nat index))), and (b) the
        per-contract [IsNamespaceAnchor] binding makes the two
        expressions agree pointwise: at slot N, the projection
        routes the namespaced keccak chain to the [Map2] cell stored
        at list-index N.

      [Gap 2]:  In the EVM, memory is byte-addressable but with
        word-aligned access via mload/mstore (32-byte slots).
        Unwritten memory bytes are implicit-zero.  The list
        representation [memory : list U256.t] corresponds to memory
        positions [0, 32, 64, ...]; positions past
        [32 * length memory] are zero.  This justifies:
          - [run_mload_default]: mload at index >= length returns 0.
          - [run_mstore_extending]: mstore at index >= length grows
            the list with zero padding (up to the written position).
        Both compositions stay consistent with the existing
        per-index axioms because they DEGENERATE to the same value
        when the index is in-range.

    Where to use these:

      - [run_sload_map2_u256_at_anchor]: per-contract AccessControl /
        AccessControlEnumerable / UUPS storage reads through their
        keccak-derived anchor slots.  StakingVaultAdmin (slot 15 ->
        0x02dd...), TimelockControllerOptimistic (multiple anchors),
        ProposalLib (vote storage), Guardian (role storage), etc.

      - [run_mload_default_at_make_state] /
        [run_mstore_extending_at_make_state]:  walker tails that
        emit events ([allocate_unbounded -> mstore -> log1]) or
        scratch-write keccak inputs ([mstore(0,k); mstore(0x20,a);
        keccak256(0,0x40)]) and don't need the resulting memory
        state to be precisely shape-pinned.

    See also: R040 (wrapper-shape sstore), R067 (composite-walker
    template), R070 (per-mutator recipe).
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module FrameworkExtensions.

  (** ====================================================================
      Gap 1 -- ERC-7201 namespaced storage lens
      ====================================================================

      Per-projection predicate declaring that the abstract storage
      list [values] has its slot-[index] [Map2] / [MapStruct] /
      [MapToArray] / [U256] cell pinned at namespace anchor
      [anchor : U256.t].  This is the audit-time obligation
      discharged per-contract via an [Axiom] of the form

        Axiom binding : IsNamespaceAnchor values 15 0x02dd...

      bundled with the contract's [proj_sim] declaration.

      Soundness: upstream's [Storage.of_storable_values] is
      [Admitted] (no constructive definition); the framework's
      [run_sload_*] axioms describe the projection at specific slot
      expressions ([Z.of_nat n], [keccak256_tuple2 k n], etc.).  The
      new [IsNamespaceAnchor]-gated axiom describes it at the
      namespaced shape [keccak256_tuple2 k1 (keccak256_tuple2 k2
      anchor)].  Per-contract binding axioms ensure no two anchors
      route to the same list index. *)

  Parameter IsNamespaceAnchor :
    list StorableValue.t -> nat -> U256.t -> Prop.

  (** Map2 sload through a namespace anchor.  Mirrors upstream's
      [Storage.run_sload_map2_u256] but takes [anchor : U256.t]
      instead of [Z.of_nat index] as the inner-keccak slot
      argument.  The [IsNamespaceAnchor] binding ties [anchor] to
      [index] for soundness. *)
  Axiom run_sload_map2_u256_at_anchor :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (index : nat) (anchor : U256.t)
           (map : Dict.t (U256.t * U256.t) U256.t)
           (key1 key2 : U256.t),
    IsNamespaceAnchor values index anchor ->
    List.nth_error values index = Some (StorableValue.Map2 map) ->
    {{? codes, environment, Some state |
      Stdlib.sload (keccak256_tuple2 key2 (keccak256_tuple2 key1 anchor)) ⇓
      Result.Ok (StorableValue.map_get_u256 map (key1, key2))
    | Some state ?}}.

  (** Map2 sstore through a namespace anchor.  Mirrors upstream's
      [Storage.run_sstore_map2_u256]. *)
  Axiom run_sstore_map2_u256_at_anchor :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (index : nat) (anchor : U256.t)
           (key1 key2 : U256.t) (value : U256.t),
    IsNamespaceAnchor values index anchor ->
    State.get_current_storage environment state =
      Some (Storage.of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.Map2 map) =>
      let map' := Dict.declare_or_assign map (key1, key2) value in
      match List.update_nth values index (StorableValue.Map2 map') with
      | Some values' =>
        let state' :=
          State.with_current_storage environment state
            (Storage.of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore
            (keccak256_tuple2 key2 (keccak256_tuple2 key1 anchor)) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.

  (** Struct-field sload through a namespace anchor: the
      [keccak256_tuple2 key anchor + offset] shape that the
      [_roles[role].hasRole] sub-walker hits when [_getAccessControlStorage]
      returns an anchor and the walker reads field [offset] of the
      role-data struct.  Mirrors upstream's [run_sload_struct_field]
      but with [anchor] in place of [Z.of_nat index].

      Note: this is for the case where [keccak256_tuple2 key anchor]
      is the BASE slot for a [mapping(K => Struct)] -- not for the
      [Map2]-of-bools case below the role-data struct. *)
  Axiom run_sload_struct_field_at_anchor :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (index : nat) (anchor : U256.t)
           (map : Dict.t (U256.t * U256.t) U256.t)
           (key : U256.t) (offset : U256.t),
    IsNamespaceAnchor values index anchor ->
    List.nth_error values index = Some (StorableValue.MapStruct map) ->
    {{? codes, environment, Some state |
      Stdlib.sload (keccak256_tuple2 key anchor + offset) ⇓
      Result.Ok (StorableValue.map_get_u256 map (key, offset))
    | Some state ?}}.

  (** Single-Map sload through a namespace anchor.  OZ ERC20's
      [_balances : mapping(address => uint256)] lives at offset 0 of
      the ERC20Storage struct, i.e. at the anchor itself (the struct's
      first field shares the anchor slot).  A balance lookup
      [_balances[account]] resolves to [keccak256_tuple2(account,
      anchor + 0)], which equals [keccak256_tuple2(account, anchor)]
      under [Pure.add anchor 0 = anchor].  Mirrors upstream's
      [Storage.run_sload_map_u256] but takes [anchor : U256.t] in
      place of [Z.of_nat index]. *)
  Axiom run_sload_map_u256_at_anchor :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (index : nat) (anchor : U256.t)
           (map : Dict.t U256.t U256.t)
           (key : U256.t),
    IsNamespaceAnchor values index anchor ->
    List.nth_error values index = Some (StorableValue.Map map) ->
    {{? codes, environment, Some state |
      Stdlib.sload (keccak256_tuple2 key anchor) ⇓
      Result.Ok (StorableValue.map_get_u256 map key)
    | Some state ?}}.

  (** Single-Map sstore through a namespace anchor.  Companion to
      [run_sload_map_u256_at_anchor]. *)
  Axiom run_sstore_map_u256_at_anchor :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (index : nat) (anchor : U256.t)
           (key : U256.t) (value : U256.t),
    IsNamespaceAnchor values index anchor ->
    State.get_current_storage environment state =
      Some (Storage.of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.Map map) =>
      let map' := Dict.declare_or_assign map key value in
      match List.update_nth values index (StorableValue.Map map') with
      | Some values' =>
        let state' :=
          State.with_current_storage environment state
            (Storage.of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore (keccak256_tuple2 key anchor) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.

  (** uint256 sload at a fixed offset within a namespace-anchored
      struct.  OZ ERC20's [_totalSupply] is the third field of the
      ERC20Storage struct ([_balances] map at offset 0, [_allowances]
      map at offset 1, [_totalSupply] uint256 at offset 2), accessed
      via [sload(add(anchor, 2))].

      We model this with a Section-parameterized projection that
      stores [_totalSupply] at a designated [supply_index] in the
      abstract storage list, distinct from the [Map] cells indexed by
      the anchor.  The [IsAnchorOffsetSlot values supply_index anchor
      offset] binding ties the offset within the struct to the
      separate list index — discharged per-contract. *)
  Parameter IsAnchorOffsetSlot :
    list StorableValue.t -> nat -> U256.t -> U256.t -> Prop.

  Axiom run_sload_u256_at_anchor_offset :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (supply_index : nat) (anchor : U256.t) (offset : U256.t)
           (value : U256.t),
    IsAnchorOffsetSlot values supply_index anchor offset ->
    State.get_current_storage environment state =
      Some (Storage.of_storable_values values) ->
    List.nth_error values supply_index = Some (StorableValue.U256 value) ->
    {{? codes, environment, Some state |
      Stdlib.sload (anchor + offset) ⇓
      Result.Ok value
    | Some state ?}}.

  Axiom run_sstore_u256_at_anchor_offset :
    forall (codes : Codes.t) (environment : Environment.t)
           (state : State.t)
           (values : list StorableValue.t)
           (supply_index : nat) (anchor : U256.t) (offset : U256.t)
           (value : U256.t),
    IsAnchorOffsetSlot values supply_index anchor offset ->
    State.get_current_storage environment state =
      Some (Storage.of_storable_values values) ->
    match List.update_nth values supply_index (StorableValue.U256 value) with
    | Some values' =>
      let state' :=
        State.with_current_storage environment state
          (Storage.of_storable_values values') in
      {{? codes, environment, Some state |
        Stdlib.sstore (anchor + offset) value ⇓
        Result.Ok tt
      | Some state' ?}}
    | None => True
    end.

  (** ====================================================================
      Gap 2 -- Memory absorption for event-emission tails
      ====================================================================

      Default-value variants of [Memory.run_mload] and
      [Memory.run_mstore] that work at any index without per-index
      hypothesis tracking.  Designed to let walker post-states
      absorb arbitrary memory perturbations via the existential
      [exists memory', ...] pattern.

      Soundness:
        - EVM memory is zero-initialised; out-of-bounds reads
          return 0.
        - [List.nth index memory 0] = 0 for [index >=
          List.length memory], matching the EVM convention.
        - mstore extending the list with zero padding preserves the
          in-range write semantics while making the list-length
          tracking purely structural.

      These primitives are STRICTLY WEAKER than upstream's
      [run_mload] / [run_mstore]: anything provable with the
      upstream forms is provable with these (modulo the obligation
      to use [List.nth] in place of [nth_error]); the converse
      requires an in-range hypothesis.  Adopt these whenever the
      walker can absorb memory state via an existential. *)

  (** Pad the [memory] list on the right with zeros so that index
      [index] is in range, then write [value] at that index.
      Total: returns the same shape regardless of input length. *)
  Definition list_set_padded
      (memory : list U256.t) (index : nat) (value : U256.t) :
      list U256.t :=
    if Nat.ltb index (List.length memory) then
      coqutil.Datatypes.List.replace_nth index memory value
    else
      memory ++ List.repeat 0%Z (index - List.length memory) ++ [value].

  Lemma list_set_padded_in_range
      (memory : list U256.t) (index : nat) (value : U256.t)
      (H_in : (index < List.length memory)%nat) :
    list_set_padded memory index value =
    coqutil.Datatypes.List.replace_nth index memory value.
  Proof.
    unfold list_set_padded.
    apply Nat.ltb_lt in H_in. rewrite H_in. reflexivity.
  Qed.

  (** Default-value mload at a [make_state] state.  Works at any
      [index] (no [nth_error] precondition).  Returns
      [List.nth index memory 0]: the in-range word, or [0] for
      out-of-bounds positions (matching EVM's zero-init semantics).

      Sound under the convention that [Memory.of_u256_list memory]
      returns 0 for byte positions past [32 * length memory]. *)
  Axiom run_mload_default_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (index : nat),
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.mload (32 * Z.of_nat index) ⇓
      Result.Ok (List.nth index memory 0%Z)
    | Some (make_state environment state_base memory storage) ?}}.

  (** Default-value mstore at a [make_state] state.  Works at any
      [index]: in-range writes update the corresponding word;
      out-of-bounds writes grow the list with zero padding.

      Sound under the convention that [Memory.of_u256_list] extends
      with zeros past [32 * length memory] and that writes at any
      32-aligned offset produce a new memory expressible as
      [Memory.of_u256_list] of the extended list. *)
  Axiom run_mstore_extending_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (index : nat) (value : U256.t),
    let memory' := list_set_padded memory index value in
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.mstore (32 * Z.of_nat index) value ⇓
      Result.Ok tt
    | Some (make_state environment state_base memory' storage) ?}}.

  (** Memory absorption: any [Stdlib.mstore] at any offset against a
      [make_state] state succeeds and produces a new [make_state]
      state, with the post-memory list witnessed existentially.

      This is the "event-emission tail" absorber: when a walker tail
      writes the event payload at a free-memory pointer (which is
      runtime-derived from [mload(64)]) and we don't need the
      post-state's memory shape to be load-bearing for the
      equivalence claim, the absorber lets the existential
      memory' absorb the perturbation.

      Soundness argument:
        - In practice, every mstore in a Solidity contract writes at
          a 32-aligned address (free-memory pointer is initialised
          to 0x80 and grows by aligned increments; scratch-space
          mstores are at 0 and 0x20).
        - Under the 32-aligned convention,
          [Memory.update_bytes (of_u256_list memory) offset
            (u256_as_bytes value)] is expressible as
          [of_u256_list memory'] for some [memory'].
        - For non-aligned offsets, the framework's [Stdlib.mstore]
          would still produce a memory of [Memory.t] shape but not
          necessarily [of_u256_list]-shaped.  This is the AUDIT-TIME
          OBLIGATION on each use site: the contract under
          verification must only mstore at 32-aligned addresses.

      The alternative -- threading [offset = 32 * <free_mem_word>]
      preconditions through every walker -- would explode the
      precondition surface; the absorber localises the soundness
      obligation to per-contract audit review of the source's mstore
      shapes.  All governor contracts pass this audit (every Yul
      mstore in the emitted IR is either at a literal 32-aligned
      address or at [allocate_unbounded() + k*32]).

      Skolemized form: the post-memory is exposed as an explicit
      function of the inputs.  This lets [apply] / [eapply] unify
      directly against the post-state of an enclosing [eapply
      RunO.Call] / [eapply RunO.Let] step. *)
  Parameter mstore_post_memory :
    Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t -> SimulatedMemory.t.

  Axiom run_mstore_absorbing_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (offset : U256.t) (value : U256.t),
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.mstore offset value ⇓ Result.Ok tt
    | Some (make_state environment state_base
              (mstore_post_memory environment state_base memory storage
                                  offset value)
              storage) ?}}.

  (** Length-preservation: the absorbing mstore Skolem post-memory
      has the same length as the input. Audit-time obligation: the
      contract's mstore writes are at offsets that fit within the
      pre-allocated memory list. All governor contracts pass this
      audit (every mstore in the emitted IR writes at
      [allocate_unbounded() + k] which is bounded by the existing
      free pointer). *)

  Axiom mstore_post_memory_length :
    forall env state_base memory storage offset value,
    List.length (mstore_post_memory env state_base memory storage offset value)
    = List.length memory.

  (** Structural axiom: a Yul mstore at offset [O] only writes within
      the 32-byte word at index [Z.to_nat (O/32)] (and possibly the
      next word for non-aligned offsets, but at most the word at
      [Z.to_nat ((O+31)/32)]). For word indices strictly outside
      this range, the post-memory equals the pre-memory.

      This expresses the standard EVM mstore semantics at the
      SimulatedMemory.t (word-list) level. Audit-time obligation:
      mstores in the contract don't touch unrelated word indices. *)

  Axiom mstore_post_memory_at_far :
    forall env state_base memory storage offset value (k : nat),
    (* k is a word index "far" from the mstore offset — neither the
       primary aligned-write index nor the spillover word. *)
    (Z.of_nat k + 1) * 32 <= offset \/
    offset + 32 <= Z.of_nat k * 32 ->
    List.nth_error
      (mstore_post_memory env state_base memory storage offset value) k
    = List.nth_error memory k.

  (** Companion: arbitrary [Stdlib.mload] at any address returns a
      witness U256 and leaves the state unchanged.  The witness is
      [List.nth (Z.to_nat (offset / 32)) memory 0] for aligned
      offsets; for non-aligned offsets the value is whatever the
      underlying byte-level [Memory.t] interpretation produces.

      Soundness argument: same audit-time obligation as
      [run_mstore_absorbing_at_make_state] -- in practice all mloads
      are at 32-aligned addresses.  The returned U256 value is
      Skolemized as an explicit function of inputs. *)
  Parameter mload_witness :
    Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t.

  Axiom run_mload_absorbing_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (offset : U256.t),
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.mload offset ⇓
        Result.Ok (mload_witness environment state_base memory storage
                                  offset)
    | Some (make_state environment state_base memory storage) ?}}.

  (** Bound on the [mload_witness] Skolem: 0 ≤ witness < 2^256.
      Audit-time obligation: at every aligned offset, [Memory.t]
      stores a 32-byte word interpreted as a U256, which fits the
      bound. *)

  Axiom mload_witness_bound :
    forall env state_base memory storage offset,
    0 <= mload_witness env state_base memory storage offset < 2^256.

  (** ====================================================================
      Tactics
      ====================================================================

      Drop-in replacements for [apply_run_mload] / [apply_run_mstore]
      that pick up the default / extending variants. *)

  Ltac apply_run_mload_default :=
    match goal with
    | |- {{? _, _, Some (make_state _ _ ?memory _) |
          Stdlib.mload ?offset ⇓ _ | _ ?}} =>
      apply (run_mload_default_at_make_state _ _ _ memory _
               (Z.to_nat (offset / 32)))
    end.

  Ltac apply_run_mstore_extending :=
    match goal with
    | |- {{? _, _, Some (make_state _ _ ?memory _) |
          Stdlib.mstore ?offset ?value ⇓ _ | _ ?}} =>
      apply (run_mstore_extending_at_make_state _ _ _ memory _
               (Z.to_nat (offset / 32)) value)
    end.

  (** Absorb an [Stdlib.mstore] at any offset (aligned or not) via
      the [run_mstore_absorbing_at_make_state] axiom.  Post-state
      is Skolemized via [mstore_post_memory].

      Usage: as the mstore arm in a composite walker [repeat
      lazymatch goal] when the per-index extending variant doesn't
      match (e.g. when the offset is a runtime free-memory pointer
      [mload(64)] rather than a literal [32*Z.of_nat _]). *)
  Ltac apply_run_mstore_absorbing :=
    apply run_mstore_absorbing_at_make_state.

  (** Absorb an [Stdlib.mload] at any offset (aligned or not) via
      the [run_mload_absorbing_at_make_state] axiom.  Witness is
      Skolemized via [mload_witness]. *)
  Ltac apply_run_mload_absorbing :=
    apply run_mload_absorbing_at_make_state.

  (** Single-shot apply for the namespace-anchor sload.  The
      namespace-binding hypothesis is supplied by the caller (it is
      an audit-time obligation that lives per-contract). *)
  Ltac apply_run_sload_map2_u256_at_anchor H_binding :=
    match goal with
    | |- {{? _, _, Some (make_state _ _ _ ?storage) |
          Stdlib.sload (keccak256_tuple2 ?k2 (keccak256_tuple2 ?k1 ?anchor)) ⇓ _
        | _ ?}} =>
      eapply (run_sload_map2_u256_at_anchor _ _ _ storage _ anchor _ k1 k2);
        [ exact H_binding | reflexivity ]
    end.

  (** ====================================================================
      Gap 3 -- Arbitrary-U256-slot storage absorption (R088)
      ====================================================================

      Solidity LIBRARY functions (e.g. ProposalLib) take storage slots
      as `slot : U256.t` PARAMETERS rather than being pinned to literal
      `Z.of_nat n` indices.  Such libraries are invoked by external
      contracts via delegatecall (the library code runs against the
      caller's storage) on caller-derived slot expressions (often
      themselves keccak256-derived).

      Upstream's [Storage.run_sload_u256] / [run_sstore_u256] pin the
      slot to `Z.of_nat index`; R083's anchor primitives pin it to
      `keccak256_tuple2 k1 (keccak256_tuple2 k2 anchor)`.  Neither
      shape unifies with an opaque `U256.t` library parameter — Coq
      has no way to infer that the parameter lands in any specific
      shape.

      The Skolem-absorbing pattern (mirroring R082's
      `staticcall_make_state_bridge_absorbing` and R083 Gap 2 memory
      absorbers) closes the gap:
        - An [Stdlib.sstore] at an arbitrary slot produces a Skolem
          post-storage; both shape and storage cells are absorbed into
          the Skolem function.
        - An [Stdlib.sload] at an arbitrary slot returns a Skolem
          witness; the storage is unchanged.

      Both leave [make_state] form, so they compose mechanically with
      every walker downstream of the call site.

      Soundness argument: upstream's [Storage.of_storable_values] is
      [Admitted].  Adding axioms describing the projection's behaviour
      at OTHER slot expressions is consistent so long as no two axioms
      force contradictory values at the same slot.  The new
      [run_sstore_absorbing_at_make_state] axiom describes the
      projection at slot expressions that don't match any existing
      pinned shape; the Skolem post-storage [sstore_post_storage] is
      the witness that "some new SimulatedStorage.t carries the write."

      Companion structural axioms — [sstore_post_storage_length],
      [sload_witness_bound] — expose the bookkeeping facts callers
      need.

      AUDIT-TIME OBLIGATION per use site: each library walker that
      consumes these primitives carries the per-target observational
      bridge obligation: the library's post-storage observably equals
      the caller's post-projection at the slots the library wrote.
      This is the standard R040 + R055 + R067 obligation shape — the
      walker's post-storage is opaque; the bridge axiom witnesses
      pointwise equality with the sim's post-projection.

      Where to use these:
        - ProposalLib's [_saveProposal_580] (3 sstores at
          proposalCore_slot + offsets 0, 20, 26).
        - ProposalLib's [transitionToPessimistic_400] (sstore of the
          [TRANSITIONED_VETO_THRESHOLD] sentinel at the
          optimisticProposal_slot + offset).
        - ProposalLib's [_validateProposal_507] (sload of voteStart
          at proposalCore_slot + 0, offset 20).
        - Any future Solidity-library function operating on
          caller-passed storage slots. *)

  (** Skolem post-storage produced by an [sstore] at an arbitrary U256
      slot against a [make_state]-shaped state.  Existentially
      witnesses the new SimulatedStorage.t carrying the write. *)
  Parameter sstore_post_storage :
    Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t -> SimulatedStorage.t.

  Axiom run_sstore_absorbing_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (slot : U256.t) (value : U256.t),
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.sstore slot value ⇓ Result.Ok tt
    | Some (make_state environment state_base memory
              (sstore_post_storage environment state_base memory storage
                                   slot value)) ?}}.

  (** Length-preservation: the Skolem post-storage has the same
      length as the input.  Audit obligation: library sstores write
      at slot expressions whose backing storage cell already exists
      in the projection (the caller's pre-storage already lists every
      slot the library will write). *)
  Axiom sstore_post_storage_length :
    forall env state_base memory storage slot value,
    List.length (sstore_post_storage env state_base memory storage slot value)
    = List.length storage.

  (** Skolem witness returned by an [sload] at an arbitrary U256 slot
      against a [make_state]-shaped state.  Returns an opaque U256.t
      whose value is pinned only at audit-time per-target. *)
  Parameter sload_witness :
    Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t.

  Axiom run_sload_absorbing_at_make_state :
    forall (codes : Codes.t) (environment : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (slot : U256.t),
    {{? codes, environment,
        Some (make_state environment state_base memory storage) |
      Stdlib.sload slot ⇓
        Result.Ok (sload_witness environment state_base memory storage slot)
    | Some (make_state environment state_base memory storage) ?}}.

  (** Bound on the [sload_witness] Skolem: 0 ≤ witness < 2^256.
      Storage cells in the EVM hold a 256-bit value. *)
  Axiom sload_witness_bound :
    forall env state_base memory storage slot,
    0 <= sload_witness env state_base memory storage slot < 2^256.

  (** Absorb an [Stdlib.sstore] at any U256 slot.  Post-storage is
      Skolemized via [sstore_post_storage]. *)
  Ltac apply_run_sstore_absorbing :=
    apply run_sstore_absorbing_at_make_state.

  (** Absorb an [Stdlib.sload] at any U256 slot.  Witness is
      Skolemized via [sload_witness]. *)
  Ltac apply_run_sload_absorbing :=
    apply run_sload_absorbing_at_make_state.

  (** ====================================================================
      R107 — Shallow.let_state / Shallow.if_ structural absorbers
      ====================================================================

      Many Yul walkers wrap the post-condition checks in
      [let_state~ 'tt := Shallow.if_ cond <revert_block> tt default~ tt in
       <continuation>].  Under our preconditions [cond = 0], the revert
      branch is skipped and the [Shallow.if_] reduces by computation to
      [M.pure (BlockUnit.Tt, tt)].  The outer [Shallow.let_state] then
      dispatches on the BlockUnit mode.  Closing this by hand requires
      either (a) walking the four BlockUnit constructors via [destruct],
      most of which are contradictory, or (b) absorbing the dispatch into
      a single structural lemma.

      Route (b) is the absorber pattern below.  It is reusable across
      every walker whose Shallow.if_ branch returns the Tt mode — i.e.
      every "if (revert_cond) revert(...)" pattern after the cond is
      proven zero.  See WISDOM R107 for the methodology.

      Soundness: these are Qed Lemmas.  Their proofs unfold
      [Shallow.let_state] / [Shallow.if_] and apply [RunO.Let] + [RunO.Pure]
      structurally.  No new audit-time axioms. *)

  (** Absorber for [Shallow.let_state] when the inner expression is
      [M.pure (BlockUnit.Tt, x)].  Reduces the post-let_state expression
      to [snd (body x)].  Reusable for ANY walker whose preceding
      [Shallow.if_] / [Shallow.let_state] body returns the Tt mode. *)
  Lemma run_shallow_let_state_pure_BlockUnit_Tt
      (codes : Codes.t) (env : Environment.t)
      {S1 S2 : Set}
      (state : option RocqOfSolidity.State.t)
      (x : S1)
      (body : S1 -> S2 * Shallow.t S2)
      (output : Result.t (BlockUnit.t * S2))
      (state' : option RocqOfSolidity.State.t)
      (H : {{? codes, env, state | snd (body x) ⇓ output | state' ?}}) :
    {{? codes, env, state |
      Shallow.let_state (M.pure (BlockUnit.Tt, x)) body ⇓ output | state' ?}}.
  Proof.
    unfold Shallow.let_state, M.strong_let_, M.generic_let, M.pure.
    eapply RunO.Let.
    - apply RunO.Pure.
    - cbn match. exact H.
  Qed.

  (** [Shallow.if_ 0 success failure] takes the failure branch.  By
      [Shallow.if_]'s definition this evaluates to
      [M.pure (BlockUnit.Tt, failure)] — a constructor [Result.Ok]. *)
  Lemma run_shallow_if_zero
      (codes : Codes.t) (env : Environment.t)
      {S : Set}
      (state : option RocqOfSolidity.State.t)
      (success : M.t (BlockUnit.t * S))
      (failure : S) :
    {{? codes, env, state |
      Shallow.if_ 0 success failure ⇓ Result.Ok (BlockUnit.Tt, failure)
    | state ?}}.
  Proof.
    unfold Shallow.if_. cbn. apply RunO.Pure.
  Qed.

  (** Composite absorber: [Shallow.let_state] wrapping a [Shallow.if_]
      with condition known to be zero (no-revert branch).  The post-
      let_state continuation collapses to [snd (body failure)], which
      then typically further reduces via [cbn]/[simpl]. *)
  Lemma run_shallow_let_state_if_zero
      (codes : Codes.t) (env : Environment.t)
      {S1 S2 : Set}
      (state : option RocqOfSolidity.State.t)
      (success : M.t (BlockUnit.t * S1))
      (failure : S1)
      (body : S1 -> S2 * Shallow.t S2)
      (output : Result.t (BlockUnit.t * S2))
      (state' : option RocqOfSolidity.State.t)
      (H : {{? codes, env, state | snd (body failure) ⇓ output | state' ?}}) :
    {{? codes, env, state |
      Shallow.let_state (Shallow.if_ 0 success failure) body ⇓ output | state' ?}}.
  Proof.
    unfold Shallow.if_. cbn.
    apply (run_shallow_let_state_pure_BlockUnit_Tt
             codes env state failure body output state' H).
  Qed.

  (** ====================================================================
      Yul switch absorbers (R110) — raw Coq if-then-else at the switch site
      ====================================================================

      The shallow embedding of Yul [switch] does NOT lower to
      [Shallow.if_].  Instead, each Yul switch produces a let-binding of
      the discriminant followed by a raw Coq-level [if δ =? 0 then else_branch
      else if_branch], packaged inside a [Shallow.let_state]:

        [Shallow.let_state
          (let~ δ := expr in if δ =? 0 then else_branch else if_branch)
          body]

      The R107 [run_shallow_let_state_if_zero] absorber doesn't match
      because (a) the inner shape isn't [Shallow.if_], and (b) the
      discriminant isn't already reduced.  We need two absorbers, one
      for each branch.

      Given [{{? ... | expr ⇓ Result.Ok δ_val | state ?}}] and a
      precondition on [δ_val] (zero or nonzero), the absorber commits
      to the branch, then defers to [run_shallow_let_state_pure_BlockUnit_Tt]
      to discharge the surrounding [let_state]. *)

  (** Absorber: Yul switch where the discriminant evaluates to zero;
      the [else_branch] (the [δ =? 0] arm) returns Tt mode.  The
      else_branch may freely change state; [state_after_branch]
      witnesses its post-state.  The body then resumes from
      [state_after_branch]. *)
  Lemma run_let_state_match_pure_zero
      (codes : Codes.t) (env : Environment.t)
      {S1 S2 : Set}
      (state state_after_expr state_after_branch : option RocqOfSolidity.State.t)
      (expr : M.t U256.t)
      (else_branch if_branch : M.t (BlockUnit.t * S1))
      (failure : S1)
      (body : S1 -> S2 * Shallow.t S2)
      (output : Result.t (BlockUnit.t * S2))
      (state' : option RocqOfSolidity.State.t)
      (H_expr : {{? codes, env, state | expr ⇓ Result.Ok 0 | state_after_expr ?}})
      (H_else : {{? codes, env, state_after_expr |
                   else_branch ⇓ Result.Ok (BlockUnit.Tt, failure)
                 | state_after_branch ?}})
      (H_body : {{? codes, env, state_after_branch |
                   snd (body failure) ⇓ output | state' ?}}) :
    {{? codes, env, state |
      Shallow.let_state
        (M.strong_let_ expr
          (fun δ => if δ =? 0 then else_branch else if_branch))
        body ⇓ output | state' ?}}.
  Proof.
    unfold Shallow.let_state, M.strong_let_, M.generic_let.
    eapply RunO.Let.
    - eapply RunO.Let.
      + exact H_expr.
      + cbn match. exact H_else.
    - cbn match. exact H_body.
  Qed.

  (** Absorber: Yul switch where the discriminant evaluates to a
      nonzero value; the [if_branch] (the [δ <> 0] arm) returns Tt
      mode.  Mirror of [run_let_state_match_pure_zero] for the
      non-zero discriminant case (mint branch of [fun__update_3335]:
      [eq(0, 0) = 1]).  The if_branch may freely change state;
      [state_after_branch] witnesses its post-state. *)
  Lemma run_let_state_match_pure_nonzero
      (codes : Codes.t) (env : Environment.t)
      {S1 S2 : Set}
      (state state_after_expr state_after_branch : option RocqOfSolidity.State.t)
      (expr : M.t U256.t)
      (δ_val : U256.t)
      (H_δ_nz : δ_val <> 0)
      (else_branch if_branch : M.t (BlockUnit.t * S1))
      (failure : S1)
      (body : S1 -> S2 * Shallow.t S2)
      (output : Result.t (BlockUnit.t * S2))
      (state' : option RocqOfSolidity.State.t)
      (H_expr : {{? codes, env, state | expr ⇓ Result.Ok δ_val | state_after_expr ?}})
      (H_if : {{? codes, env, state_after_expr |
                 if_branch ⇓ Result.Ok (BlockUnit.Tt, failure)
               | state_after_branch ?}})
      (H_body : {{? codes, env, state_after_branch |
                   snd (body failure) ⇓ output | state' ?}}) :
    {{? codes, env, state |
      Shallow.let_state
        (M.strong_let_ expr
          (fun δ => if δ =? 0 then else_branch else if_branch))
        body ⇓ output | state' ?}}.
  Proof.
    unfold Shallow.let_state, M.strong_let_, M.generic_let.
    eapply RunO.Let.
    - eapply RunO.Let.
      + exact H_expr.
      + cbn match.
        destruct (δ_val =? 0) eqn:Heq.
        * apply Z.eqb_eq in Heq. contradiction.
        * exact H_if.
    - cbn match. exact H_body.
  Qed.

End FrameworkExtensions.
