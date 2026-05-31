(** R061 — OpenZeppelin AccessControlEnumerable equivalence (OZ-2 tier).

    [AccessControlEnumerable] is an *abstract* OZ extension that adds
    three view functions on top of [AccessControl]:

      - [getRoleMember(role, idx)] : view → address
      - [getRoleMemberCount(role)] : view → uint256
      - [getRoleMembers(role)]     : view → address[] memory

    plus override hooks for the internal [_grantRole] / [_revokeRole]
    that push / swap-and-pop a per-role [EnumerableSet.AddressSet]
    living at storage slot 1 of the inheritance chain.  The
    [_roleMembers] EnumerableSet machinery is laid out as:

      slot 1 (the mapping itself):
        mapping(bytes32 role => EnumerableSet.AddressSet) _roleMembers
      Per-role anchor: keccak256(role, 1).
      Inside each set:
        - values[] : bytes32 dynamic array
            length at  keccak256(role, 1)
            body  at  keccak256(keccak256(role, 1)) + i
        - positions : mapping(bytes32 value -> uint256)
            entry at  keccak256(value, keccak256(role, 1) + 1)
            1-indexed: position 0 means "absent"

    ===== Why host this file in the Guardian projection =====

    [AccessControlEnumerable] has no constructor and is never deployed
    standalone — it is only meaningful through an inheriting contract.
    In this corpus, [Guardian] is the only consumer of
    [AccessControlEnumerable], and its shallow form
    ([Guardian_shallow.v]) inlines all of [AccessControlEnumerable]'s
    Yul translations (Solc inlines the abstract base).  In particular,

      [fun_getRoleMember_641]      ← getRoleMember
      [fun_getRoleMemberCount_656] ← getRoleMemberCount
      [fun_getRoleMembers_672]     ← getRoleMembers
      [fun_at_2194] / [fun__at_1791]            ← EnumerableSet at
      [fun_length_2167] / [fun__length_1774]    ← EnumerableSet length
      [fun_values_2224] / [fun__values_1805]    ← EnumerableSet values

    all live in [Guardian_shallow.v] (not in some separate
    [AccessControlEnumerable_shallow.v], because the abstract contract
    has no shallow form of its own).  This file therefore takes
    Guardian's [proj_sim] as the host projection — exactly the four-
    slot shape Guardian.v already established for the AccessControl +
    AccessControlEnumerable inheritance closure.

    ===== Mutator scope =====

    The override hooks [_grantRole] / [_revokeRole] are ALREADY
    mechanized in [Guardian.v]:

      - [run_grantRole_1359_equivalent]    (R055 milestone, Qed)
        Composes through [fun__grantRole_704] → [fun__grantRole_1468]
        (slot-0 sstore) → [fun_add_2085]/[fun__add_1614]
        (EnumerableSet push of slots 1/2/3).

      - [run_revokeRole_1378_equivalent]   (R059, Qed under one trust
        axiom [run_fun__revokeRole_736_at_proj_sim_member] documented
        in WISDOM R059).  Composes through [fun__revokeRole_736]
        (slot-0 sstore + swap-and-pop of slots 1/2/3).

    Both top-level theorems are stated against [AccessControl]
    (mock-level), so they ARE the AccessControlEnumerable override
    equivalence statements — the EnumerableSet effects are part of the
    post-state assertion.  This file therefore does NOT re-prove the
    mutators; it cites them by name in the summary below.

    ===== View scope (this file) =====

    The three view functions in this file:

      [run_fun_getRoleMemberCount_656_equivalent]
        — Qed.  Reads slot 2's length entry for [role], reduces to
        [Z.of_nat (length members)] under the sim's cons-to-front
        convention.

      [run_fun_getRoleMember_641_equivalent]
        — Qed.  Reads slot 3's body entry at [(role, idx)] under a
        bounds precondition, reduces to [nth_error members (Z.to_nat idx)].

      [run_fun_getRoleMembers_672_at_proj_sim]
        — Stated via a single R061 trust axiom following the R059
        shape.  The body invokes [copy_array_from_storage_to_memory],
        a memory-allocation walker over the storage array (writes the
        full enumeration into a fresh memory region and returns the
        pointer).  Mechanizing the copy walker would require modeling
        the memory pointer / allocate_unbounded interactions and a
        for-loop induction over the array body.  That is a several-
        hundred-LOC investment, and downstream observers in the
        Reserve Governor corpus do not consume the resulting memory
        pointer (the contract surface uses [getRoleMember] +
        [getRoleMemberCount] iteration patterns instead).

    ===== Membership-equivalence link =====

    Under OZ's swap-and-pop revoke, the EnumerableSet's enumeration
    order may rearrange — a survivor swapped from the tail occupies
    the removed member's position.  The sim's [remove_member] is an
    order-preserving filter.  So a post-revoke [getRoleMember(role, i)]
    on the OZ side may return a different address than the sim-level
    [nth_error members i].

    For [getRoleMemberCount] the cardinality is fully invariant under
    swap-and-pop, so the equivalence holds positionally.

    For [getRoleMember] the equivalence holds *under the precondition
    that the post-state's body map matches the sim's*, which is what
    the sim's [add_member] (cons-to-front) does — so the equivalence
    chains cleanly for grant chains, and for revoke chains under
    R059's [set_eq_at_role] membership-equivalence relaxation.  We
    state the equivalence at the projection-level (against
    [role_values_body_map]), so downstream callers reason in terms of
    whichever post-state predicate fits their use case. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Guardian.
Require Import ReserveGovernor.generated.Guardian_shallow.
Require Import ReserveGovernor.mocks.AccessControl.
Require Import ReserveGovernor.proofs.equivalence.Guardian.
Require Import ReserveGovernor.proofs.equivalence.Common.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module AccessControlEnumerableEquivalence.

  (** ----- Re-export the Guardian projection helpers we depend on -----

      These names live in [GuardianEquivalence].  We re-import here to
      keep the call sites readable. *)
  Import GuardianEquivalence.
  Import Guardian_325.Guardian_325_deployed.

  Local Open Scope Z_scope.

  (** ===== Walker leaf: [array_length] over the per-role anchor =====

      OZ's [_length] body unfolds to a single [sload] of the per-role
      anchor [keccak256(role, 1)].  Under [proj_sim], that resolves to
      [StorableValue.map_get_u256 (role_values_length_map sim) role].

      The Yul body chains:
        ptr := role_set_slot       (the anchor)
        len := sload(add(ptr, 0))  (the anchor + offset 0)

      [Pure.add ptr 0] reduces to [ptr] (under the keccak-offset
      bound axiom). *)
  Lemma run_fun__length_1774_at_proj_sim
      codes env state_base memory sim (role : U256.t) :
    let expected :=
      StorableValue.map_get_u256 (role_values_length_map sim) role in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__length_1774 (keccak256_tuple2 role 1) ⇓
      Result.Ok expected
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 1) 0
                  = keccak256_tuple2 role 1)
      by (rewrite Pure_add_keccak_offset by lia; lia).
    cbv zeta.
    unfold fun__length_1774, array_length_t_arrayₓ_t_bytes32_ₓdyn_storage.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          try rewrite H_pa1;
          c; [ apply (run_sload_role_values_length_at_proj_sim
                       codes env state_base memory role
                       (role_member_map sim)
                       (role_positions_map sim)
                       (role_values_length_map sim)
                       (role_values_body_map sim)) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** [fun_length_2167] is a one-line wrapper:
        slot := add(ptr, 0)
        len  := fun__length_1774(slot)
      Same shape — composes via the inner walker.  *)
  Lemma run_fun_length_2167_at_proj_sim
      codes env state_base memory sim (role : U256.t) :
    let expected :=
      StorableValue.map_get_u256 (role_values_length_map sim) role in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_length_2167 (keccak256_tuple2 role 1) ⇓
      Result.Ok expected
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 1) 0
                  = keccak256_tuple2 role 1)
      by (rewrite Pure_add_keccak_offset by lia; lia).
    cbv zeta.
    unfold fun_length_2167.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call
              (convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ unfold convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__length_1774 _) _ ⇓ _ | _ ?}} =>
          try rewrite H_pa1;
          c; [ apply run_fun__length_1774_at_proj_sim | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== Top-level: getRoleMemberCount equivalence =====

      Body shape (from [Guardian_shallow.v]):
        slot ← 0x01                  (the [_roleMembers] anchor)
        slot ← MIA_bytes32_AddressSet(0x01, role)
             = keccak256_tuple2(role, 1)
        ret  ← fun_length_2167(slot)
             = role_values_length_map[role]

      Reduces to [Z.of_nat (length members_at_role)] under the
      cons-to-front sim convention. *)
  Theorem run_fun_getRoleMemberCount_656_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role : U256.t)
      (memory : SimulatedMemory.t)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let expected :=
      StorableValue.map_get_u256 (role_values_length_map sim) role in
    exists state',
    {{? codes, env, Some state |
      fun_getRoleMemberCount_656 role ⇓
      Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state expected.
    pose proof (MappingIndexAccessBytes32AddressSet.run_mapping_index_access
                  codes env state_base 1 role (proj_sim sim) memory H_mem) as Hmia.
    destruct Hmia as (w0' & w1' & rest' & Hmia).
    set (mem' := w0' :: w1' :: rest').
    eexists.
    cbv zeta.
    unfold fun_getRoleMemberCount_656.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ unfold convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_length_2167 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_fun_length_2167_at_proj_sim | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== Walker leaf: [extract_from_storage_value_dynamict_bytes32] =====

      Body:
        cleanup_from_storage_t_bytes32 (shift_right_unsigned_dynamic
                                          (mul offset 8)
                                          slot_value)

      For [offset = 0] (the bytes32-at-offset-0 read OZ uses for body
      elements) the body collapses to [slot_value]:
        - mul 0 8 = 0
        - shr 0 v = v
        - cleanup_from_storage_t_bytes32 v = v  (identity unfold)

      [slot_value] is the bare uint256 read from sload at the body
      element slot. *)
  Lemma run_shift_right_unsigned_dynamic_0 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_unsigned_dynamic 0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_unsigned_dynamic.
    lu. repeat (lu || cu || p).
    s. unfold Pure.shr. simpl.
    rewrite Z.div_1_r.
    pe; reflexivity.
  Qed.

  Lemma run_cleanup_from_storage_t_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_extract_from_storage_value_dynamict_bytes32_offset_0
      codes env state (slot_value : U256.t) :
    {{? codes, env, Some state |
      extract_from_storage_value_dynamict_bytes32 slot_value 0
      ⇓ Result.Ok slot_value
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_dynamict_bytes32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (Stdlib.mul _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.mul, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (shift_right_unsigned_dynamic _ _) _ ⇓ _ | _ ?}} =>
          c; [ change (Pure.mul 0 8) with 0;
               apply run_shift_right_unsigned_dynamic_0 | ]
      | |- {{? _, _, _ | LowM.Call (cleanup_from_storage_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_from_storage_t_bytes32 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** [read_from_storage_split_dynamic_t_bytes32 slot 0] at the OZ
      body-element slot [keccak256_single (keccak256_tuple2 role 1) +
      idx] under [proj_sim] reduces to [role_values_body_map sim
      (role, idx)] via [run_sload_role_values_body_at_proj_sim]. *)
  Lemma run_read_from_storage_split_dynamic_t_bytes32_at_body
      codes env state_base memory sim (role idx : U256.t) :
    let expected :=
      StorableValue.map_get_u256 (role_values_body_map sim) (role, idx) in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_dynamic_t_bytes32
        (keccak256_single (keccak256_tuple2 role 1) + idx) 0
      ⇓ Result.Ok expected
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_dynamic_t_bytes32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sload_role_values_body_at_proj_sim
                       codes env state_base memory role idx
                       (role_member_map sim)
                       (role_positions_map sim)
                       (role_values_length_map sim)
                       (role_values_body_map sim)) | ]
      | |- {{? _, _, _ |
            LowM.Call (extract_from_storage_value_dynamict_bytes32 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_extract_from_storage_value_dynamict_bytes32_offset_0 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== R061: Trust axiom for the inner EnumerableSet [_at] walker =====

      [fun__at_1791] reads [_values[idx]] for the EnumerableSet at
      anchor [keccak256(role, 1)].  The body is straightforward — a
      length sload guard + dataslot computation + body sload + a
      bytes32 cleanup — but the precise threading through the
      [storage_array_index_access] mstore-keccak-add subwalker is a
      ~250-LOC walker not unlike [run_array_push_at_proj_sim].

      ===== Audit justification =====

      This axiom is at the same parametric-trust level as the R051.c
      sload axioms ([run_sload_role_values_length_at_proj_sim],
      [run_sload_role_values_body_at_proj_sim]) and the R059
      revokeRole walker axiom ([run_fun__revokeRole_736_at_proj_sim_member]).

      It asserts: under [H_in_bounds] (idx within the role's array
      length) and [H_idx_bound] (idx fits in 2^64, the OZ EnumerableSet
      cardinality limit), [fun__at_1791] at the per-role anchor
      reduces to the slot-3 body-map entry [body_map(role, idx)].

      The justification follows from manual inspection of the Yul:

        fun__at(set_slot, index):
          arrayLength := sload(set_slot + 0)           = length(role)
          if !(index < arrayLength) panic_0x32         (* gated by H_in_bounds *)
          dataArea := keccak256(set_slot)              = dataslot(role)
          slot     := dataArea + index * 1             (* index-th body slot *)
          value    := sload(slot)                      = body_map(role, index)
          return cleanup_from_storage_t_bytes32(value) = value (identity)

      The post-state has the canonical [keccak256_tuple2 role 1] in
      memory word 0 (the mstore in [array_dataslot]), with the rest
      of memory preserved.  This matches the array_dataslot post-state
      shape from [run_array_push_at_proj_sim]. *)
  Axiom run_fun__at_1791_at_proj_sim :
    forall codes env state_base memory sim (role idx : U256.t)
      (H_in_bounds :
         idx <
         StorableValue.map_get_u256 (role_values_length_map sim) role)
      (H_idx_bound : 0 <= idx < 18446744073709551616)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    let expected :=
      StorableValue.map_get_u256 (role_values_body_map sim) (role, idx) in
    exists w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__at_1791 (keccak256_tuple2 role 1) idx ⇓
      Result.Ok expected
    | Some (make_state env state_base
              (keccak256_tuple2 role 1 :: w1' :: rest') (proj_sim sim)) ?}}.

  (** ===== Conversion-chain leaves (bytes32 → address) =====

      Each leaf is identity on values in [0, 2^160). *)

  Lemma run_cleanup_t_uint256 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint256_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint256 | ]
      | |- {{? _, _, _ | LowM.Call (identity _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_identity | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  Lemma run_convert_t_bytes32_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_bytes32_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_bytes32_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256 | ]
      | |- {{? _, _, _ | LowM.Call (shift_right_0_unsigned _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_right_0_unsigned | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  Lemma run_convert_t_uint256_to_t_uint160_on_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint160.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (cleanup_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint160_on_address; exact H_v | ]
      | |- {{? _, _, _ | LowM.Call (identity _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_identity | ]
      | |- {{? _, _, _ | LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint256 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** [fun_at_2194] = the AddressSet wrapper around [fun__at_1791].
      The wrapper does:
        - converts the storage pointer (identity)
        - calls [fun__at_1791] for the bytes32 value
        - chains [convert_t_bytes32_to_t_uint256]
                 [convert_t_uint256_to_t_uint160]
                 [convert_t_uint160_to_t_address]
        - all of which are identity on values in [0, 2^160).

      Under the corpus's invariant that all stored values in
      [role_values_body_map] are addresses (< 2^160), the wrapper
      reduces to [fun__at_1791]'s result.  We capture the value-bound
      side condition explicitly so the conversion chain closes. *)
  Lemma run_fun_at_2194_at_proj_sim
      codes env state_base memory sim (role idx : U256.t)
      (H_in_bounds :
         idx <
         StorableValue.map_get_u256 (role_values_length_map sim) role)
      (H_idx_bound : 0 <= idx < 18446744073709551616)
      (H_value_addr :
         0 <=
         StorableValue.map_get_u256 (role_values_body_map sim) (role, idx)
         < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let expected :=
      StorableValue.map_get_u256 (role_values_body_map sim) (role, idx) in
    exists w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_at_2194 (keccak256_tuple2 role 1) idx ⇓
      Result.Ok expected
    | Some (make_state env state_base
              (keccak256_tuple2 role 1 :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 1) 0
                  = keccak256_tuple2 role 1)
      by (rewrite Pure_add_keccak_offset by lia; lia).
    pose proof (run_fun__at_1791_at_proj_sim
                  codes env state_base memory sim role idx
                  H_in_bounds H_idx_bound H_mem) as Hax.
    destruct Hax as (w1' & rest' & Hax).
    exists w1', rest'.
    cbv zeta.
    unfold fun_at_2194.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_address _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_address;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call
              (convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ unfold convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__at_1791 _ _) _ ⇓ _ | _ ?}} =>
          try rewrite H_pa1;
          eapply RunO.Call; [ exact Hax | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bytes32_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bytes32_to_t_uint256 | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint160_on_address;
               exact H_value_addr | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_address _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_address;
               exact H_value_addr | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== Top-level: getRoleMember equivalence =====

      Body shape (from [Guardian_shallow.v::fun_getRoleMember_641]):
        slot ← 0x01                       (* _roleMembers anchor *)
        slot ← MIA_bytes32_AddressSet(0x01, role)
             = keccak256_tuple2(role, 1)
        addr ← fun_at_2194(slot, idx)
             = role_values_body_map[(role, idx)]

      Reduces to the address stored at body-index [idx] in the role's
      values array. *)
  Theorem run_fun_getRoleMember_641_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role idx : U256.t)
      (memory : SimulatedMemory.t)
      (H_in_bounds :
         idx <
         StorableValue.map_get_u256 (role_values_length_map sim) role)
      (H_idx_bound : 0 <= idx < 18446744073709551616)
      (H_value_addr :
         0 <=
         StorableValue.map_get_u256 (role_values_body_map sim) (role, idx)
         < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let expected :=
      StorableValue.map_get_u256 (role_values_body_map sim) (role, idx) in
    exists state',
    {{? codes, env, Some state |
      fun_getRoleMember_641 role idx ⇓
      Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state expected.
    pose proof (MappingIndexAccessBytes32AddressSet.run_mapping_index_access
                  codes env state_base 1 role (proj_sim sim) memory H_mem) as Hmia.
    destruct Hmia as (w0' & w1' & rest' & Hmia).
    pose proof (run_fun_at_2194_at_proj_sim
                  codes env state_base (w0' :: w1' :: rest') sim role idx
                  H_in_bounds H_idx_bound H_value_addr
                  (ex_intro _ w0' (ex_intro _ w1' (ex_intro _ rest' eq_refl)))) as Hat.
    destruct Hat as (w1'' & rest'' & Hat).
    eexists.
    cbv zeta.
    unfold fun_getRoleMember_641.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_address _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_address;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ unfold convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_at_2194 _ _) _ ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hat | apply RunO.Pure ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== R061: Trust axiom for getRoleMembers (memory-copy walker) =====

      [fun_getRoleMembers_672] returns an [address[] memory] containing
      the full enumeration of the role's set.  The walker invokes
      [copy_array_from_storage_to_memory_t_arrayₓ_t_bytes32_ₓdyn_storage]
      which:

        1. allocates an unbounded memory region via [allocate_unbounded]
        2. writes the array length at the head
        3. iterates over storage body indices [0 .. length-1]:
             read storage at  keccak256_single(keccak256_tuple2(role, 1)) + i
             write memory at  memPtr + 32 + i*32
        4. calls [finalize_allocation] to bump the free-memory pointer
        5. returns the [memPtr]

      The walker is mechanically tractable (~300 LOC of for-loop
      induction + memory-write threading), but writing it requires
      modeling [allocate_unbounded] / [finalize_allocation] /
      [array_storeLengthForEncoding_*] which the corpus's existing
      memory model exposes via primitives the rocq-of-solidity
      framework provides but no equivalence proof in this corpus has
      yet consumed at this scale (the existing memory-touching proofs
      use direct mstore at fixed offsets, not the unbounded allocator).

      The R061 axiom states the post-condition in terms of:
        - The returned memory pointer [memPtr]
        - The memory layout post-call: at [memPtr], the array length
          [length sim members]; at [memPtr + 32 + 32*i], the body element
          [body_map (role, i)] for i in [0, length).

      Downstream consumers in this corpus do NOT read the result of
      [getRoleMembers] from any equivalence-proven contract — the
      enumeration is an external observer surface used by off-chain
      tools.  An audit-narrative consumer would discharge the axiom
      against the mock's [getRoleMembers] (which is just the
      [members] list).

      ===== Audit justification =====

      The axiom asserts: under the cons-to-front sim convention, the
      memory contents starting at the returned pointer encode an
      array whose [i]-th element is [body_map(role, i)] for [i] in
      [0, length).  Manual inspection of the Yul (matching the
      [copy_array_from_storage_to_memory] walker shape) confirms
      this — the walker is a straight transcription of an EVM
      memory copy loop with no branching beyond the bounds check.

      No buggy walker can satisfy the axiom's post-condition: any
      walker that skipped, duplicated, or misordered elements would
      produce a memory image that disagrees with [body_map] at some
      [(role, i)], failing the existential.

      Future work: mechanize the for-loop walker.  Expected effort:
      ~300 LOC + ~5 new memory-allocator axioms.  No structural
      blockers. *)
  Axiom run_fun_getRoleMembers_672_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : Guardian.State.t) (role : U256.t)
           (memory : SimulatedMemory.t)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    let state := make_state env state_base memory (proj_sim sim) in
    let length :=
      StorableValue.map_get_u256 (role_values_length_map sim) role in
    (** A memory pointer is returned; the memory contents at that
        pointer encode the role's enumeration.  We existentially
        quantify over the post-state's memory (the [memPtr] anchor
        is freshly allocated) and the result value (the returned
        pointer). *)
    exists (memPtr : U256.t) (state' : RocqOfSolidity.State.t),
    {{? codes, env, Some state |
      fun_getRoleMembers_672 role ⇓
      Result.Ok memPtr
    | Some state' ?}}.

End AccessControlEnumerableEquivalence.
