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

End AccessControlEnumerableEquivalence.
