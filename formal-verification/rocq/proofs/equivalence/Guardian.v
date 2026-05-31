(** Phase 3.3 (task #216) — Guardian equivalence: hasRole view function.

    Guardian inherits from OpenZeppelin's [AccessControlEnumerable]
    and adds no own storage variables. Its on-chain storage is
    entirely OZ machinery, namely:

      AccessControl (slot 0):
        mapping(bytes32 => RoleData) private _roles;
        struct RoleData {
          mapping(address => bool) members;     (* offset 0 *)
          bytes32 adminRole;                    (* offset 1 *)
        }

      AccessControlEnumerable (slot 1+):
        mapping(bytes32 => EnumerableSet.AddressSet) private _roleMembers;

    For the [hasRole(role, account)] view function, only [_roles[role].members[account]]
    matters — that's a nested mapping at:

      slot = keccak256(account, keccak256(role, 0) + 0)
           = keccak256(account, keccak256(role, 0))     (* offset 0 *)

    This matches [StorableValue.Map2]'s nested-keccak shape exactly,
    keyed by [(role_bytes32, account)]. The mutator paths (grantRole,
    revokeRole, _grantRole) touch BOTH [_roles] and [_roleMembers] (the
    EnumerableSet) — those remain Phase 4 parked. This file closes the
    view-only direction.

    The sim ([simulations/Guardian.v]) abstracts the role machinery as
    three lists ([admins], [optimisticGuardians],
    [optimisticGuardianManagers]). To project these into the Map2
    shape, we treat the OZ role constants as opaque parameters
    ([DEFAULT_ADMIN_ROLE], [OPTIMISTIC_GUARDIAN_ROLE],
    [OPTIMISTIC_GUARDIAN_MANAGER_ROLE]) and populate the dict
    list-by-list. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Guardian.
Require Import ReserveGovernor.generated.Guardian_shallow.
Require Import ReserveGovernor.mocks.AccessControl.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module GuardianEquivalence.

  Import Guardian.

  (** ----- Keccak bound axiom (mirrors ThrottleLib's) -----

      States that [keccak256_tuple2 key index] returns a U256 value
      and that adding a small offset doesn't overflow. Used to
      discharge [Pure.add x 0 = x] when [x] is a keccak result.
      Same modeling assumption as ThrottleLib's
      [keccak256_tuple2_offset_bound] — documented in Audit.v
      Caveat-5. *)
  Axiom keccak256_tuple2_offset_bound :
    forall (key index offset : U256.t),
      0 <= offset < 32 ->
      0 <= keccak256_tuple2 key index /\
      keccak256_tuple2 key index + offset < 2 ^ 256.

  Lemma Pure_add_keccak_offset (key index offset : U256.t) :
    0 <= offset < 32 ->
    Pure.add (keccak256_tuple2 key index) offset
    = keccak256_tuple2 key index + offset.
  Proof.
    intros H_off.
    pose proof (keccak256_tuple2_offset_bound key index offset H_off) as [Hnn Hb].
    unfold Pure.add. apply Z.mod_small. lia.
  Qed.

  (** ----- OZ role bytes32 constants as opaque parameters -----

      The three named roles' bytes32 identifiers come from
      [keccak256("OPTIMISTIC_GUARDIAN_ROLE")] etc., except for
      [DEFAULT_ADMIN_ROLE] which is [bytes32(0)]. We don't need their
      concrete values to state or prove the equivalence — we just need
      stable names for the dict keys. The Solidity layer reads these
      from immutable constants at the call site; the sim is parametric
      over them.

      In a stronger proof (composed with the actual deployment
      bytecode), these would be instantiated to the concrete keccaks. *)
  Parameter DEFAULT_ADMIN_ROLE_bytes32             : U256.t.
  Parameter OPTIMISTIC_GUARDIAN_ROLE_bytes32       : U256.t.
  Parameter OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 : U256.t.

  (** ----- Project a (role, list<addr>) pair into Map2 entries -----

      Each (role, account) with [account] in the list maps to 1 (true).
      Absent entries return 0 (false) via [map_get_u256]'s default. *)
  Fixpoint members_for_role
      (role : U256.t) (addrs : list Address) :
      Dict.t (U256.t * U256.t) U256.t :=
    match addrs with
    | []         => []
    | a :: rest  => ((role, a), 1) :: members_for_role role rest
    end.

  (** ----- Full role-member dict from the sim's three lists ----- *)
  Definition role_member_map (s : State.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    members_for_role DEFAULT_ADMIN_ROLE_bytes32
                     s.(State.admins) ++
    members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                     s.(State.optimisticGuardians) ++
    members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                     s.(State.optimisticGuardianManagers).

  (** ----- Full projection -----

      Single slot at index 0: the Map2-shaped role-member mapping.
      Slot 1+ would hold AccessControlEnumerable's [_roleMembers], the
      EnumerableSet machinery. For the view-only equivalence we don't
      need to populate it; the unconstrained tail covers it. *)
  Definition proj_sim (s : State.t) : SimulatedStorage.t := [
    StorableValue.Map2 (role_member_map s)
  ].

  (** ----- Well-formedness ----- *)
  Lemma proj_sim_length (s : State.t) :
    List.length (proj_sim s) = 1%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_roles (s : State.t) :
    List.nth_error (proj_sim s) 0
    = Some (StorableValue.Map2 (role_member_map s)).
  Proof. reflexivity. Qed.

  Import Guardian_325.Guardian_325_deployed.

  (** ----- Bytes32 / address cleanup leaves -----

      Both [cleanup_t_bytes32] and [convert_t_bytes32_to_t_bytes32]
      are identity transforms at the U256-representation level. Same
      for address-cleanup at the Yul level. *)
  Lemma run_cleanup_t_bytes32 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_bytes32_to_t_bytes32 codes env state v :
    {{? codes, env, Some state |
      convert_t_bytes32_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_bytes32_to_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  (** Address cleanup leaf: under the 160-bit bound, [and v 0xff..0xff]
      reduces to [v]. *)
  Lemma run_cleanup_t_uint160_on_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    lu. repeat (lu || cu || p). s.
    replace (Pure.and v 1461501637330902918203684832716283019655932542975) with v.
    - apply RunO.Pure.
    - unfold Pure.and.
      change 1461501637330902918203684832716283019655932542975 with (Z.ones 160).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
  Qed.

  Lemma run_identity codes env state (v : U256.t) :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold identity.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_uint160 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             p. } p.
  Qed.

  Lemma run_convert_t_uint160_to_t_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160. exact H_v. } p. } p.
  Qed.

  Lemma run_convert_t_address_to_t_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address. exact H_v. } p. } p.
  Qed.

  (** ----- Nested mapping_index_access — bytes32 → RoleData struct ----- *)
  Module MappingIndexAccessBytes32RoleData.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32.
      l. {
        l. {
          c. { apply run_convert_t_bytes32_to_t_bytes32. }
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_keccak256_tuple2. }
          p.
        }
        p.
      }
      p.
    Qed.

  End MappingIndexAccessBytes32RoleData.

  (** ----- Nested mapping_index_access — address → bool ----- *)
  Module MappingIndexAccessAddressBool.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_key : 0 <= key < 2^160)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address.
      l. {
        l. {
          c. { apply run_convert_t_address_to_t_address. exact H_key. }
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_keccak256_tuple2. }
          p.
        }
        p.
      }
      p.
    Qed.

  End MappingIndexAccessAddressBool.

  (** ----- Bool-path leaves (offset-0 static variants) ----- *)

  Lemma run_cleanup_from_storage_t_bool codes env state v :
    {{? codes, env, Some state |
      cleanup_from_storage_t_bool v ⇓ Result.Ok (Z.land v 0xff)
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_shift_right_0_unsigned codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.shr. simpl. rewrite Z.div_1_r. reflexivity.
  Qed.

  Lemma run_extract_from_storage_value_offset_0_t_bool codes env state v :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_bool v ⇓
      Result.Ok (Z.land v 0xff)
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_bool.
    lu. l. { c. { apply run_shift_right_0_unsigned. }
             c. { apply run_cleanup_from_storage_t_bool. }
             p. } p.
  Qed.

  (** ----- Bool-value bound: every Dict.get hit on members_for_role is 1 ----- *)
  Lemma members_for_role_get_is_one
      (role : U256.t) (addrs : list Address) (key : U256.t * U256.t) (v : U256.t) :
    Dict.get (members_for_role role addrs) key = Some v -> v = 1.
  Proof.
    induction addrs as [|a rest IH]; simpl.
    - intro H; discriminate.
    - destruct (Dict.Eq.eqb _ _).
      + intro H; injection H as <-. reflexivity.
      + exact IH.
  Qed.

  Lemma map_get_app_split
      (m1 m2 : Dict.t (U256.t * U256.t) U256.t) (k : U256.t * U256.t) :
    StorableValue.map_get_u256 (m1 ++ m2) k
    = match Dict.get m1 k with
      | Some v => v
      | None   => StorableValue.map_get_u256 m2 k
      end.
  Proof.
    unfold StorableValue.map_get_u256.
    induction m1 as [|[k' v'] rest IH]; simpl.
    - reflexivity.
    - destruct (Dict.Eq.eqb k k'); [reflexivity | exact IH].
  Qed.

  Lemma members_for_role_map_get_bool
      (role : U256.t) (addrs : list Address) (key : U256.t * U256.t) :
    StorableValue.map_get_u256 (members_for_role role addrs) key = 0 \/
    StorableValue.map_get_u256 (members_for_role role addrs) key = 1.
  Proof.
    unfold StorableValue.map_get_u256.
    destruct (Dict.get (members_for_role role addrs) key) as [v|] eqn:Hg.
    - right. apply (members_for_role_get_is_one _ _ _ _ Hg).
    - left. reflexivity.
  Qed.

  Lemma role_member_map_values_bool (s : State.t) (key : U256.t * U256.t) :
    let v := StorableValue.map_get_u256 (role_member_map s) key in
    v = 0 \/ v = 1.
  Proof.
    cbv zeta. unfold role_member_map.
    rewrite map_get_app_split.
    destruct (Dict.get (members_for_role _ s.(State.admins)) key) as [v|] eqn:Hg1.
    - right. apply (members_for_role_get_is_one _ _ _ _ Hg1).
    - rewrite map_get_app_split.
      destruct (Dict.get (members_for_role _ s.(State.optimisticGuardians)) key) as [v|] eqn:Hg2.
      + right. apply (members_for_role_get_is_one _ _ _ _ Hg2).
      + apply members_for_role_map_get_bool.
  Qed.

  (** Z.land v 0xff = v for v ∈ {0, 1}. *)
  Lemma land_0xff_bool (v : Z) : v = 0 \/ v = 1 -> Z.land v 0xff = v.
  Proof. intros [-> | ->]; reflexivity. Qed.

  (** ----- sload via Map2 + proj_sim ----- *)
  Lemma run_sload_role_member_at_proj_sim
      codes env state_base memory sim (role account : U256.t) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sload (keccak256_tuple2 account (keccak256_tuple2 role 0)) ⇓
      Result.Ok (StorableValue.map_get_u256
                   (role_member_map sim) (role, account))
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    apply (Storage.run_sload_map2_u256 (proj_sim sim) 0
             (role_member_map sim) role account).
    apply proj_sim_roles.
  Qed.

  (** ----- Read-from-storage at offset 0 returns the clean 0/1 ----- *)
  Lemma run_read_role_member_at_proj_sim
      codes env state_base memory sim (role account : U256.t) :
    let v := StorableValue.map_get_u256
               (role_member_map sim) (role, account) in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_offset_0_t_bool
        (keccak256_tuple2 account (keccak256_tuple2 role 0)) ⇓
      Result.Ok v
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_0_t_bool.
    lu. l. { c. { apply run_sload_role_member_at_proj_sim. }
             c. { apply run_extract_from_storage_value_offset_0_t_bool. }
             apply RunO.PureEq; [|reflexivity].
             rewrite (land_0xff_bool _ (role_member_map_values_bool sim (role, account))).
             reflexivity. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Main equivalence theorem for fun_hasRole_1292 -----

      Body shape:
        slot ← 0 (the [_roles] mapping base)
        slot ← mapping_index_access_bytes32_struct_RoleData(0, role)
             = keccak256_tuple2(role, 0)
        slot ← add(slot, 0)  (* members field offset *)
        slot ← mapping_index_access_address_bool(slot, account)
             = keccak256_tuple2(account, keccak256_tuple2(role, 0))
        ret ← read_from_storage_split_offset_0_t_bool(slot)
            = role_member_map[(role, account)]

      The proof composes the two mapping_index_access lemmas (with
      memory threading via the cons-of-3 structure) and the
      read-from-storage lemma. *)
  Theorem run_hasRole_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role account : U256.t)
      (memory : SimulatedMemory.t)
      (H_role : U256.Valid.t role)
      (H_account : 0 <= account < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let expected := StorableValue.map_get_u256
                      (role_member_map sim) (role, account) in
    exists state',
    {{? codes, env, Some state |
      fun_hasRole_1292 role account ⇓
      Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state expected.
    (* First mapping_index_access: role → struct ptr *)
    pose proof (MappingIndexAccessBytes32RoleData.run_mapping_index_access
                  codes env state_base 0 role (proj_sim sim) memory H_mem) as Hmia1.
    destruct Hmia1 as (w0_a & w1_a & rest_a & Hmia1).
    set (mem_after1 := w0_a :: w1_a :: rest_a).
    (* Second mapping_index_access: account → bool slot, threaded from post-state of first *)
    pose proof (MappingIndexAccessAddressBool.run_mapping_index_access
                  codes env state_base (keccak256_tuple2 role 0) account
                  (proj_sim sim) mem_after1
                  H_account (ex_intro _ w0_a (ex_intro _ w1_a (ex_intro _ rest_a eq_refl))))
      as Hmia2.
    destruct Hmia2 as (w0_b & w1_b & rest_b & Hmia2).
    (* Derive a Pure.add-wrapped form of Hmia2 — the Yul body uses
       add(structPtr, 0) for the members field offset, producing
       Pure.add (keccak256_tuple2 role 0) 0 as the slot. The offset-
       bound axiom discharges the U256-fits-after-add side condition. *)
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 0) 0
                  = keccak256_tuple2 role 0).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (H_pa2 :
      Pure.add (keccak256_tuple2 account (keccak256_tuple2 role 0)) 0
      = keccak256_tuple2 account (keccak256_tuple2 role 0)).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (Hmia2_add :
      {{? codes, env, Some (make_state env state_base mem_after1 (proj_sim sim))
      | mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address
          (Pure.add (keccak256_tuple2 role 0) 0) account
        ⇓ Result.Ok (keccak256_tuple2 account (keccak256_tuple2 role 0))
      | Some (make_state env state_base (w0_b :: w1_b :: rest_b) (proj_sim sim)) ?}}).
    { rewrite H_pa1. exact Hmia2. }
    eexists.
    cbv zeta.
    unfold fun_hasRole_1292.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _
            ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia1 | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia2_add | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_offset_0_t_bool _) _
            ⇓ _ | _ ?}} =>
          try rewrite H_pa2;
          c; [ apply run_read_role_member_at_proj_sim | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    (* Residual: the outer continuation's [match ?output_inter with ...]
       reduces once ?output_inter is instantiated by the body's
       [apply RunO.Pure]. Force the reduction and close. *)
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ----- Task #234, Phase 1 — OZ AccessControl mutator equivalence ----- *)

  (** ===== Bridging the Guardian sim to the AccessControl mock =====

      The [mocks/AccessControl.v::State] models OZ's per-role membership
      lists with admin chain ([roles : list (Role * RoleEntry)]). The
      Guardian sim collapses to three role-keyed lists. The bridge
      builds the [AccessControl.State] that the Guardian sim represents,
      using the role-bytes32 parameters as keys and assuming every role's
      admin is [DEFAULT_ADMIN_ROLE] (matching Guardian.sol, which never
      calls [_setRoleAdmin]).

      Provided here for the equivalence statements; the proof of
      [add_member]-preserves-equivalence is a downstream task. *)
  Definition project_sim_to_ac (sim : State.t) : AccessControl.State :=
    {|
      AccessControl.roles :=
        (DEFAULT_ADMIN_ROLE_bytes32,
          {| AccessControl.members := sim.(State.admins);
             AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
        :: (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
          {| AccessControl.members := sim.(State.optimisticGuardians);
             AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
        :: (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
          {| AccessControl.members := sim.(State.optimisticGuardianManagers);
             AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
        :: nil
    |}.

  (** ===== _grantRole_1468 equivalence — STATEMENT =====

      Solidity source (OZ 5.4.0 AccessControl.sol, lines 181-189):

          function _grantRole(bytes32 role, address account)
              internal virtual returns (bool) {
            if (!hasRole(role, account)) {
              _roles[role].hasRole[account] = true;
              emit RoleGranted(role, account, _msgSender());
              return true;
            } else {
              return false;
            }
          }

      The faithful AccessControl mock semantics for this function are
      captured by [AccessControl.grantRole] (modulo the auth check —
      [_grantRole] itself is unguarded; the guard lives in
      [grantRole]/[_checkRole]). The interesting *value* contract:

        - Returns true if the account was newly granted (previously
          not a member).
        - Returns false if the account was already a member.
        - Storage side-effect: [_roles[role].hasRole[account] := 1]
          when granted; idempotent otherwise.

      The intended equivalence statement, which we WOULD prove if the
      shallow form were faithful, is:

          forall sim role account env state_base memory codes ...,
            let sim_ac    := project_sim_to_ac sim in
            let was_member := AccessControl.hasRole sim_ac role account in
            let sim_ac'   := <AccessControl helper applying members
                              add_member only — _grantRole is unguarded> in
            let storage'  := project_ac_to_storage sim_ac' in
            exists state_post,
            {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
              fun__grantRole_1468 role account ⇓
              Result.Ok (if was_member then 0 else 1)
            | Some state_post ?}}
            /\ state_post = make_state env state_base memory'_with_storage'_.

      ===== Generator-bug finding =====

      Inspecting [Guardian_shallow.v]'s [fun__grantRole_1468] (printed
      via [rocq_query Print]) reveals the success branch of the inner
      Yul switch is TRUNCATED — only the [iszero(hasRole)] gate fires,
      and on the not-a-member path the body is the no-op
      [pure (BlockUnit.Tt, var__1438)] with var__1438 = 0. The required
      sstore for [_roles[role].hasRole[account] = true] and the
      [var := 1] update never made it into the shallow embedding.

      Concretely the desugared form is:

          ...
          let~ expr_1442 := fun_hasRole_1292 role account in
          let~ expr_1443 := cleanup_t_bool (iszero expr_1442) in
          let_state~ var__1439 :=
            let~ δ := pure expr_1443 in
            if δ =? 0 then    (* already a member *)
              let~ expr_1463 := pure 0 in
              let~ var__1439 := pure expr_1463 in
              pure (BlockUnit.Leave, var__1439)
            else              (* SHOULD grant, but body is a no-op *)
              pure (BlockUnit.Tt, var__1438)
          default~ var__1439 in
          pure (BlockUnit.Tt, var__1439)

      Result: this function ALWAYS returns 0 with state unchanged,
      regardless of inputs. The intended bool-of-newly-granted return
      value and the storage update are both missing from the shallow
      form. This matches the R035 follow-on / generator-emission gap
      catalogued in [notes/shallow_embed_oz_gaps.md] gap 2.

      Two consequences:

        (a) The mutator-equivalence direction CANNOT be closed against
            the current shallow form — there is no sstore to project
            into. Closing it requires the upstream `shallow_embed.py`
            fix described in WISDOM R035 (option 2 in `oz_gaps.md`).

        (b) What we CAN faithfully prove is what the shallow form
            ACTUALLY does: returns 0 with state unchanged. We do this
            below — the proof exposes the bug.

      The [grantRole]-as-public-method theorem statement (using
      [AccessControl.grantRole] from the mock) is recorded as an
      [Admitted] target so downstream proofs can cite it. *)

  (** ----- What the shallow form ACTUALLY does (Qed) =====

      The shallow form's [fun__grantRole_1468] is a constant
      function: it returns 0 with state unchanged, regardless of
      [role] and [account] inputs. This proof closes with Qed and
      exposes the generator bug — when the shallow form is fixed
      (so that the success branch actually does the sstore), this
      theorem will need to be either retired or restated, with the
      mutator-equivalence direction taking over.

      Proof technique — note for the next reader:

      The let_state~ switch has two arms that emit DIFFERENT
      BlockUnit modes (Leave vs Tt) but the SAME value (0). A
      naive [eexists; case-split] tangles the [?output_inter]
      metavariable across both arms because the two branches need
      different output shapes ([(Leave, 0)] vs [(Tt, 0)]).

      The fix: **case-split BEFORE [eexists]**. This scopes the
      witness per-branch, so each branch independently instantiates
      its own [state'] (we use [exists state_hr.] explicitly), and
      the walker's intermediate metavars also live per-branch.

      The rest of the proof in each branch:
        1. Walker fires through the prelude (zero_value, hasRole call).
        2. Goal 1: iszero + cleanup_t_bool — close by direct stepping
           [c. { unfold iszero. apply RunO.Pure. } s. c. { unfold
           cleanup_t_bool. lu. repeat (lu || cu || p). } p].
        3. Goal 2: the let_state~ switch — unfold Shallow.let_state +
           apply [rewrite Hd] to commit the branch. In hd=true
           (already-member) branch, we step through the inner
           Let-Let-Pure chain producing (Leave, 0). In hd=false
           (not-a-member) branch, we step the else arm producing
           (Tt, 0). Either way the final var__1437 is 0.
        4. Goal 3: final unwrap [match (_, var__1437) => Pure var__1437]
           reduces by [cbn match; apply RunO.Pure]. *)
  Theorem run_grantRole_1468_observed_behavior
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role account : U256.t)
      (memory : SimulatedMemory.t)
      (H_role : U256.Valid.t role)
      (H_account : 0 <= account < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    exists state',
    {{? codes, env, Some state |
      fun__grantRole_1468 role account ⇓
      Result.Ok 0
    | Some state' ?}}.
  Proof.
    intros state.
    pose proof (run_hasRole_equivalent codes env state_base sim role account
                  memory H_role H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    destruct Hhr as (state_hr & Hhr).
    set (hr_v := StorableValue.map_get_u256
                   (role_member_map sim) (role, account)) in *.
    set (cond := Pure.iszero (Pure.iszero (Pure.iszero hr_v))) in *.
    (* Case-split BEFORE [eexists] so the walker's metavars are
       scoped per-branch — bypasses the R047 if-then-else
       metavariable trap (see WISDOM entry below). *)
    destruct (cond =? 0) eqn:Hd.
    - exists state_hr.
      cbv zeta. unfold fun__grantRole_1468.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call zero_value_for_split_t_bool _
              ⇓ _ | _ ?}} =>
            c; [ unfold zero_value_for_split_t_bool;
                 lu; repeat (lu || cu || p) | ]
        | |- {{? _, _, _ |
              LowM.Call (fun_hasRole_1292 _ _) _
              ⇓ _ | _ ?}} =>
            eapply RunO.Call; [ exact Hhr | apply RunO.Pure ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      + c. { unfold iszero. apply RunO.Pure. } s.
        c. { unfold cleanup_t_bool. lu. repeat (lu || cu || p). } p.
      + cbn match.
        unfold Shallow.let_state, M.strong_let_, M.let_, M.generic_let, M.pure.
        l. { l. { p. } cbn match. fold cond. rewrite Hd.
             l. { p. } l. { p. } p. } cbn match. p.
      + cbn match. apply RunO.Pure.
    - exists state_hr.
      cbv zeta. unfold fun__grantRole_1468.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call zero_value_for_split_t_bool _
              ⇓ _ | _ ?}} =>
            c; [ unfold zero_value_for_split_t_bool;
                 lu; repeat (lu || cu || p) | ]
        | |- {{? _, _, _ |
              LowM.Call (fun_hasRole_1292 _ _) _
              ⇓ _ | _ ?}} =>
            eapply RunO.Call; [ exact Hhr | apply RunO.Pure ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      + c. { unfold iszero. apply RunO.Pure. } s.
        c. { unfold cleanup_t_bool. lu. repeat (lu || cu || p). } p.
      + cbn match.
        unfold Shallow.let_state, M.strong_let_, M.let_, M.generic_let, M.pure.
        l. { l. { p. } cbn match. fold cond. rewrite Hd. p. } cbn match. p.
      + cbn match. apply RunO.Pure.
  Qed.

  (** ----- Intended mutator-equivalence statement, parked =====

      This is the theorem we WOULD prove if the shallow form were
      faithful (see generator-bug analysis above). It's recorded here
      as [Admitted] so downstream proofs can reference it by name once
      the upstream `shallow_embed.py` patch lands.

      The shape uses [AccessControl.grantRole] from [mocks/AccessControl.v]
      — that's the canonical Gallina semantics for OZ's _grantRole + the
      surrounding admin gate. *)

  (** Helper: under the projection, [AccessControl.hasRole] on
      [project_sim_to_ac sim] for role-keys we model matches
      the sim's own role-list membership predicates. Stated
      conditionally on the bytes32 role being one of our three
      named constants; absent that, the projection lookup falls
      through to an empty member list. Proof omitted (mechanical). *)
  Lemma project_sim_to_ac_hasRole_admin (sim : State.t) (a : Address) :
    AccessControl.hasRole (project_sim_to_ac sim)
                          DEFAULT_ADMIN_ROLE_bytes32 a
    = has_admin sim a.
  Proof.
    unfold AccessControl.hasRole, AccessControl.getRoleEntry,
           AccessControl.find_entry, project_sim_to_ac,
           has_admin.
    simpl. rewrite Z.eqb_refl. reflexivity.
  Qed.

  (** Theorem statement for the public [fun_grantRole_1359] equivalence.

      This is the canonical "mutator equivalence" target for task #234.
      The mutator's specification (using the [AccessControl] mock):

        AccessControl.grantRole sim caller role account =
        - revert_missing_role if !hasRole(getRoleAdmin(role), caller)
        - else Success {| roles := set_entry roles role
                            {| members := add_member members account;
                               admin   := admin |} |}

      In the Guardian-specific projection, only DEFAULT_ADMIN_ROLE
      can admin every role (Guardian.sol uses default admin chain), so
      the gate reduces to [has_admin sim env.(caller)]. The success
      shape's [roles] then matches a sim with [account] appended to
      whichever of [admins/optimisticGuardians/optimisticGuardianManagers]
      corresponds to [role].

      ===== Status =====

      [Admitted.] — the shallow form's [fun__grantRole_1468] does not
      perform the necessary sstore (see analysis above). The theorem
      is recorded as the target statement; closure requires either
      the upstream `shallow_embed.py` fix, OR a manual patch to the
      generated [Guardian_shallow.v]'s _grantRole arm. We do not
      land the manual patch — the generator drift would re-introduce
      it on the next sweep; the right fix is upstream. *)
  Theorem run_grantRole_1359_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role account : U256.t)
      (memory : SimulatedMemory.t)
      (H_role : U256.Valid.t role)
      (H_account : 0 <= account < 2^160)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    (* AccessControl.grantRole on the projected sim. The caller-admin
       gate is checked against [getRoleAdmin role] which, under our
       Guardian model where every role's admin is DEFAULT_ADMIN_ROLE,
       reduces to [hasRole DEFAULT_ADMIN_ROLE caller]. *)
    let sim_ac  := project_sim_to_ac sim in
    let caller  := env.(Environment.caller) in
    let result  := AccessControl.grantRole sim_ac caller role account in
    match result with
    | AccessControl.Result.Success sim_ac' =>
        exists (sim' : Guardian.State.t) (state' : option RocqOfSolidity.State.t),
          project_sim_to_ac sim' = sim_ac' /\
          {{? codes, env, Some state |
            fun_grantRole_1359 role account ⇓
            Result.Ok tt
          | state' ?}} /\
          (* Storage equivalence: post-state's role-member map
             reflects the AccessControl mutation. *)
          (exists memory',
            state' = Some (make_state env state_base memory' (proj_sim sim')))
    | AccessControl.Result.Revert _ _ =>
        (* Auth check failed: the contract reverts too. We don't
           pin the specific revert payload here because the shallow
           form's revert byte encoding is OZ-specific. *)
        True
    end.
  Proof.
    (* See doc comment above: the shallow form's fun__grantRole_1468
       drops the sstore on the success path, making this theorem
       unprovable against the current generated code. *)
  Admitted.

End GuardianEquivalence.

(** ===== WISDOM R046 footnote — generator drops sstore in _grantRole =====

    Documented in this file (see [run_grantRole_1359_equivalent]'s
    docstring above) and in [notes/shallow_embed_oz_gaps.md] gap 2.
    Summary for cross-reference:

    `shallow_embed.py` emits `Shallow.let_state ~ ... := [[
    Shallow.if_(| cond, succ, _ |) ]] default~ ...` for Yul switches
    where the inner success branch ([cond != 0]) contains state-update
    statements (`sstore` in particular). The current emission strips
    the body in the let_state's body lambda — visible in the desugared
    form as `else pure (BlockUnit.Tt, var__1438)` with no surrounding
    sstore.

    The bug is the same one R035 calls out: M.monadic can't descend
    into Shallow.let_state inside [[ ]] brackets. The shallow_embed
    workaround for YulIf (R035 partial fix) pre-binds the condition,
    but when the YulIf body itself rebinds the same variable AND
    contains an sstore, the body gets dropped on the way through.

    Reproduce: `rocq_query Print
    Guardian_325.Guardian_325_deployed.fun__grantRole_1468.` against
    the current shallow form — the switch's `else` arm body is the
    bare `pure (BlockUnit.Tt, var__1438)` no-op, with no sstore visible.

    Fix path: upstream `shallow_embed.py` — option 1 from
    `notes/shallow_embed_oz_gaps.md` (extend M.monadic to traverse
    `Shallow.let_state`). Until then, every OZ AccessControl mutator
    equivalence statement is [Admitted].

    Affected proof targets:
      - Guardian.grantOptimisticGuardian (delegates to _grantRole_704
        which delegates to _grantRole_1468)
      - VersionRegistry / RewardTokenRegistry role mutators (same
        OZ inheritance chain).
      - Any TimelockController role mutation.

    What still works pre-fix:
      - View-only equivalence (hasRole, getRoleAdmin, isRegistered,
        deployments) — already landed across Guardian / VersionRegistry
        / RewardTokenRegistry.
      - Mock-level proofs against [mocks/AccessControl.v] — the mock
        is sound; the gap is only in the shallow form. *)
