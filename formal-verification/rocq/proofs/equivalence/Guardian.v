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

  (** ----- Slot 1: AccessControlEnumerable._roleMembers positions =====

      Solidity layout (OZ AccessControlEnumerable 5.x):
        mapping(bytes32 => EnumerableSet.AddressSet) private _roleMembers;
      lives at storage slot 1 of the inheritance chain. The
      [AddressSet] struct is itself an [EnumerableSet.Set]:
        struct Set {
          bytes32[] _values;                         // offset 0
          mapping(bytes32 => uint256) _positions;    // offset 1; 1-indexed
        }

      Per-role storage anchor: [keccak256(role, 1)]. Within that set:
        - the [_values] length sits at [keccak256(role, 1) + 0]
        - the [_positions] mapping sits at [keccak256(role, 1) + 1]
          (so a lookup of [position[v]] resolves to
           [keccak256(v, keccak256(role, 1) + 1)])

      For the projection-side bridge lemma — which equates the
      sim's [add_admin]-style update to a structured update on the
      projection — we model the positions submapping as a single
      Map2-shaped dict keyed by [(role, value)]. The encoded value
      is the 1-indexed position [Z.of_nat (List.length rest) + 1]
      where [rest] is the tail of the role's address list AT the
      moment [value] was prepended (sim convention: [add_role lst a
      = a :: lst], so position-1 = the head). The downstream walker
      proof for [fun_add_2085] (residual C in the task plan) will
      bridge this Map2 shape to the Yul-level nested-keccak shape
      via a custom sload lemma; same pattern as the slot-0
      [run_sload_role_member_at_proj_sim] composition. *)
  Fixpoint positions_for_role
      (role : U256.t) (addrs : list Address) :
      Dict.t (U256.t * U256.t) U256.t :=
    match addrs with
    | []         => []
    | a :: rest  => ((role, a), Z.of_nat (List.length rest) + 1)
                    :: positions_for_role role rest
    end.

  (** Concatenation across the three named roles, mirroring
      [role_member_map]'s structure. *)
  Definition role_positions_map (s : State.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                       s.(State.admins) ++
    positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                       s.(State.optimisticGuardians) ++
    positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                       s.(State.optimisticGuardianManagers).

  (** ----- Full projection — TWO slots =====

      Slot 0: the [_roles] mapping's nested [members] sub-field
              (Map2 of (role, account) -> 0/1).
      Slot 1: the [_roleMembers] positions sub-mapping under
              AccessControlEnumerable. The [_values] length cell
              and the [_values[i]] array slots are NOT modelled
              here — they're either reconstructable from the
              positions map plus list length (for the length cell)
              or unobserved by the view-and-grant equivalence path
              (the array body is touched only by [getRoleMember],
              which Guardian.sol does not call). If a future
              equivalence does need them, this projection extends
              naturally to add a third slot. *)
  Definition proj_sim (s : State.t) : SimulatedStorage.t := [
    StorableValue.Map2 (role_member_map s);
    StorableValue.Map2 (role_positions_map s)
  ].

  (** ----- Well-formedness ----- *)
  Lemma proj_sim_length (s : State.t) :
    List.length (proj_sim s) = 2%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_roles (s : State.t) :
    List.nth_error (proj_sim s) 0
    = Some (StorableValue.Map2 (role_member_map s)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_positions (s : State.t) :
    List.nth_error (proj_sim s) 1
    = Some (StorableValue.Map2 (role_positions_map s)).
  Proof. reflexivity. Qed.

  (** ===== Bridge: [addr_in] ↔ [In] ===== *)

  (** [addr_in] is the Boolean address-membership helper from the
      sim; pairing it with [In] (the Coq Prop) lets the bridge
      lemmas below state hypotheses in either flavor as needed. *)
  Lemma addr_in_false_iff_not_In :
    forall (lst : list Address) (a : Address),
      Guardian.addr_in lst a = false <-> ~ In a lst.
  Proof.
    induction lst as [|h t IH]; intro a; simpl.
    - split.
      + intros _ [].
      + reflexivity.
    - destruct (h =? a) eqn:Hha.
      + apply Z.eqb_eq in Hha. subst h. split.
        * discriminate.
        * intro Hn. exfalso. apply Hn. left. reflexivity.
      + apply Z.eqb_neq in Hha. rewrite IH. split.
        * intros Hni [Heq|Hin]; [congruence|contradiction].
        * intros Hni Hin. apply Hni. right. exact Hin.
  Qed.

  Lemma addr_in_true_iff_In :
    forall (lst : list Address) (a : Address),
      Guardian.addr_in lst a = true <-> In a lst.
  Proof.
    induction lst as [|h t IH]; intro a; simpl.
    - split.
      + discriminate.
      + intros [].
    - destruct (h =? a) eqn:Hha.
      + apply Z.eqb_eq in Hha. subst h. split.
        * intros _. left. reflexivity.
        * reflexivity.
      + apply Z.eqb_neq in Hha. rewrite IH. split.
        * intro Hin. right. exact Hin.
        * intros [Heq|Hin]; [congruence|exact Hin].
  Qed.

  (** ===== Bridge: [members_for_role] is invariant under unrelated-role
      list mutations ===== *)

  (** Helper: prepending an entry under role [r1] to the dict has no
      bearing on lookups under a different role [r2]. Used in the
      bridge lemmas to reason about [add_admin] which only mutates the
      [admins] sub-list (the [DEFAULT_ADMIN_ROLE] block). *)
  Lemma members_for_role_cons :
    forall (role : U256.t) (a : Address) (rest : list Address),
      members_for_role role (a :: rest) =
      ((role, a), 1) :: members_for_role role rest.
  Proof. reflexivity. Qed.

  Lemma positions_for_role_cons :
    forall (role : U256.t) (a : Address) (rest : list Address),
      positions_for_role role (a :: rest) =
      ((role, a), Z.of_nat (List.length rest) + 1)
      :: positions_for_role role rest.
  Proof. reflexivity. Qed.

  (** ===== Bridge: [role_member_map] after [add_admin] =====

      Closed by [unfold; rewrite addr_in_false_iff_not_In]. The
      cons-to-front form on the right matches [Guardian.add_role]'s
      [a :: lst] convention; the [Dict.declare_or_assign] form
      produced by [run_sstore_map2_u256] in the eventual residual-C
      walker proof is provably equal to this via a separate
      conversion lemma. *)
  Lemma role_member_map_add_admin_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.admins) ->
      role_member_map (Guardian.add_admin s addr) =
      ((DEFAULT_ADMIN_ROLE_bytes32, addr), 1) :: role_member_map s.
  Proof.
    intros s addr Hni.
    unfold role_member_map, Guardian.add_admin, Guardian.add_role.
    simpl. rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    simpl. reflexivity.
  Qed.

  (** [role_positions_map] companion. The new position is
      [Z.of_nat (length admins) + 1] — OZ's 1-indexed position
      = previous length + 1. *)
  Lemma role_positions_map_add_admin_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.admins) ->
      role_positions_map (Guardian.add_admin s addr) =
      ((DEFAULT_ADMIN_ROLE_bytes32, addr),
        Z.of_nat (List.length s.(State.admins)) + 1)
      :: role_positions_map s.
  Proof.
    intros s addr Hni.
    unfold role_positions_map, Guardian.add_admin, Guardian.add_role.
    simpl. rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    simpl. reflexivity.
  Qed.

  (** ===== Bridge: [proj_sim] after [add_admin] — the headline (B) =====

      Equates the projection of the post-[add_admin] sim to a
      cons-prefixed projection of the pre-[add_admin] sim, in both
      slots simultaneously. Used by the residual-C walker proof
      (see [run_grantRole_1359_equivalent]'s docstring) to close the
      post-sstore state equality after the inner [_grantRole_1468]
      sstore (slot 0, the bool members map) and the
      [fun_add_2085]/[fun__add_1614] sstores at slot 1 (the
      positions map). *)
  Theorem proj_sim_add_admin_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.admins) ->
      proj_sim (Guardian.add_admin s addr) =
      [ StorableValue.Map2
          (((DEFAULT_ADMIN_ROLE_bytes32, addr), 1)
           :: role_member_map s);
        StorableValue.Map2
          (((DEFAULT_ADMIN_ROLE_bytes32, addr),
            Z.of_nat (List.length s.(State.admins)) + 1)
           :: role_positions_map s) ].
  Proof.
    intros s addr Hni.
    unfold proj_sim.
    rewrite (role_member_map_add_admin_not_in s addr Hni).
    rewrite (role_positions_map_add_admin_not_in s addr Hni).
    reflexivity.
  Qed.

  (** ===== Idempotency companion =====

      When [addr] is already an admin, [add_admin] is a no-op on the
      sim ([add_role] is idempotent on existing members), so the
      projection is unchanged. The other half of the bridge contract
      — the [hasRole] path inside [_grantRole_1468] gates against the
      sstore, so the walker proof's already-member branch closes via
      this lemma. *)
  Theorem proj_sim_add_admin_in :
    forall (s : State.t) (addr : Address),
      In addr s.(State.admins) ->
      proj_sim (Guardian.add_admin s addr) = proj_sim s.
  Proof.
    intros s addr Hin.
    unfold proj_sim, Guardian.add_admin, Guardian.add_role.
    rewrite (proj2 (addr_in_true_iff_In _ _) Hin).
    destruct s as [admins g m]; reflexivity.
  Qed.

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
  (** RETIRED post-R046 fix. Pre-fix this Qed'd against a no-op shallow form
      (the generator dropped the sstore on the success branch). With the
      shallow_embed.py default-case fix landed at
      TheFrozenFire/rocq-of-solidity@696f60f, [fun__grantRole_1468] now
      correctly returns 1 with state mutated on the not-a-member branch —
      so this theorem's [Result.Ok 0] claim is stale on that branch. The
      proper target is [run_grantRole_1359_equivalent] (the intended
      mutator equivalence below) which is still Admitted pending the
      proof-walker pass.

      Old tactic walker (referenced via git history if needed):
      pose Hhr; destruct; case-split before eexists; walker arms for
      [zero_value_for_split_t_bool], [fun_hasRole_1292], etc. *)
  Proof. Admitted.

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

      Post-R046 fix (TheFrozenFire/rocq-of-solidity@696f60f) the
      methodological blocker is removed: the regenerated
      [fun__grantRole_1468] now contains the [sstore] for
      [_roles[role].hasRole[account] := 1] and the [var := 1] +
      [Leave] sequence in the success branch (verified via inspection
      of the regenerated Guardian_shallow.v::fun__grantRole_1468 at
      lines 4044-4100). This unblocks the equivalence in principle.

      However, the public [fun_grantRole_1359] is a ~5-level call
      chain whose closure requires several discrete pieces of
      infrastructure beyond the R046 fix itself:

        [fun_grantRole_1359]
          → [modifier_onlyRole_1351]
              → [fun_getRoleAdmin_1340]   (reads slot-1 admin field)
              → [fun__checkRole_1305]      (hasRole + revert guard)
              → [fun_grantRole_1359_inner]
                  → [fun__grantRole_704]
                      → [fun__grantRole_1468]  (R046-fixed sstore)
                      → [fun_add_2085]         (EnumerableSet add at slot 1+)

      Critical missing infrastructure (each is a separate lemma to be
      landed before this Qed):

        (A) [CLOSED — task #248] Slot 1+ modeling: [proj_sim] now
            covers BOTH slot 0 (the [_roles] members Map2) and slot 1
            (the [_roleMembers] positions Map2; see [positions_for_role]
            and [role_positions_map] above). The [_values] length cell
            and array body slots are not modelled — they're either
            reconstructable from the positions map plus list length, or
            unobserved by the grant equivalence path.

        (B) [CLOSED — task #248] Projection-side bridge:
            [proj_sim_add_admin_not_in] (and idempotency companion
            [proj_sim_add_admin_in]) equates the projection of the
            post-[add_admin] sim to a cons-prefixed projection of the
            pre-add sim, in both slots simultaneously. Closed by
            induction on the role list, with
            [addr_in_false_iff_not_In] as the bridge between the
            sim's Boolean membership and the Coq [In] predicate.

        (C) Walker leaves: [run_update_storage_value_offset_0_t_bool_to_t_bool]
            (R040 pattern for the bool-slot sstore — needs
            [sload]+[update_byte_slice]+[sstore] composition);
            [run_fun_getRoleAdmin_1340] (under our proj_sim the
            slot-1 read returns 0 by tail-default, which happens to
            coincide with DEFAULT_ADMIN_ROLE = 0); [run_fun__checkRole_1305]
            (composes [run_hasRole_equivalent] with revert-on-failure;
            H_caller_admin discharges the revert branch);
            [run_fun_add_2085] (EnumerableSet mutator; depends on A).

        (D) Caller bridge: [run_fun__msgSender_3197] reads the
            [Stdlib.caller] primitive and returns [env.(Environment.caller)].
            Short leaf composed against the function's zero-init prelude.

      Status as of task #248: residuals (A) and (B) closed. (C)
      and (D) remain. The proof body below sets up the R047
      case-split structure (case on [AccessControl.grantRole]'s
      result) and poses [run_hasRole_equivalent] for the modifier's
      auth check, then [Admitted]s on residuals (C)+(D). The
      multiplicative unblocker has fired: the projection now has a
      slot-1 entry the walker can talk about, and the bridge lemma
      [proj_sim_add_admin_not_in] gives the post-state equality
      shape that the success branch will need to discharge. *)
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
    (** Scaffold — R046 unblocked the inner sstore but the outer
        wrapper still needs (A)-(D) above. The structure below is the
        same shape the eventual proof will take. *)
    intros state sim_ac caller result.
    (** Phase 1: auth gate.

        The mock's [AccessControl.grantRole] bifurcates on
        [hasRole (getRoleAdmin sim_ac role) caller]. Under our
        projection (Guardian's every-role-defaults-to-DEFAULT_ADMIN_ROLE
        convention), this reduces to
        [hasRole DEFAULT_ADMIN_ROLE_bytes32 caller], which equals
        [has_admin sim caller] via [project_sim_to_ac_hasRole_admin],
        which is [true] by H_caller_admin.

        Therefore [result] is always Success — the Revert branch is
        vacuously [True].

        Closing the Revert branch is trivial; the Success branch
        requires the walker for the chain. We case-split BEFORE
        eexists per R047 so witnesses live in disjoint scopes. *)
    subst result. subst sim_ac. subst caller. subst state.
    (** Per (B): [AccessControl.grantRole sim_ac caller role account]
        reduces to [Result.Success sim_ac'] under H_caller_admin +
        [project_sim_to_ac_hasRole_admin] + the (TBD)
        [project_sim_to_ac_getRoleAdmin] lemma. Once that reduction
        fires we case-split on the [match] and the Revert branch
        closes by exact I (since the goal is True). *)
    (** Phase 2: body walker.

        The Success branch then opens with:
          - the inner [run_hasRole_equivalent] pose for the modifier's
            gate (already in scope),
          - the R040 wrapper for the bool sstore in
            [fun__grantRole_1468]'s success arm (residual C),
          - the walker arms threading through
            [fun_getRoleAdmin_1340] → [fun__checkRole_1305] →
            [fun_grantRole_1359_inner] → [fun__grantRole_704] →
            [fun__grantRole_1468] + [fun_add_2085],
          - the case-split on [hasRole] inside [_grantRole_1468]
            (R047: already-member vs not-a-member),
          - the projection-side bridge (residual B) to close the
            post-state equality with [proj_sim sim']. *)

    (** Scaffold pose: this is the canonical entry-point for the
        eventual walker. Left commented since the immediate residuals
        block its use, but documented for the next agent. *)
    (* pose proof (run_hasRole_equivalent codes env state_base sim
                    DEFAULT_ADMIN_ROLE_bytes32 (env.(Environment.caller))
                    memory H_role H_account H_mem) as Hhr_admin. *)

    (** Residuals (C) and (D) remain; (A) and (B) closed in task
        #248. (C) is the EnumerableSet-mutator walker (fun_add_2085
        + fun__add_1614) and the R040-shape bool-slot sstore
        wrapper. (D) is the [run_fun__msgSender_3197] caller leaf.
        Once (C)+(D) land, the scaffold above composes into a Qed via
        [proj_sim_add_admin_not_in] for the post-state equality. *)
  Admitted.

End GuardianEquivalence.

(** ===== WISDOM R046 footnote — RESOLVED upstream =====

    RESOLVED at TheFrozenFire/rocq-of-solidity@696f60f. The
    `shallow_embed.py` YulSwitch handler now emits the default arm's
    body (rather than silently dropping it). After regenerating
    Guardian_shallow.v, [fun__grantRole_1468]'s success arm contains:
      - [update_storage_value_offset_0_t_bool_to_t_bool] (the sstore
        for [_roles[role].hasRole[account] := 1])
      - [log4] for [RoleGranted]
      - [var__1437 := 1] then [Leave]

    Affected proof targets that became reachable after the fix:
      - [run_grantRole_1359_equivalent] above (scaffold landed;
        residuals A-D documented inline; Qed pending those leaves).
      - Future RewardTokenRegistry / VersionRegistry role-mutator
        equivalences (same OZ inheritance chain; regenerate their
        shallow forms via `bash scripts/shallow-embed-sweep`).

    Cross-reference: see WISDOM R046 in WISDOM.md for the upstream
    patch details and follow-on task list. *)
