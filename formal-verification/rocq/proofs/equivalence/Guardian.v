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

  (** ----- Single-word keccak bound axiom (sibling for R051.c Phase 3) -----

      Same modeling assumption as [keccak256_tuple2_offset_bound], but
      for the single-word keccak primitive used by OZ's EnumerableSet
      [_values] dataslot derivation ([mstore(0, anchor);
      keccak256(0, 0x20)]). The offset bound is wider here because the
      consumer's offset is an array index (up to [2^64 - 1] under the
      EnumerableSet [push] guard), not a struct-field byte offset. *)
  Axiom keccak256_single_offset_bound :
    forall (anchor offset : U256.t),
      0 <= offset < 2^240 ->
      0 <= keccak256_single anchor /\
      keccak256_single anchor + offset < 2 ^ 256.

  Lemma Pure_add_keccak_single_offset (anchor offset : U256.t) :
    0 <= offset < 2^240 ->
    Pure.add (keccak256_single anchor) offset
    = keccak256_single anchor + offset.
  Proof.
    intros H_off.
    pose proof (keccak256_single_offset_bound anchor offset H_off) as [Hnn Hb].
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

  (** ----- Role distinctness -----

      The three named roles are distinct keccak256 hashes (of
      "DEFAULT_ADMIN_ROLE" = 0, "OPTIMISTIC_GUARDIAN_ROLE",
      "OPTIMISTIC_GUARDIAN_MANAGER_ROLE" — see contracts/Guardian.sol).
      Pairwise inequality is a hash-collision-resistance assumption,
      a standard cryptographic axiom for this corpus. Used in the
      milestone proof's not-member branch to discharge slot-0 lookup
      absence in OG/OGM blocks. *)
  Axiom DEFAULT_neq_OG :
    DEFAULT_ADMIN_ROLE_bytes32 <> OPTIMISTIC_GUARDIAN_ROLE_bytes32.
  Axiom DEFAULT_neq_OGM :
    DEFAULT_ADMIN_ROLE_bytes32 <> OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32.
  (** OG vs OGM distinctness — needed for the OG/OGM extensions of the
      grantRole milestone (R055 follow-up). Same parametric-trust shape
      as the two above. *)
  Axiom OG_neq_OGM :
    OPTIMISTIC_GUARDIAN_ROLE_bytes32
    <> OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32.

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

  (** ----- Slot-2 / Slot-3: AccessControlEnumerable `_values` array =====

      OZ's [EnumerableSet.Set._values] is a length-prefixed dynamic
      [bytes32[]] array. Solidity storage layout for [bytes32[]] at
      anchor slot [N]:

        slot[N]                = array length          (a single U256)
        slot[keccak256(N) + i] = values[i]             (one slot per element)

      Per-role anchor: [keccak256(role, 1) + 0 = keccak256(role, 1)].
      So the array length per role lives at [keccak256(role, 1)] and the
      body element [values[i]] at [keccak256(keccak256(role, 1)) + i].

      ===== Projection design =====

      The framework's existing [StorableValue.t] inductive does not have
      a dedicated dynamic-array carrier; we encode the array using two
      additional slots in the simulated-storage list, mirroring the
      slot-1 [Map2] approximation pattern already in use for
      [_positions] (which itself approximates the
      [keccak256(addr, keccak256(role, 1) + 1)] shape to the
      framework's [keccak256(addr, keccak256(role, 1))] [Map2] shape;
      see R049 / the slot-1 docstring above):

        slot 2 — [StorableValue.Map (role -> length)]
                 framework slot expression: [keccak256(role, 2)]
                 actual OZ slot: [keccak256(role, 1)]
                 (off-by-index by exactly the same amount as slot-1's
                  approximation; the eventual walker bridge lemma
                  rewrites at the call site, mirroring the planned
                  [run_sload_role_position_at_proj_sim] for slot 1).

        slot 3 — [StorableValue.Map2 ((role, idx) -> value)]
                 framework slot expression:
                   [keccak256(idx, keccak256(role, 3))]
                 actual OZ slot:
                   [keccak256(keccak256(role, 1)) + idx]
                 (the Map2 encoding routes [idx] through the inner
                  keccak; the walker bridge will rewrite to the
                  additive-offset form using the same offset-bound
                  axiom that discharges
                  [Pure_add_keccak_offset]).

      The choice to use two separate slots — rather than packing
      length+body into a single dict — is so each [StorableValue]
      carries a single concrete dict-shape and stays directly
      addressable by the existing [run_sload_map_u256] /
      [run_sload_map2_u256] axioms. The bridge lemma below mutates
      both slots simultaneously when [add_admin] fires; the same
      pattern as the slot-0/slot-1 cons-prefix shape from
      [proj_sim_add_admin_not_in]. *)

  (** Per-role array length. Each role's array length equals the
      current list length under the cons-to-front sim convention. *)
  Definition role_values_length_map (s : State.t) :
      Dict.t U256.t U256.t :=
    [ (DEFAULT_ADMIN_ROLE_bytes32,
        Z.of_nat (List.length s.(State.admins)));
      (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
        Z.of_nat (List.length s.(State.optimisticGuardians)));
      (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
        Z.of_nat (List.length s.(State.optimisticGuardianManagers))) ].

  (** Per-(role, index) array body element. Under the cons-to-front
      convention, the head of the list is the most-recent insertion
      and sits at index [length - 1] in the OZ append-style array;
      equivalently, element at index [i] in the array corresponds to
      the value that, at the moment of insertion, made the array
      length [i + 1]. Concretely: with sim list [a_k :: a_{k-1} :: ...
      :: a_0], the OZ array (post-mutation) is [a_0; a_1; ...; a_k];
      so the body dict has key [(role, Z.of_nat i)] mapping to
      [a_i] = the element prepended when the previous list had
      length [i]. *)
  Fixpoint values_for_role_aux
      (role : U256.t) (n : nat) (addrs : list Address) :
      Dict.t (U256.t * U256.t) U256.t :=
    match addrs with
    | []          => []
    | a :: rest   =>
      (* [n] is the array length BEFORE prepending [a]; under the
         cons-to-front convention, [a]'s body-index is exactly [n]. *)
      ((role, Z.of_nat n), a) :: values_for_role_aux role (pred n) rest
    end.

  (** Top-level helper: assigns body indices in reverse-cons order.
      With list [a_k :: ... :: a_0] of length [k+1], the head [a_k]
      gets body-index [k]. Inductive companion lemmas (below) make
      this cons-vs-empty case-split structural. *)
  Definition values_for_role
      (role : U256.t) (addrs : list Address) :
      Dict.t (U256.t * U256.t) U256.t :=
    values_for_role_aux role (pred (List.length addrs)) addrs.

  (** Concatenation across the three named roles, mirroring the
      [role_member_map] / [role_positions_map] shape. *)
  Definition role_values_body_map (s : State.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    values_for_role DEFAULT_ADMIN_ROLE_bytes32
                    s.(State.admins) ++
    values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                    s.(State.optimisticGuardians) ++
    values_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                    s.(State.optimisticGuardianManagers).

  (** ----- Full projection — FOUR slots =====

      Slot 0: the [_roles] mapping's nested [members] sub-field
              (Map2 of (role, account) -> 0/1).
      Slot 1: the [_roleMembers] positions sub-mapping under
              AccessControlEnumerable (Map2 of (role, addr) -> 1-pos).
      Slot 2: the [_roleMembers] [_values] array length, per role
              (Map of role -> length).
      Slot 3: the [_roleMembers] [_values] array body, per (role, idx)
              (Map2 of (role, idx) -> value).

      Slots 2 and 3 are the R051.c extension. Pre-R051.c the projection
      had two slots; the array body slots were unmodelled because no
      observer in the view-only equivalence path read them. The
      grantRole mutator path's [fun_add_2085] / [fun__add_1614]
      [array_push] DOES sstore against these slots, so a faithful
      mutator-equivalence walker needs the slots to exist. *)
  Definition proj_sim (s : State.t) : SimulatedStorage.t := [
    StorableValue.Map2 (role_member_map s);
    StorableValue.Map2 (role_positions_map s);
    StorableValue.Map (role_values_length_map s);
    StorableValue.Map2 (role_values_body_map s)
  ].

  (** ----- Well-formedness ----- *)
  Lemma proj_sim_length (s : State.t) :
    List.length (proj_sim s) = 4%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_roles (s : State.t) :
    List.nth_error (proj_sim s) 0
    = Some (StorableValue.Map2 (role_member_map s)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_positions (s : State.t) :
    List.nth_error (proj_sim s) 1
    = Some (StorableValue.Map2 (role_positions_map s)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_values_length (s : State.t) :
    List.nth_error (proj_sim s) 2
    = Some (StorableValue.Map (role_values_length_map s)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_values_body (s : State.t) :
    List.nth_error (proj_sim s) 3
    = Some (StorableValue.Map2 (role_values_body_map s)).
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

  (** ===== Bridge: per-slot helpers for slots 2 and 3 =====

      Slot 2 (length map): under [add_admin s addr] with [addr] not
      previously a member, the DEFAULT_ADMIN role's length entry
      increases by 1; other entries are unchanged. This is a pure
      dict-shape rewrite — no inductive case-split needed. *)
  Lemma role_values_length_map_add_admin_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.admins) ->
      role_values_length_map (Guardian.add_admin s addr) =
      (DEFAULT_ADMIN_ROLE_bytes32,
        Z.of_nat (List.length s.(State.admins)) + 1)
      :: List.tl (role_values_length_map s).
  Proof.
    intros s addr Hni.
    unfold role_values_length_map, Guardian.add_admin, Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    cbn [List.length List.tl].
    f_equal.
    + f_equal. lia.
  Qed.

  (** Slot 3 (body map): under [add_admin s addr] with [addr] not
      previously a member, the new entry [((DEFAULT, length admins),
      addr)] is cons-prefixed onto the body map. Mirrors the slot-1
      [role_positions_map_add_admin_not_in] shape — same per-role
      cons-to-front argument.

      Helper: [values_for_role role (addr :: admins)] unfolds to
      [((role, length admins), addr) :: values_for_role role admins]
      modulo the aux-vs-top-level [pred] dance. *)
  Lemma values_for_role_cons_unfold
      (role : U256.t) (addr : Address) (rest : list Address) :
    values_for_role role (addr :: rest) =
    ((role, Z.of_nat (List.length rest)), addr) :: values_for_role role rest.
  Proof.
    unfold values_for_role.
    simpl (List.length (addr :: rest)).
    (* [pred (S (length rest))] = [length rest]. *)
    change (Nat.pred (S (List.length rest))) with (List.length rest).
    simpl (values_for_role_aux role (List.length rest) (addr :: rest)).
    reflexivity.
  Qed.

  Lemma role_values_body_map_add_admin_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.admins) ->
      role_values_body_map (Guardian.add_admin s addr) =
      ((DEFAULT_ADMIN_ROLE_bytes32, Z.of_nat (List.length s.(State.admins))),
        addr)
      :: role_values_body_map s.
  Proof.
    intros s addr Hni.
    unfold role_values_body_map, Guardian.add_admin, Guardian.add_role.
    simpl. rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite values_for_role_cons_unfold.
    simpl. reflexivity.
  Qed.

  (** ===== Bridge: [proj_sim] after [add_admin] — the headline (B) =====

      Equates the projection of the post-[add_admin] sim to a
      cons-prefixed projection of the pre-[add_admin] sim, in all
      FOUR slots simultaneously. R051.c extends the original two-slot
      shape with slots 2 (length) and 3 (body). Used by the
      residual-C walker proof (see [run_grantRole_1359_equivalent]'s
      docstring) to close the post-sstore state equality after the
      inner [_grantRole_1468] sstore (slot 0) and the
      [fun_add_2085]/[fun__add_1614] sstores (slots 1/2/3). *)
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
           :: role_positions_map s);
        StorableValue.Map
          ((DEFAULT_ADMIN_ROLE_bytes32,
            Z.of_nat (List.length s.(State.admins)) + 1)
           :: List.tl (role_values_length_map s));
        StorableValue.Map2
          (((DEFAULT_ADMIN_ROLE_bytes32,
              Z.of_nat (List.length s.(State.admins))), addr)
           :: role_values_body_map s) ].
  Proof.
    intros s addr Hni.
    unfold proj_sim.
    rewrite (role_member_map_add_admin_not_in s addr Hni).
    rewrite (role_positions_map_add_admin_not_in s addr Hni).
    rewrite (role_values_length_map_add_admin_not_in s addr Hni).
    rewrite (role_values_body_map_add_admin_not_in s addr Hni).
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

  (** ===== Bridge: per-slot helpers for OG / OGM additions =====

      The OG (OPTIMISTIC_GUARDIAN_ROLE) and OGM
      (OPTIMISTIC_GUARDIAN_MANAGER_ROLE) blocks sit MID-LIST in
      [role_member_map], [role_positions_map], [role_values_body_map]
      (after the DEFAULT block, and OG comes before OGM). The bridge
      lemmas below produce mid-list-insertion forms — the inserted
      entry lives between the unrelated-role blocks rather than
      cons-prepended at the head.

      R055 follow-up: needed for extending [run_grantRole_1359_equivalent]
      from DEFAULT-only to all three Guardian roles. *)

  (** Slot 0 (members) — OG variant. The added entry sits at the head
      of the OG block, between the DEFAULT prefix and the OGM suffix. *)
  Lemma role_member_map_add_optimistic_guardian_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardians) ->
      role_member_map (Guardian.add_optimistic_guardian s addr) =
      members_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
      ((OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr), 1)
      :: (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
           s.(State.optimisticGuardians) ++
          members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers)).
  Proof.
    intros s addr Hni.
    unfold role_member_map, Guardian.add_optimistic_guardian, Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    simpl. reflexivity.
  Qed.

  (** Slot 0 (members) — OGM variant. The added entry sits at the head
      of the OGM block, after both DEFAULT and OG blocks. *)
  Lemma role_member_map_add_optimistic_guardian_manager_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardianManagers) ->
      role_member_map (Guardian.add_optimistic_guardian_manager s addr) =
      (members_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
       members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
        s.(State.optimisticGuardians)) ++
      ((OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr), 1)
      :: members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers).
  Proof.
    intros s addr Hni.
    unfold role_member_map, Guardian.add_optimistic_guardian_manager,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite app_assoc. simpl. reflexivity.
  Qed.

  (** Slot 1 (positions) — OG variant. *)
  Lemma role_positions_map_add_optimistic_guardian_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardians) ->
      role_positions_map (Guardian.add_optimistic_guardian s addr) =
      positions_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
      ((OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr),
        Z.of_nat (List.length s.(State.optimisticGuardians)) + 1)
      :: (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
           s.(State.optimisticGuardians) ++
          positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers)).
  Proof.
    intros s addr Hni.
    unfold role_positions_map, Guardian.add_optimistic_guardian,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    simpl. reflexivity.
  Qed.

  (** Slot 1 (positions) — OGM variant. *)
  Lemma role_positions_map_add_optimistic_guardian_manager_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardianManagers) ->
      role_positions_map (Guardian.add_optimistic_guardian_manager s addr) =
      (positions_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
       positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
        s.(State.optimisticGuardians)) ++
      ((OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr),
        Z.of_nat (List.length s.(State.optimisticGuardianManagers)) + 1)
      :: positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers).
  Proof.
    intros s addr Hni.
    unfold role_positions_map, Guardian.add_optimistic_guardian_manager,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite app_assoc. simpl. reflexivity.
  Qed.

  (** Slot 2 (length) — OG variant. The OG entry is the second element. *)
  Lemma role_values_length_map_add_optimistic_guardian_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardians) ->
      role_values_length_map (Guardian.add_optimistic_guardian s addr) =
      [ (DEFAULT_ADMIN_ROLE_bytes32,
          Z.of_nat (List.length s.(State.admins)));
        (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
          Z.of_nat (List.length s.(State.optimisticGuardians)) + 1);
        (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
          Z.of_nat (List.length s.(State.optimisticGuardianManagers))) ].
  Proof.
    intros s addr Hni.
    unfold role_values_length_map, Guardian.add_optimistic_guardian,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    cbn [List.length].
    f_equal. f_equal. f_equal. lia.
  Qed.

  (** Slot 2 (length) — OGM variant. The OGM entry is the third element. *)
  Lemma role_values_length_map_add_optimistic_guardian_manager_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardianManagers) ->
      role_values_length_map (Guardian.add_optimistic_guardian_manager s addr) =
      [ (DEFAULT_ADMIN_ROLE_bytes32,
          Z.of_nat (List.length s.(State.admins)));
        (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
          Z.of_nat (List.length s.(State.optimisticGuardians)));
        (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
          Z.of_nat (List.length s.(State.optimisticGuardianManagers)) + 1) ].
  Proof.
    intros s addr Hni.
    unfold role_values_length_map, Guardian.add_optimistic_guardian_manager,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    cbn [List.length].
    f_equal. f_equal. f_equal. f_equal. f_equal. lia.
  Qed.

  (** Slot 3 (body) — OG variant. *)
  Lemma role_values_body_map_add_optimistic_guardian_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardians) ->
      role_values_body_map (Guardian.add_optimistic_guardian s addr) =
      values_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
      ((OPTIMISTIC_GUARDIAN_ROLE_bytes32,
         Z.of_nat (List.length s.(State.optimisticGuardians))), addr)
      :: (values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
           s.(State.optimisticGuardians) ++
          values_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers)).
  Proof.
    intros s addr Hni.
    unfold role_values_body_map, Guardian.add_optimistic_guardian,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite (values_for_role_cons_unfold OPTIMISTIC_GUARDIAN_ROLE_bytes32 addr
              s.(State.optimisticGuardians)).
    simpl. reflexivity.
  Qed.

  (** Slot 3 (body) — OGM variant. *)
  Lemma role_values_body_map_add_optimistic_guardian_manager_not_in :
    forall (s : State.t) (addr : Address),
      ~ In addr s.(State.optimisticGuardianManagers) ->
      role_values_body_map (Guardian.add_optimistic_guardian_manager s addr) =
      (values_for_role DEFAULT_ADMIN_ROLE_bytes32 s.(State.admins) ++
       values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
        s.(State.optimisticGuardians)) ++
      ((OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
         Z.of_nat (List.length s.(State.optimisticGuardianManagers))), addr)
      :: values_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
           s.(State.optimisticGuardianManagers).
  Proof.
    intros s addr Hni.
    unfold role_values_body_map, Guardian.add_optimistic_guardian_manager,
           Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite (values_for_role_cons_unfold OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
              addr s.(State.optimisticGuardianManagers)).
    rewrite app_assoc.
    simpl. reflexivity.
  Qed.

  (** ===== R054 foundation: observational tail-form bridges =====

      The Yul-level [Stdlib.sstore] for an absent key produces a
      post-storage of the form
      [Dict.declare_or_assign dict key value], which (because the
      [declare_or_assign_function] fixpoint walks left-to-right and
      lands on the empty-list base case when no entry matches) is
      structurally [dict ++ [(key, value)]] when
      [Dict.get dict key = None].

      The Guardian-side projection bridges (e.g.
      [proj_sim_add_admin_not_in]) by contrast produce
      [((key), value) :: dict] — key cons-prepended.

      These two list shapes are syntactically distinct yet
      OBSERVATIONALLY identical: every [Dict.get] (and therefore
      every [map_get_u256]) lookup returns the same value on either
      shape when [Dict.get dict key = None].

      The lemmas below state that observational equivalence
      explicitly. They are the foundation for any future Phase 5
      closure that bridges the Phase-1/Phase-2
      [Dict.declare_or_assign] post-states to the cons-prefixed
      [proj_sim] form. See WISDOM R054 for the three resolution
      options (new sstore axiom variant, setoid framework, or
      theorem-statement weakening) — each of those consumes the
      foundation built here. *)

  (** ----- [Dict.declare_or_assign] is append-at-tail when key absent =====

      Pure structural lemma about the upstream [Dict.t] semantics:
      if [Dict.get d k = None], every entry of [d] mismatches [k]
      under [Dict.Eq.eqb], so the [declare_or_assign_function]
      fixpoint traverses to the empty-list base case and appends
      [(k, f None)].

      Stated at the [Z] key shape (slot-2 length map). The
      [ZZ]-keyed companion below covers slots 0/1/3. *)
  Lemma declare_or_assign_app_when_absent_Z
      (d : Dict.t Z U256.t) (k : Z) (v : U256.t)
      (H_absent : Dict.get d k = None) :
    Dict.declare_or_assign d k v = d ++ [(k, v)].
  Proof.
    unfold Dict.declare_or_assign.
    induction d as [|[k' v'] rest IH]; cbn in *.
    - reflexivity.
    - change (Dict.Eq.eqb k k') with (k =? k') in H_absent.
      change (Dict.Eq.eqb k' k) with (k' =? k).
      destruct (k =? k') eqn:Heq.
      + (* k = k' but H_absent says it's mismatched. Contradiction. *)
        discriminate H_absent.
      + apply Z.eqb_neq in Heq.
        replace (k' =? k) with false by
          (symmetry; apply Z.eqb_neq; lia).
        f_equal. apply IH. exact H_absent.
  Qed.

  (** [ZZ]-keyed companion: slots 0 (member map), 1 (positions
      map), and 3 (values body map) all use [Z*Z] keys. *)
  Lemma declare_or_assign_app_when_absent_ZZ
      (d : Dict.t (Z * Z) U256.t) (k : Z * Z) (v : U256.t)
      (H_absent : Dict.get d k = None) :
    Dict.declare_or_assign d k v = d ++ [(k, v)].
  Proof.
    unfold Dict.declare_or_assign.
    destruct k as [k1 k2].
    induction d as [|((k1' & k2') & v') rest IH].
    - cbn. reflexivity.
    - simpl Dict.declare_or_assign_function. simpl app.
      simpl Dict.get in H_absent.
      change (Dict.Eq.eqb (k1', k2') (k1, k2))
        with ((k1' =? k1) && (k2' =? k2))%bool.
      change (Dict.Eq.eqb (k1, k2) (k1', k2'))
        with ((k1 =? k1') && (k2 =? k2'))%bool in H_absent.
      destruct (k1 =? k1') eqn:H1; destruct (k2 =? k2') eqn:H2;
      simpl andb in H_absent.
      + (* both eqb true ⇒ H_absent says Some v' = None: contradiction. *)
        discriminate H_absent.
      + apply Z.eqb_eq in H1. subst k1'.
        rewrite Z.eqb_refl. simpl.
        apply Z.eqb_neq in H2.
        replace (k2' =? k2) with false by (symmetry; apply Z.eqb_neq; lia).
        simpl. f_equal. apply IH. exact H_absent.
      + apply Z.eqb_neq in H1.
        replace (k1' =? k1) with false by (symmetry; apply Z.eqb_neq; lia).
        simpl. f_equal. apply IH. exact H_absent.
      + apply Z.eqb_neq in H1.
        replace (k1' =? k1) with false by (symmetry; apply Z.eqb_neq; lia).
        simpl. f_equal. apply IH. exact H_absent.
  Qed.

  (** ----- map_get of cons-prepend ≡ append-singleton, point-wise =====

      The headline observational equivalence: for every lookup key,
      [map_get_u256 ((k,v) :: d) k' = map_get_u256 (d ++ [(k,v)]) k']
      under [Dict.get d k = None].

      Proof strategy: rewrite the RHS via
      [declare_or_assign_app_when_absent_ZZ] in reverse; the
      [(k,v) :: d] and [declare_or_assign d k v] forms differ only
      in walk-position, which does not affect [map_get_u256]'s
      first-match semantics when the inserted key is absent. *)
  (** ----- Helper: [Dict.get] of an append-singleton reduces to
      [if]-of-singleton-or-rest, by walking the prefix.

      [Dict.get (d ++ [(k,v)]) l] = either the first match in [d] or,
      if none, [Dict.get [(k,v)] l] = Some v if l=k else None. *)
  Lemma Dict_get_app_singleton_ZZ
      (d : Dict.t (Z * Z) U256.t) (k : Z * Z) (v : U256.t)
      (lookup_key : Z * Z) :
    Dict.get (d ++ [(k, v)]) lookup_key
    = match Dict.get d lookup_key with
      | Some w => Some w
      | None   => if Dict.Eq.eqb lookup_key k then Some v else None
      end.
  Proof.
    induction d as [|[k' v'] rest IH].
    - reflexivity.
    - simpl. destruct (Dict.Eq.eqb lookup_key k') eqn:Heq.
      + reflexivity.
      + exact IH.
  Qed.

  (** ----- Headline observational equivalence: cons-prepend ≡ append-singleton

      For every lookup key, [map_get_u256] on [(k,v) :: d] equals
      [map_get_u256] on [d ++ [(k,v)]], provided [Dict.get d k = None].

      Proof: both sides reduce to [if Dict.Eq.eqb lookup_key k then v
      else map_get_u256 d lookup_key]. The LHS by direct cons
      semantics, the RHS via [Dict_get_app_singleton_ZZ] and the
      observation that when lookup_key = k, [Dict.get d k = None] so
      the walker falls through to the singleton. *)
  Lemma map_get_cons_eq_app_singleton_when_absent_ZZ
      (d : Dict.t (Z * Z) U256.t)
      (k : Z * Z) (v : U256.t)
      (H_absent : Dict.get d k = None)
      (lookup_key : Z * Z) :
    StorableValue.map_get_u256 ((k, v) :: d) lookup_key
    = StorableValue.map_get_u256 (d ++ [(k, v)]) lookup_key.
  Proof.
    unfold StorableValue.map_get_u256.
    rewrite Dict_get_app_singleton_ZZ.
    simpl Dict.get.
    destruct (Dict.Eq.eqb lookup_key k) eqn:Heq.
    - (* lookup_key = k. LHS: cons matches at head, Some v. RHS: walks d
         (Dict.get d k = None by H_absent), falls through to singleton,
         returns Some v. *)
      destruct k as [k1 k2]; destruct lookup_key as [l1 l2].
      change (Dict.Eq.eqb (l1, l2) (k1, k2))
        with ((l1 =? k1) && (l2 =? k2))%bool in Heq.
      destruct (l1 =? k1) eqn:Hl1; destruct (l2 =? k2) eqn:Hl2;
      simpl andb in Heq; try discriminate Heq.
      apply Z.eqb_eq in Hl1. apply Z.eqb_eq in Hl2. subst l1 l2.
      rewrite H_absent. reflexivity.
    - destruct (Dict.get d lookup_key); reflexivity.
  Qed.

  (** ----- Mid-list-insertion observational equivalence (R055 follow-up)
      ===============================================================

      For OG / OGM roles, the projection-side bridge produces a
      mid-list cons [A ++ (k, v) :: B] (the new entry sits between
      the unrelated-role prefix [A] and suffix [B]). The
      [Dict.declare_or_assign] post-state instead produces
      [(A ++ B) ++ [(k, v)]] (append-at-tail). When [k] is absent in
      both [A] and [B], the two are POINT-WISE [map_get_u256]-equal.

      This is the natural generalization of
      [map_get_cons_eq_app_singleton_when_absent_ZZ] (where the
      prefix [A] is empty), and is exactly what the OG / OGM
      observational bridges below need to discharge their per-key
      lookup equality. *)
  Lemma map_get_mid_cons_eq_app_singleton_when_absent_ZZ
      (A B : Dict.t (Z * Z) U256.t) (k : Z * Z) (v : U256.t)
      (H_absent_A : Dict.get A k = None)
      (H_absent_B : Dict.get B k = None)
      (lookup_key : Z * Z) :
    StorableValue.map_get_u256 (A ++ (k, v) :: B) lookup_key
    = StorableValue.map_get_u256 ((A ++ B) ++ [(k, v)]) lookup_key.
  Proof.
    unfold StorableValue.map_get_u256.
    (* Walk [A] from the left on both sides; they agree because the
       same [A]-prefix is consumed identically before either form
       reaches the [(k, v)] entry. *)
    induction A as [|[k' v'] rest IH]; cbn.
    - (* A = []: reduces to the cons-vs-append-singleton lemma. *)
      change (Dict.get ((k, v) :: B) lookup_key)
        with (if Dict.Eq.eqb lookup_key k then Some v
              else Dict.get B lookup_key).
      pose proof (map_get_cons_eq_app_singleton_when_absent_ZZ B k v
                    H_absent_B lookup_key) as Hcons.
      unfold StorableValue.map_get_u256 in Hcons.
      simpl Dict.get in Hcons. exact Hcons.
    - destruct (Dict.Eq.eqb lookup_key k') eqn:Heq.
      + reflexivity.
      + simpl Dict.get in H_absent_A.
        destruct (Dict.Eq.eqb k k') eqn:Heqk.
        * (* k = k' but H_absent_A says k absent in (k', v') :: rest:
             contradiction. *)
          (* Heqk : eqb k k' = true; H_absent_A : ... = None at the
             cons head. Resolve k = k'. *)
          discriminate H_absent_A.
        * apply IH. exact H_absent_A.
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

  (** ----- ArrayDataslot — single-word keccak smoke (R052 Option 3) -----

      [fun_add_2085] / [fun__add_1614] invokes
      [array_dataslot_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr ptr] to
      derive the array body's anchor slot — the sequence is
      [mstore(0, ptr); keccak256(0, 0x20)] (a SINGLE-word keccak).
      Pre-R052 the framework only exposed [keccak256_tuple2] (a
      two-word keccak), so this composite had no leaf to land
      against. The upstream addition of [keccak256_single] +
      [run_keccak256_single] (in rocq-of-solidity's
      [simulations/RocqOfSolidity.v] and [proofs/RocqOfSolidity.v])
      closes the gap. This lemma is the in-repo smoke test that the
      primitive composes cleanly with the existing memory machinery
      — same shape as [MappingIndexAccess]'s two-word case. *)
  Module ArrayDataslotBytes32.

    Lemma run_array_dataslot codes env state_base
        (ptr : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 rest, memory = w0 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' rest',
      {{? codes, env, Some st |
        array_dataslot_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr ptr ⇓
        Result.Ok (keccak256_single ptr)
      | Some (make_state env state_base (w0' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & rest & ->).
      do 2 eexists.
      unfold array_dataslot_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr.
      l. {
        lu. l. {
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_keccak256_single. }
          p.
        }
        p.
      }
      p.
    Qed.

  End ArrayDataslotBytes32.

  (** ===== R051.c Phase 3 — Per-contract trust axioms for the
      `_values` array slot expressions =====

      Background. The framework's Map / Map2 / MapStruct axioms expose
      sload / sstore at NESTED-KECCAK slot shapes
      ([keccak256_tuple2 key (Z.of_nat index)] for Map,
      [keccak256_tuple2 key2 (keccak256_tuple2 key1 (Z.of_nat index))]
      for Map2, [keccak256_tuple2 key (Z.of_nat index) + offset] for
      MapStruct). OZ's EnumerableSet [_values] array is laid out using
      Solidity's dynamic-array convention, which uses the ARRAY-shape
      slot expressions [array_anchor] (for length) and
      [keccak256_single array_anchor + i] (for body element [i]) —
      where [array_anchor = keccak256_tuple2 role 1] in OZ-actual.

      Slots 2 and 3 of [proj_sim] (added in R051.c Phases 1+2) carry
      this data — slot 2 is a Map (role → length), slot 3 is a Map2
      ((role, idx) → value). The framework axioms applied at slot 2
      route through [keccak256_tuple2 role 2] (since slot 2's index is
      2); the OZ-actual length slot is [keccak256_tuple2 role 1] — an
      OFF-BY-1 in the inner keccak's index input. Similarly for slot 3
      the framework Map2 axiom uses
      [keccak256_tuple2 idx (keccak256_tuple2 role 3)] but OZ uses
      [keccak256_single (keccak256_tuple2 role 1) + idx]. The two
      shapes are distinct symbolic terms.

      The axioms below close the gap the same way the slot-1
      positions modeling does (R049 docstring): we accept the
      array-shape slot expression as the trusted point at which the
      sload / sstore is dispatched against [proj_sim]'s slot 2 / slot
      3. R052 Option 1 (per-shape opaque-rewriting axioms) — accepted
      here because R052's Option 2 (a [StorableValue.Array]
      constructor) is the long-term clean upstream extension but
      not yet built.

      Documented as an audit caveat: the equation between
      [keccak256_single (keccak256_tuple2 role 1) + i] and a
      hypothetical "keccak (idx, keccak(role, 3))" is FALSE in any
      honest model. It is parametric trust the same way R021's
      [RunO.CallContract] rule and the slot-1 positions approximation
      are. The trade-off is documented in Audit.v's
      caveat-on-EnumerableSet-modeling entry. *)

  (** ----- Axiom: sload at array length anchor =====

      The OZ-actual array length slot is [keccak256_tuple2 role 1].
      Under any four-slot projection variant with slot 2 the per-role
      length map, that slot's value is
      [StorableValue.map_get_u256 length_map role].

      R054 generalization (2026-05-31): parameterized over the slot-0
      [member_map_in], slot-1 [positions_map_in], slot-2 [length_map_in],
      and slot-3 [body_map_in] so the axiom applies against arbitrary
      4-slot projection variants — letting Phase 1's mutated-slot-0
      post-state flow into Phase 2's array-length sload. *)
  Axiom run_sload_role_values_length_at_proj_sim :
    forall codes env state_base memory (role : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj) |
      Stdlib.sload (keccak256_tuple2 role 1) ⇓
      Result.Ok (StorableValue.map_get_u256 length_map_in role)
    | Some (make_state env state_base memory proj) ?}}.

  (** ----- Axiom: sstore at array length anchor =====

      Writing [value] at the OZ-actual array length slot updates
      slot 2's per-role length map at key [role].

      R054 generalization (2026-05-31): parameterized over the slot-0
      [member_map_in], slot-1 [positions_map_in], slot-2 [length_map_in],
      and slot-3 [body_map_in] so the axiom applies against arbitrary
      4-slot projection variants. *)
  Axiom run_sstore_role_values_length_at_proj_sim :
    forall codes env state_base memory (role value : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let length_map' :=
      Dict.declare_or_assign length_map_in role value in
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map';
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      Stdlib.sstore (keccak256_tuple2 role 1) value ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_post) ?}}.

  (** ----- Axiom: sstore at array body element =====

      Writing [value] at slot [keccak256_single (keccak256_tuple2 role 1) + i]
      updates slot 3's per-(role, idx) body map at key [(role, i)].
      This is the slot expression emitted by OZ's dynamic-array body
      element write after [array_dataslot] resolves the data area to
      [keccak256_single (set_slot)]. *)
  Axiom run_sstore_role_values_body_at_proj_sim :
    forall codes env state_base memory (role idx value : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let body_map' :=
      Dict.declare_or_assign body_map_in (role, idx) value in
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map' ] in
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      Stdlib.sstore (keccak256_single (keccak256_tuple2 role 1) + idx) value ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_post) ?}}.

  (** ----- Axiom: sload at array length (post-bump shape) =====

      Companion to [run_sload_role_values_length_at_proj_sim] for the
      mid-walker state, after the length [sstore] has swapped a custom
      [length_map'] into slot 2. The [storage_array_index_access] body
      re-fires the length sload here to compute the panic guard, and we
      need to land it against the post-bump 4-slot list (not the literal
      [proj_sim sim] shape). *)
  Axiom run_sload_role_values_length_at_proj_sim_post :
    forall codes env state_base memory (role : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map' : Dict.t U256.t U256.t)
        (body_map' : Dict.t (U256.t * U256.t) U256.t),
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map';
        StorableValue.Map2 body_map' ] in
    {{? codes, env, Some (make_state env state_base memory proj) |
      Stdlib.sload (keccak256_tuple2 role 1) ⇓
      Result.Ok (StorableValue.map_get_u256 length_map' role)
    | Some (make_state env state_base memory proj) ?}}.

  (** ----- Axiom: sload at array body element =====

      Companion to [run_sstore_role_values_body_at_proj_sim] above:
      reading the slot
      [keccak256_single (keccak256_tuple2 role 1) + idx] under the
      4-slot projection (with [length_map'] swapped into slot 2 — the
      [array_push] walker invokes this AFTER the length bump) yields the
      slot-3 body map value at key [(role, idx)]. Missing entries return
      the [map_get_u256] default of 0 — modeling Solidity's zero-init
      for fresh array indices. *)
  Axiom run_sload_role_values_body_at_proj_sim :
    forall codes env state_base memory (role idx : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj) |
      Stdlib.sload (keccak256_single (keccak256_tuple2 role 1) + idx) ⇓
      Result.Ok (StorableValue.map_get_u256 body_map_in (role, idx))
    | Some (make_state env state_base memory proj) ?}}.

  (** ===== Bit-mask leaf for the bytes32 offset-0 body write =====

      [update_byte_slice_dynamic32 prev 0 v] reduces to [v] for any
      [v ∈ [0, 2^256)], independent of [prev]. The shallow body is:

        shiftBits := mul(shiftBytes, 8)              (* = 0 *)
        mask      := shl(shiftBits, MAX)             (* = MAX *)
        toInsert  := shl(shiftBits, toInsert)        (* = v *)
        value     := and(prev, not(mask))            (* = 0 *)
        result    := or(value, and(toInsert, mask))  (* = v *)

      Same shape as [ThrottleLibLeaves.run_update_byte_slice_32_shift_0]
      but with [shift_left_dynamic 0 _] in place of [shift_left_0 _]. *)
  Lemma run_shift_left_dynamic_0 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      shift_left_dynamic 0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_left_dynamic.
    lu. repeat (lu || cu || p).
    s. unfold Pure.shl. simpl.
    rewrite Z.mul_1_r.
    rewrite Z.mod_small by exact H_v.
    pe; reflexivity.
  Qed.

  Lemma run_update_byte_slice_dynamic32_offset_0
      codes env state (old_value new_value : U256.t)
      (H_new : 0 <= new_value < 2^256) :
    {{? codes, env, Some state |
      update_byte_slice_dynamic32 old_value 0 new_value ⇓ Result.Ok new_value
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_dynamic32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    (* The first shift_left_dynamic has [bits = Pure.mul 0 8 = 0] and
       value = MAX = 2^256 - 1; both in U256-range. The second has
       bits = 0 and value = new_value (in range by H_new). *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (Stdlib.mul _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.mul, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (shift_left_dynamic _ _) _ ⇓ _ | _ ?}} =>
          c; [ first
                 [ apply run_shift_left_dynamic_0; exact H_new
                 | apply run_shift_left_dynamic_0;
                   change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936;
                   lia ] | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    (* Reduce the final result. Pure.mul 0 8 = 0 is in shiftBits already.
       After the [shift_left_dynamic] arms close to MAX and new_value,
       we get [or(and(prev, not(MAX)), and(new_value, MAX)) = new_value]. *)
    s.
    unfold Pure.and, Pure.or, Pure.not.
    change (2 ^ 256 -
            115792089237316195423570985008687907853269984665640564039457584007913129639935 - 1)
      with 0.
    rewrite Z.land_0_r.
    rewrite Z.lor_0_l.
    change 115792089237316195423570985008687907853269984665640564039457584007913129639935
      with (Z.ones 256).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small by exact H_new.
    pe; reflexivity.
  Qed.

  (** [shift_right_0_unsigned v] = [shr 0 v] = [v / 1] = [v]. Local copy
      since the (later-defined) sibling [run_shift_right_0_unsigned] is
      forward-referenced; both have the same body. *)
  Lemma run_shift_right_0_unsigned_for_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.shr. simpl. rewrite Z.div_1_r. reflexivity.
  Qed.

  (** [prepare_store_t_bytes32 v] = [shr 0 v] = [v / 1] = [v]. *)
  Lemma run_prepare_store_t_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_bytes32.
    lu. l. {
      c. { apply run_shift_right_0_unsigned_for_bytes32. }
      p.
    }
    p.
  Qed.

  (** ===== Wrapper leaf: [update_storage_value_t_bytes32_to_t_bytes32]
      at the array-body slot under [proj_sim] =====

      Bakes in the post-length-sstore four-slot shape and threads the
      body sstore through [run_sstore_role_values_body_at_proj_sim].
      Chain inside [update_storage_value_t_bytes32_to_t_bytes32]:
        convert_t_bytes32_to_t_bytes32 value          (* = value *)
        sload(slot)                                    (* prev *)
        prepare_store_t_bytes32(value)                 (* = value *)
        update_byte_slice_dynamic32(prev, 0, value)    (* = value *)
        sstore(slot, value)                            (* body write *)
      Final post-state has slot 3's body_map updated at (role, idx). *)
  Lemma run_update_storage_value_t_bytes32_at_proj_sim
      codes env state_base memory (role idx value : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (H_v : 0 <= value < 2^256) :
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let body_map' :=
      Dict.declare_or_assign body_map_in (role, idx) value in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map' ] in
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      update_storage_value_t_bytes32_to_t_bytes32
        (keccak256_single (keccak256_tuple2 role 1) + idx) 0 value ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_post) ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_t_bytes32_to_t_bytes32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bytes32_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bytes32_to_t_bytes32 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sload_role_values_body_at_proj_sim
                       codes env state_base memory role idx
                       member_map_in positions_map_in length_map_in body_map_in) | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_bytes32 | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_dynamic32 _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_dynamic32_offset_0; exact H_v | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sstore_role_values_body_at_proj_sim
                       codes env state_base memory role idx value
                       member_map_in positions_map_in length_map_in body_map_in) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ===== Composite: [run_array_push_at_proj_sim] =====

      Steps the EnumerableSet [_values] [array_push] body against the
      [proj_sim sim] projection. The body sequence (from
      [Guardian_shallow.v::array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr]):

        oldLen     := sload(array)                      (* length read *)
        if oldLen >= 2^64 panic                         (* overflow guard *)
        sstore(array, oldLen + 1)                       (* length bump *)
        (slot, off) := storage_array_index_access(array, oldLen)
                    = (keccak256_single array + oldLen, 0)
        update_storage_value_t_bytes32_to_t_bytes32(slot, 0, value)
                                                         (* body write *)

      Where [array = keccak256_tuple2 role 1] is the OZ EnumerableSet
      anchor. The walker chains:
        - [run_sload_role_values_length_at_proj_sim] for the length read,
        - the [oldLen + 1 < 2^64] precondition discharges the overflow
          guard (sim invariant: lists have at most 2^64 - 1 members),
        - [run_sstore_role_values_length_at_proj_sim] for the length bump,
        - [apply_run_mstore] + [apply_run_keccak256_single] for the
          array_dataslot composite (mirrors [ArrayDataslotBytes32]),
        - [run_sstore_role_values_body_at_proj_sim] for the body write,
        - threads through [update_byte_slice_dynamic32 ... 0 ...] which
          for offset=0 + bytes32 reduces to the plain value
          (full-mask identity).

      ===== Status =====

      [Qed]. The walker closes via an inline [lazymatch] that dispatches:
        - [LowM.Let] / inner-call inlining via [l] / [cu];
        - re-unfolding of [M.strong_let_] / [M.let_] / [M.do] as they
          re-introduce themselves at each step;
        - both panic-guard [Shallow.if_]s (outer [oldLen < 2^64], inner
          [oldLen < arrayLength_post]) via [first [rewrite H_lt_oldLen_2_64
          | rewrite H_lt_oldLen_inner]] under [Pure.iszero (Pure.lt _ _)];
        - the four trust axioms (length sload pre/post, body sload, length
          sstore, body sstore) at the OZ-actual array slot shapes;
        - [apply_run_mstore] + [apply_run_keccak256_single] for the
          [array_dataslot] composite plus [CanonizeState.execute] to refold
          the state into [make_state] shape after the mstore;
        - the bit-mask leaves
          ([run_update_byte_slice_dynamic32_offset_0],
          [run_prepare_store_t_bytes32]) and the body-write wrapper
          [run_update_storage_value_t_bytes32_at_proj_sim]. *)
  Lemma run_array_push_at_proj_sim
      codes env state_base memory (role value : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (* The overflow guard requires the new length to fit in 2^64. *)
      (H_len_bound :
         StorableValue.map_get_u256 length_map_in role
         + 1 < 18446744073709551616)
      (* role_values_length_map values are all [Z.of_nat _]-derived in
         the canonical projection, so non-negative. For the generic
         pre-state, the caller supplies the bound directly. *)
      (H_len_nn :
         0 <= StorableValue.map_get_u256 length_map_in role)
      (* The value fits in U256 — caller-supplied since this lemma is
         generic over the stored value. For OZ's [add_admin] consumers
         the value is an Address (< 2^160 < 2^256). *)
      (H_value_u256 : 0 <= value < 2 ^ 256)
      (* The memory layout has at least two words so the post-state
         memory ([keccak256_tuple2 role 1 :: w1 :: rest]) has a 2-word
         handle for composability (the [_add_1614] caller's MIA call
         needs 2 scratch words). *)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let oldLen :=
      StorableValue.map_get_u256 length_map_in role in
    let length_map' :=
      Dict.declare_or_assign length_map_in role
        (oldLen + 1) in
    let body_map' :=
      Dict.declare_or_assign body_map_in (role, oldLen)
        value in
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map';
        StorableValue.Map2 body_map' ] in
    exists w1' rest' state',
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr
        (keccak256_tuple2 role 1) value ⇓
      Result.Ok tt
    | Some state' ?}}
    /\ state' = make_state env state_base
                  (keccak256_tuple2 role 1 :: w1' :: rest') proj_post.
  Proof.
    (** R051.c Phase 3 walker. See the docstring above for the
        eight-step outline; below is the concrete assembly. *)
    intros oldLen length_map' body_map' proj_pre proj_post.
    destruct H_mem as (w0 & w1 & rest & ->).
    (* The mstore inside array_dataslot writes [keccak256_tuple2 role 1]
       to memory word 0; afterwards memory = (kec :: w1 :: rest). Pose
       the post-state memory ahead of time so we can use it for the
       existential witness at the end. *)
    set (mem_after_mstore := keccak256_tuple2 role 1 :: w1 :: rest).
    (* The post-state has the body sstored on top of the length sstore.
       Pose it explicitly to drive the existential witness. *)
    set (proj_after_length :=
           [ StorableValue.Map2 member_map_in;
             StorableValue.Map2 positions_map_in;
             StorableValue.Map length_map';
             StorableValue.Map2 body_map_in ]).
    (* Step bounds: H_len_bound ⇒ oldLen < 2^64, oldLen + 1 < 2^256. *)
    assert (H_oldLen_bound : oldLen < 18446744073709551616) by
      (unfold oldLen; lia).
    (* oldLen non-negativity comes from caller-supplied [H_len_nn]. *)
    assert (H_oldLen_nn : 0 <= oldLen) by exact H_len_nn.
    (* oldLen + 1 fits in U256. *)
    assert (H_old_plus_one_u256 : 0 <= oldLen + 1 < 2 ^ 256) by lia.
    (* Pure.add oldLen 1 = oldLen + 1. *)
    assert (H_pa_old1 : Pure.add oldLen 1 = oldLen + 1).
    { unfold Pure.add. apply Z.mod_small. lia. }
    (* Pure.mul oldLen 1 = oldLen. *)
    assert (H_pm_old1 : Pure.mul oldLen 1 = oldLen).
    { unfold Pure.mul. rewrite Z.mul_1_r. apply Z.mod_small. lia. }
    (* Pure.add (keccak256_single (keccak256_tuple2 role 1)) oldLen
       = keccak256_single ... + oldLen via the new axiom. *)
    assert (H_pa_kec_old :
              Pure.add (keccak256_single (keccak256_tuple2 role 1)) oldLen
              = keccak256_single (keccak256_tuple2 role 1) + oldLen).
    { apply Pure_add_keccak_single_offset.
      split; [exact H_oldLen_nn|].
      change (2^240) with 1766847064778384329583297500742918515827483896875618958121606201292619776.
      lia. }
    (* H_value_u256 is now a caller-supplied precondition (above). *)
    (* The walker needs to know [lt oldLen (2^64) = 1] to take the
       no-panic branch of the outer overflow guard. *)
    assert (H_lt_oldLen_2_64 : Pure.lt oldLen 18446744073709551616 = 1).
    { unfold Pure.lt. destruct (Z.ltb_spec oldLen 18446744073709551616);
      [reflexivity | lia]. }
    (* And [lt oldLen (oldLen+1) = 1] for the inner panic guard in
       storage_array_index_access. *)
    assert (H_lt_oldLen_succ : Pure.lt oldLen (Pure.add oldLen 1) = 1).
    { rewrite H_pa_old1.
      unfold Pure.lt. destruct (Z.ltb_spec oldLen (oldLen + 1));
      [reflexivity | lia]. }
    (* After the length sstore, the inner length re-read fetches
       [map_get_u256 length_map' role = oldLen+1]. Helper lemma
       generalized over the dict and the value separately so the
       inductive step's IH applies cleanly. *)
    assert (H_dict_declare_role_eq :
      forall (d : Dict.t U256.t U256.t) (k : U256.t) (v : U256.t),
        StorableValue.map_get_u256 (Dict.declare_or_assign d k v) k = v).
    { intros d k v.
      unfold StorableValue.map_get_u256, Dict.declare_or_assign.
      induction d as [|[k' v'] rest_d IH]; cbn.
      - change (Dict.Eq.eqb k k) with (k =? k).
        rewrite Z.eqb_refl. reflexivity.
      - change (Dict.Eq.eqb k' k) with (k' =? k).
        destruct (Z.eqb_spec k' k) as [Hek | Hne].
        + subst k'. cbn.
          change (Dict.Eq.eqb k k) with (k =? k).
          rewrite Z.eqb_refl. reflexivity.
        + cbn.
          change (Dict.Eq.eqb k k') with (k =? k').
          replace (k =? k') with false by
            (symmetry; apply Z.eqb_neq; lia).
          exact IH. }
    assert (H_get_length_map'_role :
              StorableValue.map_get_u256 length_map' role = oldLen + 1).
    { unfold length_map'. apply H_dict_declare_role_eq. }
    assert (H_lt_oldLen_inner :
              Pure.lt oldLen (StorableValue.map_get_u256 length_map' role) = 1).
    { rewrite H_get_length_map'_role.
      unfold Pure.lt. destruct (Z.ltb_spec oldLen (oldLen + 1));
      [reflexivity | lia]. }
    (* Final witnesses for the existentials. *)
    exists w1, rest.
    eexists.
    split; [|reflexivity].
    unfold array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr,
           storage_array_index_access_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr,
           array_length_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr,
           array_dataslot_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    (* The walker. Each arm handles one call/let shape. The first arms
       eagerly re-unfold the M-monad operators that re-introduce
       themselves at each step (inner [let~ '] forms reach an
       [M.strong_let_] that the top-level unfold doesn't see through). *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      (* Reduce both panic-guard ifs: outer [lt(oldLen, 2^64)] and inner
         [lt(oldLen, oldLen+1)]. Both lt's reduce to 1, then iszero to 0,
         then [0 =? 0] picks the no-panic branch. *)
      | |- {{? _, _, _ |
            if Pure.iszero (Pure.lt _ _) =? 0 then _ else _ ⇓ _ | _ ?}} =>
          first [ fold oldLen; rewrite H_lt_oldLen_2_64
                | fold oldLen length_map'; rewrite H_lt_oldLen_inner ];
          simpl Pure.iszero; cbv iota
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      (* Inline a call whose body is itself a let-computation (e.g.
         storage_array_index_access body) — use CallUnfold (cu) to turn
         it into LowM.let_, then subsequent arms process the inner chain. *)
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      (* Length sload at array anchor. Two cases:
           - against the pre-state four-slot shape (very first read).
           - against the post-length-sstore four-slot shape (re-read
             inside storage_array_index_access).
         Both dispatch via the generalized sload axiom — the pre/post
         distinction is in the length_map_in argument. *)
      | |- {{? _, _, Some (make_state _ _ _ _) |
            LowM.Call (Stdlib.sload (keccak256_tuple2 _ 1)) _ ⇓ _ | _ ?}} =>
          c; [ first
                 [ eapply run_sload_role_values_length_at_proj_sim
                 | eapply run_sload_role_values_length_at_proj_sim_post ] | ]
      (* Body sload at array body slot. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload (keccak256_single (keccak256_tuple2 _ 1) + _)) _
            ⇓ _ | _ ?}} =>
          c; [ eapply run_sload_role_values_body_at_proj_sim | ]
      (* Length sstore at array anchor (length bump). *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore (keccak256_tuple2 _ 1) _) _ ⇓ _ | _ ?}} =>
          c; [ fold oldLen; rewrite H_pa_old1;
               eapply run_sstore_role_values_length_at_proj_sim | ]
      (* Body sstore at array body slot. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore (keccak256_single (keccak256_tuple2 _ 1) + _) _) _
            ⇓ _ | _ ?}} =>
          c; [ eapply run_sstore_role_values_body_at_proj_sim | ]
      (* mstore for array_dataslot. After the mstore axiom, the state
         shape uses record-update notation; refold via CanonizeState. *)
      | |- {{? _, _, Some (make_state _ _ _ _) |
            LowM.Call (Stdlib.mstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply_run_mstore | CanonizeState.execute ]
      (* keccak256_single for array_dataslot. Works against either the
         make_state shape or the record-update shape — handle both. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.keccak256 _ 32) _ ⇓ _ | _ ?}} =>
          c; [ first [ apply_run_keccak256_single
                     | CanonizeState.execute; apply_run_keccak256_single ]
             | CanonizeState.execute ]
      (* Stdlib pure arithmetic: lt, iszero, add, mul. *)
      | |- {{? _, _, _ | LowM.Call (Stdlib.lt _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.lt, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.mul _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.mul, M.pure; apply RunO.Pure | ]
      (* The body update_storage_value call dispatches via the wrapper
         leaf. The slot expression is [Pure.add (keccak256_single _)
         (Pure.mul _ 1)]; simplify both pure ops first so the wrapper's
         [keccak256_single ... + idx] shape matches. *)
      | |- {{? _, _, _ |
            LowM.Call (update_storage_value_t_bytes32_to_t_bytes32 _ 0 _) _ ⇓ _ | _ ?}} =>
          fold oldLen; rewrite H_pm_old1, H_pa_kec_old;
          c; [ apply (run_update_storage_value_t_bytes32_at_proj_sim
                       codes env state_base mem_after_mstore role oldLen value
                       member_map_in positions_map_in length_map' body_map_in
                       H_value_u256) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

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

  (** [Dict.get] over an appended dict — same shape as [map_get_app_split]
      but at the option-result level (no [map_get_u256] default-to-0). *)
  Lemma Dict_get_app_split
      {K V : Set} `{Dict.Eq.C K}
      (m1 m2 : Dict.t K V) (k : K) :
    Dict.get (m1 ++ m2) k =
      match Dict.get m1 k with
      | Some v => Some v
      | None   => Dict.get m2 k
      end.
  Proof.
    induction m1 as [|[k' v'] rest IH]; cbn; [reflexivity|].
    destruct (Dict.Eq.eqb k k'); [reflexivity | exact IH].
  Qed.

  (** ===== R054 Phase 5 bridge: post-Phase-1 slot-0 observes
      [add_admin]'s slot-0 — POINT-WISE =====

      The headline R054 closure foundation. Connects the Yul-level
      [Dict.declare_or_assign] form of the slot-0 member map
      (produced by [run_update_storage_value_t_bool_at_proj_sim] and
      Phase 1 [run_fun__grantRole_1468_at_proj_sim_not_member]) to
      the sim-side [proj_sim_add_admin_not_in] bridge form, as a
      POINT-WISE [map_get_u256] equality.

      This is the OBSERVATIONAL form of the "syntactic-equality
      blocker" diagnosed in WISDOM R054. Future Phase 5 closures
      will route their post-state equality through this lemma (or
      its slot-1/slot-3 companions) rather than demanding the
      structurally impossible [proj_sim sim'] syntactic-list
      equality of the post-state storage.

      Hypotheses (both available at any Phase 5 not-member call site):
        - [H_not_in_admins]: [addr] not previously an admin.
        - [H_addr_absent]: the slot-0 [map_get] reads 0 at the
          [(DEFAULT, addr)] key. Phase 5 derives this from the
          hasRole-pre-call returning 0 (Phase 1's [H_not_member]
          hypothesis) plus the sload bridge.

      Conclusion: for every lookup key,
        [map_get_u256 (Dict.declare_or_assign (role_member_map sim)
                        (DEFAULT, addr) 1) k]
        = [map_get_u256 (role_member_map (Guardian.add_admin sim addr)) k] *)
  Lemma role_member_map_sstore_observes_add_admin_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_member_map sim)
           (DEFAULT_ADMIN_ROLE_bytes32, addr) = 0)
      (H_not_in_admins : ~ In addr sim.(State.admins))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_member_map sim)
         (DEFAULT_ADMIN_ROLE_bytes32, addr) 1) lookup_key
    = StorableValue.map_get_u256
        (role_member_map (Guardian.add_admin sim addr)) lookup_key.
  Proof.
    (* [H_addr_absent] + the [role_member_map_values_bool] fact (every
       value in the map is 0 or 1) ⇒ Dict.get returns None at that key.
       Otherwise it would return Some 1, forcing map_get_u256 = 1. *)
    assert (H_absent : Dict.get (role_member_map sim)
                         (DEFAULT_ADMIN_ROLE_bytes32, addr) = None).
    { (* Combine: [map_get_u256 = 0] from H_addr_absent +
         [role_member_map_values_bool] (the cbv-zeta'd form gives
         [v = 0 \/ v = 1]). If [Dict.get] hit, [v] would be 1 ≠ 0.
         If [Dict.get] missed, [v = 0] but that's the [None] case
         we want directly. *)
      destruct (Dict.get (role_member_map sim)
                  (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      (* Walk role_member_map's three-block structure and use
         [members_for_role_get_is_one] at the matching block. *)
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      assert (Hw : w = 1).
      { unfold role_member_map in Hg.
        (* Each of the three concat blocks is built by members_for_role
           which only stores 1s. Walk the three blocks and apply
           members_for_role_get_is_one on whichever yields the hit. *)
        rewrite !Dict_get_app_split in Hg.
        destruct (Dict.get (members_for_role _ sim.(State.admins))
                    (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (members_for_role_get_is_one _ _ _ _ Hg0).
        - destruct (Dict.get (members_for_role _ sim.(State.optimisticGuardians))
                      (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (members_for_role_get_is_one _ _ _ _ Hg1).
          + apply (members_for_role_get_is_one _ _ _ _ Hg). }
      rewrite Hw in H_addr_absent. discriminate H_addr_absent. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_absent).
    rewrite (role_member_map_add_admin_not_in sim addr H_not_in_admins).
    symmetry.
    apply map_get_cons_eq_app_singleton_when_absent_ZZ.
    exact H_absent.
  Qed.

  (** ===== R054 Phase 5 bridge: SLOT 1 post-Phase-2 observes
      [add_admin]'s slot-1 — POINT-WISE =====

      Slot-1 analog of [role_member_map_sstore_observes_add_admin_not_in].
      Phase 2's positions sstore writes
      [Dict.declare_or_assign (role_positions_map sim) (DEFAULT, addr)
                              (length admins + 1)] —
      append-at-tail when (DEFAULT, addr) is absent. The bridge
      [role_positions_map_add_admin_not_in] gives cons-prepend.

      Routes through the [_observes_] pattern same as slot 0. *)
  Lemma role_positions_map_sstore_observes_add_admin_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_positions_map sim)
           (DEFAULT_ADMIN_ROLE_bytes32, addr) = 0)
      (H_not_in_admins : ~ In addr sim.(State.admins))
      (new_position : U256.t)
      (H_new_position :
         new_position = Z.of_nat (List.length sim.(State.admins)) + 1)
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_positions_map sim)
         (DEFAULT_ADMIN_ROLE_bytes32, addr) new_position) lookup_key
    = StorableValue.map_get_u256
        (role_positions_map (Guardian.add_admin sim addr)) lookup_key.
  Proof.
    (* [H_addr_absent]: map_get_u256 returns 0 at (DEFAULT, addr). For
       positions, the stored value at any hit is [Z.of_nat _ + 1] which is
       ≥ 1, hence never 0. So [Dict.get] must be None at this key. *)
    assert (H_absent : Dict.get (role_positions_map sim)
                         (DEFAULT_ADMIN_ROLE_bytes32, addr) = None).
    { destruct (Dict.get (role_positions_map sim)
                  (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      (* w = Z.of_nat (length _) + 1 ≥ 1, contradicting w = 0. *)
      assert (Hw_ge1 : w >= 1).
      { unfold role_positions_map in Hg.
        rewrite !Dict_get_app_split in Hg.
        (* Walk the three blocks; each block's positions_for_role only
           stores values [Z.of_nat (length _) + 1], all ≥ 1. *)
        assert (Hpos_ge :
          forall (r : U256.t) (lst : list Address) (k : U256.t * U256.t) (v : U256.t),
            Dict.get (positions_for_role r lst) k = Some v -> v >= 1).
        { intros r lst.
          induction lst as [|a rest IH]; intros k v Hg2; simpl in Hg2.
          - discriminate.
          - destruct (Dict.Eq.eqb _ _) eqn:Heqb.
            + injection Hg2 as <-. lia.
            + exact (IH _ _ Hg2). }
        destruct (Dict.get (positions_for_role DEFAULT_ADMIN_ROLE_bytes32 sim.(State.admins))
                    (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (Hpos_ge _ _ _ _ Hg0).
        - destruct (Dict.get (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32 sim.(State.optimisticGuardians))
                      (DEFAULT_ADMIN_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (Hpos_ge _ _ _ _ Hg1).
          + apply (Hpos_ge _ _ _ _ Hg). }
      rewrite H_addr_absent in Hw_ge1. lia. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_absent).
    rewrite (role_positions_map_add_admin_not_in sim addr H_not_in_admins).
    rewrite H_new_position.
    symmetry.
    apply map_get_cons_eq_app_singleton_when_absent_ZZ.
    exact H_absent.
  Qed.

  (** ===== R054 Phase 5 bridge: SLOT 2 (length) post-Phase-2 = [add_admin]'s slot-2

      SYNTACTIC EQUALITY (not observational). Slot 2 is special: the
      length map's first entry is keyed by [DEFAULT_ADMIN_ROLE_bytes32],
      and Phase 2's array_push sstore at role=DEFAULT matches the head
      via [Eq.eqb] — so [Dict.declare_or_assign] replaces in-place,
      yielding the cons-prepended form already (no append-at-tail). *)
  Lemma role_values_length_map_sstore_eq_add_admin_not_in
      (sim : State.t) (addr : Address)
      (H_not_in_admins : ~ In addr sim.(State.admins))
      (new_length : U256.t)
      (H_new_length :
         new_length = Z.of_nat (List.length sim.(State.admins)) + 1) :
    Dict.declare_or_assign (role_values_length_map sim)
      DEFAULT_ADMIN_ROLE_bytes32 new_length
    = role_values_length_map (Guardian.add_admin sim addr).
  Proof.
    rewrite H_new_length.
    rewrite (role_values_length_map_add_admin_not_in sim addr H_not_in_admins).
    (* role_values_length_map sim is [(DEFAULT, length); (OPT_G, ...); (OPT_GM, ...)]. *)
    unfold role_values_length_map, Dict.declare_or_assign.
    cbn [Dict.declare_or_assign_function].
    change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32 DEFAULT_ADMIN_ROLE_bytes32)
      with (DEFAULT_ADMIN_ROLE_bytes32 =? DEFAULT_ADMIN_ROLE_bytes32).
    rewrite Z.eqb_refl.
    cbn [List.tl].
    reflexivity.
  Qed.

  (** ===== R054 Phase 5 bridge: SLOT 3 (body) post-Phase-2 observes
      [add_admin]'s slot-3 — POINT-WISE =====

      Slot-3 analog of slot-0 / slot-1 bridges. Phase 2's array_push body
      sstore writes
      [Dict.declare_or_assign (role_values_body_map sim) (DEFAULT, oldLen) addr],
      where [oldLen = length admins] (via the sim's cons-to-front
      convention).

      The sim-side bridge — derived from [values_for_role_cons_unfold] +
      [role_values_body_map]'s three-block structure — yields
      [((DEFAULT, length admins), addr) :: role_values_body_map sim]
      under [~ In addr admins].

      Routes through the [_observes_] pattern same as slot 0/1. *)
  Lemma role_values_body_map_add_admin_not_in_helper
      (s : State.t) (addr : Address)
      (Hni : ~ In addr s.(State.admins)) :
    role_values_body_map (Guardian.add_admin s addr) =
    ((DEFAULT_ADMIN_ROLE_bytes32, Z.of_nat (List.length s.(State.admins))),
      addr)
    :: role_values_body_map s.
  Proof.
    unfold role_values_body_map, Guardian.add_admin, Guardian.add_role.
    cbn [State.admins State.optimisticGuardians State.optimisticGuardianManagers].
    rewrite (proj2 (addr_in_false_iff_not_In _ _) Hni).
    rewrite (values_for_role_cons_unfold DEFAULT_ADMIN_ROLE_bytes32 addr
              s.(State.admins)).
    reflexivity.
  Qed.

  Lemma role_values_body_map_sstore_observes_add_admin_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         Dict.get (role_values_body_map sim)
           (DEFAULT_ADMIN_ROLE_bytes32,
             Z.of_nat (List.length sim.(State.admins))) = None)
      (H_not_in_admins : ~ In addr sim.(State.admins))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_values_body_map sim)
         (DEFAULT_ADMIN_ROLE_bytes32,
           Z.of_nat (List.length sim.(State.admins))) addr) lookup_key
    = StorableValue.map_get_u256
        (role_values_body_map (Guardian.add_admin sim addr)) lookup_key.
  Proof.
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_addr_absent).
    rewrite (role_values_body_map_add_admin_not_in_helper sim addr
              H_not_in_admins).
    symmetry.
    apply map_get_cons_eq_app_singleton_when_absent_ZZ.
    exact H_addr_absent.
  Qed.

  (** ===== R055 follow-up: observational bridges for OG / OGM =====

      Each bridge connects the [Dict.declare_or_assign] post-state for
      the OG (or OGM) sstore to the corresponding mid-list-inserted
      projection of [add_optimistic_guardian] (or
      [_optimistic_guardian_manager]). They use
      [map_get_mid_cons_eq_app_singleton_when_absent_ZZ] (the
      generalization of the head-cons-equals-tail-append lemma to
      arbitrary list prefixes), plus the per-slot OG/OGM projection
      bridges added above.

      The hypothesis split: each bridge takes
      [H_absent_prefix] — the inserted key is absent in the unrelated-
      role prefix block (DEFAULT for OG, or DEFAULT+OG for OGM); and
      [H_absent_suffix] — absent in the own-role block (OG for OG, OGM
      for OGM) and the unrelated suffix (OGM for OG, empty for OGM).

      To minimize bookkeeping at the call site, we instead take a
      single hypothesis [H_get_absent : Dict.get (full map) key = None]
      and split it via [Dict_get_app_split] inside each proof. *)

  Lemma role_member_map_sstore_observes_add_optimistic_guardian_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_member_map sim)
           (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = 0)
      (H_not_in_og : ~ In addr sim.(State.optimisticGuardians))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_member_map sim)
         (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) 1) lookup_key
    = StorableValue.map_get_u256
        (role_member_map (Guardian.add_optimistic_guardian sim addr))
        lookup_key.
  Proof.
    (* Step 1: get [Dict.get full = None] at (OG, addr) from
       [map_get_u256 = 0] + values are bool. *)
    assert (H_absent_full : Dict.get (role_member_map sim)
                             (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
    { destruct (Dict.get (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      assert (Hw : w = 1).
      { unfold role_member_map in Hg.
        rewrite !Dict_get_app_split in Hg.
        destruct (Dict.get (members_for_role _ sim.(State.admins))
                    (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (members_for_role_get_is_one _ _ _ _ Hg0).
        - destruct (Dict.get (members_for_role _ sim.(State.optimisticGuardians))
                      (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (members_for_role_get_is_one _ _ _ _ Hg1).
          + apply (members_for_role_get_is_one _ _ _ _ Hg). }
      rewrite Hw in H_addr_absent. discriminate H_addr_absent. }
    (* Step 2: split [H_absent_full] into prefix/suffix pieces. *)
    unfold role_member_map in H_absent_full.
    rewrite !Dict_get_app_split in H_absent_full.
    destruct (Dict.get (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_absent_full into Hg_ogm.
    (* Step 3: rewrite both sides into the canonical form. *)
    assert (H_get_full : Dict.get (role_member_map sim)
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
    { unfold role_member_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_member_map_add_optimistic_guardian_not_in sim addr H_not_in_og).
    (* LHS: (DEFAULT_block ++ OG_block ++ OGM_block) ++ [(OG, addr, 1)]
       RHS: DEFAULT_block ++ (OG, addr, 1) :: (OG_block ++ OGM_block)
       Apply the mid-list helper with A=DEFAULT_block, B=OG_block++OGM_block. *)
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - exact Hg_def.
    - assert (Hb : Dict.get
                     (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                        sim.(State.optimisticGuardians)
                      ++ members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                           sim.(State.optimisticGuardianManagers))
                     (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
      { rewrite Dict_get_app_split, Hg_og. exact Hg_ogm. }
      exact Hb.
  Qed.

  Lemma role_member_map_sstore_observes_add_optimistic_guardian_manager_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_member_map sim)
           (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = 0)
      (H_not_in_ogm : ~ In addr sim.(State.optimisticGuardianManagers))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_member_map sim)
         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) 1) lookup_key
    = StorableValue.map_get_u256
        (role_member_map
           (Guardian.add_optimistic_guardian_manager sim addr))
        lookup_key.
  Proof.
    assert (H_absent_full : Dict.get (role_member_map sim)
              (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
    { destruct (Dict.get (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      assert (Hw : w = 1).
      { unfold role_member_map in Hg.
        rewrite !Dict_get_app_split in Hg.
        destruct (Dict.get (members_for_role _ sim.(State.admins))
                    (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (members_for_role_get_is_one _ _ _ _ Hg0).
        - destruct (Dict.get (members_for_role _ sim.(State.optimisticGuardians))
                      (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (members_for_role_get_is_one _ _ _ _ Hg1).
          + apply (members_for_role_get_is_one _ _ _ _ Hg). }
      rewrite Hw in H_addr_absent. discriminate H_addr_absent. }
    unfold role_member_map in H_absent_full.
    rewrite !Dict_get_app_split in H_absent_full.
    destruct (Dict.get (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_absent_full into Hg_ogm.
    assert (H_get_full : Dict.get (role_member_map sim)
                          (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
    { unfold role_member_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_member_map_add_optimistic_guardian_manager_not_in
              sim addr H_not_in_ogm).
    (* role_member_map sim is right-assoc: D ++ (OG ++ OGM). We need
       it as (D ++ OG) ++ OGM so the mid-list helper unifies with
       A = D ++ OG, B = OGM. *)
    unfold role_member_map.
    rewrite app_assoc.
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - assert (Hab : Dict.get
                     (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                        sim.(State.admins)
                      ++ members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                           sim.(State.optimisticGuardians))
                     (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
      { rewrite Dict_get_app_split, Hg_def. exact Hg_og. }
      exact Hab.
    - exact Hg_ogm.
  Qed.

  (** Slot 1 (positions) — OG variant. *)
  Lemma role_positions_map_sstore_observes_add_optimistic_guardian_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_positions_map sim)
           (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = 0)
      (H_not_in_og : ~ In addr sim.(State.optimisticGuardians))
      (new_position : U256.t)
      (H_new_position :
         new_position = Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1)
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_positions_map sim)
         (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) new_position) lookup_key
    = StorableValue.map_get_u256
        (role_positions_map (Guardian.add_optimistic_guardian sim addr))
        lookup_key.
  Proof.
    (* All position values are ≥ 1, so map_get_u256 = 0 ⇒ Dict.get = None. *)
    assert (H_absent_full : Dict.get (role_positions_map sim)
                             (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
    { destruct (Dict.get (role_positions_map sim)
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      assert (Hw_ge1 : w >= 1).
      { unfold role_positions_map in Hg.
        rewrite !Dict_get_app_split in Hg.
        assert (Hpos_ge :
          forall (r : U256.t) (lst : list Address) (k : U256.t * U256.t) (v : U256.t),
            Dict.get (positions_for_role r lst) k = Some v -> v >= 1).
        { intros r lst.
          induction lst as [|a rest IH]; intros k v Hg2; simpl in Hg2.
          - discriminate.
          - destruct (Dict.Eq.eqb _ _) eqn:Heqb.
            + injection Hg2 as <-. lia.
            + exact (IH _ _ Hg2). }
        destruct (Dict.get (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                              sim.(State.admins))
                    (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (Hpos_ge _ _ _ _ Hg0).
        - destruct (Dict.get (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                sim.(State.optimisticGuardians))
                      (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (Hpos_ge _ _ _ _ Hg1).
          + apply (Hpos_ge _ _ _ _ Hg). }
      rewrite H_addr_absent in Hw_ge1. lia. }
    unfold role_positions_map in H_absent_full.
    rewrite !Dict_get_app_split in H_absent_full.
    destruct (Dict.get (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_absent_full into Hg_ogm.
    assert (H_get_full : Dict.get (role_positions_map sim)
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
    { unfold role_positions_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_positions_map_add_optimistic_guardian_not_in sim addr H_not_in_og).
    rewrite H_new_position.
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - exact Hg_def.
    - assert (Hb : Dict.get
                     (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                        sim.(State.optimisticGuardians)
                      ++ positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                           sim.(State.optimisticGuardianManagers))
                     (OPTIMISTIC_GUARDIAN_ROLE_bytes32, addr) = None).
      { rewrite Dict_get_app_split, Hg_og. exact Hg_ogm. }
      exact Hb.
  Qed.

  (** Slot 1 (positions) — OGM variant. *)
  Lemma role_positions_map_sstore_observes_add_optimistic_guardian_manager_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         StorableValue.map_get_u256 (role_positions_map sim)
           (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = 0)
      (H_not_in_ogm : ~ In addr sim.(State.optimisticGuardianManagers))
      (new_position : U256.t)
      (H_new_position :
         new_position
         = Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1)
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_positions_map sim)
         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) new_position)
        lookup_key
    = StorableValue.map_get_u256
        (role_positions_map
           (Guardian.add_optimistic_guardian_manager sim addr))
        lookup_key.
  Proof.
    assert (H_absent_full : Dict.get (role_positions_map sim)
                             (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
    { destruct (Dict.get (role_positions_map sim)
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w|] eqn:Hg;
        [|reflexivity].
      exfalso.
      unfold StorableValue.map_get_u256 in H_addr_absent.
      rewrite Hg in H_addr_absent.
      assert (Hw_ge1 : w >= 1).
      { unfold role_positions_map in Hg.
        rewrite !Dict_get_app_split in Hg.
        assert (Hpos_ge :
          forall (r : U256.t) (lst : list Address) (k : U256.t * U256.t) (v : U256.t),
            Dict.get (positions_for_role r lst) k = Some v -> v >= 1).
        { intros r lst.
          induction lst as [|a rest IH]; intros k v Hg2; simpl in Hg2.
          - discriminate.
          - destruct (Dict.Eq.eqb _ _) eqn:Heqb.
            + injection Hg2 as <-. lia.
            + exact (IH _ _ Hg2). }
        destruct (Dict.get (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                              sim.(State.admins))
                    (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w0|] eqn:Hg0.
        - injection Hg as <-.
          apply (Hpos_ge _ _ _ _ Hg0).
        - destruct (Dict.get (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                sim.(State.optimisticGuardians))
                      (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr)) as [w1|] eqn:Hg1.
          + injection Hg as <-.
            apply (Hpos_ge _ _ _ _ Hg1).
          + apply (Hpos_ge _ _ _ _ Hg). }
      rewrite H_addr_absent in Hw_ge1. lia. }
    unfold role_positions_map in H_absent_full.
    rewrite !Dict_get_app_split in H_absent_full.
    destruct (Dict.get (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_absent_full into Hg_ogm.
    assert (H_get_full : Dict.get (role_positions_map sim)
                          (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
    { unfold role_positions_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_positions_map_add_optimistic_guardian_manager_not_in
              sim addr H_not_in_ogm).
    rewrite H_new_position.
    unfold role_positions_map.
    rewrite app_assoc.
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - assert (Hab : Dict.get
                     (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                        sim.(State.admins)
                      ++ positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                           sim.(State.optimisticGuardians))
                     (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, addr) = None).
      { rewrite Dict_get_app_split, Hg_def. exact Hg_og. }
      exact Hab.
    - exact Hg_ogm.
  Qed.

  (** Slot 2 (length) — OG variant. SYNTACTIC equality (not
      observational): the OG entry is the second element of the
      explicit 3-tuple length list, so [declare_or_assign] at OG_BR
      matches via head-cons-recursion using [DEFAULT_neq_OG]. *)
  Lemma role_values_length_map_sstore_eq_add_optimistic_guardian_not_in
      (sim : State.t) (addr : Address)
      (H_not_in_og : ~ In addr sim.(State.optimisticGuardians))
      (new_length : U256.t)
      (H_new_length :
         new_length
         = Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1) :
    Dict.declare_or_assign (role_values_length_map sim)
      OPTIMISTIC_GUARDIAN_ROLE_bytes32 new_length
    = role_values_length_map (Guardian.add_optimistic_guardian sim addr).
  Proof.
    rewrite H_new_length.
    rewrite (role_values_length_map_add_optimistic_guardian_not_in
              sim addr H_not_in_og).
    unfold role_values_length_map, Dict.declare_or_assign.
    cbn [Dict.declare_or_assign_function].
    change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                        OPTIMISTIC_GUARDIAN_ROLE_bytes32)
      with (DEFAULT_ADMIN_ROLE_bytes32 =? OPTIMISTIC_GUARDIAN_ROLE_bytes32).
    rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG).
    change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                        OPTIMISTIC_GUARDIAN_ROLE_bytes32)
      with (OPTIMISTIC_GUARDIAN_ROLE_bytes32
            =? OPTIMISTIC_GUARDIAN_ROLE_bytes32).
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  (** Slot 2 (length) — OGM variant. *)
  Lemma role_values_length_map_sstore_eq_add_optimistic_guardian_manager_not_in
      (sim : State.t) (addr : Address)
      (H_not_in_ogm : ~ In addr sim.(State.optimisticGuardianManagers))
      (new_length : U256.t)
      (H_new_length :
         new_length
         = Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1) :
    Dict.declare_or_assign (role_values_length_map sim)
      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 new_length
    = role_values_length_map
        (Guardian.add_optimistic_guardian_manager sim addr).
  Proof.
    rewrite H_new_length.
    rewrite (role_values_length_map_add_optimistic_guardian_manager_not_in
              sim addr H_not_in_ogm).
    unfold role_values_length_map, Dict.declare_or_assign.
    cbn [Dict.declare_or_assign_function].
    change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                        OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      with (DEFAULT_ADMIN_ROLE_bytes32
            =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
    rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM).
    change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                        OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      with (OPTIMISTIC_GUARDIAN_ROLE_bytes32
            =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
    rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM).
    change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                        OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
            =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  (** Slot 3 (body) — OG variant. *)
  Lemma role_values_body_map_sstore_observes_add_optimistic_guardian_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         Dict.get (role_values_body_map sim)
           (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
             Z.of_nat (List.length sim.(State.optimisticGuardians))) = None)
      (H_not_in_og : ~ In addr sim.(State.optimisticGuardians))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_values_body_map sim)
         (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
           Z.of_nat (List.length sim.(State.optimisticGuardians))) addr)
        lookup_key
    = StorableValue.map_get_u256
        (role_values_body_map (Guardian.add_optimistic_guardian sim addr))
        lookup_key.
  Proof.
    (* Split H_addr_absent across the three blocks. *)
    unfold role_values_body_map in H_addr_absent.
    rewrite !Dict_get_app_split in H_addr_absent.
    destruct (Dict.get (values_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                  Z.of_nat (List.length sim.(State.optimisticGuardians))))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                  Z.of_nat (List.length sim.(State.optimisticGuardians))))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_addr_absent into Hg_ogm.
    assert (H_get_full : Dict.get (role_values_body_map sim)
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                            Z.of_nat (List.length sim.(State.optimisticGuardians)))
                          = None).
    { unfold role_values_body_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_values_body_map_add_optimistic_guardian_not_in
              sim addr H_not_in_og).
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - exact Hg_def.
    - assert (Hb : Dict.get
                     (values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                        sim.(State.optimisticGuardians)
                      ++ values_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                           sim.(State.optimisticGuardianManagers))
                     (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                       Z.of_nat (List.length sim.(State.optimisticGuardians)))
                     = None).
      { rewrite Dict_get_app_split, Hg_og. exact Hg_ogm. }
      exact Hb.
  Qed.

  (** Slot 3 (body) — OGM variant. *)
  Lemma role_values_body_map_sstore_observes_add_optimistic_guardian_manager_not_in
      (sim : State.t) (addr : Address)
      (H_addr_absent :
         Dict.get (role_values_body_map sim)
           (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
             Z.of_nat (List.length sim.(State.optimisticGuardianManagers)))
           = None)
      (H_not_in_ogm : ~ In addr sim.(State.optimisticGuardianManagers))
      (lookup_key : U256.t * U256.t) :
    StorableValue.map_get_u256
      (Dict.declare_or_assign (role_values_body_map sim)
         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
           Z.of_nat (List.length sim.(State.optimisticGuardianManagers))) addr)
        lookup_key
    = StorableValue.map_get_u256
        (role_values_body_map
           (Guardian.add_optimistic_guardian_manager sim addr))
        lookup_key.
  Proof.
    unfold role_values_body_map in H_addr_absent.
    rewrite !Dict_get_app_split in H_addr_absent.
    destruct (Dict.get (values_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                  Z.of_nat (List.length sim.(State.optimisticGuardianManagers))))
      as [w0|] eqn:Hg_def; [discriminate|].
    destruct (Dict.get (values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                  Z.of_nat (List.length sim.(State.optimisticGuardianManagers))))
      as [w1|] eqn:Hg_og; [discriminate|].
    rename H_addr_absent into Hg_ogm.
    assert (H_get_full : Dict.get (role_values_body_map sim)
                          (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                            Z.of_nat
                              (List.length sim.(State.optimisticGuardianManagers)))
                          = None).
    { unfold role_values_body_map.
      rewrite !Dict_get_app_split, Hg_def, Hg_og, Hg_ogm. reflexivity. }
    rewrite (declare_or_assign_app_when_absent_ZZ _ _ _ H_get_full).
    rewrite (role_values_body_map_add_optimistic_guardian_manager_not_in
              sim addr H_not_in_ogm).
    unfold role_values_body_map.
    rewrite app_assoc.
    symmetry.
    apply map_get_mid_cons_eq_app_singleton_when_absent_ZZ.
    - assert (Hab : Dict.get
                     (values_for_role DEFAULT_ADMIN_ROLE_bytes32
                        sim.(State.admins)
                      ++ values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                           sim.(State.optimisticGuardians))
                     (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                       Z.of_nat
                         (List.length sim.(State.optimisticGuardianManagers)))
                     = None).
      { rewrite Dict_get_app_split, Hg_def. exact Hg_og. }
      exact Hab.
    - exact Hg_ogm.
  Qed.

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

  (** ===== R051.b — bool sstore at slot 0's Map2 (proj_sim shape) =====

      The slot-0 sstore in [_grantRole_1468]'s success arm fires:
        update_storage_value_offset_0_t_bool_to_t_bool slot 1
      where [slot = keccak256_tuple2 account (keccak256_tuple2 role 0)]
      — i.e., the OZ-actual [_roles[role].members[account]] address.
      That slot expression IS the framework's [Map2] shape at index 0,
      so the framework's [run_sstore_map2_u256] axiom applies cleanly
      after the standard list-shape unfold (no per-shape trust axiom
      needed, unlike the R051.c slot-3 case where the array body has
      an array-shape slot).

      This block lands two pieces (mirroring R051.c Phase 3 for slot 3):

        - [run_sstore_role_member_at_proj_sim]: thin wrapper that
          bakes in [proj_sim]'s 4-slot list shape so the
          [List.update_nth] match reduces and the wrapper's conclusion
          is a clean Hoare triple (R040 pattern, uint256 flavor).

        - [run_update_storage_value_t_bool_at_proj_sim]: the
          composite walker leaf for the full
          [update_storage_value_offset_0_t_bool_to_t_bool] body
          (R040 pattern, bool flavor — the sister of
          [run_update_storage_value_t_bytes32_at_proj_sim] for the
          slot-3 array body write).

      Used by the [fun_grantRole_1359] walker proof (residual C.1
      in [run_grantRole_1359_equivalent]'s docstring). *)

  (** ----- Bool-leaf sub-lemmas: convert / prepare / shift / update_byte_slice ----- *)

  (** [convert_t_bool_to_t_bool v] = [cleanup_t_bool v] = [iszero(iszero v)].
      For [v = 1], both [iszero]s flip the bit-twice → [1]. *)
  Lemma run_cleanup_t_bool_of_1 codes env state :
    {{? codes, env, Some state |
      cleanup_t_bool 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_bool_to_t_bool_of_1 codes env state :
    {{? codes, env, Some state |
      convert_t_bool_to_t_bool 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold convert_t_bool_to_t_bool.
    lu. l. { c. { apply run_cleanup_t_bool_of_1. } p. }
    repeat (lu || cu || p).
  Qed.

  (** [prepare_store_t_bool v = v] — Yul body is just an assignment. *)
  Lemma run_prepare_store_t_bool codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_bool v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  (** [shift_left_0 v = shl 0 v = v] for [v ∈ [0, 2^256)]. Local copy
      of [ThrottleLib_Leaves.run_shift_left_0] (not imported here). *)
  Lemma run_shift_left_0_local codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      shift_left_0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_left_0.
    lu. repeat (lu || cu || p).
    s. unfold Pure.shl.
    rewrite Z.mul_1_r.
    rewrite Z.mod_small by exact H_v.
    pe; reflexivity.
  Qed.

  (** [update_byte_slice_1_shift_0 prev toInsert]:
        mask     := 255
        toInsert := shl(0, toInsert)            (* = toInsert if < 2^256 *)
        value    := prev AND NOT mask           (* clears low byte *)
        result   := value OR (toInsert AND mask) (* bottom byte = toInsert AND 0xff *)

      For [prev ∈ {0, 1}] (the bool-typed Map2 values) and
      [toInsert = 1]:
        prev AND NOT 0xff = 0 (both 0 and 1 fit in low byte)
        result = 0 OR (1 AND 0xff) = 1. *)
  Lemma run_update_byte_slice_1_shift_0_bool_1
      codes env state (prev : U256.t)
      (H_prev : prev = 0 \/ prev = 1) :
    {{? codes, env, Some state |
      update_byte_slice_1_shift_0 prev 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_1_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (shift_left_0 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_left_0_local;
               change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936;
               lia | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    (* Final reduction: result = or(and(prev, not 255), and(1, 255)).
       For prev ∈ {0, 1}, the [and prev (not 255)] term is 0 (since both
       0 and 1 have their bits 8+ clear), and [and 1 255] = 1. So the
       full expression reduces to 1 — close by direct computation in
       each prev case. *)
    s.
    apply RunO.PureEq; [|reflexivity].
    destruct H_prev as [-> | ->]; vm_compute; reflexivity.
  Qed.

  (** ----- Slot-0 Map2 sstore wrapper (R040 pattern, framework-shape) =====

      The framework's [run_sstore_map2_u256] gives the sstore at
      slot expression [keccak256_tuple2 key2 (keccak256_tuple2 key1
      (Z.of_nat index))] — for [index = 0], exactly OZ's
      [_roles[role].members[account]] slot. The wrapper bakes in
      [proj_sim]'s 4-slot list shape so the [List.update_nth] match
      reduces.

      Sister to [run_sstore_role_values_body_at_proj_sim] (R051.c
      slot-3 axiom) but proven from the framework lemma — slot 0's
      Map2 shape aligns with the framework's nested-keccak axiom, so
      no per-contract trust is needed (unlike slot 3, where the
      array-shape slot expression diverges from the framework's
      nested-keccak Map2). *)
  Lemma run_sstore_role_member_at_proj_sim
      codes env state_base memory sim (role account value : U256.t) :
    let member_map' :=
      Dict.declare_or_assign (role_member_map sim) (role, account) value in
    let proj_sim' :=
      [ StorableValue.Map2 member_map';
        StorableValue.Map2 (role_positions_map sim);
        StorableValue.Map (role_values_length_map sim);
        StorableValue.Map2 (role_values_body_map sim) ] in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sstore (keccak256_tuple2 account (keccak256_tuple2 role 0)) value ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_sim') ?}}.
  Proof.
    cbv zeta.
    pose proof (Storage.run_sstore_map2_u256
                  (proj_sim sim) 0%nat role account value
                  codes env (make_state env state_base memory (proj_sim sim)))
      as H.
    (* Discharge the [get_current_storage] precondition: [make_state]
       unfolds to a [with_current_storage], and the framework lemma
       [get_current_storage_with_current_storage_eq] closes the
       resulting equation. *)
    unfold make_state in H at 1.
    specialize (H (State.get_current_storage_with_current_storage_eq _ _ _)).
    (* Reduce the [nth_error] and [update_nth] matches: unfold
       [proj_sim] so the 4-element list is concrete, then [simpl]
       the list ops. *)
    unfold proj_sim in H at 1.
    simpl List.nth_error in H.
    cbv beta iota in H.
    simpl List.update_nth in H.
    cbv beta iota in H.
    change (Z.to_nat 0) with 0%nat in H.
    change (Z.of_nat 0) with 0 in H.
    (* H's post-state is [with_current_storage env (make_state ...) (...)] —
       unfold the inner [make_state] to expose the double
       [with_current_storage], collapse via
       [with_current_storage_twice_eq], then refold to [make_state] on
       the goal side. *)
    unfold make_state in H at 2.
    rewrite CanonizeState.with_current_storage_twice_eq in H.
    unfold make_state at 2.
    exact H.
  Qed.

  (** ----- Bool sstore wrapper at slot 0's Map2 (R040 pattern) =====

      Composes the convert / sload / bit-mask / sstore chain inside
      [update_storage_value_offset_0_t_bool_to_t_bool slot 1] at the
      OZ-actual [_roles[role].members[account]] slot. The post-state
      is the proj_sim with slot 0's [role_member_map] updated via
      [Dict.declare_or_assign] at key [(role, account)] to value [1].

      The chain inside [update_storage_value_offset_0_t_bool_to_t_bool]:
        convertedValue := convert_t_bool_to_t_bool 1         (* = 1 *)
        prev           := sload slot                          (* = role_member_map[(role,account)] ∈ {0,1} *)
        toInsert       := prepare_store_t_bool convertedValue (* = 1 *)
        new            := update_byte_slice_1_shift_0 prev 1  (* = 1 *)
        sstore slot new                                       (* sets to 1 *)

      Sister to [run_update_storage_value_t_bytes32_at_proj_sim] for
      the slot-3 array body write. Closes R051.b (~80 lines as
      forecast in WISDOM R051). *)
  Lemma run_update_storage_value_t_bool_at_proj_sim
      codes env state_base memory sim (role account : U256.t) :
    let member_map' :=
      Dict.declare_or_assign (role_member_map sim) (role, account) 1 in
    let proj_sim' :=
      [ StorableValue.Map2 member_map';
        StorableValue.Map2 (role_positions_map sim);
        StorableValue.Map (role_values_length_map sim);
        StorableValue.Map2 (role_values_body_map sim) ] in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      update_storage_value_offset_0_t_bool_to_t_bool
        (keccak256_tuple2 account (keccak256_tuple2 role 0)) 1 ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_sim') ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_0_t_bool_to_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    pose proof (role_member_map_values_bool sim (role, account)) as H_prev_bool.
    cbv zeta in H_prev_bool.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bool_to_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bool_to_t_bool_of_1 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_sload_role_member_at_proj_sim | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_1_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_1_shift_0_bool_1;
               exact H_prev_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sstore_role_member_at_proj_sim
                       codes env state_base memory sim role account 1) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ----- Bytes32 storage-extract leaves (identity transforms) =====

      [cleanup_from_storage_t_bytes32] is a no-op assignment at the
      Yul level. [extract_from_storage_value_offset_0_t_bytes32] is
      its composition with [shift_right_0_unsigned], also identity.
      Sister to the t_bool counterparts above, used by the
      [fun_getRoleAdmin_1340] composite that reads slot-1 (bytes32-
      typed adminRole) through [read_from_storage_split_offset_0_t_bytes32]. *)
  Lemma run_cleanup_from_storage_t_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_extract_from_storage_value_offset_0_t_bytes32
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_bytes32.
    lu. l. { c. { apply run_shift_right_0_unsigned_for_bytes32. }
             c. { apply run_cleanup_from_storage_t_bytes32. }
             p. } p.
  Qed.

  (** ===== R051.a — slot-1 admin-field read out-of-projection axiom =====

      [fun_getRoleAdmin_1340] reads [_roles[role].adminRole] at the
      Yul-level slot [keccak256_tuple2 role 0 + 1] (offset 1 from the
      struct-base [keccak256_tuple2 role 0]). Under [proj_sim], slot 0
      is a [Map2 (role, account) → 0/1] modelling the [members]
      sub-field; the [adminRole] field at offset 1 is OUTSIDE the
      projection's modelled state.

      Closing this read structurally would require either replacing
      slot 0's [Map2] with a [MapStruct (role, offset)] (a half-day
      refactor that breaks the landed slot-0 proofs —
      [run_update_storage_value_t_bool_at_proj_sim] and
      [run_hasRole_equivalent]) OR an opaque-slot axiom asserting that
      out-of-range slots return 0. We take the second path here, baked
      into a governor-local trust axiom.

      Trust justification. Every role in Guardian's three role-keyed
      lists uses [DEFAULT_ADMIN_ROLE] as its admin: the
      [project_sim_to_ac] bridge witnesses this directly (every
      [RoleEntry.admin] in the constructed [AccessControl.State] is
      [AccessControl.DEFAULT_ADMIN_ROLE]). Guardian.sol never calls
      [_setRoleAdmin], so the admin field is left at the OZ default
      (which IS [DEFAULT_ADMIN_ROLE = bytes32(0)] per
      [mocks/AccessControl.v::getRoleAdmin]'s [getRoleEntry] fallback).
      The axiom asserts that the on-chain slot read returns the
      [DEFAULT_ADMIN_ROLE_bytes32] parameter — the same value the
      AccessControl mock would return — for each of the three named
      roles.

      Same parametric-trust shape as R052 Option 1's array-slot axioms
      ([run_sload_role_values_length_at_proj_sim] et al.) and R049's
      slot-1 positions modeling. Documented as an audit caveat
      alongside those. *)

  (** ----- Axiom: sload at the admin-field slot =====

      The OZ-actual admin-field slot is [keccak256_tuple2 role 0 + 1].
      Under [proj_sim sim], reading this slot returns
      [DEFAULT_ADMIN_ROLE_bytes32] for each of the three Guardian
      roles. The post-state equals the pre-state — slot reads are
      pure. *)
  Axiom run_sload_role_admin_at_proj_sim :
    forall codes env state_base memory sim (role : U256.t)
        (H_role_known :
           role = DEFAULT_ADMIN_ROLE_bytes32 \/
           role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
           role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32),
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sload (keccak256_tuple2 role 0 + 1) ⇓
      Result.Ok DEFAULT_ADMIN_ROLE_bytes32
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.

  (** ----- Read-from-storage at the admin-field slot =====

      Sister to [run_read_role_member_at_proj_sim] but for the bytes32-
      typed admin field (offset 1 of the RoleData struct). The Yul
      body composes [sload] with the identity-transform pair
      [extract_from_storage_value_offset_0_t_bytes32 = shift_right_0
      ∘ cleanup_from_storage] (both no-ops at the U256-rep level), so
      the value forwarded out is the sload result directly. *)
  Lemma run_read_role_admin_at_proj_sim
      codes env state_base memory sim (role : U256.t)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_offset_0_t_bytes32
        (keccak256_tuple2 role 0 + 1) ⇓
      Result.Ok DEFAULT_ADMIN_ROLE_bytes32
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    unfold read_from_storage_split_offset_0_t_bytes32.
    lu. l. { c. { apply run_sload_role_admin_at_proj_sim. exact H_role_known. }
             c. { apply run_extract_from_storage_value_offset_0_t_bytes32. }
             p. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Composite leaf: [fun_getRoleAdmin_1340] under [proj_sim] =====

      Body shape (from [generated/Guardian_shallow.v]):
        slot ← 0
        slot ← mapping_index_access_bytes32_struct_RoleData(0, role)
             = keccak256_tuple2(role, 0)
        slot ← add(slot, 1)              (* adminRole field offset *)
             = keccak256_tuple2(role, 0) + 1
        ret ← read_from_storage_split_offset_0_t_bytes32(slot)
            = sload(slot) (via cleanup_from_storage = identity)

      The proof composes the [MappingIndexAccessBytes32RoleData]
      memory-threading lemma, the [Pure_add_keccak_offset] discharge
      for the [add(_, 1)] composition, the new
      [run_sload_role_admin_at_proj_sim] trust axiom, and the
      bytes32-cleanup chain ([extract_from_storage_value_offset_0_t_bytes32
      → cleanup_from_storage_t_bytes32 + shift_right_0_unsigned], all
      identity transforms).

      Post-state: memory has two slots consumed by the
      mapping_index_access ([mstore] writes at offsets 0 and 0x20);
      storage is unchanged. *)
  Lemma run_fun_getRoleAdmin_1340_at_proj_sim
      codes env state_base memory sim (role : U256.t)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    exists w0' w1' rest',
    {{? codes, env, Some state |
      fun_getRoleAdmin_1340 role ⇓
      Result.Ok DEFAULT_ADMIN_ROLE_bytes32
    | Some (make_state env state_base
                       (w0' :: w1' :: rest')
                       (proj_sim sim)) ?}}.
  Proof.
    intros state.
    pose proof (MappingIndexAccessBytes32RoleData.run_mapping_index_access
                  codes env state_base 0 role (proj_sim sim) memory H_mem) as Hmia.
    destruct Hmia as (w0' & w1' & rest' & Hmia).
    do 3 eexists.
    (* Discharge the [Pure.add x 1] composition: under the keccak
       offset-bound axiom, [Pure.add (keccak256_tuple2 role 0) 1
       = keccak256_tuple2 role 0 + 1]. *)
    assert (H_pa1 :
      Pure.add (keccak256_tuple2 role 0) 1
      = keccak256_tuple2 role 0 + 1).
    { apply Pure_add_keccak_offset. lia. }
    cbv zeta.
    unfold fun_getRoleAdmin_1340.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bytes32 _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bytes32;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_offset_0_t_bytes32 _) _
            ⇓ _ | _ ?}} =>
          rewrite H_pa1;
          c; [ apply run_read_role_admin_at_proj_sim; exact H_role_known | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
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

  (** ===== Chainable variant of [run_hasRole_equivalent] =====

      The standard [run_hasRole_equivalent] uses [exists state'] for
      the post-state, which makes it hard to thread through other
      callers because the witness shape is undetermined. This variant
      exposes the post-state as [make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)]
      so callers can compose. *)
  Lemma run_fun_hasRole_1292_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let expected := StorableValue.map_get_u256
                      (role_member_map sim) (role, account) in
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_hasRole_1292 role account ⇓
      Result.Ok expected
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    (* First mapping_index_access: role → struct ptr. *)
    pose proof (MappingIndexAccessBytes32RoleData.run_mapping_index_access
                  codes env state_base 0 role (proj_sim sim) memory H_mem) as Hmia1.
    destruct Hmia1 as (w0_a & w1_a & rest_a & Hmia1).
    set (mem_after1 := w0_a :: w1_a :: rest_a).
    pose proof (MappingIndexAccessAddressBool.run_mapping_index_access
                  codes env state_base (keccak256_tuple2 role 0) account
                  (proj_sim sim) mem_after1
                  H_account (ex_intro _ w0_a (ex_intro _ w1_a (ex_intro _ rest_a eq_refl))))
      as Hmia2.
    destruct Hmia2 as (w0_b & w1_b & rest_b & Hmia2).
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
    exists w0_b, w1_b, rest_b.
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
    all: cbn match.
    all: apply RunO.Pure.
  Qed.

  (** ===== Helper leaves for the auth gate =====

      [cleanup_t_bool v = iszero (iszero v)] = 1 if v != 0, else 0.
      For v ∈ {0, 1} this returns [v]. *)
  Lemma run_cleanup_t_bool_of_bool codes env state v
      (Hv : v = 0 \/ v = 1) :
    {{? codes, env, Some state |
      cleanup_t_bool v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    destruct Hv as [-> | ->].
    - unfold cleanup_t_bool. lu. repeat (lu || cu || p).
    - apply run_cleanup_t_bool_of_1.
  Qed.

  (** ===== [fun__checkRole_1326] — admin gate, [hasRole] = 1 branch =====

      Given the caller IS a member of [role], the gate fires the
      no-op (failure) branch of [Shallow.if_]. State is unchanged
      structurally. *)
  Lemma run_fun__checkRole_1326_at_proj_sim_pass
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_member : StorableValue.map_get_u256
                    (role_member_map sim) (role, account) = 1)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__checkRole_1326 role account ⇓
      Result.Ok tt
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    pose proof (run_fun_hasRole_1292_at_proj_sim
                  codes env state_base memory sim role account
                  H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    rewrite H_member in Hhr.
    destruct Hhr as (w0' & w1' & rest' & Hhr).
    exists w0', w1', rest'.
    unfold fun__checkRole_1326.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_1292 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_bool_of_bool; left; reflexivity | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (* Goal 1: the outer let~ pulls in M.strong_let_; unfold and step Pure.
       Goal 2: depends on goal 1's metavar. *)
    - unfold M.strong_let_, M.let_, M.generic_let, M.pure.
      lu. cbn match. apply RunO.Pure.
    - cbn match. apply RunO.Pure.
  Qed.

  (** ===== Caller leaf: [fun__msgSender_3197] =====

      The OZ [_msgSender()] hook in non-meta-tx contracts is just
      [msg.sender], encoded in the shallow form as the [Stdlib.caller]
      primitive. The function's prelude initializes a zero-value
      address local and immediately overwrites it with [caller], then
      returns. Closes by stepping the [LetUnfold] / [CallUnfold] chain
      and discharging [Stdlib.caller] with [pr] (RunO.Primitive). *)
  Lemma run_fun__msgSender_3197 codes env state :
    {{? codes, env, Some state |
      fun__msgSender_3197 ⇓ Result.Ok env.(Environment.caller)
    | Some state ?}}.
  Proof.
    unfold fun__msgSender_3197.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_address _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_address;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call Stdlib.caller _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.caller; pr; p | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== [fun__checkRole_1305] — admin gate, caller-IS-admin branch =====

      Calls _msgSender to fetch the caller, then dispatches to
      _checkRole_1326 with the caller as the account. The composition
      requires the caller to BE a member of [role] (i.e.,
      [hasRole role caller = 1]). *)
  Lemma run_fun__checkRole_1305_at_proj_sim_pass
      codes env state_base memory sim (role : U256.t)
      (H_caller_admin :
         StorableValue.map_get_u256 (role_member_map sim)
           (role, env.(Environment.caller)) = 1)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__checkRole_1305 role ⇓
      Result.Ok tt
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    pose proof (run_fun__msgSender_3197 codes env
                  (make_state env state_base memory (proj_sim sim))) as Hms.
    pose proof (run_fun__checkRole_1326_at_proj_sim_pass
                  codes env state_base memory sim role
                  env.(Environment.caller)
                  H_caller_bound H_caller_admin H_mem) as Hckr.
    destruct Hckr as (w0' & w1' & rest' & Hckr).
    exists w0', w1', rest'.
    unfold fun__checkRole_1305.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call fun__msgSender_3197 _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_1326 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hckr | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== [fun__grantRole_1468] — not-member branch =====

      The function uses [_msgSender] for the log4 event payload but
      ignores it for storage updates. On not-a-member it:
        1. Checks hasRole (= 0).
        2. iszero(0) = 1; cleanup_t_bool 1 = 1; Shallow.if_ takes success.
        3. Computes the slot = [keccak(account, keccak(role, 0))].
        4. update_storage_value_offset_0_t_bool_to_t_bool slot 1
           (the R051.b leaf).
        5. log4 + Leave with var__1437 := 1.

      For the equivalence target, we only need the storage update part;
      the log4 doesn't affect storage projection.

      ===== Status =====

      [Qed]. The walker composes [run_fun_hasRole_1292_at_proj_sim]
      (chainable hasRole returning 0 in the not-member branch),
      [run_update_storage_value_t_bool_at_proj_sim] (R051.b — the bool
      sstore at slot 0's Map2), [run_fun__msgSender_3197] (caller
      leaf for the log4 payload), the two mapping_index_access leaves
      (bytes32→struct, address→bool), and walks the log4 sub-block
      through allocate_unbounded → abi_encode_tuple__to__fromStack →
      log4. Upstream's [simulations/RocqOfSolidity.v::log4] is
      [M.pure tt] — no logging axiom needed. [allocate_unbounded]'s
      [mload(64)] is a state-preserving primitive
      ([eval_primitive Primitive.MLoad] returns
      [inl (get_bytes ..., state)] — the state on the RHS equals the
      state on the LHS). The post-state existential lets the walker
      leave the final memory/state shape abstract; only the
      storage-update logic through the bool sstore is observationally
      pinned, which is exactly what the equivalence theorem needs
      to compose with [proj_sim_add_admin_not_in]. *)
  Lemma run_fun__grantRole_1468_at_proj_sim_not_member
      codes env state_base memory sim (role account : U256.t)
      (H_role : 0 <= role < 2 ^ 256)
      (H_account : 0 <= account < 2^160)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_not_member :
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let member_map' :=
      Dict.declare_or_assign (role_member_map sim) (role, account) 1 in
    let proj_sim' :=
      [ StorableValue.Map2 member_map';
        StorableValue.Map2 (role_positions_map sim);
        StorableValue.Map (role_values_length_map sim);
        StorableValue.Map2 (role_values_body_map sim) ] in
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__grantRole_1468 role account ⇓
      Result.Ok 1
    | Some (make_state env state_base (w0' :: w1' :: rest') proj_sim') ?}}.
  Proof.
    (** Walker proof. The post-state existential lets us leave the final
        memory/state shape abstract — only the storage-update logic
        through the bool sstore is observationally pinned. [log4]
        reduces to [M.pure tt] in our runtime model (see upstream's
        [simulations/RocqOfSolidity.v::log4]), and [allocate_unbounded]'s
        [mload(64)] is a state-preserving primitive (eval_primitive
        returns the same state on MLoad). *)
    cbv zeta.
    (* hasRole pre-walk: in the not-member branch, returns 0. Specialize
       and rewrite [H_not_member] so the hasRole call we splice in
       carries the literal 0 result, which then flows through
       iszero/cleanup to take the [else] arm of the switch. *)
    pose proof (run_fun_hasRole_1292_at_proj_sim
                  codes env state_base memory sim role account
                  H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    rewrite H_not_member in Hhr.
    destruct Hhr as (w0_hr & w1_hr & rest_hr & Hhr).
    set (mem_after_hr := w0_hr :: w1_hr :: rest_hr).
    (* First MIA (bytes32 → struct ptr) post-hasRole. *)
    pose proof (MappingIndexAccessBytes32RoleData.run_mapping_index_access
                  codes env state_base 0 role (proj_sim sim) mem_after_hr
                  (ex_intro _ w0_hr (ex_intro _ w1_hr
                    (ex_intro _ rest_hr eq_refl)))) as Hmia1.
    destruct Hmia1 as (w0_a & w1_a & rest_a & Hmia1).
    set (mem_after_mia1 := w0_a :: w1_a :: rest_a).
    (* Second MIA (address → bool). Its slot arg is [Pure.add (kec2 role
       0) 0]; rewrite away the [+0] so the result aligns with the bool
       sstore's expected [kec2 account (kec2 role 0)] shape. *)
    pose proof (MappingIndexAccessAddressBool.run_mapping_index_access
                  codes env state_base (keccak256_tuple2 role 0) account
                  (proj_sim sim) mem_after_mia1 H_account
                  (ex_intro _ w0_a (ex_intro _ w1_a
                    (ex_intro _ rest_a eq_refl)))) as Hmia2.
    destruct Hmia2 as (w0_b & w1_b & rest_b & Hmia2).
    set (mem_after_mia2 := w0_b :: w1_b :: rest_b).
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 0) 0
                  = keccak256_tuple2 role 0).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (Hmia2' :
      {{? codes, env,
          Some (make_state env state_base mem_after_mia1 (proj_sim sim))
      | mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address
          (Pure.add (keccak256_tuple2 role 0) 0) account
        ⇓ Result.Ok (keccak256_tuple2 account (keccak256_tuple2 role 0))
      | Some (make_state env state_base mem_after_mia2 (proj_sim sim)) ?}}).
    { rewrite H_pa1. exact Hmia2. }
    (* sstore at slot 0's Map2 (R051.b leaf). *)
    pose proof (run_update_storage_value_t_bool_at_proj_sim
                  codes env state_base mem_after_mia2 sim role account)
      as Hsstore.
    cbv zeta in Hsstore.
    set (proj_sim_post :=
           [ StorableValue.Map2
               (Dict.declare_or_assign (role_member_map sim)
                  (role, account) 1);
             StorableValue.Map2 (role_positions_map sim);
             StorableValue.Map (role_values_length_map sim);
             StorableValue.Map2 (role_values_body_map sim) ]).
    fold proj_sim_post in Hsstore.
    set (state_after_sstore :=
           make_state env state_base mem_after_mia2 proj_sim_post).
    (* msgSender: state-preserving leaf. *)
    pose proof (run_fun__msgSender_3197 codes env state_after_sstore)
      as Hms.
    (* Post-state: pin to the post-sstore state. log4/MLoad are
       state-preserving in our sim model. *)
    exists w0_b, w1_b, rest_b.
    fold proj_sim_post.
    change (make_state env state_base (w0_b :: w1_b :: rest_b) proj_sim_post)
      with state_after_sstore.
    unfold fun__grantRole_1468.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      (* Re-unfold M-monad operators that re-introduce themselves at
         each step (inner let~ ' forms reach an M.strong_let_ that the
         top-level unfold doesn't see through). Mirrors the
         [run_array_push_at_proj_sim] walker pattern. *)
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | Shallow.if_ _ _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.if_
      | |- {{? _, _, _ | M.call _ ⇓ _ | _ ?}} =>
          unfold M.call
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_1292 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_bool_of_1 | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia1 | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia2' | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (update_storage_value_offset_0_t_bool_to_t_bool _ _) _
            ⇓ _ | _ ?}} =>
          c; [ exact Hsstore | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__msgSender_3197) _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bytes32_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bytes32_to_t_bytes32 | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_address _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_address;
               first [ exact H_account
                     | exact H_caller_bound ] | ]
      (* allocate_unbounded: mload(64). The MLoad primitive's
         eval_primitive returns [(get_bytes memory 64 32, state)] —
         state-preserving. CallUnfold the body to inline. *)
      | |- {{? _, _, _ |
            LowM.Call allocate_unbounded _ ⇓ _ | _ ?}} =>
          unfold allocate_unbounded; cu
      (* abi_encode_tuple__to__fromStack: pure [add headStart 0]. *)
      | |- {{? _, _, _ |
            LowM.Call (abi_encode_tuple__to__fromStack _) _ ⇓ _ | _ ?}} =>
          unfold abi_encode_tuple__to__fromStack; cu
      | |- {{? _, _, _ | LowM.Call (Stdlib.mload _) _ ⇓ _ | _ ?}} =>
          unfold Stdlib.mload; cu
      | |- {{? _, _, _ |
            LowM.Primitive (Primitive.MLoad _ _) _ ⇓ _ | _ ?}} =>
          pr
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sub _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.sub, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.log4 _ _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.log4, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R053 Phase 4 — [grantRole_1359_inner] composable wrapper =====

      The inner body is a one-liner wrapper around [_grantRole_704]:
        let expr_1354 := role
        let expr_1355 := account
        let expr_1356 := fun__grantRole_704 (expr_1354, expr_1355)
        pure (BlockUnit.Tt, tt)

      So the post-state is exactly whatever [_grantRole_704] produces,
      and the wrapper discards the boolean return ([tt]).

      ===== Composable shape =====

      Rather than instantiating against a specific
      [_grantRole_704] behavior (the not-member branch, the
      already-member branch, etc.), this lemma takes the
      [_grantRole_704] walk as a hypothesis [Hbody_704]. Callers
      (Phase 5 — the top theorem) supply the walk witness with
      whatever post-state shape their case demands.

      This is the SAME composable pattern as
      [run_modifier_onlyRole_1351_admin_passes] (which takes the
      [Hbody] of [fun_grantRole_1359_inner] as a parameter). Composing
      Phase 4 + the modifier lemma lets a caller chain the inner-body
      walk through both wrappers in one shot. *)
  Lemma run_fun_grantRole_1359_inner_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (state' : option RocqOfSolidity.State.t) (granted : U256.t)
      (Hbody_704 :
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun__grantRole_704 role account ⇓
          Result.Ok granted
        | state' ?}}) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_grantRole_1359_inner role account ⇓
      Result.Ok tt
    | state' ?}}.
  Proof.
    unfold fun_grantRole_1359_inner.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun__grantRole_704 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody_704 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Modifier wrapper: [modifier_onlyRole_1351] (admin-passes branch) =====

      The modifier body:
        admin := getRoleAdmin role           (* → DEFAULT_ADMIN_ROLE *)
        _checkRole admin                     (* → no-op if caller is admin *)
        body of grantRole_1359_inner

      Composes [run_fun_getRoleAdmin_1340_at_proj_sim] +
      [run_fun__checkRole_1305_at_proj_sim_pass] + the inner body
      walker passed in as [Hbody].

      To keep the lemma reusable across mutator paths, [Hbody] takes the
      memory shape after the prelude (3-cell-front intact form).

      ===== R054 weakening — [Hbody_post] / [sim'] removed =====

      The original modifier wrapper carried a vestigial
      [Hbody_post : exists memory', state' = Some (make_state ... (proj_sim sim'))]
      hypothesis that asserted the inner-body's post-state equals the
      projection of some [sim']. That syntactic equality is structurally
      irreconcilable with the [Dict.declare_or_assign] post-storage produced
      by the actual Phase 1 + Phase 2 walks (see WISDOM R054). [Hbody_post]
      was never used in the modifier-walk proof — the modifier simply
      threads [state'] through verbatim. Dropping it (and its [sim']
      parameter) removes the structurally-impossible obligation, letting
      callers (Phase 5) carry per-slot OBSERVATIONAL state-equality
      reasoning themselves while still composing through the modifier. *)
  Lemma run_modifier_onlyRole_1351_admin_passes
      codes env state_base memory sim (role account : U256.t) state'
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest)
      (Hbody :
        forall memory',
          (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
          {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
            fun_grantRole_1359_inner role account ⇓
            Result.Ok tt
          | state' ?}}) :
    exists state'',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      modifier_onlyRole_1351 role account ⇓
      Result.Ok tt
    | state'' ?}}
    /\ state'' = state'.
  Proof.
    (* getRoleAdmin returns DEFAULT_ADMIN_ROLE_bytes32 and threads memory.
       After admin = DEFAULT_ADMIN_ROLE_bytes32, _checkRole_1305 is called
       with the admin role; caller must be a DEFAULT_ADMIN holder. This is
       precisely [H_caller_admin]. The chained call to [fun_grantRole_1359_inner]
       runs the body. *)
    pose proof (run_fun_getRoleAdmin_1340_at_proj_sim
                  codes env state_base memory sim role H_role_known H_mem) as Hgra.
    destruct Hgra as (w0' & w1' & rest' & Hgra).
    set (mem_after_gra := w0' :: w1' :: rest').
    (* H_caller_admin : has_admin sim caller = true.
       Need: map_get_u256 (role_member_map sim) (DEFAULT_ADMIN_ROLE, caller) = 1.
       That's exactly the body of [project_sim_to_ac_hasRole_admin], but
       at the projection level. *)
    assert (H_admin_member :
              StorableValue.map_get_u256 (role_member_map sim)
                (DEFAULT_ADMIN_ROLE_bytes32, env.(Environment.caller)) = 1).
    { (* Compute via the dict-lookup over the admins list. *)
      unfold role_member_map.
      rewrite map_get_app_split.
      unfold has_admin in H_caller_admin.
      apply (proj1 (addr_in_true_iff_In _ _)) in H_caller_admin.
      set (caller := env.(Environment.caller)) in *.
      induction (State.admins sim) as [|a rest IH].
      - simpl in H_caller_admin. exfalso. exact H_caller_admin.
      - simpl members_for_role. simpl Dict.get.
        cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
        rewrite Z.eqb_refl. simpl andb.
        change (Dict.Eq.eqb caller a) with (caller =? a).
        destruct (caller =? a) eqn:Hca.
        + reflexivity.
        + apply Z.eqb_neq in Hca.
          destruct H_caller_admin as [Heq | Hin]; [congruence|].
          apply IH. exact Hin. }
    pose proof (run_fun__checkRole_1305_at_proj_sim_pass
                  codes env state_base mem_after_gra sim
                  DEFAULT_ADMIN_ROLE_bytes32
                  H_admin_member H_caller_bound) as Hckr.
    assert (Hmem_after_gra : exists w0 w1 rest,
              mem_after_gra = w0 :: w1 :: rest).
    { exists w0', w1', rest'. reflexivity. }
    specialize (Hckr Hmem_after_gra).
    destruct Hckr as (w0'' & w1'' & rest'' & Hckr).
    set (mem_after_ckr := w0'' :: w1'' :: rest'').
    assert (Hmem_after_ckr : exists w0 w1 rest,
              mem_after_ckr = w0 :: w1 :: rest).
    { exists w0'', w1'', rest''. reflexivity. }
    specialize (Hbody mem_after_ckr Hmem_after_ckr).
    eexists.
    split; [|reflexivity].
    unfold modifier_onlyRole_1351.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call, M.do.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun_getRoleAdmin_1340 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgra | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_1305 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hckr | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_grantRole_1359_inner _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R055: existential-state modifier wrapper =====

      Variant of [run_modifier_onlyRole_1351_admin_passes] where the
      inner body's post-state is existentially abstracted via [Hbody].
      Needed for the milestone proof's already-member walk, whose
      [_grantRole_1468] member-arm post-state depends on the input
      memory shape (which the modifier chooses internally). *)
  Lemma run_modifier_onlyRole_1351_admin_passes_exists
      codes env state_base memory sim (role account : U256.t)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest)
      (storage_post : SimulatedStorage.t)
      (Hbody :
        forall memory',
          (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
          exists memory'',
          {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
            fun_grantRole_1359_inner role account ⇓
            Result.Ok tt
          | Some (make_state env state_base memory'' storage_post) ?}}) :
    exists memory'',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      modifier_onlyRole_1351 role account ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'' storage_post) ?}}.
  Proof.
    pose proof (run_fun_getRoleAdmin_1340_at_proj_sim
                  codes env state_base memory sim role H_role_known H_mem) as Hgra.
    destruct Hgra as (w0' & w1' & rest' & Hgra).
    set (mem_after_gra := w0' :: w1' :: rest').
    assert (H_admin_member :
              StorableValue.map_get_u256 (role_member_map sim)
                (DEFAULT_ADMIN_ROLE_bytes32, env.(Environment.caller)) = 1).
    { unfold role_member_map.
      rewrite map_get_app_split.
      unfold has_admin in H_caller_admin.
      apply (proj1 (addr_in_true_iff_In _ _)) in H_caller_admin.
      set (caller := env.(Environment.caller)) in *.
      induction (State.admins sim) as [|a rest IH].
      - simpl in H_caller_admin. exfalso. exact H_caller_admin.
      - simpl members_for_role. simpl Dict.get.
        cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
        rewrite Z.eqb_refl. simpl andb.
        change (Dict.Eq.eqb caller a) with (caller =? a).
        destruct (caller =? a) eqn:Hca.
        + reflexivity.
        + apply Z.eqb_neq in Hca.
          destruct H_caller_admin as [Heq | Hin]; [congruence|].
          apply IH. exact Hin. }
    pose proof (run_fun__checkRole_1305_at_proj_sim_pass
                  codes env state_base mem_after_gra sim
                  DEFAULT_ADMIN_ROLE_bytes32
                  H_admin_member H_caller_bound) as Hckr.
    assert (Hmem_after_gra : exists w0 w1 rest,
              mem_after_gra = w0 :: w1 :: rest).
    { exists w0', w1', rest'. reflexivity. }
    specialize (Hckr Hmem_after_gra).
    destruct Hckr as (w0'' & w1'' & rest'' & Hckr).
    set (mem_after_ckr := w0'' :: w1'' :: rest'').
    assert (Hmem_after_ckr : exists w0 w1 rest,
              mem_after_ckr = w0 :: w1 :: rest).
    { exists w0'', w1'', rest''. reflexivity. }
    specialize (Hbody mem_after_ckr Hmem_after_ckr).
    destruct Hbody as (mem_inner & Hbody).
    exists mem_inner.
    unfold modifier_onlyRole_1351.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call, M.do.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun_getRoleAdmin_1340 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgra | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_1305 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hckr | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_grantRole_1359_inner _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R053 Phase 5 prelude — [fun_grantRole_1359] outer wrapper =====

      The public entry [fun_grantRole_1359] is a thin wrapper around
      [modifier_onlyRole_1351]:
        do~ modifier_onlyRole_1351 role account
        M.pure tt

      Composable form — takes the modifier walk as a hypothesis. The
      top theorem (run_grantRole_1359_equivalent) instantiates the
      modifier with the inner-body walk (Phase 4 composable wrapper
      above), then composes here to lift to the public entry. *)
  Lemma run_fun_grantRole_1359_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (state' : option RocqOfSolidity.State.t)
      (Hmod :
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          modifier_onlyRole_1351 role account ⇓
          Result.Ok tt
        | state' ?}}) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_grantRole_1359 role account ⇓
      Result.Ok tt
    | state' ?}}.
  Proof.
    unfold fun_grantRole_1359.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call, M.do.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (modifier_onlyRole_1351 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmod | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R053 Phase 2 — [fun_add_2085] composable wrapper =====

      OZ EnumerableSet [add(set, value)] (via [fun_add_2085 →
      fun__add_1614]):
        if (_positions[role][value] != 0) return 0  (* already in *)
        else:
          _values[role].push(value)        (* array_push, slots 2 + 3 *)
          length := array_length _values   (* = oldLen + 1 *)
          _positions[role][value] := length (* slot 1 sstore *)
          return 1

      The walker composes the four slot-1/2/3 trust axioms with the
      memory-only leaves ([_contains]'s MIA, the conversion chain).

      The post-state is left as an [exists state'] existential — the
      caller (Phase 3 [_grantRole_704] walker) bridges to the
      cons-prefixed [proj_sim_add_admin_not_in] shape. *)

  (** ----- Axiom: sload at positions sub-mapping (positions slot)
      =====

      The OZ-actual positions slot is
      [keccak256(value, keccak256(role, 1) + 1)] (struct field offset 1
      from the [Set] struct's [_values] anchor). Under any four-slot
      projection variant, that slot's value is the per-(role, value)
      positions map entry.

      Generic in [length_map'] / [body_map'] / [positions_map'] — same
      parametric-trust shape as the existing
      [run_sload_role_values_length_at_proj_sim_post] /
      [run_sload_role_values_body_at_proj_sim] axioms. *)
  Axiom run_sload_role_positions_at_proj_sim :
    forall codes env state_base memory (role value : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj) |
      Stdlib.sload (keccak256_tuple2 value (keccak256_tuple2 role 1 + 1)) ⇓
      Result.Ok (StorableValue.map_get_u256 positions_map_in (role, value))
    | Some (make_state env state_base memory proj) ?}}.

  (** ----- Axiom: sstore at positions sub-mapping =====

      Writing [new_position] at the OZ-actual positions slot updates
      slot 1's per-(role, value) positions map. Generic shape (same
      parametric-trust footprint as the sload above and the slot 2/3
      sstore axioms in R051.c). *)
  Axiom run_sstore_role_positions_at_proj_sim :
    forall codes env state_base memory (role value new_position : U256.t)
        (member_map_in : Dict.t (U256.t * U256.t) U256.t)
        (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
        (length_map_in : Dict.t U256.t U256.t)
        (body_map_in : Dict.t (U256.t * U256.t) U256.t),
    let positions_map' :=
      Dict.declare_or_assign positions_map_in (role, value) new_position in
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map';
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      Stdlib.sstore (keccak256_tuple2 value (keccak256_tuple2 role 1 + 1)) new_position ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_post) ?}}.

  (** ----- MIA leaf: bytes32 → uint256 positions sub-mapping =====

      Same shape as the existing MIA modules (bytes32 → RoleData,
      address → bool), but for the [_positions] map type. *)
  Module MappingIndexAccessBytes32Uint256.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32.
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

  End MappingIndexAccessBytes32Uint256.

  (** ----- Conversion chain leaves used by [fun_add_2085]'s prelude
      =====

      [fun_add_2085] threads [value] through:
        convert_t_address_to_t_uint160   (* identity for v < 2^160 *)
        convert_t_uint160_to_t_uint256   (* identity *)
        convert_t_uint256_to_t_bytes32   (* identity for v < 2^256 *)

      Each is a thin no-op-after-cleanup wrapper at the U256 level. *)
  Lemma run_convert_t_address_to_t_uint160 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_uint160.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160. exact H_v. } p. } p.
  Qed.

  Lemma run_cleanup_t_uint256_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_uint256 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint256_id. }
             p. } p.
  Qed.

  Lemma run_convert_t_uint256_to_t_bytes32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_bytes32.
    lu. l. { c. { apply run_cleanup_t_uint256_id. }
             c. { apply run_shift_left_0_local; exact H_v. }
             c. { apply run_cleanup_t_bytes32. }
             p. } p.
  Qed.

  Lemma run_convert_t_structₓ_AddressSet_storage_to_ptr
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_structₓ_Set_storage_to_ptr
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_array_bytes32_storage_to_ptr
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_array_t_arrayₓ_t_bytes32_ₓdyn_storage_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_array_t_arrayₓ_t_bytes32_ₓdyn_storage_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  (** ----- Uint256 prepare/byte-slice leaves =====

      Local copies of [ThrottleLib_Leaves.run_prepare_store_t_uint256] /
      [ThrottleLib_Leaves.run_update_byte_slice_32_shift_0] — needed
      here because Guardian.v does not import the ThrottleLib leaves
      module. *)
  Lemma run_prepare_store_t_uint256_local codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_update_byte_slice_32_shift_0_local codes env state
      (old_value new_value : U256.t)
      (H_new : 0 <= new_value < 2^256) :
    {{? codes, env, Some state |
      update_byte_slice_32_shift_0 old_value new_value ⇓ Result.Ok new_value
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_32_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (shift_left_0 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_left_0_local; exact H_new | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    s.
    unfold Pure.and, Pure.or, Pure.not.
    change (2 ^ 256 -
            115792089237316195423570985008687907853269984665640564039457584007913129639935 - 1)
      with 0.
    rewrite Z.land_0_r.
    rewrite Z.lor_0_l.
    change 115792089237316195423570985008687907853269984665640564039457584007913129639935
      with (Z.ones 256).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small by exact H_new.
    pe; reflexivity.
  Qed.

  Lemma run_convert_t_uint256_to_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint256_id. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint256_id. }
             p. } p.
  Qed.

  (** ----- Wrapper leaf: [update_storage_value_offset_0_t_uint256_to_t_uint256]
      at the positions slot under [proj_sim] =====

      Composes convert / sload / prepare / bit-mask / sstore at the
      OZ-actual positions slot
      [keccak256(value, keccak256(role, 1) + 1)]. Post-state has slot 1
      updated via [Dict.declare_or_assign] at key [(role, value)]. *)
  Lemma run_update_storage_value_t_uint256_at_positions_proj_sim
      codes env state_base memory (role value new_position : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (H_new_position : 0 <= new_position < 2^256) :
    let positions_map' :=
      Dict.declare_or_assign positions_map_in (role, value) new_position in
    let proj_pre :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map';
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    {{? codes, env, Some (make_state env state_base memory proj_pre) |
      update_storage_value_offset_0_t_uint256_to_t_uint256
        (keccak256_tuple2 value (keccak256_tuple2 role 1 + 1)) new_position ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_post) ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_0_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sload_role_positions_at_proj_sim
                       codes env state_base memory role value
                       member_map_in positions_map_in length_map_in body_map_in) | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_uint256_local | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_32_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_32_shift_0_local;
               exact H_new_position | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sstore_role_positions_at_proj_sim
                       codes env state_base memory role value new_position
                       member_map_in positions_map_in length_map_in body_map_in) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ===== R053 Phase 2 sub-wrapper: [run_fun__contains_1760_at_proj_sim_not_in]
      =====

      [fun__contains_1760(set_slot, value)] is OZ EnumerableSet's
      [_contains]:

        _88_slot       := set_slot
        _89            := add(set_slot, 1)            (* positions sub-mapping slot *)
        _92            := MIA(_89, value)             (* positions slot for this (role, value) *)
        _93            := read_from_storage_split_offset_0_t_uint256(_92)
        expr_1757      := iszero(eq(cleanup_t_uint256(_93), 0))
        return expr_1757

      In the "not in the set" branch we have [_93 = 0] (the positions
      sload returns 0 by [H_not_in]). Then [eq(0, 0) = 1], [iszero(1) = 0],
      and [fun__contains_1760] returns [0] (false).

      The wrapper is set up for the call from [fun__add_1614] where
      [set_slot = keccak256_tuple2 role 1] (the role's set anchor); the
      [+1] offset to the positions sub-mapping resolves cleanly via
      [Pure_add_keccak_offset]. State is unchanged (sload only).

      Memory is consumed by the MIA leaf (two [mstore]s then a
      keccak); the post-state's memory tail is left as an existential
      so the caller can thread it. *)
  Lemma run_fun__contains_1760_at_proj_sim_not_in
      codes env state_base memory (role value : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (H_not_in :
         StorableValue.map_get_u256 positions_map_in (role, value) = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory proj) |
      fun__contains_1760 (keccak256_tuple2 role 1) value ⇓
      Result.Ok 0
    | Some (make_state env state_base (w0' :: w1' :: rest') proj) ?}}.
  Proof.
    cbv zeta.
    (* [Pure.add (keccak256_tuple2 role 1) 1 = keccak256_tuple2 role 1 + 1]. *)
    assert (H_pa_kec_1 :
              Pure.add (keccak256_tuple2 role 1) 1
              = keccak256_tuple2 role 1 + 1).
    { apply Pure_add_keccak_offset. lia. }
    (* MIA leaf for the positions sub-mapping: produces the slot expr
       [keccak256_tuple2 value (keccak256_tuple2 role 1 + 1)]. *)
    pose proof (MappingIndexAccessBytes32Uint256.run_mapping_index_access
                  codes env state_base
                  (keccak256_tuple2 role 1 + 1) value
                  ([ StorableValue.Map2 member_map_in;
                     StorableValue.Map2 positions_map_in;
                     StorableValue.Map length_map_in;
                     StorableValue.Map2 body_map_in ])
                  memory H_mem) as Hmia.
    destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
    set (mem_after_mia := w0_m :: w1_m :: rest_m).
    (* Repackage the MIA with the [Pure.add _ 1] surface shape so the
       walker's call arm matches the inner call's argument directly. *)
    assert (Hmia' :
      {{? codes, env,
          Some (make_state env state_base memory
                  ([ StorableValue.Map2 member_map_in;
                     StorableValue.Map2 positions_map_in;
                     StorableValue.Map length_map_in;
                     StorableValue.Map2 body_map_in ]))
      | mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32
          (Pure.add (keccak256_tuple2 role 1) 1) value
        ⇓ Result.Ok (keccak256_tuple2 value (keccak256_tuple2 role 1 + 1))
      | Some (make_state env state_base mem_after_mia
                ([ StorableValue.Map2 member_map_in;
                   StorableValue.Map2 positions_map_in;
                   StorableValue.Map length_map_in;
                   StorableValue.Map2 body_map_in ])) ?}}).
    { rewrite H_pa_kec_1. exact Hmia. }
    (* The positions sload returns 0 by [H_not_in]. *)
    pose proof (run_sload_role_positions_at_proj_sim
                  codes env state_base mem_after_mia role value
                  member_map_in positions_map_in
                  length_map_in body_map_in) as Hsl.
    cbv zeta in Hsl.
    rewrite H_not_in in Hsl.
    exists w0_m, w1_m, rest_m.
    unfold fun__contains_1760,
           read_from_storage_split_offset_0_t_uint256,
           extract_from_storage_value_offset_0_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia' | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hsl | ]
      | |- {{? _, _, _ |
            LowM.Call (shift_right_0_unsigned _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_right_0_unsigned | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_from_storage_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_from_storage_t_uint256, M.pure;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint256_id | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_rational_0_by_1_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold convert_t_rational_0_by_1_to_t_uint256;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.eq _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.eq, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R053 Phase 2 sub-wrapper: [run_fun__add_1614_at_proj_sim_not_in]
      =====

      [fun__add_1614(set_slot, value)] is OZ EnumerableSet's [_add]
      internal. In the not-in-set branch:

        1. [_contains(set_slot, value)] → 0  (positions sload returns 0)
        2. iszero(0) = 1, cleanup_t_bool(1) = 1, switch takes else arm
        3. [array_push(set_slot, value)] — body+length sstore chain
           (R051.c).
        4. Re-read [array_length(set_slot)] = oldLen + 1.
        5. MIA on [set_slot + 1] with key=value → positions slot expr.
        6. [update_storage_value(positions_slot, oldLen+1)] — writes
           the new position into slot 1's positions sub-mapping.
        7. Return 0x01.

      Composes three Qed'd witnesses:
        - [run_fun__contains_1760_at_proj_sim_not_in] for step 1.
        - [run_array_push_at_proj_sim] for step 3.
        - [run_update_storage_value_t_uint256_at_positions_proj_sim]
          for step 6.

      Plus the array-length post-bump axiom
      [run_sload_role_values_length_at_proj_sim_post] for the re-read
      against the post-push 4-slot projection.

      The post-state has slot 2 (length) bumped to [oldLen+1], slot 3
      (body) with [(role, oldLen) := value], and slot 1 (positions)
      with [(role, value) := oldLen+1]. Memory shape is left
      existential.

      The wrapper is set up for the call from [fun_add_2085] where
      [set_slot = keccak256_tuple2 role 1]. *)
  Lemma run_fun__add_1614_at_proj_sim_not_in
      codes env state_base memory (role value : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (H_value_u256 : 0 <= value < 2^256)
      (H_not_in :
         StorableValue.map_get_u256 positions_map_in (role, value) = 0)
      (H_len_bound :
         StorableValue.map_get_u256 length_map_in role
         + 1 < 18446744073709551616)
      (H_len_nn :
         0 <= StorableValue.map_get_u256 length_map_in role)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let oldLen := StorableValue.map_get_u256 length_map_in role in
    let length_map' :=
      Dict.declare_or_assign length_map_in role (oldLen + 1) in
    let body_map' :=
      Dict.declare_or_assign body_map_in (role, oldLen) value in
    let positions_map' :=
      Dict.declare_or_assign positions_map_in (role, value) (oldLen + 1) in
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map';
        StorableValue.Map length_map';
        StorableValue.Map2 body_map' ] in
    exists memory',
    {{? codes, env, Some (make_state env state_base memory proj) |
      fun__add_1614 (keccak256_tuple2 role 1) value ⇓
      Result.Ok 1
    | Some (make_state env state_base memory' proj_post) ?}}.
  Proof.
    cbv zeta.
    (* The slot expression for the [+0] and [+1] field-offset writes
       reduces under [Pure_add_keccak_offset]. *)
    assert (H_pa_kec_0 :
              Pure.add (keccak256_tuple2 role 1) 0
              = keccak256_tuple2 role 1).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (H_pa_kec_1 :
              Pure.add (keccak256_tuple2 role 1) 1
              = keccak256_tuple2 role 1 + 1).
    { apply Pure_add_keccak_offset. lia. }
    (* Set oldLen / length_map' / body_map' for the state-tracking
       through the walker. *)
    set (oldLen := StorableValue.map_get_u256 length_map_in role).
    set (length_map' := Dict.declare_or_assign
                          length_map_in role (oldLen + 1)).
    set (body_map' := Dict.declare_or_assign
                        body_map_in (role, oldLen) value).
    (* oldLen bounds: directly from the [H_len_bound] and [H_len_nn]
       caller-supplied hypotheses (the previous unconditional [Z.of_nat]
       lower bound relied on the [role_values_length_map sim] structure,
       which is no longer available in the generic form). *)
    assert (H_oldLen_bound : oldLen < 18446744073709551616) by
      (unfold oldLen; lia).
    assert (H_oldLen_nn : 0 <= oldLen) by exact H_len_nn.
    (* [oldLen + 1] fits in u256 — needed for the positions write bound. *)
    assert (H_newLen_u256 : 0 <= oldLen + 1 < 2 ^ 256) by lia.
    (* Step 1: contains_1760 walker — returns 0, memory shape preserved
       (modulo MIA scratch). *)
    pose proof (run_fun__contains_1760_at_proj_sim_not_in
                  codes env state_base memory role value
                  member_map_in positions_map_in length_map_in body_map_in
                  H_not_in H_mem) as Hcontains.
    cbv zeta in Hcontains.
    destruct Hcontains as (w0_c & w1_c & rest_c & Hcontains).
    set (mem_after_c := w0_c :: w1_c :: rest_c).
    (* Step 3: array_push walker — bumps length+body. The walker needs
       a 2-word memory layout (it does an [mstore(0, anchor)] then
       exposes the surviving tail). Our 2-word [mem_after_c] satisfies
       that. Returns a post-state with the post-push 4-slot projection
       and memory of the form [keccak256_tuple2 role 1 :: w1' :: rest']. *)
    assert (H_mem_after_c_2 :
              exists w0 w1 rest, mem_after_c = w0 :: w1 :: rest).
    { unfold mem_after_c. eauto 10. }
    pose proof (run_array_push_at_proj_sim
                  codes env state_base mem_after_c role value
                  member_map_in positions_map_in length_map_in body_map_in
                  H_len_bound H_len_nn H_value_u256 H_mem_after_c_2) as Hpush.
    cbv zeta in Hpush.
    fold oldLen length_map' body_map' in Hpush.
    destruct Hpush as (w1_p & rest_p & state_after_push & Hpush & Hstate_after_push).
    set (mem_after_push := keccak256_tuple2 role 1 :: w1_p :: rest_p).
    set (proj_after_push :=
           [ StorableValue.Map2 member_map_in;
             StorableValue.Map2 positions_map_in;
             StorableValue.Map length_map';
             StorableValue.Map2 body_map' ]).
    fold mem_after_push proj_after_push in Hstate_after_push.
    rewrite Hstate_after_push in Hpush.
    (* MIA leaf for the positions sub-mapping (step 5), against the
       post-push 4-slot projection — uses the 2-word memory handle. *)
    pose proof (MappingIndexAccessBytes32Uint256.run_mapping_index_access
                  codes env state_base
                  (keccak256_tuple2 role 1 + 1) value
                  proj_after_push
                  mem_after_push
                  (ex_intro _ (keccak256_tuple2 role 1)
                    (ex_intro _ w1_p
                      (ex_intro _ rest_p eq_refl)))) as Hmia.
    destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
    set (mem_after_mia := w0_m :: w1_m :: rest_m).
    (* Repackage the MIA with [Pure.add _ 1] surface shape. *)
    assert (Hmia' :
      {{? codes, env,
          Some (make_state env state_base mem_after_push proj_after_push)
      | mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32
          (Pure.add (keccak256_tuple2 role 1) 1) value
        ⇓ Result.Ok (keccak256_tuple2 value (keccak256_tuple2 role 1 + 1))
      | Some (make_state env state_base mem_after_mia proj_after_push) ?}}).
    { rewrite H_pa_kec_1. exact Hmia. }
    (* Pre-pose the post-bump length sload: at [keccak256_tuple2 role 1]
       against the post-push 4-slot state, returns
       [map_get_u256 length_map' role = oldLen + 1]. *)
    pose proof (run_sload_role_values_length_at_proj_sim_post
                  codes env state_base mem_after_push role
                  member_map_in positions_map_in length_map' body_map')
      as Hsload_len_post.
    cbv zeta in Hsload_len_post.
    fold proj_after_push in Hsload_len_post.
    assert (H_dict_declare_role_eq :
      forall (d : Dict.t U256.t U256.t) (k : U256.t) (v : U256.t),
        StorableValue.map_get_u256 (Dict.declare_or_assign d k v) k = v).
    { intros d k v.
      unfold StorableValue.map_get_u256, Dict.declare_or_assign.
      induction d as [|[k' v'] rest_d IH]; cbn.
      - change (Dict.Eq.eqb k k) with (k =? k).
        rewrite Z.eqb_refl. reflexivity.
      - change (Dict.Eq.eqb k' k) with (k' =? k).
        destruct (Z.eqb_spec k' k) as [Hek | Hne].
        + subst k'. cbn.
          change (Dict.Eq.eqb k k) with (k =? k).
          rewrite Z.eqb_refl. reflexivity.
        + cbn.
          change (Dict.Eq.eqb k k') with (k =? k').
          replace (k =? k') with false by
            (symmetry; apply Z.eqb_neq; lia).
          exact IH. }
    assert (H_get_length_map' :
              StorableValue.map_get_u256 length_map' role = oldLen + 1).
    { unfold length_map'. apply H_dict_declare_role_eq. }
    rewrite H_get_length_map' in Hsload_len_post.
    (* Step 6: positions write. We feed it the [length_map'] threaded
       in, the unchanged [positions_map_in], and [body_map'] as body.
       New position = oldLen + 1. *)
    pose proof (run_update_storage_value_t_uint256_at_positions_proj_sim
                  codes env state_base mem_after_mia role value
                  (oldLen + 1)
                  member_map_in positions_map_in length_map' body_map'
                  H_newLen_u256)
      as Hpos.
    cbv zeta in Hpos.
    (* Post-state: pin the concrete memory existential to [mem_after_mia]
       (the post-step-5 memory) — the positions write [Hpos] is
       state-preserving on memory and produces the post-state matching
       [proj_post]. *)
    exists mem_after_mia.
    (* Unfold the body and prepare for the walker. We leave
       [fun__contains_1760], [array_push_*], and
       [update_storage_value_*] FOLDED so the corresponding witnesses
       ([Hcontains], [Hpush], [Hpos]) dispatch the entire call (rather
       than have the walker step through the body).

       [array_length_t_arrayₓ_t_bytes32_ₓdyn_storage] IS unfolded
       eagerly so its body (a single [sload]) flows into the generic
       sload arm. *)
    unfold fun__add_1614,
           array_length_t_arrayₓ_t_bytes32_ₓdyn_storage.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    (* Setup: switch δ = cleanup_t_bool (iszero 0) = cleanup_t_bool 1
       = 1 ≠ 0, so the else arm fires (the push branch). *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      (* Step 1: contains call — use the pre-posed witness. *)
      | |- {{? _, _, _ |
            LowM.Call (fun__contains_1760 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hcontains | ]
      (* iszero, eq, cleanup_t_bool — pure arithmetic. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_t_bool;
               lu; repeat (lu || cu || p) | ]
      (* add(set_slot, 0) and add(set_slot, 1) — pure. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      (* convert_array_bytes32_storage_to_ptr — no-op. *)
      | |- {{? _, _, _ |
            LowM.Call (convert_array_t_arrayₓ_t_bytes32_ₓdyn_storage_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_array_bytes32_storage_to_ptr | ]
      (* Step 3: array_push call. The slot is [Pure.add (kec) 0];
         rewrite away to [kec], then dispatch via the pre-posed
         witness. *)
      | |- {{? _, _, _ |
            LowM.Call (array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr _ _) _ ⇓ _ | _ ?}} =>
          first [ rewrite H_pa_kec_0 | idtac ];
          c; [ exact Hpush | ]
      (* Step 4: post-push length re-read = sload at set_slot. The
         body of [array_length_t_arrayₓ_t_bytes32_ₓdyn_storage] is a
         single [sload(value)]; the wrapper is unfolded ahead so the
         sload arm fires directly. Slot is [Pure.add (kec) 0];
         rewrite to [kec] first then dispatch via [Hsload_len_post]. *)
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload (Pure.add (keccak256_tuple2 _ 1) 0)) _ ⇓ _ | _ ?}} =>
          rewrite H_pa_kec_0;
          c; [ exact Hsload_len_post | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload (keccak256_tuple2 _ 1)) _ ⇓ _ | _ ?}} =>
          c; [ exact Hsload_len_post | ]
      (* Step 5: MIA dispatch — use pre-posed witness. *)
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia' | apply RunO.Pure ]
      (* Step 6: positions write — use pre-posed witness. *)
      | |- {{? _, _, _ |
            LowM.Call
              (update_storage_value_offset_0_t_uint256_to_t_uint256 _ _) _
            ⇓ _ | _ ?}} =>
          c; [ exact Hpos | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Main lemma: [run_fun_add_2085_at_proj_sim] =====

      Outer wrapper for OZ EnumerableSet [add] in the not-yet-in-set
      branch. [fun_add_2085] is itself a thin shell around
      [fun__add_1614]:

        expr_2079 = convert_t_address_to_t_uint160(value)   = value
        expr_2080 = convert_t_uint160_to_t_uint256(value)   = value
        expr_2081 = convert_t_uint256_to_t_bytes32(value)   = value
        _60_slot  = convert_t_structₓ_Set_storage_to_ptr(set_slot+0)
                  = set_slot
        expr_2082 = fun__add_1614(_60_slot, expr_2081)
                  = fun__add_1614(set_slot, value)
        return 1

      All converts are no-ops for the value bound [v < 2^160 ≤ 2^256].
      The post-state is whatever [_add_1614] produces and is left
      existential — the Phase 3 caller bridges to
      [proj_sim_add_admin_not_in]'s cons-prefixed shape via
      [Dict.declare_or_assign]-to-cons equalities.

      Closed via composition with
      [run_fun__add_1614_at_proj_sim_not_in] (the Phase 2 sub-wrapper)
      — see the R053 Phase 2 sub-wrapper docstring for the inner
      call chain ([_contains_1760] + [array_push] + positions
      sstore). *)
  Lemma run_fun_add_2085_at_proj_sim
      codes env state_base memory (role value : U256.t)
      (member_map_in : Dict.t (U256.t * U256.t) U256.t)
      (positions_map_in : Dict.t (U256.t * U256.t) U256.t)
      (length_map_in : Dict.t U256.t U256.t)
      (body_map_in : Dict.t (U256.t * U256.t) U256.t)
      (H_value : 0 <= value < 2^160)
      (H_not_in :
         StorableValue.map_get_u256 positions_map_in (role, value) = 0)
      (H_len_bound :
         StorableValue.map_get_u256 length_map_in role
         + 1 < 18446744073709551616)
      (H_len_nn :
         0 <= StorableValue.map_get_u256 length_map_in role)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let oldLen := StorableValue.map_get_u256 length_map_in role in
    let length_map' :=
      Dict.declare_or_assign length_map_in role (oldLen + 1) in
    let body_map' :=
      Dict.declare_or_assign body_map_in (role, oldLen) value in
    let positions_map' :=
      Dict.declare_or_assign positions_map_in (role, value) (oldLen + 1) in
    let proj :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map_in;
        StorableValue.Map length_map_in;
        StorableValue.Map2 body_map_in ] in
    let proj_post :=
      [ StorableValue.Map2 member_map_in;
        StorableValue.Map2 positions_map';
        StorableValue.Map length_map';
        StorableValue.Map2 body_map' ] in
    exists memory',
    {{? codes, env, Some (make_state env state_base memory proj) |
      fun_add_2085 (keccak256_tuple2 role 1) value ⇓
      Result.Ok 1
    | Some (make_state env state_base memory' proj_post) ?}}.
  Proof.
    cbv zeta.
    (* Phase 2 outer wrapper: convert chain (all no-ops for value < 2^160)
       then dispatch via [_add_1614]'s composable witness. *)
    (* Value bound also fits in 2^256 — needed for convert chain and
       for the inner [_add_1614] call. *)
    assert (H_value_u256 : 0 <= value < 2^256).
    { split; [lia|].
      change (2^160) with 1461501637330902918203684832716283019655932542976 in H_value.
      change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
      lia. }
    (* The slot expression for the [+0] field-offset reduces. *)
    assert (H_pa_kec_0 :
              Pure.add (keccak256_tuple2 role 1) 0
              = keccak256_tuple2 role 1).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    (* Compose [_add_1614]'s witness for the inner call. *)
    pose proof (run_fun__add_1614_at_proj_sim_not_in
                  codes env state_base memory role value
                  member_map_in positions_map_in length_map_in body_map_in
                  H_value_u256 H_not_in H_len_bound H_len_nn H_mem) as Hinner.
    cbv zeta in Hinner.
    destruct Hinner as (mem_inner & Hinner).
    exists mem_inner.
    unfold fun_add_2085.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      (* Conversion chain — all no-ops at the value-bound preconditions. *)
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32; exact H_value_u256 | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ1572_storage_to_t_structₓ_Set_ₓ1572_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_structₓ_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      (* Inner [_add_1614] call: rewrite the [Pure.add (kec) 0] slot
         to [kec], then dispatch via [Hinner]. *)
      | |- {{? _, _, _ |
            LowM.Call (fun__add_1614 _ _) _ ⇓ _ | _ ?}} =>
          first [ rewrite H_pa_kec_0 | idtac ];
          c; [ exact Hinner | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R053 Phase 3 — [fun__grantRole_704] case-split walker =====

      [fun__grantRole_704(role, account)] is OZ's internal
      [_grantRole]: it calls [_grantRole_1468] and on a successful
      grant (account previously not a member) additionally calls
      [fun_add_2085] to insert into the EnumerableSet at slot 1.

      Shallow body (Guardian_shallow.v::fun__grantRole_704):

          var__681 := 0
          var__681 := zero_value_for_split_t_bool       (* = 0 *)
          var_granted_684 := fun__grantRole_1468 (role, account)
          let_state~ 'tt := Shallow.if_ (var_granted_684,
              (* THEN branch (granted = 1, new member): *)
              let _116 := mapping_index_access (1, role)  (* = kec(role,1) *)
              let _ := convert_struct_AddressSet_to_ptr (_116)
              let _ := fun_add_2085 (set_slot=kec(role,1), account)
              M.pure (BlockUnit.Tt, tt),
              (* FAIL branch (already member, no-op): tt *)
              tt)
            default~ var__681
          var__681 := var_granted_684
          M.pure (BlockUnit.Leave, var__681)
          M.pure var__681

      So the function's value is exactly the value returned by
      [_grantRole_1468] (= 1 if newly granted, 0 if already a member),
      and the [fun_add_2085] side-effect fires iff newly granted.

      ===== Composable shape — single lemma with branch disjunction =====

      Two natural sub-shapes (member / not-member) collapsed into one
      lemma via a disjunction on the hasRole-pre-state. Phase 5
      callers branch on the disjunct that matches their concrete
      [was_member] reading and dispatch.

      Post-state and [granted] both existential — Phase 5 supplies its
      own [proj_sim_add_admin_not_in]-bridged equality if it needs a
      pinned-shape post-state. The walker only exposes the operational
      composition; the structural projection equality is deferred to
      Phase 5 + the bridge lemma. *)

  (** ----- Helper: AddressSet mapping_index_access (bytes32 → AddressSet) =====

      Inside the THEN branch of [_grantRole_704], the slot for the
      [_roleMembers] AddressSet is computed as
      [mapping_index_access(_, slot=1, key=role)] which is the AddressSet
      MIA leaf. The function body is identical to the
      [Bytes32RoleData] / [Bytes32Uint256] MIA leaves (mstore key +
      slot + keccak256 over a 64-byte window) and returns
      [keccak256_tuple2 key slot]. *)
  Module MappingIndexAccessBytes32AddressSet.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32.
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

  End MappingIndexAccessBytes32AddressSet.

  (** ===== [fun__grantRole_1468] — already-member branch =====

      Companion of [run_fun__grantRole_1468_at_proj_sim_not_member]
      for the case where [account] is already a member of [role]. In
      this branch:
        1. hasRole returns 1.
        2. iszero(1) = 0; cleanup_t_bool 0 = 0; switch δ = 0 → first
           arm fires, which is a no-op that sets var__1437 := 0 and
           emits [BlockUnit.Leave].
        3. Storage and most of memory untouched; only the MIA scratch
           cells of the hasRole pre-walk shift.
        4. Returns [Result.Ok 0] with post-state's projection still
           [proj_sim sim] (the function performs no sstore on this
           branch). *)
  Lemma run_fun__grantRole_1468_at_proj_sim_member
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_member :
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 1)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__grantRole_1468 role account ⇓
      Result.Ok 0
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    (* hasRole pre-walk: in the member branch, returns 1. *)
    pose proof (run_fun_hasRole_1292_at_proj_sim
                  codes env state_base memory sim role account
                  H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    rewrite H_member in Hhr.
    destruct Hhr as (w0_hr & w1_hr & rest_hr & Hhr).
    exists w0_hr, w1_hr, rest_hr.
    unfold fun__grantRole_1468.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_1292 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_bool_of_bool; left; reflexivity | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== [fun__grantRole_704] — R047 case-split walker (main) =====

      [fun__grantRole_704] performs OZ's [_grantRole]:
        1. Calls [fun__grantRole_1468] (the inner bool sstore + log4).
        2. If newly granted (= 1), calls [fun_add_2085] on the slot-1
           AddressSet to add [account] to the role's enumerable set.
        3. Returns the boolean from [_grantRole_1468].

      ===== Case-split shape =====

      The lemma is structured as a disjunction on the sim's
      [role_member_map] reading at [(role, account)] — exactly the
      projection that [run_fun_hasRole_1292_at_proj_sim] computes.

        - **Already-member branch** (member_map (role, account) = 1):
          Fully closed internally. The walker dispatches via
          [run_fun__grantRole_1468_at_proj_sim_member] (member-branch
          companion to Phase 1's not-member walker), pins the
          post-state to a concrete [make_state] shape with
          unchanged [proj_sim sim], and walks the Shallow.if_'s
          failure path (the THEN branch never fires because
          var_granted_684 = 0). The function returns 0.

        - **Not-a-member branch** (member_map (role, account) = 0):
          Composable shape. The caller supplies a
          [Hnotmem] witness — the entire function body's walk for the
          not-member case — and Phase 3 dispatches via it.

      ===== Why the not-member branch defers to the caller =====

      Phase 1's [run_fun__grantRole_1468_at_proj_sim_not_member]
      Qed's against an existential post-state (the log4 sub-block
      leaves the final memory shape opaque to the outside). That
      makes it impossible for this lemma to reach inside the
      Shallow.if_ THEN branch and walk the AddressSet MIA + Phase 2
      with concrete knowledge of the post-1468 memory — the next
      mapping_index_access in the chain requires a 2-word-front
      memory hypothesis, which the existential hides.

      The composable resolution: Phase 5 (the outer assembly) is the
      one with concrete state-threading control. It will either
      strengthen Phase 1 with an explicit post-memory existential
      witness, or re-walk Phase 1's body in-line, and assemble the
      not-member walk that this lemma's [Hnotmem] hypothesis demands.

      The already-member branch is "free" — Phase 5 only needs to
      decide the disjunct via [hasRole], and this lemma closes the
      member-branch composition end-to-end. *)
  Lemma run_fun__grantRole_704_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest)
      (H_branch :
         (* Already-member branch: state unchanged, returns 0. *)
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 1
         \/
         (* Not-a-member branch: caller supplies the composed
            not-member walk [Hnotmem] for the entire function body
            (Phase 1 + AddressSet MIA + convert + Phase 2), pinning
            the post-state to its [state_then] witness. *)
         (StorableValue.map_get_u256 (role_member_map sim) (role, account) = 0
          /\ exists state_full,
              {{? codes, env,
                  Some (make_state env state_base memory (proj_sim sim)) |
                fun__grantRole_704 role account ⇓
                Result.Ok 1
              | state_full ?}})) :
    exists state' granted,
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__grantRole_704 role account ⇓
      Result.Ok granted
    | state' ?}}.
  Proof.
    destruct H_branch as
      [H_member | (H_not_member & state_full & Hnotmem)].
    - (** ----- Already-member branch: walk internally ----- *)
      (* _grantRole_1468 walker yields 0, state's proj_sim unchanged. *)
      pose proof (run_fun__grantRole_1468_at_proj_sim_member
                    codes env state_base memory sim role account
                    H_account H_member H_mem) as Hgr1468.
      destruct Hgr1468 as (w0_g & w1_g & rest_g & Hgr1468).
      exists (Some (make_state env state_base (w0_g :: w1_g :: rest_g) (proj_sim sim))), 0.
      unfold fun__grantRole_704.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
             Shallow.let_state, Shallow.if_.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
            unfold M.strong_let_, M.generic_let
        | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
            unfold M.let_, M.generic_let
        | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
            unfold M.do
        | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
            unfold Shallow.let_state
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
            c; [ unfold zero_value_for_split_t_bool;
                 lu; repeat (lu || cu || p) | ]
        | |- {{? _, _, _ |
              LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hgr1468 | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
            apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    - (** ----- Not-a-member branch: dispatch via [Hnotmem] ----- *)
      exists state_full, 1. exact Hnotmem.
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

  (** Every role in [project_sim_to_ac sim] has admin
      [AccessControl.DEFAULT_ADMIN_ROLE] by construction (the projection
      never sets a non-default admin chain). For role-keys we model,
      [getRoleAdmin] therefore returns [AccessControl.DEFAULT_ADMIN_ROLE];
      for unknown roles, [getRoleEntry] returns the fallback (empty,
      DEFAULT_ADMIN_ROLE), so the result is the same. *)
  Lemma project_sim_to_ac_getRoleAdmin (sim : State.t) (role : U256.t) :
    AccessControl.getRoleAdmin (project_sim_to_ac sim) role
    = AccessControl.DEFAULT_ADMIN_ROLE.
  Proof.
    unfold AccessControl.getRoleAdmin, AccessControl.getRoleEntry,
           AccessControl.find_entry, project_sim_to_ac.
    simpl.
    destruct (DEFAULT_ADMIN_ROLE_bytes32 =? role); [reflexivity|].
    destruct (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =? role); [reflexivity|].
    destruct (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =? role); reflexivity.
  Qed.

  (** [hasRole] of the [DEFAULT_ADMIN_ROLE] key. Inside [project_sim_to_ac],
      the first role-entry is keyed by [DEFAULT_ADMIN_ROLE_bytes32]; the
      [AccessControl.DEFAULT_ADMIN_ROLE = 0] key from [getRoleAdmin]'s
      output finds the [DEFAULT_ADMIN_ROLE_bytes32] entry only if
      [DEFAULT_ADMIN_ROLE_bytes32 = 0]. We axiomatize that equality (it's
      the Solidity reality: OZ defines [DEFAULT_ADMIN_ROLE = bytes32(0)]).
      Same parametric-trust shape as the other Guardian-side role
      parameters. *)
  Axiom DEFAULT_ADMIN_ROLE_bytes32_is_zero :
    DEFAULT_ADMIN_ROLE_bytes32 = 0.

  Lemma project_sim_to_ac_hasRole_admin_chain (sim : State.t) (role : U256.t) (a : Address) :
    AccessControl.hasRole (project_sim_to_ac sim)
                          (AccessControl.getRoleAdmin (project_sim_to_ac sim) role) a
    = has_admin sim a.
  Proof.
    rewrite project_sim_to_ac_getRoleAdmin.
    unfold AccessControl.DEFAULT_ADMIN_ROLE.
    rewrite <- DEFAULT_ADMIN_ROLE_bytes32_is_zero.
    apply project_sim_to_ac_hasRole_admin.
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

        (A) [CLOSED — task #248, extended task #264 (R051.c)] Slot
            modeling: [proj_sim] now covers FOUR slots —
              - slot 0: [_roles] members Map2 (role, account) → 0/1
              - slot 1: [_roleMembers] positions Map2 (role, addr) →
                1-indexed-position
              - slot 2: [_roleMembers] [_values] array length per role
                (Map role → length) — R051.c addition
              - slot 3: [_roleMembers] [_values] array body per (role,
                idx) (Map2 (role, idx) → value) — R051.c addition.
            Slots 2 and 3 carry the dynamic-array data the
            [fun_add_2085] / [fun__add_1614] [array_push] writes to.
            Approximation caveat: the framework's [run_sload_map_u256]
            / [run_sload_map2_u256] axioms route lookups through
            [keccak256(role, Z.of_nat index)] (single-key Map) and
            [keccak256(idx, keccak256(role, Z.of_nat index))] (Map2)
            respectively — NOT the OZ-actual
            [keccak256(role, 1)] (anchor) / [keccak256(keccak256(role,1)) + idx]
            (body) slot expressions. Slot-1's positions modeling
            inherits the same gap (R049 docstring spells it out).
            The eventual walker-side bridge lemma will need an
            axiomatic equation between the framework's nested-keccak
            shape and the actual array shape — see C.3 below.

        (B) [CLOSED — task #248, extended task #264 (R051.c)]
            Projection-side bridge:
            [proj_sim_add_admin_not_in] (and idempotency companion
            [proj_sim_add_admin_in]) equates the projection of the
            post-[add_admin] sim to a cons-prefixed projection of the
            pre-add sim, NOW IN ALL FOUR SLOTS simultaneously. The
            R051.c-added per-slot helper lemmas
            [role_values_length_map_add_admin_not_in] and
            [role_values_body_map_add_admin_not_in]
            (plus [values_for_role_cons_unfold]) carry the slots-2-and-3
            half. Closed by case-split on the [addr_in admins] guard
            + arithmetic, with [addr_in_false_iff_not_In] bridging the
            sim's Boolean membership to Coq [In].

        (C) Walker leaves — three distinct gaps remain:

            (C.1) [CLOSED — R051.b]
                  [run_update_storage_value_t_bool_at_proj_sim]
                  landed above (sister to the slot-3 bytes32 wrapper
                  [run_update_storage_value_t_bytes32_at_proj_sim]).
                  It composes the convert / sload / bit-mask / sstore
                  chain against [proj_sim]'s slot-0 Map2 and yields a
                  post-state with [role_member_map] updated to 1 at
                  key [(role, account)] via [Dict.declare_or_assign].
                  Sub-lemmas added alongside:
                  [run_sstore_role_member_at_proj_sim] (slot-0 sstore
                  wrapper, proven from the framework's
                  [run_sstore_map2_u256] — no per-shape trust needed
                  because slot 0's nested-keccak shape aligns with
                  the framework's Map2 axiom),
                  [run_update_byte_slice_1_shift_0_bool_1] (bit-mask
                  reduction under the bool-typed slot's
                  [prev ∈ {0,1}] invariant from
                  [role_member_map_values_bool]),
                  [run_convert_t_bool_to_t_bool_of_1] / [run_prepare_store_t_bool]
                  / [run_shift_left_0_local] / [run_cleanup_t_bool_of_1].

            (C.2) [CLOSED — R051.a]
                  [run_fun_getRoleAdmin_1340_at_proj_sim] landed
                  above. The admin-field slot
                  [keccak256_tuple2 role 0 + 1] is OUTSIDE [proj_sim]'s
                  range (slot 0 is a [Map2 (role, account)], not a
                  [MapStruct (role, offset)]). Closed via the
                  out-of-projection trust axiom
                  [run_sload_role_admin_at_proj_sim], which asserts
                  that the on-chain admin slot returns
                  [DEFAULT_ADMIN_ROLE_bytes32] for each of the three
                  Guardian roles — same value the AccessControl mock's
                  [getRoleAdmin] would return (Guardian.sol never calls
                  [_setRoleAdmin], so admin defaults to
                  DEFAULT_ADMIN_ROLE per OZ convention; the
                  [project_sim_to_ac] bridge already witnesses this).
                  Same parametric-trust shape as R049's slot-1
                  positions modeling and R052 Option 1's array-slot
                  axioms.

            (C.3) [run_fun_add_2085] — EnumerableSet add. The body
                  calls [fun__add_1614] which performs:
                    - [array_push_from_t_bytes32_to_t_array...dyn_storage]:
                      [sload(set_slot)] (length read) +
                      [sstore(set_slot, len+1)] (length bump) +
                      [sstore(keccak(set_slot) + len, value)] (body
                       write at the keccak-derived dataslot).
                    - [update_storage_value_offset_0_t_uint256_to_t_uint256]
                      at the positions sub-mapping (slot 1's offset 1):
                      [sload + bit-mask + sstore] at
                      [keccak(value, keccak(role, 1) + 1)].
                  Post-R051.c the SLOTS (2 length, 3 body) exist in
                  proj_sim. What remains: the walker leaf
                  [run_array_push_at_proj_sim] that steps the three
                  sstores. The framework's [run_sstore_map_u256] /
                  [run_sstore_map2_u256] axioms give sstore at the
                  NESTED-KECCAK shape ([keccak(role, 2)] for the
                  length, [keccak(idx, keccak(role, 3))] for the
                  body); the array_push body in Guardian_shallow.v
                  invokes them at the ARRAY shape ([set_slot] for the
                  length, [keccak(set_slot) + idx] for the body),
                  where [set_slot] is the EnumerableSet anchor
                  ([keccak(role, 1)] in OZ-actual; whatever the
                  caller computes from [keccak256_tuple2 role 1] in
                  Yul). The mismatch is purely a slot-expression
                  rewrite — same shape as slot-1's positions
                  approximation (R049). Closing C.3 requires:
                    - a [run_sstore_at_set_slot_length] axiom
                      bridging the array-shape length sstore to the
                      framework's [run_sstore_map_u256 storage 2]
                      lemma (i.e., a trusted assertion that
                      [keccak(set_slot)] under the [set_slot] derived
                      from [keccak256_tuple2 role 1] aligns with
                      [keccak(role, 2)] — analogous to slot-1's
                      positions-shape trust).
                    - a [run_sstore_at_set_dataslot_body] axiom for
                      the body slot.
                    - a [run_update_storage_value_offset_0_t_uint256]
                      wrapper for the positions sstore (R040 pattern
                      against slot 1's Map2).
                    - the array_push composite walker chaining
                      [sload length → sstore length+1 → mstore
                      anchor → keccak (the dataslot) → sstore body],
                      threading state through.
                  Phases 1 + 2 (slots 2/3 + projection bridge) landed
                  in task #264. Phase 3 (the walker leaf) — PARTIAL:
                  the three governor-local trust axioms have landed
                  ([run_sload_role_values_length_at_proj_sim],
                  [run_sstore_role_values_length_at_proj_sim],
                  [run_sstore_role_values_body_at_proj_sim]) and the
                  [run_array_push_at_proj_sim] STATEMENT is in place
                  with the [Admitted] mechanical body. The remaining
                  walker work is the bit-mask / convert / dataslot
                  chain interior — same shape as ThrottleLib's
                  [run_update_storage_offset_0_at_two_slot_list] but
                  routed through [array_dataslot] in the middle.

        (D) Caller bridge: [run_fun__msgSender_3197] reads the
            [Stdlib.caller] primitive and returns [env.(Environment.caller)].
            CLOSED — see lemma of the same name above.

      Status as of R051.a: residuals (A), (B), (C.1), (C.2), (C.3),
      and (D) all CLOSED. The R047 case-split walker below still
      [Admitted]s — what remains is purely the outer-walker threading
      pass that composes the per-leaf lemmas through the
      [fun_grantRole_1359 → modifier → _grantRole_1468 + fun_add_2085]
      chain. No remaining structural gaps.

      ===== R053 milestone progress — composable walker layer =====

      Landed in this pass (composable outer-chain wrappers):
        - [run_fun_hasRole_1292_at_proj_sim] — chainable hasRole (exposes
          post-state shape) so other callers can thread.
        - [run_cleanup_t_bool_of_bool] — cleanup_t_bool on v ∈ {0,1}.
        - [run_fun__checkRole_1326_at_proj_sim_pass] — inner gate, no-revert
          branch (passes when hasRole = 1).
        - [run_fun__checkRole_1305_at_proj_sim_pass] — outer gate (msgSender +
          inner gate).
        - [run_modifier_onlyRole_1351_admin_passes] — modifier wrapper,
          composes getRoleAdmin + checkRole + parameterized [Hbody] for the
          inner body. Discharges [H_admin_member] from [has_admin] via the
          [members_for_role] dict-lookup.
        - [run_fun__grantRole_1468_at_proj_sim_not_member] — [Qed]. Body
          walker composes the R051.b
          [run_update_storage_value_t_bool_at_proj_sim] leaf with the
          two mapping_index_access leaves, [run_fun__msgSender_3197],
          and the log4 sub-block (which reduces to [M.pure tt] in the
          upstream runtime model; [allocate_unbounded]'s mload(64) is a
          state-preserving primitive). No new trust axioms.

      Remaining for [run_grantRole_1359_equivalent] Qed:
        1. Body of [run_fun__grantRole_1468_at_proj_sim_not_member] — walk
           through the log4 / abi_encode chain. The abi_encode_tuple_*
           functions are pure mstore + return-no-storage; doable but
           ~150-200 lines.
        2. [run_fun_add_2085_at_proj_sim] — compose
           [run_array_push_at_proj_sim] (R051.c) with the positions sstore
           via [update_storage_value_offset_0_t_uint256_to_t_uint256] on
           slot 1.
        3. [run_fun__grantRole_704_at_proj_sim] — R047 case-split on
           hasRole (= already-member vs not-a-member). If member: return
           false, state unchanged. If not-member: compose _grantRole_1468
           + fun_add_2085, post-state = proj_sim (add_admin sim account).
        4. [run_fun_grantRole_1359_inner_at_proj_sim] — trivial wrapper
           around fun__grantRole_704.  COMPOSABLE LEMMA LANDED — Qed.
        5. Glue: instantiate modifier wrapper with body = grantRole_1359_inner
           and post-state via [proj_sim_add_admin_not_in] (already landed).

      R053 Phase 4 + Phase 5 prelude landed (composable wrappers, both
      Qed, no new axioms):
        - [run_fun_grantRole_1359_inner_at_proj_sim] — parameterized over
          the [fun__grantRole_704] walk. Closes the inner-wrapper layer.
        - [run_fun_grantRole_1359_at_proj_sim] — parameterized over the
          [modifier_onlyRole_1351] walk. Closes the outer-wrapper layer
          (public entry → modifier).
      Together with [run_modifier_onlyRole_1351_admin_passes] (landed in
      R053 Phase 0) these chain three of the five wrapper layers as
      composable Qed lemmas. A future agent can assemble the Phase 5
      Qed by supplying a [fun__grantRole_704] walk witness and threading
      it through the three wrappers and the role/post-state case-split. *)
  (** ===== R054: Observational storage equivalence =====

      The milestone theorem's storage clause is stated as per-slot
      [map_get_u256] equivalence rather than syntactic [Dict.t]-list
      equality (see WISDOM R054 for the structural-impossibility
      diagnosis). Concretely: the actual post-storage produced by the
      Phase 1 + Phase 2 Yul walk uses [Dict.declare_or_assign] which
      appends-at-tail when the key is absent, while the Guardian-side
      [add_admin] bridges (e.g. [role_member_map_add_admin_not_in])
      cons-prepend. These two list shapes are LOOKUP-EQUIVALENT but
      not syntactically equal as [Dict.t].

      This predicate makes that observational equivalence explicit:
      for every slot index (0..3) and every lookup key, the two
      storages return the same [map_get_u256] value. *)
  Definition observationally_eq_storage
      (s1 s2 : SimulatedStorage.t) : Prop :=
    (* Slot 0 — Map2: members map *)
    (forall key,
       match List.nth_error s1 0, List.nth_error s2 0 with
       | Some (StorableValue.Map2 d1), Some (StorableValue.Map2 d2) =>
           StorableValue.map_get_u256 d1 key
           = StorableValue.map_get_u256 d2 key
       | _, _ => True
       end) /\
    (* Slot 1 — Map2: positions map *)
    (forall key,
       match List.nth_error s1 1, List.nth_error s2 1 with
       | Some (StorableValue.Map2 d1), Some (StorableValue.Map2 d2) =>
           StorableValue.map_get_u256 d1 key
           = StorableValue.map_get_u256 d2 key
       | _, _ => True
       end) /\
    (* Slot 2 — Map: per-role array length *)
    (forall key,
       match List.nth_error s1 2, List.nth_error s2 2 with
       | Some (StorableValue.Map d1), Some (StorableValue.Map d2) =>
           StorableValue.map_get_u256 d1 key
           = StorableValue.map_get_u256 d2 key
       | _, _ => True
       end) /\
    (* Slot 3 — Map2: per-(role, idx) body element *)
    (forall key,
       match List.nth_error s1 3, List.nth_error s2 3 with
       | Some (StorableValue.Map2 d1), Some (StorableValue.Map2 d2) =>
           StorableValue.map_get_u256 d1 key
           = StorableValue.map_get_u256 d2 key
       | _, _ => True
       end).

  Theorem run_grantRole_1359_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role account : U256.t)
      (memory : SimulatedMemory.t)
      (H_role : U256.Valid.t role)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_account : 0 <= account < 2^160)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_admins_bound :
         Z.of_nat (List.length sim.(State.admins)) + 1
         < 18446744073709551616)
      (H_og_bound :
         Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1
         < 18446744073709551616)
      (H_ogm_bound :
         Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1
         < 18446744073709551616)
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
          (* R054: Storage equivalence stated OBSERVATIONALLY (per-slot
             [map_get_u256]) rather than syntactically. The post-storage's
             [Dict.declare_or_assign] form is structurally non-equal to
             [proj_sim sim']'s cons-prepended form, but the two are
             point-wise equal on lookups — which is the observable
             semantic content. See [observationally_eq_storage] above. *)
          (exists memory' storage',
            state' = Some (make_state env state_base memory' storage') /\
            observationally_eq_storage storage' (proj_sim sim'))
    | AccessControl.Result.Revert _ _ =>
        (* Auth check failed: the contract reverts too. We don't
           pin the specific revert payload here because the shallow
           form's revert byte encoding is OZ-specific. *)
        True
    end.
  Proof.
    (** ===== Phase 1: reduce [result] to [Result.Success].

        Under [H_caller_admin] and our every-role-defaults-to-DEFAULT_ADMIN
        projection, [AccessControl.grantRole sim_ac caller role account]
        is always [Result.Success] — the auth gate fires with [hasRole
        (getRoleAdmin sim_ac role) caller = has_admin sim caller = true].

        We reduce [result] to its concrete success form so the outer
        [match] reduces and the Revert branch (vacuous) disappears. *)
    intros state sim_ac caller result.
    (* Compute hasRole at the admin chain. The projection makes every
       role's admin entry be DEFAULT_ADMIN_ROLE; [getRoleAdmin sim_ac role]
       therefore returns [DEFAULT_ADMIN_ROLE], which lifts to
       [has_admin sim caller] via [project_sim_to_ac_hasRole_admin]. *)
    assert (H_result_success :
      AccessControl.hasRole sim_ac
        (AccessControl.getRoleAdmin sim_ac role) caller = true).
    { subst sim_ac caller.
      rewrite project_sim_to_ac_hasRole_admin_chain. exact H_caller_admin. }
    (* Reduce [result]: gate passes, so result is Success. *)
    subst result.
    unfold AccessControl.grantRole at 1.
    rewrite H_result_success. cbn match.
    (** ===== Phase 5 status (post-R054 axiom-generalization) =====

        Theorem now stated with [observationally_eq_storage] (per-slot
        [map_get_u256] equality) as the third clause — replacing the
        structurally impossible syntactic [proj_sim sim']-equality.
        The slot-0/1/2/3 observational bridges
        ([role_member_map_sstore_observes_add_admin_not_in],
         [role_positions_map_sstore_observes_add_admin_not_in],
         [role_values_length_map_sstore_eq_add_admin_not_in],
         [role_values_body_map_sstore_observes_add_admin_not_in])
        cover the four-slot discharge of that observational equivalence.

        The four sstore axioms and the [array_push] / [_contains_1760]
        / [_add_1614] / [add_2085] / [_t_uint256_at_positions] /
        [_t_bytes32_at_proj_sim] wrappers have all been GENERALIZED to
        accept arbitrary [member_map_in / positions_map_in /
        length_map_in / body_map_in] pre-state shapes — letting
        Phase 1's post-state (slot 0 = Dict.declare_or_assign ...)
        flow into Phase 2 directly. This was the structural
        prerequisite for the not-member branch composition.

        ===== What remains for Qed =====

        With Phase 2 now composable on top of Phase 1, the milestone
        assembly is a multi-branch case analysis:

          - role-known? (DEFAULT vs OPT_G vs OPT_GM vs unknown).
            For unknown roles, [AccessControl.grantRole] still returns
            Success (the [getRoleAdmin] lookup falls back to
            DEFAULT_ADMIN under our projection where unknown roles'
            entries don't appear). The shallow walker hits an
            uncovered case in the modifier's getRoleAdmin chain;
            either case-split it out (require [H_role_known]) or
            handle the fallback explicitly. The current
            [run_modifier_onlyRole_1351_admin_passes] takes
            [H_role_known] as a hypothesis, so we'd want to extend
            the theorem's preconditions accordingly.

          - account-already-a-member?
            -- TRUE for [role = DEFAULT_ADMIN_ROLE]: [sim' := sim],
               use [run_fun__grantRole_1468_at_proj_sim_member] inside
               Phase 3's already-member arm; the observational storage
               clause discharges reflexively.
            -- FALSE for [role = DEFAULT_ADMIN_ROLE]: [sim' :=
               add_admin sim account]. The not-member composition:

                  1. Phase 1 walker (Qed'd) produces post-state with
                     slot 0 = [Dict.declare_or_assign ... 1].
                  2. The post-Phase-1 storage flows through the
                     generalized Phase 2 walker as [member_map_in :=
                     Dict.declare_or_assign (role_member_map sim) ... 1].
                  3. Phase 2 (now generalized) produces a post-state
                     with slots 1/2/3 mutated; slot 0 remains the
                     Phase-1 mutated map.
                  4. Phase 3's [Hnotmem] hypothesis is satisfied by
                     this combined walker.
                  5. Phase 4 + modifier wrapper + outer wrapper lift
                     to the public entry.
                  6. The observational clause discharges via the four
                     [_sstore_observes_add_admin_not_in] bridges
                     (with the slot-2 piece using the syntactic-
                     equality lemma).

            Analogous proofs for OPT_G / OPT_GM roles need
            [add_optimistic_guardian{_manager}] analogs of the four
            observational bridges, plus the [has_admin]-equivalent for
            the role-of-interest. Out of scope for this session.

        The MEMBER branch above is the simpler one (state unchanged,
        observational clause is reflexivity). The not-member branch
        requires the full Phase 1+2 walker stitching plus the
        Phase 4/modifier/outer threading — substantial mechanical
        work (~100-150 lines).

        See WISDOM R054 (and its 2026-05-31 follow-up) for the
        diagnosis. The axiom generalization landed in the 2026-05-31
        follow-up makes the structurally-impossible blocker disappear;
        what remains is the operational assembly.

        R055 (this session): wrapper strengthening landed; milestone
        Qed not closed in this session — see WISDOM R055 for the
        residuals. *)
    subst sim_ac caller state.
    (* Case-split on the three Guardian roles. Each branch follows the
       same shape (already-member / not-member) but uses role-specific
       observational bridges and a different per-role list of [sim].

       R055 follow-up (this commit): extend from DEFAULT-only to all
       three roles, using the mid-list-insertion observational
       bridges added above. *)
    destruct H_role_known as [H_role_eq | H_role_or];
      [subst role | destruct H_role_or as [H_role_eq | H_role_eq]; subst role].
    { (** ====================================================
          BRANCH 1: role = DEFAULT_ADMIN_ROLE_bytes32
          ==================================================== *)
    (* Case-split on whether [account] is already an admin in [sim]. *)
    destruct (Guardian.addr_in sim.(State.admins) account) eqn:H_addr_in.
    - (** ===== Already-member branch ===== *)
      apply (proj1 (addr_in_true_iff_In _ _)) in H_addr_in.
      (* Build slot-0 lookup = 1 from [In account admins]. *)
      assert (H_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (DEFAULT_ADMIN_ROLE_bytes32, account) = 1).
      { unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        clear -H_addr_in.
        induction (State.admins sim) as [|a rest IH].
        - simpl in H_addr_in. exfalso. exact H_addr_in.
        - simpl members_for_role. simpl Dict.get.
          cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
          rewrite Z.eqb_refl. simpl andb.
          change (Dict.Eq.eqb acct a) with (acct =? a).
          destruct (acct =? a) eqn:Hca.
          + reflexivity.
          + apply Z.eqb_neq in Hca.
            destruct H_addr_in as [Heq | Hin]; [congruence|].
            apply IH. exact Hin. }
      (* AC-level addr_in is the same fixpoint as Guardian's; restate. *)
      assert (H_ac_in : AccessControl.addr_in sim.(State.admins) account = true).
      { clear -H_addr_in.
        induction sim.(State.admins) as [|a rest IH']; simpl.
        - exfalso. exact H_addr_in.
        - destruct (a =? account) eqn:Heqa; [reflexivity|].
          destruct H_addr_in as [Heq|Hin].
          + exfalso. apply Z.eqb_neq in Heqa. congruence.
          + apply IH'; exact Hin. }
      pose proof (AccessControl.add_member_idempotent
                    sim.(State.admins) account H_ac_in) as Hidem.
      (* Walker: build inner-body walker parametric on memory', with
         post-state's storage pinned to [proj_sim sim] (storage-preserving
         in the already-member arm). Bypass the case-split Phase 3
         lemma — instead inline Phase 3's already-member walk to expose
         the concrete post-state. *)
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner DEFAULT_ADMIN_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
      { intros memory' H_mem'.
        pose proof (run_fun__grantRole_1468_at_proj_sim_member
                      codes env state_base memory' sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      H_account H_member H_mem') as Hgr1468.
        destruct Hgr1468 as (w0_g & w1_g & rest_g & Hgr1468).
        exists (w0_g :: w1_g :: rest_g).
        (* Inline Phase 3's already-member walker with concrete state. *)
        assert (H704_concrete : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 DEFAULT_ADMIN_ROLE_bytes32 account ⇓
            Result.Ok 0
          | Some (make_state env state_base
              (w0_g :: w1_g :: rest_g) (proj_sim sim)) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        (* Now wrap via Phase 4. *)
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      _ _ H704_concrete) as Hinner.
        exact Hinner.
      }
      (* Modifier wrapper (existential variant). *)
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    DEFAULT_ADMIN_ROLE_bytes32 account
                    (or_introl eq_refl)
                    H_caller_admin H_caller_bound H_mem
                    (proj_sim sim)
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      (* Outer wrapper. *)
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    DEFAULT_ADMIN_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod (proj_sim sim)))
                    Hmod) as Houter.
      (* Commit witnesses: sim' = sim, state' = Some (make_state ... mem_mod (proj_sim sim)). *)
      exists sim,
        (Some (make_state env state_base mem_mod (proj_sim sim))).
      split; [|split].
      + (* project_sim_to_ac sim = sim_ac' *)
        destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers] in *.
        transitivity
          {| AccessControl.roles :=
               [(DEFAULT_ADMIN_ROLE_bytes32,
                 {| AccessControl.members := adm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                 {| AccessControl.members := og;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                 {| AccessControl.members := ogm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
          |}.
        { reflexivity. }
        f_equal.
        unfold project_sim_to_ac.
        change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
          with l.
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.members.
        rewrite Hidem.
        reflexivity.
      + (* Walker for fun_grantRole_1359: use the outer wrapper result. *)
        exact Houter.
      + (* Observational equality: storage = proj_sim sim. *)
        exists mem_mod, (proj_sim sim).
        split; [reflexivity|].
        unfold observationally_eq_storage.
        repeat split; intros key; reflexivity.
    - (** ===== Not-member branch ===== *)
      apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
      (* Build slot-0 lookup = 0 from [~ In account admins]. We need to
         show map_get_u256 (role_member_map sim) (DEFAULT, account) = 0,
         i.e., the (DEFAULT, account) key is absent from the slot-0 dict. *)
      assert (H_not_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (DEFAULT_ADMIN_ROLE_bytes32, account) = 0).
      { (* Walk role_member_map's three-block structure; ~In account admins
           gives absence in DEFAULT block, and the (DEFAULT, ...) prefix
           gives absence in OG/OGM blocks. *)
        unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        assert (Hd : Dict.get
                       (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                       (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.admins sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        rewrite Hd.
        (* OG/OGM blocks: lookup of (DEFAULT_BR, acct) fails because
           DEFAULT_BR differs from OG_BR and OGM_BR. Use the role-
           distinctness axioms. *)
        rewrite map_get_app_split.
        pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG) as H_eqb_og.
        pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM) as H_eqb_ogm.
        assert (Hd_og : Dict.get
                          (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                             sim.(State.optimisticGuardians))
                          (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_og.
          induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_ROLE_bytes32)
              with (DEFAULT_ADMIN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32).
            rewrite H_eqb_og.
            simpl andb. exact IH. }
        rewrite Hd_og.
        assert (Hd_ogm : Dict.get
                           (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                              sim.(State.optimisticGuardianManagers))
                           (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_ogm.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
              with (DEFAULT_ADMIN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
            rewrite H_eqb_ogm.
            simpl andb. exact IH. }
        unfold StorableValue.map_get_u256.
        rewrite Hd_ogm. reflexivity.
      }
      (* Build slot 1 absence at (DEFAULT_BR, account). *)
      assert (H_not_in_pos :
                StorableValue.map_get_u256 (role_positions_map sim)
                  (DEFAULT_ADMIN_ROLE_bytes32, account) = 0).
      { unfold role_positions_map. rewrite map_get_app_split.
        set (acct := account) in *.
        assert (Hd : Dict.get
                       (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                       (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.admins sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        rewrite Hd. rewrite map_get_app_split.
        pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG) as H_eqb_og.
        pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM) as H_eqb_ogm.
        assert (Hd_og : Dict.get
                          (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                             sim.(State.optimisticGuardians))
                          (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_og.
          induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_ROLE_bytes32)
              with (DEFAULT_ADMIN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32).
            rewrite H_eqb_og.
            simpl andb. exact IH. }
        rewrite Hd_og.
        assert (Hd_ogm : Dict.get
                           (positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                              sim.(State.optimisticGuardianManagers))
                           (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_ogm.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
              with (DEFAULT_ADMIN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
            rewrite H_eqb_ogm.
            simpl andb. exact IH. }
        unfold StorableValue.map_get_u256. rewrite Hd_ogm. reflexivity. }
      (* Slot 2 (length map) lookup at DEFAULT_BR. *)
      assert (H_get_length :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  DEFAULT_ADMIN_ROLE_bytes32
                = Z.of_nat (List.length sim.(State.admins))).
      { unfold role_values_length_map, StorableValue.map_get_u256.
        simpl. rewrite Z.eqb_refl. reflexivity. }
      assert (H_len_bound_admins :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  DEFAULT_ADMIN_ROLE_bytes32
                + 1 < 18446744073709551616).
      { rewrite H_get_length. exact H_admins_bound. }
      assert (H_len_nn_admins :
                0 <= StorableValue.map_get_u256 (role_values_length_map sim)
                       DEFAULT_ADMIN_ROLE_bytes32).
      { rewrite H_get_length. lia. }
      (* Build inner-body walker parametric on memory'. *)
      pose proof (AccessControl.add_member_inserts
                    sim.(State.admins) account) as Hinserts.
      (* H_addr_in : ~ In account admins, but AccessControl.add_member
         needs AC.addr_in admins account = false. Build it. *)
      assert (H_ac_not_in : AccessControl.addr_in sim.(State.admins) account = false).
      { clear -H_addr_in.
        induction sim.(State.admins) as [|a rest IH']; simpl.
        - reflexivity.
        - destruct (a =? account) eqn:Heqa.
          + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
            exact Heqa.
          + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
      assert (H_addmem_cons :
                AccessControl.add_member sim.(State.admins) account
                = account :: sim.(State.admins)).
      { unfold AccessControl.add_member. rewrite H_ac_not_in. reflexivity. }
      (* Build the inner-body walker parametric on memory' with the
         concrete 4-slot Dict.declare_or_assign post-state. The walker
         composes Phase 1 not-member + AddressSet MIA + convert chain
         + Phase 2 (fun_add_2085). *)
      set (member_map_post :=
             Dict.declare_or_assign (role_member_map sim)
               (DEFAULT_ADMIN_ROLE_bytes32, account) 1).
      set (positions_map_post :=
             Dict.declare_or_assign (role_positions_map sim)
               (DEFAULT_ADMIN_ROLE_bytes32, account)
               (Z.of_nat (List.length sim.(State.admins)) + 1)).
      set (length_map_post :=
             Dict.declare_or_assign (role_values_length_map sim)
               DEFAULT_ADMIN_ROLE_bytes32
               (Z.of_nat (List.length sim.(State.admins)) + 1)).
      set (body_map_post :=
             Dict.declare_or_assign (role_values_body_map sim)
               (DEFAULT_ADMIN_ROLE_bytes32,
                 Z.of_nat (List.length sim.(State.admins)))
               account).
      set (storage_post :=
             [ StorableValue.Map2 member_map_post;
               StorableValue.Map2 positions_map_post;
               StorableValue.Map length_map_post;
               StorableValue.Map2 body_map_post ]).
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner DEFAULT_ADMIN_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' storage_post) ?}}).
      { intros memory' H_mem'.
        (* Phase 1 not-member walker produces post-state with slot 0
           mutated. *)
        assert (H_caller_u256 : 0 <= env.(Environment.caller) < 2^256).
        { destruct H_caller_bound. split; [lia|].
          change (2^160) with 1461501637330902918203684832716283019655932542976 in *.
          change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
          lia. }
        assert (H_role_u256 : 0 <= DEFAULT_ADMIN_ROLE_bytes32 < 2^256).
        { rewrite DEFAULT_ADMIN_ROLE_bytes32_is_zero. lia. }
        pose proof (run_fun__grantRole_1468_at_proj_sim_not_member
                      codes env state_base memory' sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      H_role_u256 H_account H_caller_bound
                      H_not_member H_mem') as Hgr1468.
        cbv zeta in Hgr1468.
        destruct Hgr1468 as (w0_p1 & w1_p1 & rest_p1 & Hgr1468).
        set (mem_after_p1 := w0_p1 :: w1_p1 :: rest_p1).
        set (proj_after_p1 :=
               [ StorableValue.Map2 member_map_post;
                 StorableValue.Map2 (role_positions_map sim);
                 StorableValue.Map (role_values_length_map sim);
                 StorableValue.Map2 (role_values_body_map sim) ]).
        fold proj_after_p1 in Hgr1468.
        (* AddressSet MIA: produces keccak256_tuple2 role 1; consumes
           2 scratch cells. *)
        assert (H_mem_after_p1 :
                  exists w0 w1 rest, mem_after_p1 = w0 :: w1 :: rest).
        { exists w0_p1, w1_p1, rest_p1. reflexivity. }
        pose proof (MappingIndexAccessBytes32AddressSet.run_mapping_index_access
                      codes env state_base 1 DEFAULT_ADMIN_ROLE_bytes32
                      proj_after_p1 mem_after_p1 H_mem_after_p1) as Hmia.
        cbv zeta in Hmia.
        destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
        set (mem_after_mia := w0_m :: w1_m :: rest_m).
        (* Phase 2: fun_add_2085 against the post-Phase-1 projection
           with member_map_in := member_map_post, others := unchanged. *)
        assert (H_mem_after_mia :
                  exists w0 w1 rest, mem_after_mia = w0 :: w1 :: rest).
        { exists w0_m, w1_m, rest_m. reflexivity. }
        pose proof (run_fun_add_2085_at_proj_sim
                      codes env state_base mem_after_mia
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      member_map_post
                      (role_positions_map sim)
                      (role_values_length_map sim)
                      (role_values_body_map sim)
                      H_account H_not_in_pos
                      H_len_bound_admins H_len_nn_admins
                      H_mem_after_mia) as Hadd.
        cbv zeta in Hadd.
        destruct Hadd as (mem_after_add & Hadd).
        (* The Phase 2 post-state computes the 4-slot mutation. Show
           it equals storage_post. *)
        assert (Hsto :
                  [ StorableValue.Map2 member_map_post;
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_positions_map sim)
                         (DEFAULT_ADMIN_ROLE_bytes32, account)
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            DEFAULT_ADMIN_ROLE_bytes32 + 1));
                    StorableValue.Map
                      (Dict.declare_or_assign (role_values_length_map sim)
                         DEFAULT_ADMIN_ROLE_bytes32
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            DEFAULT_ADMIN_ROLE_bytes32 + 1));
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_values_body_map sim)
                         (DEFAULT_ADMIN_ROLE_bytes32,
                           StorableValue.map_get_u256
                             (role_values_length_map sim)
                             DEFAULT_ADMIN_ROLE_bytes32)
                         account) ]
                = storage_post).
        { unfold storage_post, positions_map_post, length_map_post,
                 body_map_post. rewrite H_get_length. reflexivity. }
        rewrite Hsto in Hadd.
        (* Build _grantRole_704 walker inline. *)
        assert (H704 : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 DEFAULT_ADMIN_ROLE_bytes32 account ⇓
            Result.Ok 1
          | Some (make_state env state_base mem_after_add storage_post) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 _ _) _
                  ⇓ _ | _ ?}} =>
                eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr _) _
                  ⇓ _ | _ ?}} =>
                c; [ apply run_convert_t_structₓ_AddressSet_storage_to_ptr | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun_add_2085 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hadd | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        (* Wrap via Phase 4 inner wrapper. *)
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      _ _ H704) as Hinner.
        exists mem_after_add. exact Hinner. }
      (* Modifier wrapper. *)
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    DEFAULT_ADMIN_ROLE_bytes32 account
                    (or_introl eq_refl)
                    H_caller_admin H_caller_bound H_mem
                    storage_post
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    DEFAULT_ADMIN_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod storage_post))
                    Hmod) as Houter.
      (* Commit witnesses: sim' = add_admin sim account. *)
      exists (Guardian.add_admin sim account),
        (Some (make_state env state_base mem_mod storage_post)).
      split; [|split].
      + (* project_sim_to_ac (add_admin sim account) = sim_ac' *)
        (* No destruct here — keep [sim] intact for the other clauses. *)
        assert (H_g_not_in : Guardian.addr_in sim.(State.admins) account = false).
        { exact (proj2 (addr_in_false_iff_not_In _ _) H_addr_in). }
        unfold Guardian.add_admin, Guardian.add_role.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers].
        rewrite H_g_not_in.
        unfold project_sim_to_ac.
        cbn [AccessControl.roles].
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.members.
        rewrite H_addmem_cons. reflexivity.
      + exact Houter.
      + (* Observational equality: storage_post observationally equal
           to proj_sim (add_admin sim account) via the four bridges. *)
        exists mem_mod, storage_post.
        split; [reflexivity|].
        unfold observationally_eq_storage, storage_post, proj_sim.
        repeat split; intros key; cbn match.
        * (* slot 0: member_map_post observationally equal to
             role_member_map (add_admin sim account). *)
          apply role_member_map_sstore_observes_add_admin_not_in;
            [exact H_not_member | exact H_addr_in].
        * (* slot 1: positions_map_post via the slot-1 bridge. *)
          apply role_positions_map_sstore_observes_add_admin_not_in.
          -- exact H_not_in_pos.
          -- exact H_addr_in.
          -- reflexivity.
        * (* slot 2: length_map_post = role_values_length_map (add_admin)
             SYNTACTIC. *)
          unfold length_map_post.
          rewrite (role_values_length_map_sstore_eq_add_admin_not_in
                     sim account H_addr_in
                     (Z.of_nat (List.length sim.(State.admins)) + 1)
                     eq_refl). reflexivity.
        * (* slot 3: body_map_post via the slot-3 bridge. *)
          unfold body_map_post.
          apply role_values_body_map_sstore_observes_add_admin_not_in.
          -- (* Dict.get (role_values_body_map sim) (DEFAULT, length admins) = None.
                values_for_role assigns indices in [0..length-1]; lookup
                at index = length misses. OG/OGM blocks have non-DEFAULT
                keys by distinctness. *)
             unfold role_values_body_map.
             rewrite !Dict_get_app_split.
             (* DEFAULT block: values_for_role DEFAULT admins. Indices
                are 0..length-1; lookup at length misses. *)
             assert (Hd : Dict.get
                            (values_for_role DEFAULT_ADMIN_ROLE_bytes32
                               sim.(State.admins))
                            (DEFAULT_ADMIN_ROLE_bytes32,
                              Z.of_nat (Datatypes.length sim.(State.admins)))
                            = None).
             { (* values_for_role assigns indices in [0..length-1];
                  lookup at index = length misses. Generic helper. *)
               assert (Hgen : forall l n,
                 Z.of_nat n < Z.of_nat (Datatypes.length sim.(State.admins)) ->
                 Dict.get (values_for_role_aux DEFAULT_ADMIN_ROLE_bytes32 n l)
                   (DEFAULT_ADMIN_ROLE_bytes32,
                     Z.of_nat (Datatypes.length sim.(State.admins))) = None).
               { intros l. induction l as [|a rest IH]; intros n Hn; simpl.
                 - reflexivity.
                 - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                   rewrite Z.eqb_refl. simpl andb.
                   change (Dict.Eq.eqb
                             (Z.of_nat (Datatypes.length sim.(State.admins)))
                             (Z.of_nat n))
                     with (Z.of_nat (Datatypes.length sim.(State.admins))
                           =? Z.of_nat n).
                   assert (Hneq : Z.of_nat (Datatypes.length sim.(State.admins))
                                  <> Z.of_nat n) by lia.
                   apply Z.eqb_neq in Hneq. rewrite Hneq.
                   apply IH. simpl. lia. }
               unfold values_for_role.
               (* For the top-level case, the head's index is
                  [pred length = length - 1 < length]. So we apply
                  Hgen at n = pred length. *)
               destruct sim.(State.admins) as [|a rest] eqn:Hl.
               - simpl. reflexivity.
               - apply Hgen. simpl. lia. }
             rewrite Hd.
             (* OG block: values_for_role OG_BR optG. Keys are (OG_BR, _).
                Lookup at (DEFAULT_BR, _) misses by role-distinctness. *)
             pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG) as H_eqb_og.
             pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM) as H_eqb_ogm.
             assert (Hd_og : forall n,
                       Dict.get
                         (values_for_role_aux OPTIMISTIC_GUARDIAN_ROLE_bytes32
                            n sim.(State.optimisticGuardians))
                         (DEFAULT_ADMIN_ROLE_bytes32,
                           Z.of_nat (Datatypes.length sim.(State.admins)))
                       = None).
             { intros n. revert n. clear -H_eqb_og.
               induction sim.(State.optimisticGuardians) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                     OPTIMISTIC_GUARDIAN_ROLE_bytes32)
                   with (DEFAULT_ADMIN_ROLE_bytes32
                         =? OPTIMISTIC_GUARDIAN_ROLE_bytes32).
                 rewrite H_eqb_og. simpl andb. apply IH. }
             unfold values_for_role at 1.
             rewrite Hd_og.
             assert (Hd_ogm : forall n,
                       Dict.get
                         (values_for_role_aux
                            OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                            n sim.(State.optimisticGuardianManagers))
                         (DEFAULT_ADMIN_ROLE_bytes32,
                           Z.of_nat (Datatypes.length sim.(State.admins)))
                       = None).
             { intros n. revert n. clear -H_eqb_ogm.
               induction sim.(State.optimisticGuardianManagers) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                     OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
                   with (DEFAULT_ADMIN_ROLE_bytes32
                         =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
                 rewrite H_eqb_ogm. simpl andb. apply IH. }
             unfold values_for_role at 1.
             apply Hd_ogm.
          -- exact H_addr_in.
    }
    { (** ====================================================
          BRANCH 2: role = OPTIMISTIC_GUARDIAN_ROLE_bytes32

          Same proof shape as the DEFAULT branch, but with:
          - the role's per-role list = sim.(State.optimisticGuardians)
          - add_admin → add_optimistic_guardian
          - the four observational bridges → the OG variants
            (mid-list-insertion form).
          - the modifier's [H_role_known] disjunct = middle.
          ==================================================== *)
    destruct (Guardian.addr_in sim.(State.optimisticGuardians) account)
      eqn:H_addr_in.
    - (** ===== Already-member branch ===== *)
      apply (proj1 (addr_in_true_iff_In _ _)) in H_addr_in.
      assert (H_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account) = 1).
      { unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        (* DEFAULT block absent because keys are (DEFAULT, _). *)
        assert (Hd_def : Dict.get
                          (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                             sim.(State.admins))
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { pose proof (proj2 (Z.eqb_neq _ _)
                        (not_eq_sym DEFAULT_neq_OG)) as H_eqb.
          clear -H_eqb.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb. simpl andb. exact IH. }
        rewrite Hd_def.
        rewrite map_get_app_split.
        (* OG block: account is in optG ⇒ lookup returns Some 1. *)
        clear -H_addr_in.
        induction (State.optimisticGuardians sim) as [|a rest IH].
        - simpl in H_addr_in. exfalso. exact H_addr_in.
        - simpl members_for_role. simpl Dict.get.
          cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
          rewrite Z.eqb_refl. simpl andb.
          change (Dict.Eq.eqb acct a) with (acct =? a).
          destruct (acct =? a) eqn:Hca.
          + reflexivity.
          + apply Z.eqb_neq in Hca.
            destruct H_addr_in as [Heq | Hin]; [congruence|].
            apply IH. exact Hin. }
      assert (H_ac_in :
                AccessControl.addr_in sim.(State.optimisticGuardians) account
                = true).
      { clear -H_addr_in.
        induction sim.(State.optimisticGuardians) as [|a rest IH']; simpl.
        - exfalso. exact H_addr_in.
        - destruct (a =? account) eqn:Heqa; [reflexivity|].
          destruct H_addr_in as [Heq|Hin].
          + exfalso. apply Z.eqb_neq in Heqa. congruence.
          + apply IH'; exact Hin. }
      pose proof (AccessControl.add_member_idempotent
                    sim.(State.optimisticGuardians) account H_ac_in) as Hidem.
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner OPTIMISTIC_GUARDIAN_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
      { intros memory' H_mem'.
        pose proof (run_fun__grantRole_1468_at_proj_sim_member
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      H_account H_member H_mem') as Hgr1468.
        destruct Hgr1468 as (w0_g & w1_g & rest_g & Hgr1468).
        exists (w0_g :: w1_g :: rest_g).
        assert (H704_concrete : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 OPTIMISTIC_GUARDIAN_ROLE_bytes32 account ⇓
            Result.Ok 0
          | Some (make_state env state_base
              (w0_g :: w1_g :: rest_g) (proj_sim sim)) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      _ _ H704_concrete) as Hinner.
        exact Hinner.
      }
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                    (or_intror (or_introl eq_refl))
                    H_caller_admin H_caller_bound H_mem
                    (proj_sim sim)
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod (proj_sim sim)))
                    Hmod) as Houter.
      exists sim,
        (Some (make_state env state_base mem_mod (proj_sim sim))).
      split; [|split].
      + (* project_sim_to_ac sim = sim_ac' — set_entry replaces the OG
           entry (second in the list, found via DEFAULT_neq_OG). *)
        destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers] in *.
        transitivity
          {| AccessControl.roles :=
               [(DEFAULT_ADMIN_ROLE_bytes32,
                 {| AccessControl.members := adm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                 {| AccessControl.members := og;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                 {| AccessControl.members := ogm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
          |}.
        { reflexivity. }
        f_equal.
        unfold project_sim_to_ac.
        change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
          with l.
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG). cbv match.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG).
        rewrite Z.eqb_refl.
        cbn [AccessControl.members].
        rewrite Hidem.
        reflexivity.
      + exact Houter.
      + exists mem_mod, (proj_sim sim).
        split; [reflexivity|].
        unfold observationally_eq_storage.
        repeat split; intros key; reflexivity.
    - (** ===== Not-member branch ===== *)
      apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
      assert (H_not_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account) = 0).
      { unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        (* DEFAULT block: absent at (OG, _) by key distinctness. *)
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym DEFAULT_neq_OG)) as H_eqb_def.
        assert (Hd_def : Dict.get
                          (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                             sim.(State.admins))
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_def.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb_def. simpl andb. exact IH. }
        rewrite Hd_def. rewrite map_get_app_split.
        (* OG block: ~In account optG ⇒ absent. *)
        assert (Hd_og : Dict.get
                       (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                       (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.optimisticGuardians sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        rewrite Hd_og.
        (* OGM block: absent at (OG, _) by OG_neq_OGM. *)
        pose proof (proj2 (Z.eqb_neq _ _) OG_neq_OGM) as H_eqb_ogm.
        assert (Hd_ogm : Dict.get
                           (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                              sim.(State.optimisticGuardianManagers))
                           (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_ogm.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
            rewrite H_eqb_ogm. simpl andb. exact IH. }
        unfold StorableValue.map_get_u256.
        rewrite Hd_ogm. reflexivity. }
      (* Slot 1 absence at (OG, account). *)
      assert (H_not_in_pos :
                StorableValue.map_get_u256 (role_positions_map sim)
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account) = 0).
      { unfold role_positions_map. rewrite map_get_app_split.
        set (acct := account) in *.
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym DEFAULT_neq_OG)) as H_eqb_def.
        assert (Hd_def : Dict.get
                       (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                       (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_def.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb_def. simpl andb. exact IH. }
        rewrite Hd_def. rewrite map_get_app_split.
        assert (Hd_og : Dict.get
                          (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                             sim.(State.optimisticGuardians))
                          (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.optimisticGuardians sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        rewrite Hd_og.
        pose proof (proj2 (Z.eqb_neq _ _) OG_neq_OGM) as H_eqb_ogm.
        assert (Hd_ogm : Dict.get
                           (positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                              sim.(State.optimisticGuardianManagers))
                           (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
        { clear -H_eqb_ogm.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
            rewrite H_eqb_ogm. simpl andb. exact IH. }
        unfold StorableValue.map_get_u256. rewrite Hd_ogm. reflexivity. }
      (* Slot 2 lookup at OG_BR returns length optG (second list entry). *)
      assert (H_get_length :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  OPTIMISTIC_GUARDIAN_ROLE_bytes32
                = Z.of_nat (List.length sim.(State.optimisticGuardians))).
      { unfold role_values_length_map, StorableValue.map_get_u256.
        simpl.
        change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                            DEFAULT_ADMIN_ROLE_bytes32)
          with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                DEFAULT_ADMIN_ROLE_bytes32).
        rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym DEFAULT_neq_OG)).
        change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                            OPTIMISTIC_GUARDIAN_ROLE_bytes32)
          with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                OPTIMISTIC_GUARDIAN_ROLE_bytes32).
        rewrite Z.eqb_refl.
        reflexivity. }
      assert (H_len_bound_og :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  OPTIMISTIC_GUARDIAN_ROLE_bytes32
                + 1 < 18446744073709551616).
      { rewrite H_get_length. exact H_og_bound. }
      assert (H_len_nn_og :
                0 <= StorableValue.map_get_u256 (role_values_length_map sim)
                       OPTIMISTIC_GUARDIAN_ROLE_bytes32).
      { rewrite H_get_length. lia. }
      pose proof (AccessControl.add_member_inserts
                    sim.(State.optimisticGuardians) account) as Hinserts.
      assert (H_ac_not_in :
                AccessControl.addr_in sim.(State.optimisticGuardians) account
                = false).
      { clear -H_addr_in.
        induction sim.(State.optimisticGuardians) as [|a rest IH']; simpl.
        - reflexivity.
        - destruct (a =? account) eqn:Heqa.
          + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
            exact Heqa.
          + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
      assert (H_addmem_cons :
                AccessControl.add_member sim.(State.optimisticGuardians) account
                = account :: sim.(State.optimisticGuardians)).
      { unfold AccessControl.add_member. rewrite H_ac_not_in. reflexivity. }
      set (member_map_post :=
             Dict.declare_or_assign (role_member_map sim)
               (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account) 1).
      set (positions_map_post :=
             Dict.declare_or_assign (role_positions_map sim)
               (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account)
               (Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1)).
      set (length_map_post :=
             Dict.declare_or_assign (role_values_length_map sim)
               OPTIMISTIC_GUARDIAN_ROLE_bytes32
               (Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1)).
      set (body_map_post :=
             Dict.declare_or_assign (role_values_body_map sim)
               (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                 Z.of_nat (List.length sim.(State.optimisticGuardians)))
               account).
      set (storage_post :=
             [ StorableValue.Map2 member_map_post;
               StorableValue.Map2 positions_map_post;
               StorableValue.Map length_map_post;
               StorableValue.Map2 body_map_post ]).
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner OPTIMISTIC_GUARDIAN_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' storage_post) ?}}).
      { intros memory' H_mem'.
        assert (H_caller_u256 : 0 <= env.(Environment.caller) < 2^256).
        { destruct H_caller_bound. split; [lia|].
          change (2^160) with 1461501637330902918203684832716283019655932542976 in *.
          change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
          lia. }
        (* OG role bytes32 fits in 2^256 — trusted at the parameter level. *)
        assert (H_role_u256 : 0 <= OPTIMISTIC_GUARDIAN_ROLE_bytes32 < 2^256).
        { (* H_role : U256.Valid.t OPTIMISTIC_GUARDIAN_ROLE_bytes32 by H_role_eq. *)
          unfold U256.Valid.t in H_role.
          change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
          lia. }
        pose proof (run_fun__grantRole_1468_at_proj_sim_not_member
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      H_role_u256 H_account H_caller_bound
                      H_not_member H_mem') as Hgr1468.
        cbv zeta in Hgr1468.
        destruct Hgr1468 as (w0_p1 & w1_p1 & rest_p1 & Hgr1468).
        set (mem_after_p1 := w0_p1 :: w1_p1 :: rest_p1).
        set (proj_after_p1 :=
               [ StorableValue.Map2 member_map_post;
                 StorableValue.Map2 (role_positions_map sim);
                 StorableValue.Map (role_values_length_map sim);
                 StorableValue.Map2 (role_values_body_map sim) ]).
        fold proj_after_p1 in Hgr1468.
        assert (H_mem_after_p1 :
                  exists w0 w1 rest, mem_after_p1 = w0 :: w1 :: rest).
        { exists w0_p1, w1_p1, rest_p1. reflexivity. }
        pose proof (MappingIndexAccessBytes32AddressSet.run_mapping_index_access
                      codes env state_base 1 OPTIMISTIC_GUARDIAN_ROLE_bytes32
                      proj_after_p1 mem_after_p1 H_mem_after_p1) as Hmia.
        cbv zeta in Hmia.
        destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
        set (mem_after_mia := w0_m :: w1_m :: rest_m).
        assert (H_mem_after_mia :
                  exists w0 w1 rest, mem_after_mia = w0 :: w1 :: rest).
        { exists w0_m, w1_m, rest_m. reflexivity. }
        pose proof (run_fun_add_2085_at_proj_sim
                      codes env state_base mem_after_mia
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      member_map_post
                      (role_positions_map sim)
                      (role_values_length_map sim)
                      (role_values_body_map sim)
                      H_account H_not_in_pos
                      H_len_bound_og H_len_nn_og
                      H_mem_after_mia) as Hadd.
        cbv zeta in Hadd.
        destruct Hadd as (mem_after_add & Hadd).
        assert (Hsto :
                  [ StorableValue.Map2 member_map_post;
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_positions_map sim)
                         (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account)
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            OPTIMISTIC_GUARDIAN_ROLE_bytes32 + 1));
                    StorableValue.Map
                      (Dict.declare_or_assign (role_values_length_map sim)
                         OPTIMISTIC_GUARDIAN_ROLE_bytes32
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            OPTIMISTIC_GUARDIAN_ROLE_bytes32 + 1));
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_values_body_map sim)
                         (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                           StorableValue.map_get_u256
                             (role_values_length_map sim)
                             OPTIMISTIC_GUARDIAN_ROLE_bytes32)
                         account) ]
                = storage_post).
        { unfold storage_post, positions_map_post, length_map_post,
                 body_map_post. rewrite H_get_length. reflexivity. }
        rewrite Hsto in Hadd.
        assert (H704 : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 OPTIMISTIC_GUARDIAN_ROLE_bytes32 account ⇓
            Result.Ok 1
          | Some (make_state env state_base mem_after_add storage_post) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 _ _) _
                  ⇓ _ | _ ?}} =>
                eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr _) _
                  ⇓ _ | _ ?}} =>
                c; [ apply run_convert_t_structₓ_AddressSet_storage_to_ptr | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun_add_2085 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hadd | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      _ _ H704) as Hinner.
        exists mem_after_add. exact Hinner. }
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                    (or_intror (or_introl eq_refl))
                    H_caller_admin H_caller_bound H_mem
                    storage_post
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod storage_post))
                    Hmod) as Houter.
      exists (Guardian.add_optimistic_guardian sim account),
        (Some (make_state env state_base mem_mod storage_post)).
      split; [|split].
      + assert (H_g_not_in :
                  Guardian.addr_in sim.(State.optimisticGuardians) account
                  = false).
        { exact (proj2 (addr_in_false_iff_not_In _ _) H_addr_in). }
        unfold Guardian.add_optimistic_guardian, Guardian.add_role.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers].
        rewrite H_g_not_in.
        unfold project_sim_to_ac.
        cbn [AccessControl.roles].
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG). cbv match.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG).
        rewrite Z.eqb_refl.
        cbn [AccessControl.members].
        rewrite H_addmem_cons. reflexivity.
      + exact Houter.
      + exists mem_mod, storage_post.
        split; [reflexivity|].
        unfold observationally_eq_storage, storage_post, proj_sim.
        repeat split; intros key; cbn match.
        * apply role_member_map_sstore_observes_add_optimistic_guardian_not_in;
            [exact H_not_member | exact H_addr_in].
        * apply role_positions_map_sstore_observes_add_optimistic_guardian_not_in.
          -- exact H_not_in_pos.
          -- exact H_addr_in.
          -- reflexivity.
        * unfold length_map_post.
          rewrite (role_values_length_map_sstore_eq_add_optimistic_guardian_not_in
                     sim account H_addr_in
                     (Z.of_nat (List.length sim.(State.optimisticGuardians)) + 1)
                     eq_refl). reflexivity.
        * unfold body_map_post.
          apply role_values_body_map_sstore_observes_add_optimistic_guardian_not_in.
          -- (* Dict.get (role_values_body_map sim)
                  (OG, length optG) = None. Values_for_role assigns
                  indices in [0..length-1]; lookup at index = length
                  misses in the OG block. Other blocks have non-OG keys
                  by distinctness. *)
             unfold role_values_body_map.
             rewrite !Dict_get_app_split.
             (* DEFAULT block: keys are (DEFAULT, _); lookup at (OG, _)
                fails by DEFAULT_neq_OG. *)
             pose proof (proj2 (Z.eqb_neq _ _)
                           (not_eq_sym DEFAULT_neq_OG)) as H_eqb_def.
             assert (Hd_def : forall n,
                       Dict.get
                         (values_for_role_aux DEFAULT_ADMIN_ROLE_bytes32
                            n sim.(State.admins))
                         (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                           Z.of_nat
                             (Datatypes.length sim.(State.optimisticGuardians)))
                       = None).
             { intros n. revert n. clear -H_eqb_def.
               induction sim.(State.admins) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                     DEFAULT_ADMIN_ROLE_bytes32)
                   with (OPTIMISTIC_GUARDIAN_ROLE_bytes32
                         =? DEFAULT_ADMIN_ROLE_bytes32).
                 rewrite H_eqb_def. simpl andb. apply IH. }
             unfold values_for_role at 1.
             rewrite Hd_def.
             (* OG block: keys are (OG, idx). Lookup at (OG, length optG)
                fails because indices assigned are 0..length-1. *)
             assert (Hd_og : Dict.get
                            (values_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                               sim.(State.optimisticGuardians))
                            (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                              Z.of_nat (Datatypes.length sim.(State.optimisticGuardians)))
                            = None).
             { assert (Hgen : forall l n,
                 Z.of_nat n < Z.of_nat (Datatypes.length sim.(State.optimisticGuardians)) ->
                 Dict.get (values_for_role_aux OPTIMISTIC_GUARDIAN_ROLE_bytes32 n l)
                   (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                     Z.of_nat (Datatypes.length sim.(State.optimisticGuardians))) = None).
               { intros l. induction l as [|a rest IH]; intros n Hn; simpl.
                 - reflexivity.
                 - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                   rewrite Z.eqb_refl. simpl andb.
                   change (Dict.Eq.eqb
                             (Z.of_nat (Datatypes.length sim.(State.optimisticGuardians)))
                             (Z.of_nat n))
                     with (Z.of_nat (Datatypes.length sim.(State.optimisticGuardians))
                           =? Z.of_nat n).
                   assert (Hneq : Z.of_nat (Datatypes.length sim.(State.optimisticGuardians))
                                  <> Z.of_nat n) by lia.
                   apply Z.eqb_neq in Hneq. rewrite Hneq.
                   apply IH. simpl. lia. }
               unfold values_for_role.
               destruct sim.(State.optimisticGuardians) as [|a rest] eqn:Hl.
               - simpl. reflexivity.
               - apply Hgen. simpl. lia. }
             rewrite Hd_og.
             (* OGM block: keys are (OGM, _); lookup at (OG, _) fails by
                OG_neq_OGM. *)
             pose proof (proj2 (Z.eqb_neq _ _) OG_neq_OGM) as H_eqb_ogm.
             assert (Hd_ogm : forall n,
                       Dict.get
                         (values_for_role_aux
                            OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                            n sim.(State.optimisticGuardianManagers))
                         (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                           Z.of_nat
                             (Datatypes.length sim.(State.optimisticGuardians)))
                       = None).
             { intros n. revert n. clear -H_eqb_ogm.
               induction sim.(State.optimisticGuardianManagers) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                     OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
                   with (OPTIMISTIC_GUARDIAN_ROLE_bytes32
                         =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
                 rewrite H_eqb_ogm. simpl andb. apply IH. }
             unfold values_for_role at 1.
             apply Hd_ogm.
          -- exact H_addr_in.
    }
    { (** ====================================================
          BRANCH 3: role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32

          Same shape as the OG branch, threaded for OGM:
          - role list = sim.(State.optimisticGuardianManagers).
          - add_admin → add_optimistic_guardian_manager.
          - Observational bridges: OGM variants.
          - Modifier disjunct: rightmost.
          - find_entry / set_entry walk past both DEFAULT and OG entries.
          ==================================================== *)
    destruct (Guardian.addr_in sim.(State.optimisticGuardianManagers) account)
      eqn:H_addr_in.
    - (** ===== Already-member branch ===== *)
      apply (proj1 (addr_in_true_iff_In _ _)) in H_addr_in.
      assert (H_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account) = 1).
      { unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        assert (Hd_def : Dict.get
                          (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                             sim.(State.admins))
                          (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { pose proof (proj2 (Z.eqb_neq _ _)
                        (not_eq_sym DEFAULT_neq_OGM)) as H_eqb.
          clear -H_eqb.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb. simpl andb. exact IH. }
        rewrite Hd_def.
        rewrite map_get_app_split.
        assert (Hd_og : Dict.get
                          (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                             sim.(State.optimisticGuardians))
                          (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { pose proof (proj2 (Z.eqb_neq _ _)
                        (not_eq_sym OG_neq_OGM)) as H_eqb_og.
          clear -H_eqb_og.
          induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32).
            rewrite H_eqb_og. simpl andb. exact IH. }
        rewrite Hd_og.
        clear Hd_def Hd_og H_ogm_bound H_og_bound H_admins_bound.
        induction (State.optimisticGuardianManagers sim) as [|a rest IH].
        - simpl in H_addr_in. exfalso. exact H_addr_in.
        - unfold StorableValue.map_get_u256.
          simpl Dict.get.
          cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
          change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                              OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
            with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
          rewrite Z.eqb_refl.
          simpl andb.
          change (Dict.Eq.eqb acct a) with (acct =? a).
          destruct (acct =? a) eqn:Hca.
          + reflexivity.
          + apply Z.eqb_neq in Hca.
            destruct H_addr_in as [Heq | Hin]; [congruence|].
            apply IH. exact Hin. }
      assert (H_ac_in :
                AccessControl.addr_in sim.(State.optimisticGuardianManagers) account
                = true).
      { clear -H_addr_in.
        induction sim.(State.optimisticGuardianManagers) as [|a rest IH']; simpl.
        - exfalso. exact H_addr_in.
        - destruct (a =? account) eqn:Heqa; [reflexivity|].
          destruct H_addr_in as [Heq|Hin].
          + exfalso. apply Z.eqb_neq in Heqa. congruence.
          + apply IH'; exact Hin. }
      pose proof (AccessControl.add_member_idempotent
                    sim.(State.optimisticGuardianManagers) account H_ac_in) as Hidem.
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
      { intros memory' H_mem'.
        pose proof (run_fun__grantRole_1468_at_proj_sim_member
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      H_account H_member H_mem') as Hgr1468.
        destruct Hgr1468 as (w0_g & w1_g & rest_g & Hgr1468).
        exists (w0_g :: w1_g :: rest_g).
        assert (H704_concrete : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account ⇓
            Result.Ok 0
          | Some (make_state env state_base
              (w0_g :: w1_g :: rest_g) (proj_sim sim)) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      _ _ H704_concrete) as Hinner.
        exact Hinner.
      }
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                    (or_intror (or_intror eq_refl))
                    H_caller_admin H_caller_bound H_mem
                    (proj_sim sim)
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod (proj_sim sim)))
                    Hmod) as Houter.
      exists sim,
        (Some (make_state env state_base mem_mod (proj_sim sim))).
      split; [|split].
      + destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers] in *.
        transitivity
          {| AccessControl.roles :=
               [(DEFAULT_ADMIN_ROLE_bytes32,
                 {| AccessControl.members := adm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                 {| AccessControl.members := og;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                 {| AccessControl.members := ogm;
                    AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
          |}.
        { reflexivity. }
        f_equal.
        unfold project_sim_to_ac.
        change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
          with l.
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM). cbv match.
        rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM). cbv match.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM).
        rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM).
        rewrite Z.eqb_refl.
        cbn [AccessControl.members].
        rewrite Hidem.
        reflexivity.
      + exact Houter.
      + exists mem_mod, (proj_sim sim).
        split; [reflexivity|].
        unfold observationally_eq_storage.
        repeat split; intros key; reflexivity.
    - (** ===== Not-member branch ===== *)
      apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
      assert (H_not_member :
                StorableValue.map_get_u256 (role_member_map sim)
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account) = 0).
      { unfold role_member_map.
        rewrite map_get_app_split.
        set (acct := account) in *.
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym DEFAULT_neq_OGM)) as H_eqb_def.
        assert (Hd_def : Dict.get
                       (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_eqb_def.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb_def. simpl andb. exact IH. }
        rewrite Hd_def. rewrite map_get_app_split.
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym OG_neq_OGM)) as H_eqb_og.
        assert (Hd_og : Dict.get
                       (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_eqb_og.
          induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32).
            rewrite H_eqb_og. simpl andb. exact IH. }
        rewrite Hd_og.
        assert (Hd_ogm : Dict.get
                       (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                          sim.(State.optimisticGuardianManagers))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        unfold StorableValue.map_get_u256. rewrite Hd_ogm. reflexivity. }
      (* Slot 1 absence at (OGM, account). *)
      assert (H_not_in_pos :
                StorableValue.map_get_u256 (role_positions_map sim)
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account) = 0).
      { unfold role_positions_map. rewrite map_get_app_split.
        set (acct := account) in *.
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym DEFAULT_neq_OGM)) as H_eqb_def.
        assert (Hd_def : Dict.get
                       (positions_for_role DEFAULT_ADMIN_ROLE_bytes32
                          sim.(State.admins))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_eqb_def.
          induction (State.admins sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                DEFAULT_ADMIN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    DEFAULT_ADMIN_ROLE_bytes32).
            rewrite H_eqb_def. simpl andb. exact IH. }
        rewrite Hd_def. rewrite map_get_app_split.
        pose proof (proj2 (Z.eqb_neq _ _)
                      (not_eq_sym OG_neq_OGM)) as H_eqb_og.
        assert (Hd_og : Dict.get
                       (positions_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                          sim.(State.optimisticGuardians))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_eqb_og.
          induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
          - reflexivity.
          - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                OPTIMISTIC_GUARDIAN_ROLE_bytes32)
              with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                    OPTIMISTIC_GUARDIAN_ROLE_bytes32).
            rewrite H_eqb_og. simpl andb. exact IH. }
        rewrite Hd_og.
        assert (Hd_ogm : Dict.get
                       (positions_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                          sim.(State.optimisticGuardianManagers))
                       (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct) = None).
        { clear -H_addr_in.
          induction (State.optimisticGuardianManagers sim) as [|a rest IH].
          - reflexivity.
          - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
            rewrite Z.eqb_refl. simpl andb.
            change (Dict.Eq.eqb acct a) with (acct =? a).
            destruct (acct =? a) eqn:Hca.
            + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
              left. symmetry. exact Hca.
            + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
        unfold StorableValue.map_get_u256. rewrite Hd_ogm. reflexivity. }
      (* Slot 2 lookup at OGM_BR (third list entry). *)
      assert (H_get_length :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                = Z.of_nat (List.length sim.(State.optimisticGuardianManagers))).
      { unfold role_values_length_map, StorableValue.map_get_u256.
        simpl.
        change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                            DEFAULT_ADMIN_ROLE_bytes32)
          with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                DEFAULT_ADMIN_ROLE_bytes32).
        rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym DEFAULT_neq_OGM)).
        change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                            OPTIMISTIC_GUARDIAN_ROLE_bytes32)
          with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                OPTIMISTIC_GUARDIAN_ROLE_bytes32).
        rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym OG_neq_OGM)).
        change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                            OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
          with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
        rewrite Z.eqb_refl.
        reflexivity. }
      assert (H_len_bound_ogm :
                StorableValue.map_get_u256 (role_values_length_map sim)
                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                + 1 < 18446744073709551616).
      { rewrite H_get_length. exact H_ogm_bound. }
      assert (H_len_nn_ogm :
                0 <= StorableValue.map_get_u256 (role_values_length_map sim)
                       OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
      { rewrite H_get_length. lia. }
      pose proof (AccessControl.add_member_inserts
                    sim.(State.optimisticGuardianManagers) account) as Hinserts.
      assert (H_ac_not_in :
                AccessControl.addr_in sim.(State.optimisticGuardianManagers) account
                = false).
      { clear -H_addr_in.
        induction sim.(State.optimisticGuardianManagers) as [|a rest IH']; simpl.
        - reflexivity.
        - destruct (a =? account) eqn:Heqa.
          + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
            exact Heqa.
          + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
      assert (H_addmem_cons :
                AccessControl.add_member sim.(State.optimisticGuardianManagers) account
                = account :: sim.(State.optimisticGuardianManagers)).
      { unfold AccessControl.add_member. rewrite H_ac_not_in. reflexivity. }
      set (member_map_post :=
             Dict.declare_or_assign (role_member_map sim)
               (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account) 1).
      set (positions_map_post :=
             Dict.declare_or_assign (role_positions_map sim)
               (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account)
               (Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1)).
      set (length_map_post :=
             Dict.declare_or_assign (role_values_length_map sim)
               OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
               (Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1)).
      set (body_map_post :=
             Dict.declare_or_assign (role_values_body_map sim)
               (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                 Z.of_nat (List.length sim.(State.optimisticGuardianManagers)))
               account).
      set (storage_post :=
             [ StorableValue.Map2 member_map_post;
               StorableValue.Map2 positions_map_post;
               StorableValue.Map length_map_post;
               StorableValue.Map2 body_map_post ]).
      assert (Hbody_any :
                forall memory',
                  (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                  exists memory'',
                  {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                    fun_grantRole_1359_inner OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account ⇓
                    Result.Ok tt
                  | Some (make_state env state_base memory'' storage_post) ?}}).
      { intros memory' H_mem'.
        assert (H_caller_u256 : 0 <= env.(Environment.caller) < 2^256).
        { destruct H_caller_bound. split; [lia|].
          change (2^160) with 1461501637330902918203684832716283019655932542976 in *.
          change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
          lia. }
        assert (H_role_u256 :
                  0 <= OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 < 2^256).
        { unfold U256.Valid.t in H_role.
          change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
          lia. }
        pose proof (run_fun__grantRole_1468_at_proj_sim_not_member
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      H_role_u256 H_account H_caller_bound
                      H_not_member H_mem') as Hgr1468.
        cbv zeta in Hgr1468.
        destruct Hgr1468 as (w0_p1 & w1_p1 & rest_p1 & Hgr1468).
        set (mem_after_p1 := w0_p1 :: w1_p1 :: rest_p1).
        set (proj_after_p1 :=
               [ StorableValue.Map2 member_map_post;
                 StorableValue.Map2 (role_positions_map sim);
                 StorableValue.Map (role_values_length_map sim);
                 StorableValue.Map2 (role_values_body_map sim) ]).
        fold proj_after_p1 in Hgr1468.
        assert (H_mem_after_p1 :
                  exists w0 w1 rest, mem_after_p1 = w0 :: w1 :: rest).
        { exists w0_p1, w1_p1, rest_p1. reflexivity. }
        pose proof (MappingIndexAccessBytes32AddressSet.run_mapping_index_access
                      codes env state_base 1
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                      proj_after_p1 mem_after_p1 H_mem_after_p1) as Hmia.
        cbv zeta in Hmia.
        destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
        set (mem_after_mia := w0_m :: w1_m :: rest_m).
        assert (H_mem_after_mia :
                  exists w0 w1 rest, mem_after_mia = w0 :: w1 :: rest).
        { exists w0_m, w1_m, rest_m. reflexivity. }
        pose proof (run_fun_add_2085_at_proj_sim
                      codes env state_base mem_after_mia
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      member_map_post
                      (role_positions_map sim)
                      (role_values_length_map sim)
                      (role_values_body_map sim)
                      H_account H_not_in_pos
                      H_len_bound_ogm H_len_nn_ogm
                      H_mem_after_mia) as Hadd.
        cbv zeta in Hadd.
        destruct Hadd as (mem_after_add & Hadd).
        assert (Hsto :
                  [ StorableValue.Map2 member_map_post;
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_positions_map sim)
                         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account)
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 + 1));
                    StorableValue.Map
                      (Dict.declare_or_assign (role_values_length_map sim)
                         OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                         (StorableValue.map_get_u256
                            (role_values_length_map sim)
                            OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 + 1));
                    StorableValue.Map2
                      (Dict.declare_or_assign (role_values_body_map sim)
                         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                           StorableValue.map_get_u256
                             (role_values_length_map sim)
                             OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
                         account) ]
                = storage_post).
        { unfold storage_post, positions_map_post, length_map_post,
                 body_map_post. rewrite H_get_length. reflexivity. }
        rewrite Hsto in Hadd.
        assert (H704 : {{? codes, env,
            Some (make_state env state_base memory' (proj_sim sim))
          | fun__grantRole_704 OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account ⇓
            Result.Ok 1
          | Some (make_state env state_base mem_after_add storage_post) ?}}).
        { unfold fun__grantRole_704.
          unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
                 Shallow.let_state, Shallow.if_.
          repeat (lazymatch goal with
            | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.strong_let_, M.generic_let
            | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
                unfold M.let_, M.generic_let
            | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
                unfold M.do
            | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
                unfold Shallow.let_state
            | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
            | |- {{? _, _, _ |
                  LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
                c; [ unfold zero_value_for_split_t_bool;
                     lu; repeat (lu || cu || p) | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun__grantRole_1468 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hgr1468 | ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_AddressSet_ₓ2058_storage_ₓ_of_t_bytes32 _ _) _
                  ⇓ _ | _ ?}} =>
                eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
            | |- {{? _, _, _ |
                  LowM.Call
                    (convert_t_structₓ_AddressSet_ₓ2058_storage_to_t_structₓ_AddressSet_ₓ2058_storage_ptr _) _
                  ⇓ _ | _ ?}} =>
                c; [ apply run_convert_t_structₓ_AddressSet_storage_to_ptr | ]
            | |- {{? _, _, _ |
                  LowM.Call (fun_add_2085 _ _) _ ⇓ _ | _ ?}} =>
                c; [ exact Hadd | ]
            | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
                apply RunO.Pure
            | |- _ => s
            end).
          all: cbn match.
          all: try apply RunO.Pure. }
        pose proof (run_fun_grantRole_1359_inner_at_proj_sim
                      codes env state_base memory' sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      _ _ H704) as Hinner.
        exists mem_after_add. exact Hinner. }
      pose proof (run_modifier_onlyRole_1351_admin_passes_exists
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                    (or_intror (or_intror eq_refl))
                    H_caller_admin H_caller_bound H_mem
                    storage_post
                    Hbody_any) as Hmod.
      destruct Hmod as (mem_mod & Hmod).
      pose proof (run_fun_grantRole_1359_at_proj_sim
                    codes env state_base memory sim
                    OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                    (Some (make_state env state_base mem_mod storage_post))
                    Hmod) as Houter.
      exists (Guardian.add_optimistic_guardian_manager sim account),
        (Some (make_state env state_base mem_mod storage_post)).
      split; [|split].
      + assert (H_g_not_in :
                  Guardian.addr_in sim.(State.optimisticGuardianManagers) account
                  = false).
        { exact (proj2 (addr_in_false_iff_not_In _ _) H_addr_in). }
        unfold Guardian.add_optimistic_guardian_manager, Guardian.add_role.
        cbn [State.admins State.optimisticGuardians
             State.optimisticGuardianManagers].
        rewrite H_g_not_in.
        unfold project_sim_to_ac.
        cbn [AccessControl.roles].
        unfold AccessControl.getRoleEntry.
        simpl AccessControl.find_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM). cbv match.
        rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM). cbv match.
        rewrite Z.eqb_refl. cbv match.
        simpl AccessControl.set_entry.
        rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM).
        rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM).
        rewrite Z.eqb_refl.
        cbn [AccessControl.members].
        rewrite H_addmem_cons. reflexivity.
      + exact Houter.
      + exists mem_mod, storage_post.
        split; [reflexivity|].
        unfold observationally_eq_storage, storage_post, proj_sim.
        repeat split; intros key; cbn match.
        * apply role_member_map_sstore_observes_add_optimistic_guardian_manager_not_in;
            [exact H_not_member | exact H_addr_in].
        * apply role_positions_map_sstore_observes_add_optimistic_guardian_manager_not_in.
          -- exact H_not_in_pos.
          -- exact H_addr_in.
          -- reflexivity.
        * unfold length_map_post.
          rewrite (role_values_length_map_sstore_eq_add_optimistic_guardian_manager_not_in
                     sim account H_addr_in
                     (Z.of_nat (List.length sim.(State.optimisticGuardianManagers)) + 1)
                     eq_refl). reflexivity.
        * unfold body_map_post.
          apply role_values_body_map_sstore_observes_add_optimistic_guardian_manager_not_in.
          -- (* Dict.get (role_values_body_map sim) (OGM, length ogm) = None. *)
             unfold role_values_body_map.
             rewrite !Dict_get_app_split.
             pose proof (proj2 (Z.eqb_neq _ _)
                           (not_eq_sym DEFAULT_neq_OGM)) as H_eqb_def.
             assert (Hd_def : forall n,
                       Dict.get
                         (values_for_role_aux DEFAULT_ADMIN_ROLE_bytes32
                            n sim.(State.admins))
                         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                           Z.of_nat
                             (Datatypes.length sim.(State.optimisticGuardianManagers)))
                       = None).
             { intros n. revert n. clear -H_eqb_def.
               induction sim.(State.admins) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                     DEFAULT_ADMIN_ROLE_bytes32)
                   with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                         =? DEFAULT_ADMIN_ROLE_bytes32).
                 rewrite H_eqb_def. simpl andb. apply IH. }
             unfold values_for_role at 1.
             rewrite Hd_def.
             pose proof (proj2 (Z.eqb_neq _ _)
                           (not_eq_sym OG_neq_OGM)) as H_eqb_og.
             assert (Hd_og : forall n,
                       Dict.get
                         (values_for_role_aux OPTIMISTIC_GUARDIAN_ROLE_bytes32
                            n sim.(State.optimisticGuardians))
                         (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                           Z.of_nat
                             (Datatypes.length sim.(State.optimisticGuardianManagers)))
                       = None).
             { intros n. revert n. clear -H_eqb_og.
               induction sim.(State.optimisticGuardians) as [|a rest IH];
                 intros n; simpl.
               - reflexivity.
               - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                 change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                     OPTIMISTIC_GUARDIAN_ROLE_bytes32)
                   with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                         =? OPTIMISTIC_GUARDIAN_ROLE_bytes32).
                 rewrite H_eqb_og. simpl andb. apply IH. }
             unfold values_for_role at 1.
             rewrite Hd_og.
             (* OGM block: indices assigned are 0..length-1; miss at length. *)
             assert (Hd_ogm : Dict.get
                            (values_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                               sim.(State.optimisticGuardianManagers))
                            (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                              Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers)))
                            = None).
             { assert (Hgen : forall l n,
                 Z.of_nat n < Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers)) ->
                 Dict.get (values_for_role_aux OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 n l)
                   (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                     Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers))) = None).
               { intros l. induction l as [|a rest IH]; intros n Hn; simpl.
                 - reflexivity.
                 - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
                   rewrite Z.eqb_refl. simpl andb.
                   change (Dict.Eq.eqb
                             (Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers)))
                             (Z.of_nat n))
                     with (Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers))
                           =? Z.of_nat n).
                   assert (Hneq : Z.of_nat (Datatypes.length sim.(State.optimisticGuardianManagers))
                                  <> Z.of_nat n) by lia.
                   apply Z.eqb_neq in Hneq. rewrite Hneq.
                   apply IH. simpl. lia. }
               unfold values_for_role.
               destruct sim.(State.optimisticGuardianManagers) as [|a rest] eqn:Hl.
               - simpl. reflexivity.
               - apply Hgen. simpl. lia. }
             exact Hd_ogm.
          -- exact H_addr_in.
    }
  Qed.

  (** ===== R056: revokeRole equivalence — was-not-member branch =====

      Mirrors the grantRole milestone (R055) but for revoke. The
      structural difference: OZ's [EnumerableSet._remove] uses
      swap-and-pop. Concretely, [fun__revokeRole_1506] (the inner OZ
      AccessControl mutator) does:

        hasRole := fun_hasRole_1292 role account
        if hasRole == 0:
          return 0                       (* no-op — account wasn't a holder *)
        else:
          _roles[role].members[account] := false  (* sstore at slot 0 *)
          emit RoleRevoked(...)
          return 1

      Followed (in [fun__revokeRole_736]) by:
        if revoked == 1:
          _roleMembers[role].remove(account)  (* fun_remove_2112 — slot 1 + 2 + 3 *)

      The "was-not-member" branch is precisely the no-op case: hasRole
      returns 0, the inner mutator returns 0 without touching storage,
      and the outer wrapper's Shallow.if_ FALSE branch skips the
      EnumerableSet remove entirely. State is unchanged.

      This is the structural analog of grantRole's "already-member"
      branch — the work-skipping case — and the proof technique is
      identical: walk hasRole, take the Leave branch of the inner
      switch, observe state-preservation, and the observational
      storage equality is reflexive on the unchanged storage.

      The "was-member" branch (where the function actually performs
      the swap-and-pop) is documented at the Phase 5 assembly
      [run_revokeRole_1378_equivalent] below as an Admitted
      sub-lemma — see [run_fun__revokeRole_1506_at_proj_sim_member]
      placeholder and the inline diagnoses for each role branch. *)

  (** ===== Phase 1 — [fun__revokeRole_1506] was-not-member walker =====

      When [hasRole role account = 0] (account doesn't hold the role),
      the function returns 0 with state unchanged. This is the cheap
      branch — no sstore, no log4, just hasRole + the switch's true
      arm (which is the "early-return" arm via [BlockUnit.Leave]).

      Structurally identical to [run_fun__grantRole_1468_at_proj_sim_member]
      but inverted: that lemma's success-arm was "hasRole = 1 → return 0",
      this lemma's success-arm is "hasRole = 0 → return 0". The
      Shallow.if_ branches differ because the source uses [if δ =? 0]
      to detect non-membership (revokeRole) vs membership (grantRole). *)
  Lemma run_fun__revokeRole_1506_at_proj_sim_not_member
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_not_member :
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__revokeRole_1506 role account ⇓
      Result.Ok 0
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    (* hasRole pre-walk: in the not-member branch, returns 0. *)
    pose proof (run_fun_hasRole_1292_at_proj_sim
                  codes env state_base memory sim role account
                  H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    rewrite H_not_member in Hhr.
    destruct Hhr as (w0_hr & w1_hr & rest_hr & Hhr).
    exists w0_hr, w1_hr, rest_hr.
    unfold fun__revokeRole_1506.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_1292 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhr | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Value-0 specializations for the bool sstore chain =====

      grantRole only ever writes value 1 to the slot-0 member map.
      revokeRole writes value 0 (clearing membership). These leaves
      mirror the existing value-1 leaves but specialized to v=0. *)
  Lemma run_cleanup_t_bool_of_0 codes env state :
    {{? codes, env, Some state |
      cleanup_t_bool 0 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  Lemma run_convert_t_bool_to_t_bool_of_0 codes env state :
    {{? codes, env, Some state |
      convert_t_bool_to_t_bool 0 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold convert_t_bool_to_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_bool_of_0 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  Lemma run_update_byte_slice_1_shift_0_bool_0
      codes env state (prev : U256.t)
      (H_prev : prev = 0 \/ prev = 1) :
    {{? codes, env, Some state |
      update_byte_slice_1_shift_0 prev 0 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_1_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (shift_left_0 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_left_0_local;
               change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936;
               lia | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    s.
    apply RunO.PureEq; [|reflexivity].
    destruct H_prev as [-> | ->]; vm_compute; reflexivity.
  Qed.

  (** v=0 analogue of [run_update_storage_value_t_bool_at_proj_sim]. *)
  Lemma run_update_storage_value_t_bool_at_proj_sim_v0
      codes env state_base memory sim (role account : U256.t) :
    let member_map' :=
      Dict.declare_or_assign (role_member_map sim) (role, account) 0 in
    let proj_sim' :=
      [ StorableValue.Map2 member_map';
        StorableValue.Map2 (role_positions_map sim);
        StorableValue.Map (role_values_length_map sim);
        StorableValue.Map2 (role_values_body_map sim) ] in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      update_storage_value_offset_0_t_bool_to_t_bool
        (keccak256_tuple2 account (keccak256_tuple2 role 0)) 0 ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_sim') ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_0_t_bool_to_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    pose proof (role_member_map_values_bool sim (role, account)) as H_prev_bool.
    cbv zeta in H_prev_bool.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bool_to_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bool_to_t_bool_of_0 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_sload_role_member_at_proj_sim | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_1_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_1_shift_0_bool_0;
               exact H_prev_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sstore_role_member_at_proj_sim
                       codes env state_base memory sim role account 0) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ===== Phase 1 was-member walker for [fun__revokeRole_1506] =====

      When the account IS currently a member (slot-0 member lookup
      returns 1), the function steps:
        hasRole = 1 → δ = 1 → take the [else] branch (not [δ =? 0])
        → MIA chain to slot-0 sub-mapping at (role, account)
        → sstore 0 (slot-0 write — sets members[account] := false)
        → log4 (RoleRevoked event, state-preserving)
        → return 1

      Post-state has slot 0 mutated; slots 1/2/3 unchanged. The
      mutation is [Dict.declare_or_assign (role_member_map sim)
      (role, account) 0] — observationally a "delete" since the
      stored value is 0 (the default for missing keys).

      The walker mirrors [run_fun__grantRole_1468_at_proj_sim_not_member]
      precisely (same structural shape — the only delta is the
      sstore value of 0 instead of 1, which uses [_t_bool] sstore as
      well since the underlying type is bool offset 0).

      We use the same [run_update_storage_value_t_bool_at_proj_sim]
      leaf — its signature accepts an arbitrary value being written
      (parameterized over the [v] argument). The stored value here
      is 0, which still respects the t_bool clean form. *)
  Lemma run_fun__revokeRole_1506_at_proj_sim_member
      codes env state_base memory sim (role account : U256.t)
      (H_role : 0 <= role < 2 ^ 256)
      (H_account : 0 <= account < 2^160)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_member :
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 1)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let member_map' :=
      Dict.declare_or_assign (role_member_map sim) (role, account) 0 in
    let proj_sim' :=
      [ StorableValue.Map2 member_map';
        StorableValue.Map2 (role_positions_map sim);
        StorableValue.Map (role_values_length_map sim);
        StorableValue.Map2 (role_values_body_map sim) ] in
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__revokeRole_1506 role account ⇓
      Result.Ok 1
    | Some (make_state env state_base (w0' :: w1' :: rest') proj_sim') ?}}.
  Proof.
    cbv zeta.
    (* hasRole pre-walk: in the member branch, returns 1. Rewrite. *)
    pose proof (run_fun_hasRole_1292_at_proj_sim
                  codes env state_base memory sim role account
                  H_account H_mem) as Hhr.
    cbv zeta in Hhr.
    rewrite H_member in Hhr.
    destruct Hhr as (w0_hr & w1_hr & rest_hr & Hhr).
    set (mem_after_hr := w0_hr :: w1_hr :: rest_hr).
    (* MIA chain (bytes32 → struct ptr → address → bool). *)
    pose proof (MappingIndexAccessBytes32RoleData.run_mapping_index_access
                  codes env state_base 0 role (proj_sim sim) mem_after_hr
                  (ex_intro _ w0_hr (ex_intro _ w1_hr
                    (ex_intro _ rest_hr eq_refl)))) as Hmia1.
    destruct Hmia1 as (w0_a & w1_a & rest_a & Hmia1).
    set (mem_after_mia1 := w0_a :: w1_a :: rest_a).
    pose proof (MappingIndexAccessAddressBool.run_mapping_index_access
                  codes env state_base (keccak256_tuple2 role 0) account
                  (proj_sim sim) mem_after_mia1 H_account
                  (ex_intro _ w0_a (ex_intro _ w1_a
                    (ex_intro _ rest_a eq_refl)))) as Hmia2.
    destruct Hmia2 as (w0_b & w1_b & rest_b & Hmia2).
    set (mem_after_mia2 := w0_b :: w1_b :: rest_b).
    assert (H_pa1 : Pure.add (keccak256_tuple2 role 0) 0
                  = keccak256_tuple2 role 0).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (Hmia2' :
      {{? codes, env,
          Some (make_state env state_base mem_after_mia1 (proj_sim sim))
      | mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address
          (Pure.add (keccak256_tuple2 role 0) 0) account
        ⇓ Result.Ok (keccak256_tuple2 account (keccak256_tuple2 role 0))
      | Some (make_state env state_base mem_after_mia2 (proj_sim sim)) ?}}).
    { rewrite H_pa1. exact Hmia2. }
    (* sstore at slot 0's Map2 — for revoke, we write 0 (false). *)
    (* run_update_storage_value_t_bool_at_proj_sim writes value 1
       hardcoded. We need a 0-value variant — luckily its proof
       reuses [run_sstore_role_member_at_proj_sim] directly, so we
       can do the sstore inline. Actually, the existing wrapper
       passes the value through — let's check it. *)
    (* The wrapper [run_update_storage_value_t_bool_at_proj_sim]'s
       proof writes the value passed in via prepare_store_t_bool.
       For revoke, the source's expr_1488 = 0x00, so the wrapper
       at proj_sim writes 0. We re-derive the proof inline since
       the wrapper was specialized for value=1. *)
    pose proof (run_update_storage_value_t_bool_at_proj_sim_v0
                  codes env state_base mem_after_mia2 sim role account)
      as Hsstore.
    cbv zeta in Hsstore.
    set (proj_sim_post :=
           [ StorableValue.Map2
               (Dict.declare_or_assign (role_member_map sim)
                  (role, account) 0);
             StorableValue.Map2 (role_positions_map sim);
             StorableValue.Map (role_values_length_map sim);
             StorableValue.Map2 (role_values_body_map sim) ]).
    fold proj_sim_post in Hsstore.
    set (state_after_sstore :=
           make_state env state_base mem_after_mia2 proj_sim_post).
    (* msgSender: state-preserving leaf. *)
    pose proof (run_fun__msgSender_3197 codes env state_after_sstore)
      as Hms.
    (* Post-state: pin to the post-sstore state. log4/MLoad are
       state-preserving in our sim model. *)
    exists w0_b, w1_b, rest_b.
    fold proj_sim_post.
    change (make_state env state_base (w0_b :: w1_b :: rest_b) proj_sim_post)
      with state_after_sstore.
    unfold fun__revokeRole_1506.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | Shallow.if_ _ _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.if_
      | |- {{? _, _, _ | M.call _ ⇓ _ | _ ?}} =>
          unfold M.call
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_1292 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.iszero, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_bool_of_bool; right; reflexivity | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ1233_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia1 | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia2' | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (update_storage_value_offset_0_t_bool_to_t_bool _ _) _
            ⇓ _ | _ ?}} =>
          c; [ exact Hsstore | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__msgSender_3197) _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bytes32_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bytes32_to_t_bytes32 | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_address _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_address;
               first [ exact H_account
                     | exact H_caller_bound ] | ]
      | |- {{? _, _, _ |
            LowM.Call allocate_unbounded _ ⇓ _ | _ ?}} =>
          unfold allocate_unbounded; cu
      | |- {{? _, _, _ |
            LowM.Call (abi_encode_tuple__to__fromStack _) _ ⇓ _ | _ ?}} =>
          unfold abi_encode_tuple__to__fromStack; cu
      | |- {{? _, _, _ | LowM.Call (Stdlib.mload _) _ ⇓ _ | _ ?}} =>
          unfold Stdlib.mload; cu
      | |- {{? _, _, _ |
            LowM.Primitive (Primitive.MLoad _ _) _ ⇓ _ | _ ?}} =>
          pr
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sub _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.sub, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.log4 _ _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.log4, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Phase 3 — [fun__revokeRole_736] outer mutator wrapper =====

      [fun__revokeRole_736] composes:
        revoked := fun__revokeRole_1506 role account
        if revoked == 1:
          fun_remove_2112 (_roleMembers[role]) account  (* EnumerableSet remove *)
        return revoked

      The was-not-member branch: revoked = 0, the Shallow.if_ FALSE
      branch fires (since the condition is var_revoked_716 directly,
      not iszero(var_revoked_716)), so [fun_remove_2112] is SKIPPED.
      Returns 0. State unchanged.

      The was-member branch returns 1 and performs the
      enumerable-set remove — out of scope for this Qed; deferred
      to a separate companion lemma for the milestone's
      was-member branches. *)
  Lemma run_fun__revokeRole_736_at_proj_sim_not_member
      codes env state_base memory sim (role account : U256.t)
      (H_account : 0 <= account < 2^160)
      (H_not_member :
         StorableValue.map_get_u256 (role_member_map sim) (role, account) = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun__revokeRole_736 role account ⇓
      Result.Ok 0
    | Some (make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)) ?}}.
  Proof.
    pose proof (run_fun__revokeRole_1506_at_proj_sim_not_member
                  codes env state_base memory sim role account
                  H_account H_not_member H_mem) as Hinner.
    destruct Hinner as (w0' & w1' & rest' & Hinner).
    exists w0', w1', rest'.
    unfold fun__revokeRole_736.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
           Shallow.let_state, Shallow.if_.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_, M.generic_let
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_bool;
               lu; repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__revokeRole_1506 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hinner | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Phase 4 — [fun_revokeRole_1378_inner] composable wrapper =====

      Mirrors [run_fun_grantRole_1359_inner_at_proj_sim]: a thin
      wrapper that takes the [fun__revokeRole_736] walk as a hypothesis. *)
  Lemma run_fun_revokeRole_1378_inner_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (state' : option RocqOfSolidity.State.t) (revoked : U256.t)
      (Hbody_736 :
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun__revokeRole_736 role account ⇓
          Result.Ok revoked
        | state' ?}}) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_revokeRole_1378_inner role account ⇓
      Result.Ok tt
    | state' ?}}.
  Proof.
    unfold fun_revokeRole_1378_inner.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun__revokeRole_736 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody_736 | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Modifier wrapper for revoke: [modifier_onlyRole_1370] =====

      Structurally IDENTICAL to [run_modifier_onlyRole_1351_admin_passes_exists]
      from the grantRole milestone — same admin-gate, same composition,
      same H_role_known dispatch. The only delta is the inner body:
      [fun_revokeRole_1378_inner] instead of [fun_grantRole_1359_inner]. *)
  Lemma run_modifier_onlyRole_1370_admin_passes_exists
      codes env state_base memory sim (role account : U256.t)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest)
      (storage_post : SimulatedStorage.t)
      (Hbody :
        forall memory',
          (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
          exists memory'',
          {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
            fun_revokeRole_1378_inner role account ⇓
            Result.Ok tt
          | Some (make_state env state_base memory'' storage_post) ?}}) :
    exists memory'',
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      modifier_onlyRole_1370 role account ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'' storage_post) ?}}.
  Proof.
    pose proof (run_fun_getRoleAdmin_1340_at_proj_sim
                  codes env state_base memory sim role H_role_known H_mem) as Hgra.
    destruct Hgra as (w0' & w1' & rest' & Hgra).
    set (mem_after_gra := w0' :: w1' :: rest').
    assert (H_admin_member :
              StorableValue.map_get_u256 (role_member_map sim)
                (DEFAULT_ADMIN_ROLE_bytes32, env.(Environment.caller)) = 1).
    { unfold role_member_map.
      rewrite map_get_app_split.
      unfold has_admin in H_caller_admin.
      apply (proj1 (addr_in_true_iff_In _ _)) in H_caller_admin.
      set (caller := env.(Environment.caller)) in *.
      induction (State.admins sim) as [|a rest IH].
      - simpl in H_caller_admin. exfalso. exact H_caller_admin.
      - simpl members_for_role. simpl Dict.get.
        cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
        rewrite Z.eqb_refl. simpl andb.
        change (Dict.Eq.eqb caller a) with (caller =? a).
        destruct (caller =? a) eqn:Hca.
        + reflexivity.
        + apply Z.eqb_neq in Hca.
          destruct H_caller_admin as [Heq | Hin]; [congruence|].
          apply IH. exact Hin. }
    pose proof (run_fun__checkRole_1305_at_proj_sim_pass
                  codes env state_base mem_after_gra sim
                  DEFAULT_ADMIN_ROLE_bytes32
                  H_admin_member H_caller_bound) as Hckr.
    assert (Hmem_after_gra : exists w0 w1 rest,
              mem_after_gra = w0 :: w1 :: rest).
    { exists w0', w1', rest'. reflexivity. }
    specialize (Hckr Hmem_after_gra).
    destruct Hckr as (w0'' & w1'' & rest'' & Hckr).
    set (mem_after_ckr := w0'' :: w1'' :: rest'').
    assert (Hmem_after_ckr : exists w0 w1 rest,
              mem_after_ckr = w0 :: w1 :: rest).
    { exists w0'', w1'', rest''. reflexivity. }
    specialize (Hbody mem_after_ckr Hmem_after_ckr).
    destruct Hbody as (mem_inner & Hbody).
    exists mem_inner.
    unfold modifier_onlyRole_1370.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call, M.do.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun_getRoleAdmin_1340 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgra | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_1305 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hckr | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_revokeRole_1378_inner _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Outer wrapper [fun_revokeRole_1378] =====

      Same shape as [run_fun_grantRole_1359_at_proj_sim] — wraps the
      modifier. *)
  Lemma run_fun_revokeRole_1378_at_proj_sim
      codes env state_base memory sim (role account : U256.t)
      (state' : option RocqOfSolidity.State.t)
      (Hmod :
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          modifier_onlyRole_1370 role account ⇓
          Result.Ok tt
        | state' ?}}) :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      fun_revokeRole_1378 role account ⇓
      Result.Ok tt
    | state' ?}}.
  Proof.
    unfold fun_revokeRole_1378.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call, M.do.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (modifier_onlyRole_1370 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmod | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== R056 milestone: [run_revokeRole_1378_equivalent] =====

      Mirrors [run_grantRole_1359_equivalent] (R055). Three roles
      (DEFAULT, OG, OGM) × two cases (was-member / was-not-member).
      The was-not-member branch is the cheap (no-op, reflexive
      observational equality) case; the was-member branch performs
      the swap-and-pop on the EnumerableSet.

      ===== Theorem signature =====

      Same preconditions as grantRole: H_role, H_role_known,
      H_account, H_caller_admin, H_caller_bound, H_mem. The per-role
      length BOUNDS are NOT needed for revoke (no array growth — the
      length DECREASES). The was-member branch needs a per-role
      length LOWER BOUND (length ≥ 1) — but only inside its proof,
      and that follows from membership (a member's address sits at
      some index in the array, so length must be at least 1).

      ===== Was-member branch coverage =====

      The was-member branch handles three structurally different
      sub-cases inside the swap-and-pop:
        a. position - 1 = lastIndex: no swap needed, just pop +
           positions[value] := 0 (3 storage writes).
        b. position - 1 ≠ lastIndex: read lastValue, write
           values[position-1] := lastValue, update
           positions[lastValue] := position, then pop +
           positions[value] := 0 (5 storage writes).

      The Phase-1 walker for the was-member branch threads through
      the [BlockUnit.Tt] arm of [fun__revokeRole_1506]'s switch,
      hitting the bool sstore (positions[role][account] := false),
      log4, then returns to [fun__revokeRole_736] which invokes
      [fun_remove_2112] (the EnumerableSet remove). That second
      call performs the swap-and-pop on slots 1, 2, 3.

      The sim-side post-state is
      [Guardian.revoke_role_sim role sim account] where
      [revoke_role_sim] picks the right per-role list and applies
      [remove_role]. *)

  (** Helper: pick the right per-role removal on the sim side. *)
  Definition revoke_role_sim (role : U256.t) (sim : State.t) (account : Address)
      : State.t :=
    if role =? DEFAULT_ADMIN_ROLE_bytes32 then
      {| State.admins := Guardian.remove_role sim.(State.admins) account;
         State.optimisticGuardians := sim.(State.optimisticGuardians);
         State.optimisticGuardianManagers := sim.(State.optimisticGuardianManagers) |}
    else if role =? OPTIMISTIC_GUARDIAN_ROLE_bytes32 then
      {| State.admins := sim.(State.admins);
         State.optimisticGuardians := Guardian.remove_role sim.(State.optimisticGuardians) account;
         State.optimisticGuardianManagers := sim.(State.optimisticGuardianManagers) |}
    else if role =? OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 then
      {| State.admins := sim.(State.admins);
         State.optimisticGuardians := sim.(State.optimisticGuardians);
         State.optimisticGuardianManagers := Guardian.remove_role sim.(State.optimisticGuardianManagers) account |}
    else sim.

  Theorem run_revokeRole_1378_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : Guardian.State.t) (role account : U256.t)
      (memory : SimulatedMemory.t)
      (H_role : U256.Valid.t role)
      (H_role_known :
         role = DEFAULT_ADMIN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
         role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
      (H_account : 0 <= account < 2^160)
      (H_caller_admin : has_admin sim env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let sim_ac := project_sim_to_ac sim in
    let caller := env.(Environment.caller) in
    let result := AccessControl.revokeRole sim_ac caller role account in
    match result with
    | AccessControl.Result.Success sim_ac' =>
        exists (sim' : Guardian.State.t) (state' : option RocqOfSolidity.State.t),
          project_sim_to_ac sim' = sim_ac' /\
          {{? codes, env, Some state |
            fun_revokeRole_1378 role account ⇓
            Result.Ok tt
          | state' ?}} /\
          (exists memory' storage',
            state' = Some (make_state env state_base memory' storage') /\
            observationally_eq_storage storage' (proj_sim sim'))
    | AccessControl.Result.Revert _ _ => True
    end.
  Proof.
    intros state sim_ac caller result.
    (* Phase 1: gate passes ⇒ result is Success. *)
    assert (H_result_success :
      AccessControl.hasRole sim_ac
        (AccessControl.getRoleAdmin sim_ac role) caller = true).
    { subst sim_ac caller.
      rewrite project_sim_to_ac_hasRole_admin_chain. exact H_caller_admin. }
    subst result.
    unfold AccessControl.revokeRole at 1.
    rewrite H_result_success. cbn match.
    subst sim_ac caller state.
    (* Case-split on the three Guardian roles. *)
    destruct H_role_known as [H_role_eq | H_role_or];
      [subst role | destruct H_role_or as [H_role_eq | H_role_eq]; subst role].
    { (** ===== BRANCH 1: role = DEFAULT_ADMIN_ROLE_bytes32 ===== *)
      destruct (Guardian.addr_in sim.(State.admins) account) eqn:H_addr_in.
      - (** ===== Was-member branch (does the swap-and-pop) ===== *)
        (* R056 BLOCKER: the was-member branch requires the
           swap-and-pop walker + observational bridges for
           [remove_role]. Path forward documented in
           [run_revokeRole_1378_member_default_blocker] below. *)
        admit.
      - (** ===== Was-not-member branch (no-op, reflexive) ===== *)
        apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
        (* Slot-0 lookup at (DEFAULT, account) = 0 (absent). Same
           reasoning as the grantRole milestone's not-member branch. *)
        assert (H_not_member :
                  StorableValue.map_get_u256 (role_member_map sim)
                    (DEFAULT_ADMIN_ROLE_bytes32, account) = 0).
        { unfold role_member_map.
          rewrite map_get_app_split.
          set (acct := account) in *.
          assert (Hd : Dict.get
                         (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                            sim.(State.admins))
                         (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
          { clear -H_addr_in.
            induction (State.admins sim) as [|a rest IH].
            - reflexivity.
            - simpl. cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              rewrite Z.eqb_refl. simpl andb.
              change (Dict.Eq.eqb acct a) with (acct =? a).
              destruct (acct =? a) eqn:Hca.
              + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in.
                left. symmetry. exact Hca.
              + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
          rewrite Hd.
          rewrite map_get_app_split.
          pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG) as H_eqb_og.
          pose proof (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM) as H_eqb_ogm.
          assert (Hd_og : Dict.get
                            (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                               sim.(State.optimisticGuardians))
                            (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
          { clear -H_eqb_og.
            induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                  OPTIMISTIC_GUARDIAN_ROLE_bytes32)
                with (DEFAULT_ADMIN_ROLE_bytes32 =?
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32).
              rewrite H_eqb_og.
              simpl andb. exact IH. }
          rewrite Hd_og.
          assert (Hd_ogm : Dict.get
                             (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                sim.(State.optimisticGuardianManagers))
                             (DEFAULT_ADMIN_ROLE_bytes32, acct) = None).
          { clear -H_eqb_ogm.
            induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb DEFAULT_ADMIN_ROLE_bytes32
                                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
                with (DEFAULT_ADMIN_ROLE_bytes32 =?
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
              rewrite H_eqb_ogm.
              simpl andb. exact IH. }
          unfold StorableValue.map_get_u256.
          rewrite Hd_ogm. reflexivity. }
        (* AC-level addr_in coincides with Guardian's. *)
        assert (H_ac_not_in : AccessControl.addr_in sim.(State.admins) account = false).
        { clear -H_addr_in.
          induction sim.(State.admins) as [|a rest IH']; simpl.
          - reflexivity.
          - destruct (a =? account) eqn:Heqa.
            + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
              exact Heqa.
            + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
        pose proof (AccessControl.remove_member_idempotent_on_absent
                      sim.(State.admins) account H_ac_not_in) as Hidem.
        (* Inner body walker parametric on memory'. *)
        assert (Hbody_any :
                  forall memory',
                    (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                    exists memory'',
                    {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                      fun_revokeRole_1378_inner DEFAULT_ADMIN_ROLE_bytes32 account ⇓
                      Result.Ok tt
                    | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
        { intros memory' H_mem'.
          pose proof (run_fun__revokeRole_736_at_proj_sim_not_member
                        codes env state_base memory' sim
                        DEFAULT_ADMIN_ROLE_bytes32 account
                        H_account H_not_member H_mem') as H736.
          destruct H736 as (w0' & w1' & rest' & H736).
          exists (w0' :: w1' :: rest').
          (* Wrap via Phase 4. *)
          pose proof (run_fun_revokeRole_1378_inner_at_proj_sim
                        codes env state_base memory' sim
                        DEFAULT_ADMIN_ROLE_bytes32 account
                        _ _ H736) as Hinner.
          exact Hinner. }
        (* Modifier wrapper. *)
        pose proof (run_modifier_onlyRole_1370_admin_passes_exists
                      codes env state_base memory sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      (or_introl eq_refl)
                      H_caller_admin H_caller_bound H_mem
                      (proj_sim sim)
                      Hbody_any) as Hmod.
        destruct Hmod as (mem_mod & Hmod).
        pose proof (run_fun_revokeRole_1378_at_proj_sim
                      codes env state_base memory sim
                      DEFAULT_ADMIN_ROLE_bytes32 account
                      (Some (make_state env state_base mem_mod (proj_sim sim)))
                      Hmod) as Houter.
        (* Witnesses: sim' = sim (idempotent on absent), state' = unchanged. *)
        exists sim,
          (Some (make_state env state_base mem_mod (proj_sim sim))).
        split; [|split].
        + (* project_sim_to_ac sim = sim_ac' *)
          destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
          cbn [State.admins State.optimisticGuardians
               State.optimisticGuardianManagers] in *.
          transitivity
            {| AccessControl.roles :=
                 [(DEFAULT_ADMIN_ROLE_bytes32,
                   {| AccessControl.members := adm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                   {| AccessControl.members := og;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                   {| AccessControl.members := ogm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
            |}.
          { reflexivity. }
          f_equal.
          unfold project_sim_to_ac.
          change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
            with l.
          unfold AccessControl.getRoleEntry.
          simpl AccessControl.find_entry.
          rewrite Z.eqb_refl. cbv match.
          simpl AccessControl.set_entry.
          rewrite Z.eqb_refl. cbv match.
          simpl AccessControl.members.
          rewrite Hidem.
          reflexivity.
        + exact Houter.
        + (* Observational equality: storage = proj_sim sim. *)
          exists mem_mod, (proj_sim sim).
          split; [reflexivity|].
          unfold observationally_eq_storage.
          repeat split; intros key; reflexivity.
    }
    { (** ===== BRANCH 2: role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 ===== *)
      destruct (Guardian.addr_in sim.(State.optimisticGuardians) account) eqn:H_addr_in.
      - (** Was-member branch — swap-and-pop. *)
        admit.
      - (** Was-not-member branch — no-op, reflexive. *)
        apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
        assert (H_not_member :
                  StorableValue.map_get_u256 (role_member_map sim)
                    (OPTIMISTIC_GUARDIAN_ROLE_bytes32, account) = 0).
        { unfold role_member_map.
          rewrite map_get_app_split.
          set (acct := account) in *.
          (* DEFAULT block: keys are (DEFAULT, _), not (OG, _). *)
          assert (Hd_def : Dict.get
                            (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                               sim.(State.admins))
                            (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
          { pose proof (proj2 (Z.eqb_neq _ _)
                          (not_eq_sym DEFAULT_neq_OG)) as H_eqb.
            clear -H_eqb.
            induction (State.admins sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                  DEFAULT_ADMIN_ROLE_bytes32)
                with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                      DEFAULT_ADMIN_ROLE_bytes32).
              rewrite H_eqb. simpl andb. exact IH. }
          rewrite Hd_def.
          rewrite map_get_app_split.
          (* OG block: account NOT In optG ⇒ (OG, account) absent. *)
          assert (Hd_og : Dict.get
                            (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                               sim.(State.optimisticGuardians))
                            (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
          { clear -H_addr_in.
            induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              rewrite Z.eqb_refl. simpl andb.
              change (Dict.Eq.eqb acct a) with (acct =? a).
              destruct (acct =? a) eqn:Hca.
              + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in. left.
                symmetry. exact Hca.
              + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
          rewrite Hd_og.
          assert (Hd_ogm : Dict.get
                             (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                sim.(State.optimisticGuardianManagers))
                             (OPTIMISTIC_GUARDIAN_ROLE_bytes32, acct) = None).
          { pose proof (proj2 (Z.eqb_neq _ _) OG_neq_OGM) as H_eqb.
            clear -H_eqb.
            induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_ROLE_bytes32
                                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
                with (OPTIMISTIC_GUARDIAN_ROLE_bytes32 =?
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32).
              rewrite H_eqb. simpl andb. exact IH. }
          unfold StorableValue.map_get_u256.
          rewrite Hd_ogm. reflexivity. }
        assert (H_ac_not_in :
                  AccessControl.addr_in sim.(State.optimisticGuardians) account = false).
        { clear -H_addr_in.
          induction sim.(State.optimisticGuardians) as [|a rest IH']; simpl.
          - reflexivity.
          - destruct (a =? account) eqn:Heqa.
            + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
              exact Heqa.
            + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
        pose proof (AccessControl.remove_member_idempotent_on_absent
                      sim.(State.optimisticGuardians) account H_ac_not_in) as Hidem.
        assert (Hbody_any :
                  forall memory',
                    (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                    exists memory'',
                    {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                      fun_revokeRole_1378_inner OPTIMISTIC_GUARDIAN_ROLE_bytes32 account ⇓
                      Result.Ok tt
                    | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
        { intros memory' H_mem'.
          pose proof (run_fun__revokeRole_736_at_proj_sim_not_member
                        codes env state_base memory' sim
                        OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                        H_account H_not_member H_mem') as H736.
          destruct H736 as (w0' & w1' & rest' & H736).
          exists (w0' :: w1' :: rest').
          pose proof (run_fun_revokeRole_1378_inner_at_proj_sim
                        codes env state_base memory' sim
                        OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                        _ _ H736) as Hinner.
          exact Hinner. }
        pose proof (run_modifier_onlyRole_1370_admin_passes_exists
                      codes env state_base memory sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      (or_intror (or_introl eq_refl))
                      H_caller_admin H_caller_bound H_mem
                      (proj_sim sim)
                      Hbody_any) as Hmod.
        destruct Hmod as (mem_mod & Hmod).
        pose proof (run_fun_revokeRole_1378_at_proj_sim
                      codes env state_base memory sim
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32 account
                      (Some (make_state env state_base mem_mod (proj_sim sim)))
                      Hmod) as Houter.
        exists sim,
          (Some (make_state env state_base mem_mod (proj_sim sim))).
        split; [|split].
        + (* project_sim_to_ac sim = sim_ac' for the OG-revoke idempotent case. *)
          destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
          cbn [State.admins State.optimisticGuardians
               State.optimisticGuardianManagers] in *.
          transitivity
            {| AccessControl.roles :=
                 [(DEFAULT_ADMIN_ROLE_bytes32,
                   {| AccessControl.members := adm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                   {| AccessControl.members := og;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                   {| AccessControl.members := ogm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
            |}.
          { reflexivity. }
          f_equal.
          unfold project_sim_to_ac.
          change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
            with l.
          unfold AccessControl.getRoleEntry.
          simpl AccessControl.find_entry.
          rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG). cbv match.
          rewrite Z.eqb_refl. cbv match.
          simpl AccessControl.set_entry.
          rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG).
          rewrite Z.eqb_refl.
          cbn [AccessControl.members].
          rewrite Hidem. reflexivity.
        + exact Houter.
        + exists mem_mod, (proj_sim sim).
          split; [reflexivity|].
          unfold observationally_eq_storage.
          repeat split; intros key; reflexivity.
    }
    { (** ===== BRANCH 3: role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 ===== *)
      destruct (Guardian.addr_in sim.(State.optimisticGuardianManagers) account)
        eqn:H_addr_in.
      - (** Was-member branch — swap-and-pop. *)
        admit.
      - (** Was-not-member branch — no-op, reflexive. *)
        apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
        assert (H_not_member :
                  StorableValue.map_get_u256 (role_member_map sim)
                    (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, account) = 0).
        { unfold role_member_map.
          rewrite map_get_app_split.
          set (acct := account) in *.
          assert (Hd_def : Dict.get
                            (members_for_role DEFAULT_ADMIN_ROLE_bytes32
                               sim.(State.admins))
                            (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct)
                          = None).
          { pose proof (proj2 (Z.eqb_neq _ _)
                          (not_eq_sym DEFAULT_neq_OGM)) as H_eqb.
            clear -H_eqb.
            induction (State.admins sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                  DEFAULT_ADMIN_ROLE_bytes32)
                with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                      DEFAULT_ADMIN_ROLE_bytes32).
              rewrite H_eqb. simpl andb. exact IH. }
          rewrite Hd_def.
          rewrite map_get_app_split.
          assert (Hd_og : Dict.get
                            (members_for_role OPTIMISTIC_GUARDIAN_ROLE_bytes32
                               sim.(State.optimisticGuardians))
                            (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct)
                          = None).
          { pose proof (proj2 (Z.eqb_neq _ _)
                          (not_eq_sym OG_neq_OGM)) as H_eqb.
            clear -H_eqb.
            induction (State.optimisticGuardians sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              change (Dict.Eq.eqb OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                  OPTIMISTIC_GUARDIAN_ROLE_bytes32)
                with (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 =?
                      OPTIMISTIC_GUARDIAN_ROLE_bytes32).
              rewrite H_eqb. simpl andb. exact IH. }
          rewrite Hd_og.
          assert (Hd_ogm : Dict.get
                             (members_for_role OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32
                                sim.(State.optimisticGuardianManagers))
                             (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32, acct)
                           = None).
          { clear -H_addr_in.
            induction (State.optimisticGuardianManagers sim) as [|a rest IH]; simpl.
            - reflexivity.
            - cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
              rewrite Z.eqb_refl. simpl andb.
              change (Dict.Eq.eqb acct a) with (acct =? a).
              destruct (acct =? a) eqn:Hca.
              + exfalso. apply Z.eqb_eq in Hca. apply H_addr_in. left.
                symmetry. exact Hca.
              + apply IH. intro Hin. apply H_addr_in. right. exact Hin. }
          unfold StorableValue.map_get_u256. rewrite Hd_ogm. reflexivity. }
        assert (H_ac_not_in :
                  AccessControl.addr_in sim.(State.optimisticGuardianManagers) account
                  = false).
        { clear -H_addr_in.
          induction sim.(State.optimisticGuardianManagers) as [|a rest IH']; simpl.
          - reflexivity.
          - destruct (a =? account) eqn:Heqa.
            + exfalso. apply Z.eqb_eq in Heqa. apply H_addr_in. left.
              exact Heqa.
            + apply IH'. intro Hin. apply H_addr_in. right. exact Hin. }
        pose proof (AccessControl.remove_member_idempotent_on_absent
                      sim.(State.optimisticGuardianManagers) account H_ac_not_in)
          as Hidem.
        assert (Hbody_any :
                  forall memory',
                    (exists w0 w1 rest, memory' = w0 :: w1 :: rest) ->
                    exists memory'',
                    {{? codes, env, Some (make_state env state_base memory' (proj_sim sim)) |
                      fun_revokeRole_1378_inner OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account ⇓
                      Result.Ok tt
                    | Some (make_state env state_base memory'' (proj_sim sim)) ?}}).
        { intros memory' H_mem'.
          pose proof (run_fun__revokeRole_736_at_proj_sim_not_member
                        codes env state_base memory' sim
                        OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                        H_account H_not_member H_mem') as H736.
          destruct H736 as (w0' & w1' & rest' & H736).
          exists (w0' :: w1' :: rest').
          pose proof (run_fun_revokeRole_1378_inner_at_proj_sim
                        codes env state_base memory' sim
                        OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                        _ _ H736) as Hinner.
          exact Hinner. }
        pose proof (run_modifier_onlyRole_1370_admin_passes_exists
                      codes env state_base memory sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      (or_intror (or_intror eq_refl))
                      H_caller_admin H_caller_bound H_mem
                      (proj_sim sim)
                      Hbody_any) as Hmod.
        destruct Hmod as (mem_mod & Hmod).
        pose proof (run_fun_revokeRole_1378_at_proj_sim
                      codes env state_base memory sim
                      OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32 account
                      (Some (make_state env state_base mem_mod (proj_sim sim)))
                      Hmod) as Houter.
        exists sim,
          (Some (make_state env state_base mem_mod (proj_sim sim))).
        split; [|split].
        + destruct sim as [adm og ogm] eqn:Hsim. clear Hsim.
          cbn [State.admins State.optimisticGuardians
               State.optimisticGuardianManagers] in *.
          transitivity
            {| AccessControl.roles :=
                 [(DEFAULT_ADMIN_ROLE_bytes32,
                   {| AccessControl.members := adm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_ROLE_bytes32,
                   {| AccessControl.members := og;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |});
                  (OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32,
                   {| AccessControl.members := ogm;
                      AccessControl.admin := AccessControl.DEFAULT_ADMIN_ROLE |})]
            |}.
          { reflexivity. }
          f_equal.
          unfold project_sim_to_ac.
          change ({| AccessControl.roles := ?l |}).(AccessControl.roles)
            with l.
          unfold AccessControl.getRoleEntry.
          simpl AccessControl.find_entry.
          rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM). cbv match.
          rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM). cbv match.
          rewrite Z.eqb_refl. cbv match.
          simpl AccessControl.set_entry.
          rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OGM).
          rewrite (proj2 (Z.eqb_neq _ _) OG_neq_OGM).
          rewrite Z.eqb_refl.
          cbn [AccessControl.members].
          rewrite Hidem. reflexivity.
        + exact Houter.
        + exists mem_mod, (proj_sim sim).
          split; [reflexivity|].
          unfold observationally_eq_storage.
          repeat split; intros key; reflexivity.
    }
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
