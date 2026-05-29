(** Phase 3.3 (task #182) — Guardian equivalence scaffold.

    Guardian inherits from OpenZeppelin's [AccessControlEnumerable]
    and adds no own storage variables. Its on-chain storage is
    entirely OZ machinery:

      AccessControl:
        mapping(bytes32 => RoleData) private _roles;
        struct RoleData { mapping(address => bool) members; bytes32 adminRole; }

      AccessControlEnumerable adds:
        mapping(bytes32 => EnumerableSet.AddressSet) private _roleMembers;

    The sim ([simulations/Guardian.v]) abstracts the role machinery
    into

      State.roles : list (RoleId * Address)  (* set of grants *)
      State.admin_roles : list (RoleId * RoleId)

    Closing the equivalence requires:

      1. A projection from [State.roles] into both OZ structures:
         the [_roles[r].members[addr]] bool flag AND the
         [_roleMembers[r]] EnumerableSet.
      2. Adminr-role projection.
      3. Equivalence proofs for [grantRole], [revokeRole],
         [renounceRole], [_grantRole], [_revokeRole], [_setRoleAdmin]
         — each touches both the `_roles` mapping and the
         `_roleMembers` enumerable set.
      4. Reuse of RewardTokenRegistry's EnumerableSet projection
         (Phase 3.2).

    This file scaffolds the trust boundary. The full OZ AccessControl
    + AccessControlEnumerable equivalence is a multi-day effort and
    is parked behind the Phase 4 decision.

    The honest stance: Guardian's `audit_*` theorems hold against the
    sim's pure role-set abstraction. The contract's role-management is
    implemented by widely-deployed OZ libraries; treating that as a
    trusted base is the practical convention until OZ AccessControl
    is itself mechanized. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

(** ----- Trust-boundary documentation -----

    The Guardian sim's role-set is the abstraction. The contract's
    on-chain storage is OZ's [_roles] + [_roleMembers] mappings.
    Closure under sim ↔ contract requires:

      [OZ_AccessControl_correct]:
        forall role addr,
          sim_has_role role addr  <->
          on_chain_roles[role].members[addr] = true

      [OZ_AccessControlEnumerable_correct]:
        forall role,
          set_of (sim_has_role role) = enumerable_set_of (_roleMembers[role])

    Both predicates are folklore — OZ has the relevant invariants
    documented and audited — but neither is mechanized in this
    workstream. The sim-level theorems remain valid as long as the
    OZ libraries behave per their specification, which is the same
    trust assumption every audit treats as a given.

    No new projection functions live here; the file is a placeholder
    so [proofs/equivalence/] has consistent per-contract coverage. *)

Module GuardianEquivalence.

  (** Empty by design — see header. *)

End GuardianEquivalence.
