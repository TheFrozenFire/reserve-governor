# Threading the shared AccessControl mock across domains

This memo accompanies the new
[`mocks/AccessControl.v`](../rocq/mocks/AccessControl.v) and lays
out the per-domain integration path for the three Tier-4 contracts
that currently model OZ AccessControl locally.

The mock itself is complete and compiles cleanly. The per-domain
adaptations are deferred to a future round because they require
re-proving validity in each domain against the new state shape —
substantive work, no audit-narrative blocker.

---

## What the mock provides

`mocks/AccessControl.v` exports:

- `AccessControl.State` — the OZ-faithful role map
  `mapping(bytes32 role => (members : EnumerableSet<address>;
  adminRole : bytes32))`, encoded as `list (Role * RoleEntry)`.
- `hasRole`, `getRoleAdmin`, `getRoleEntry` — query helpers.
- `grantRole`, `revokeRole`, `renounceRole`, `setRoleAdmin` — the
  full OZ surface, gated by admin-of-admin lookups.
- `Valid.state` — invariant carrying no-duplicate role keys,
  no-duplicate members per role, and no-zero-address members.

## Current per-domain modelings

| Domain | Current role surface | Mock-side replacement |
|---|---|---|
| Guardian | 3 local role lists (admins, optimisticGuardians, optimisticGuardianManagers); Valid.state has 6 invariants over these | One `AccessControl.State` with 3 role-set entries; Valid.state defers to `AccessControl.Valid.state` |
| VersionRegistry | `is_owner` and `is_owner_or_emergency` as per-call Parameter predicates with axioms | `AccessControl.hasRole s OWNER caller` and `AccessControl.hasRole s EMERGENCY caller` as direct lookups |
| RewardTokenRegistry | Single `owner` Parameter predicate with axiom | `AccessControl.hasRole s OWNER caller` |

## The integration path

For each of the three domains, the adaptation is mechanical but
non-trivial:

1. **Replace the local role storage with an `AccessControl.State`
   field** in the domain's `State.t`. The Guardian's existing
   triple `(admins, optimisticGuardians, optimisticGuardianManagers)`
   becomes a single `acl : AccessControl.State` with three role
   entries.

2. **Rewrite role queries** (`has_admin`, `is_owner`, etc.) to
   call `AccessControl.hasRole`. Existing call sites pass the role
   constant; the lookup is structurally identical.

3. **Rewrite role-management operations** (`grantOptimisticGuardian`,
   `revokeRole`, etc.) to dispatch to
   `AccessControl.grantRole` / `revokeRole`. The mock's reverts
   match the existing per-domain reverts in shape.

4. **Adapt the domain's `Valid.state`** to require
   `AccessControl.Valid.state acl` as a sub-invariant. Existing
   no-dup / no-zero per-role-list invariants become consequences.

5. **Re-prove the existing validity-preservation lemmas** against
   the new shape. The proofs become simpler — they cite
   `AccessControl`-level lemmas rather than re-proving NoDup
   maintenance from scratch.

6. **Replace the `is_owner` / `is_owner_or_emergency` parameters
   and their axioms** in VersionRegistry / RewardTokenRegistry
   with `hasRole` lookups. The hierarchy axiom
   `owner_implies_owner_or_emergency` becomes a direct consequence
   of the admin chain in `AccessControl.State`.

## Why deferring is the right call

The adaptation is mechanical but **invasive**: it touches every
state-shape definition in the three Tier-4 domains, every
operation that reads or writes role state, and every validity
proof for those operations. Estimated scope: 4-6 hours of focused
work, all of it bookkeeping rather than new theorem content.

The current per-domain modelings are observably equivalent on
every audit-narrative claim (role gates work as expected, the
hierarchy axiom is sound by construction). The shared mock
provides the same observability with a single source of truth —
its value is in **reducing the trust surface** and **making the
admin-chain explicit**, not in unlocking new theorems.

A future contributor can pick up by adapting one domain at a
time, starting with VersionRegistry (smallest role surface — just
two roles). The mock is ready and tested; the work is purely
proof restructuring.

## Tracked

Future work: per-domain adaptation, three rounds (one per Tier-4
domain). Each round closes by re-proving validity + re-running
the matching CAS witness to confirm observational equivalence.
