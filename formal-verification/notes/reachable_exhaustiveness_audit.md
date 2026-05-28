# Reachable-inductive exhaustiveness audit

Each Tier-5 negative theorem defines a `Reachable` inductive
enumerating the simulation transitions a contract's state can pass
through. If the inductive's constructor list omits any
state-mutating operation, the negative theorem says nothing about
sequences containing that operation — a silent coverage hole.

This memo audits each of the four `Reachable` inductives in the
tree against the matching simulation's actual operation surface.

**Conclusion: all four are exhaustive.** Either the constructor list
covers every state-mutating operation explicitly, or the inductive
uses a generic `R_step (... apply_op op s ...)` with `op : Op` where
the `Op` inductive itself enumerates all operations.

## 1. UnstakingManager (`proofs/UnstakingManager_no_double_spend.v:120`)

```
Inductive Reachable : State.t -> Prop :=
| R_empty
| R_step (s : State.t) (op : Op) (s' : State.t) :
    Reachable s -> apply_op op s = Result.Success s' -> Reachable s'.
```

with `Op` defined as:

```
Inductive Op : Set :=
| OpCreate (vault user : Address) (amount unlockTime : U256.t)
| OpCancel (lockId : U256.t) (caller : Address)
| OpClaim  (lockId : U256.t) (now : U256.t).
```

Simulation operations on `UnstakingManager.State.t` (from
`simulations/UnstakingManager.v`):

| Operation | Constructor | Notes |
|---|---|---|
| `createLock` | `OpCreate` | full match |
| `cancelLock` | `OpCancel` | full match |
| `claimLock` | `OpClaim` | full match |
| `set_lock` | n/a | private helper, not externally callable |

**Result: exhaustive.** Every external entry point in the
simulation has a corresponding `Op` constructor.

## 2. Timelock (`proofs/Timelock_single_shot.v:140`)

```
Inductive Reachable : State.t -> Prop :=
| R_empty
| R_step (s s' : State.t) (o : Op) :
    Reachable s -> apply_op s o = Result.Success s' -> Reachable s'.
```

with `Op` covering the four Timelock operations:
`OpSchedule`, `OpExecute`, `OpCancel`, `OpBypass`.

Simulation operations on `Timelock.State.t` (from
`simulations/Timelock.v`):

| Operation | Constructor | Notes |
|---|---|---|
| `scheduleBatch` | `OpSchedule` | full match |
| `executeBatch` | `OpExecute` | full match |
| `cancel` | `OpCancel` | full match |
| `executeBatchBypass` | `OpBypass` | full match |
| `set_state_ts` | n/a | private helper |

**Result: exhaustive.** Every external entry point in the
simulation has a corresponding `Op` constructor.

## 3. Governor (`proofs/Governor_no_double_execution.v:365`)

This one has 9 specific constructors rather than a single `R_step
over Op`, so exhaustiveness must be argued constructor-by-constructor.

Simulation operations on `Governor.Proposal.t` (from
`simulations/Governor.v`):

| Operation | Reachable constructor |
|---|---|
| `fresh_optimistic` | `reach_fresh_opt` |
| `fresh_standard_child` | `reach_fresh_std` |
| `add_veto` | `reach_add_veto` |
| `transition_to_pessimistic` (parent leg) | `reach_transition_parent` |
| `transition_to_pessimistic` (child leg) | `reach_transition_child` |
| `mark_std_succeeded` | `reach_mark_std_succeeded` |
| `queue_operations` | `reach_queue` |
| `execute_standard` | `reach_execute_standard` |
| `execute_optimistic` | `reach_execute_optimistic` |
| `cancel` | `reach_cancel` |

**Result: exhaustive.** All 9 simulation operations + the two legs
of `transition_to_pessimistic` are explicitly named.

Note on the sentinel-encoded transition
(`transition_to_pessimistic_sentinel` in
`proofs/Governor_no_de_escalation.v`): the parallel sentinel form
lives in the proof file, not the simulation, so it doesn't
participate in the canonical Reachable. Audit #101 records that
the sentinel encoding is observationally equivalent to the
phase-direct form on every audit-narrative theorem.

The Governor case warrants an explicit meta-lemma since the
constructor list is hand-maintained. Added as
`Governor_no_double_execution.reach_step_covers_all_ops` (see file).

## 4. ProposerThrottle (`proofs/Integration_no_throttle_bypass.v:98`)

```
Inductive Reachable_throttle_sequence
    (capacity : U256.t) : Throttle.t -> Throttle.t -> nat -> Prop :=
| Reachable_init ...
| Reachable_step ... consume t_mid capacity now = Result.Success t_next.
```

Simulation operations on `ProposerThrottle.Throttle.t` (from
`simulations/ProposerThrottle.v`):

| Operation | Reachable form | Notes |
|---|---|---|
| `consume` | `Reachable_step` | full match |
| `readCharge` | n/a | pure query, doesn't mutate state |
| `proposalsAvailable` | n/a | pure query |

**Result: exhaustive.** `consume` is the only state-mutating
operation; the throttle's read-only queries don't change state and
don't need a Reachable transition.

## Audit posture

This memo serves as the standing exhaustiveness certificate. If a
future contributor adds a new state-mutating operation to any of
the four simulations, they MUST also extend the matching `Op`
inductive (for UnstakingManager/Timelock) or add a new constructor
(for Governor), then revisit this memo. The Governor meta-lemma
acts as a compile-time canary for that last case.

No new pending coverage gaps surfaced by this audit.
