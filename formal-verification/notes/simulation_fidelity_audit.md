# Simulation fidelity audit (Reserve Governor)

The `simulations/<Domain>.v` files under `rocq/simulations/` are
hand-written Gallina models of the production contracts. The proof
tree's invariants are stated and proved against these models, not
against the Solidity directly. Any divergence between simulation and
production is a gap the proofs do not cover.

This file is the audit catalog: cross-cutting findings that recur
across simulations, followed by per-simulation summaries.

Status: scaffold only. Sections fill in as simulations land.

---

# Part 1 — Cross-cutting findings

## 1. Edge-case guards

For each simulation, the question is: does the simulation handle all
the input edge cases that the production contract handles, and does
it do so with the same semantics (return value, revert, no-op)?

| Simulation | Zero-input handling | Empty-collection | Terminal-state | Observations |
|---|---|---|---|---|
| _(to be populated as simulations land)_ | | | | |

## 2. Live-state vs deployment-time arguments

When production stores a parameter (so governance can mutate it
mid-flight), does the simulation either store it (allowing mutation)
or take it as a function arg (making it a frozen snapshot)?
Mismatches mean proofs apply to a frozen-snapshot model that the
production contract never sees.

| Simulation | Storage params | Frozen-arg params | Mutation operations modeled? |
|---|---|---|---|
| _(to be populated)_ | | | |

## 3. Storage layout vs `_uint256_bounds.v`

Production storage uses packed integer types (`uint48`, `uint176`,
`uint192`) chosen for slot-packing efficiency. Each simulation's
`Valid.t` predicate should bound storage values at the *production*
type's ceiling, not the looser `<= UINT256_MAX`.

| Field (production type) | Production limit | Simulation `Valid.t` bound | Notes |
|---|---|---|---|
| _(to be populated)_ | | | |

## 4. `Result.t` vs `option` vs total-with-`Valid` encoding

How does each simulation surface production reverts? The protocol
repo settled on three encodings:

- `Result.t` (two-constructor inductive) for Yul-equivalence-bearing
  paths where revert offsets matter.
- `option` for plain success/failure boundary cases (e.g. governance
  setters).
- Total functions with `Valid`-hypothesis preconditions when the
  precondition is naturally discharged at call sites.

Mark each simulation's choice as it lands.

| Simulation | Encoding | Reverts modeled |
|---|---|---|
| _(to be populated)_ | | |

---

# Part 2 — Per-simulation summaries

Each section follows the protocol-repo template: state omitted,
operations omitted, what the simulation faithfully models,
implications for proof transferability.

## StakingVault

_(scaffold)_

The production contract: ERC4626 share vault with vote-locking
(inherits OZ `ERC20Votes`), dual delegation (standard + optimistic
ledgers), multi-token rewards, and an unstaking delay enforced
through the companion `UnstakingManager`.

## UnstakingManager

_(scaffold)_

Time-locked withdrawal queue. Created by `StakingVault.initialize()`.
Mirrors the per-account shape of the protocol's StRSR draft queue but
with a per-token delay timer rather than the protocol's
seizure-driven era model.

## ReserveOptimisticGovernor

_(scaffold)_

OZ-Governor-based contract with two parallel proposal flows
(optimistic and standard) that share the same proposal storage. The
key state-machine claim to formalize: an optimistic proposal that
accumulates AGAINST-votes above the veto threshold spawns a
confirmation vote under a new proposal ID, atomically and exactly
once.

## OptimisticSelectorRegistry

_(scaffold)_

EnumerableSet-backed whitelist of `(target, selector)` pairs. The
basic property: membership is preserved across add/remove operations.

## TimelockControllerOptimistic

_(scaffold)_

Single timelock with two execution paths:
- `scheduleBatch()` followed by `executeBatch()` after the delay
  (standard path).
- `executeBatchBypass()` (optimistic path).

The key invariant: the bypass path does not interfere with queued
standard-path operations.

## ProposalLib (proposer throttle)

_(scaffold)_

Per-account 12-hour sliding-window throttle for optimistic proposals.
Same shape as the protocol's `Throttle.sol` library, with the
throttle struct owned by the governor contract rather than the
RToken.

---

# Part 3 — Parked workstreams

Items deferred for future iteration. Add as work surfaces them.

- _(none yet)_
