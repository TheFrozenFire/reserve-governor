# Reserve Governor Rocq proof tree

This directory holds the Coq 8.20.1 simulations and proofs for the
Reserve Governor contracts (`contracts/governance/`,
`contracts/staking/`).

## File-pattern conventions

Mirrors the protocol repo's per-domain tier shape:

| File pattern | Role |
|---|---|
| `simulations/<Domain>.v` | Pure functional model of the production contract — written by hand in Gallina, with a `Storage.t` record (or a math kernel for pure libraries), the public operation signatures, and a `Valid.t` predicate carrying the invariants the operations maintain. |
| `proofs/<Domain>.v` | Domain-level helpers — calibration constants (e.g. `rt_genesis_storage`), per-shape arithmetic lemmas (e.g. `stake_genesis_eq`), and any rewrites that the rest of the tree consumes. |
| `proofs/<Domain>_xcheck.v` | Cross-check theorems pinning the simulation against concrete witness values from production deployments / CAS scripts. Closed by `vm_compute` over named witnesses. |
| `proofs/<Domain>_validity.v` | The `_preserves_validity` lemma for each public operation. Establishes that each operation lands in a state satisfying `Valid.t`, given the operation's natural preconditions. |
| `proofs/<Domain>_chain.v` | Composition theorems — `op1_then_op2_preserves_validity` shape. Captures the production sequencing patterns (e.g. `payoutRewards();rewardRatio = val;`) and proves the composed transition is sound. |
| `proofs/<Domain>_witnesses.v` | Numerical witnesses — `vm_compute`-closed reflexivity theorems on the calibration corpus. Each `W<N>_<predicate>` is a witness anchoring one CAS probe. |
| `proofs/<Domain>_uint256_bounds.v` | The `InputBounded.t` predicate (uint256 ceilings on storage scalars) and per-field bound projections used at integration sites where the full `Valid.t` is too heavy. |
| `Audit.v` | Audit-facing index. Re-exports every decision-relevant theorem via `Notation audit_<feature> := ...`. Read top-to-bottom for the headline coverage map. |

## Logical library

The governor's Rocq tree maps `-R . ReserveGovernor`. Theorems are
accessible as `ReserveGovernor.simulations.Foo` etc. This is distinct
from the protocol repo's `Reserve.*` namespace so cross-repo
namespaces don't collide if the two trees are ever loaded together.

## Quick build

```sh
bash scripts/rocq-build               # all files in _RocqProject
bash scripts/rocq-build simulations/StakingVault.v  # single file
```

The build requires Coq 8.20.1 and a built
[`rocq-of-solidity`](https://github.com/formal-land/rocq-of-solidity)
checkout at `$HOME/git/reserve/_tools/rocq-of-solidity` (override with
`ROCQ_TREE`). Each file is timeout-wrapped at 180s by default — see
[`WISDOM.md`](WISDOM.md) R001/R012 on tactic-explosion symptoms.

## Where to start reading

Start with [`Audit.v`](Audit.v): it surfaces every theorem the audit
cares about, with one-paragraph context for each. Drill into the
underlying `_validity` / `_chain` files only as needed.
