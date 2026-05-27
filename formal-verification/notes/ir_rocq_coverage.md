# `--ir-rocq` compile coverage of governor contracts

Sweep of every governor source file declaring a `contract` or `library`
(pure interfaces excluded), each compiled individually through
`solc-rocq --ir-rocq`. Regenerate with:

```sh
bash formal-verification/scripts/ir-rocq-coverage
```

The script exits non-zero on any failure, so it can be wired into CI.

## Current matrix

All numbers are wall-clock seconds and Rocq-IR line counts from a single
sweep on M-class macOS arm64 against the patched native solc-rocq
(`solc.macos-patched`).

| File | secs | Rocq IR lines |
|---|---:|---:|
| `contracts/Deployer.sol` | 2 | 324 940 |
| `contracts/Guardian.sol` | <1 | 23 147 |
| `contracts/VersionRegistry.sol` | <1 | 8 341 |
| `contracts/artifacts/GuardianDeployer.sol` | 1 | 456 |
| `contracts/artifacts/OptimisticSelectorRegistryDeployer.sol` | <1 | 456 |
| `contracts/artifacts/ProposalLibDeployer.sol` | <1 | 456 |
| `contracts/artifacts/ReserveOptimisticGovernanceVersionRegistryDeployer.sol` | <1 | 456 |
| `contracts/artifacts/ReserveOptimisticGovernorDeployer.sol` | <1 | 456 |
| `contracts/artifacts/ReserveOptimisticGovernorDeployerDeployer.sol` | <1 | 456 |
| `contracts/artifacts/RewardTokenRegistryDeployer.sol` | <1 | 456 |
| `contracts/artifacts/StakingVaultDeployer.sol` | <1 | 456 |
| `contracts/artifacts/ThrottleLibDeployer.sol` | <1 | 456 |
| `contracts/artifacts/TimelockControllerOptimisticDeployer.sol` | <1 | 456 |
| `contracts/artifacts/utils/DeployHelper.sol` | <1 | 228 |
| `contracts/governance/OptimisticSelectorRegistry.sol` | 1 | 194 476 |
| `contracts/governance/ReserveOptimisticGovernor.sol` | 1 | 194 476 |
| `contracts/governance/TimelockControllerOptimistic.sol` | 1 | 63 215 |
| `contracts/governance/lib/ProposalLib.sol` | 1 | 194 476 |
| `contracts/governance/lib/ThrottleLib.sol` | <1 | 2 929 |
| `contracts/staking/RewardTokenRegistry.sol` | <1 | 9 915 |
| `contracts/staking/StakingVault.sol` | 1 | 107 364 |
| `contracts/staking/UnstakingManager.sol` | 1 | 8 963 |

**22 / 22 PASS, 0 FAIL.**

## What unblocked this

Two prior blockers, both now resolved:

1. **`std::length_error` crash in `Object::toRocq`** (rocq-of-solidity fork).
   Padding to 32-byte boundaries computed `64 - hex_name.size()` as
   `size_t`, underflowing whenever the Yul-side object name
   (`<contract>_<id>` or `…_deployed`) exceeded 32 bytes. Every modern
   OZ-derived contract hit this. Fixed by rounding hex length up to the
   next 64-character (32-byte) boundary:
   `padTo = ((hex.size() + 63) / 64) * 64`. Patched at both
   `libyul/Object.cpp` and `libyul/AsmRocqConverter.cpp`. Branch:
   `TheFrozenFire/rocq-of-solidity:fix/rocq-length-error-and-macos-build`.
   Regression test at `test/cmdlineTests/ir_rocq_long_contract_name/`.

2. **Foundry remappings not visible to solc-rocq**. The wrapper passed
   `--base-path` and `--include-path node_modules` but never expanded
   `remappings.txt`. Source files using `@interfaces/`, `@governance/`,
   `@staking/`, `@utils/`, `@src/` couldn't resolve their imports. The
   wrapper now reads `remappings.txt` from `REPO_TREE` and passes each
   `prefix=path` line as a positional argument to solc (solc's native
   remapping syntax — there's no dedicated flag).

## What this coverage doesn't yet prove

- **The generated IR isn't yet fed into `coqc`.** A single .sol that
  pulls in multiple compilation units emits multiple top-level
  `Definition codes` blocks, so `coqc <file>.v` errors with
  `codes already exists`. Fix is upstream-fork: scope each unit into
  its own `Module`. Until then, the IR is useful for inspection but
  the cross-check workstream stays parked behind hand-written
  simulations.
- **No semantic equivalence.** Compile-passing only says solc-rocq
  produced *some* IR. Whether that IR faithfully captures the
  contract's storage layout, ABI, or runtime behaviour is a separate
  question that the hand-written `rocq/simulations/` answer for the
  surfaces that matter to the proof tree.

## Why this matters anyway

A compiling `--ir-rocq` pipeline across every governor contract is the
floor for any future cross-check work. Until this commit, the
toolchain dropped most of our heavy contracts on the floor; nothing
useful could be derived without re-running the broken upstream and
hoping it survived. With 22/22 green and a regeneration script, any
regression in the fork or in our remapping plumbing is immediately
visible.
