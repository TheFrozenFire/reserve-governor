# OpenZeppelin version pin and drift mitigation

The equivalence-proof workstream is **version-locked to OpenZeppelin
5.4.0**. This note captures what "pinned" means in practice, how to
detect when OZ moves, and what to re-run when it does.

## Current pin

| Package | package.json range | pnpm-lock.yaml resolved | npm public latest (as of 2026-05-30) |
|---|---|---|---|
| `@openzeppelin/contracts` | `^5.4.0` | `5.4.0` | `5.6.1` |
| `@openzeppelin/contracts-upgradeable` | `^5.4.0` | `5.4.0` (patched) | `5.6.1` |

Sources of truth, in priority order:

1. **`pnpm-lock.yaml`** — the only artefact that actually determines
   the bytes pulled into `node_modules`. The relevant entries:

   ```yaml
   '@openzeppelin/contracts@5.4.0':
     resolution:
       integrity: sha512-eCYgWnLg6WO+X52I16TZt8uEjbtdkgLC0SUX/xnAksjjrQI4Xfn4iBRoI5j55dmlOhDv1Y7BoR3cU7e3WWhC6A==

   '@openzeppelin/contracts-upgradeable@5.4.0':
     resolution:
       integrity: sha512-STJKyDzUcYuB35Zub1JpWW58JxvrFFVgQ+Ykdr8A9PGXgtq/obF5uoh07k2XmFyPxfnZdPdBdhkJ/n2YxJ87HQ==
     peerDependencies:
       '@openzeppelin/contracts': 5.4.0
   ```

2. **`patches/@openzeppelin__contracts-upgradeable.patch`** — pnpm
   applies this patch on install. Patch hash:
   `0bffbc4488ca2b60087b08ff462cd91ca320c810d09c6f482aeda3b47280fcb4`.
   It widens the visibility of two ERC-7201 storage accessors from
   `private` to `internal` so derived contracts in the governor tree
   can reach them:
   - `GovernorUpgradeable._getGovernorStorage()`
   - `TimelockControllerUpgradeable._getTimelockControllerStorage()`

   Equivalence proofs are sensitive to this — the patched bodies are
   what `--ir-rocq` sees, not stock OZ.

3. **`package.json`** — declares `^5.4.0`, which on its own would
   accept any 5.x release ≥ 5.4.0. The lockfile is what actually
   restrains it. **Do not rely on the package.json range** to keep
   us at 5.4.0; a `pnpm install --no-frozen-lockfile` (or any tool
   that ignores the lockfile) will float us up to whatever is
   latest on the registry.

4. `node_modules/@openzeppelin/contracts/.git` is **absent** — pnpm
   installs tarballs, not git submodules. The integrity hash above
   is therefore the only verifiable per-byte fingerprint of what's
   on disk.

## What we actually use

`@openzeppelin/contracts-upgradeable` is a real runtime dependency,
not a dev-only one. Five governor contracts import from it:

```
contracts/governance/OptimisticSelectorRegistry.sol  (UUPSUpgradeable, Initializable)
contracts/governance/ReserveOptimisticGovernor.sol   (GovernorUpgradeable, UUPSUpgradeable, NoncesUpgradeable, Initializable)
contracts/governance/TimelockControllerOptimistic.sol (Initializable, UUPSUpgradeable)
contracts/governance/lib/ProposalLib.sol              (GovernorUpgradeable — read-only access)
contracts/staking/StakingVault.sol                    (ERC20Upgradeable, ERC4626Upgradeable, Initializable, UUPSUpgradeable)
```

The full curated allowlist that `ir-rocq-coverage --include-oz`
sweeps lives in the script as `OZ_ALLOWLIST` (12 entries from
`contracts`, 6 from `contracts-upgradeable`).

## Why this pin is load-bearing

Equivalence proofs under `rocq/proofs/equivalence/` are
**byte-for-byte sensitive** to the OZ source tree. Each proof shows
that a hand-written Coq simulation has the same observable
behaviour as a specific Yul IR — the Yul IR produced by the patched
solc-rocq from the exact OZ 5.4.0 sources currently on disk.

If OZ moves, the IR moves. If the IR moves, the proof needs to be
re-run. There is no "this proof was valid for 5.4.0 and will still
be valid for 5.4.1" hedge: even a no-op-looking refactor inside
OZ Governor (the audit-relevant base our `ReserveOptimisticGovernor`
inherits) can change the Yul output enough that proofs no longer
unify.

A non-exhaustive list of innocuous-looking OZ changes that would
invalidate proofs:

- Adding a `revert` reason string (changes constant pool layout).
- Reordering struct fields (changes storage slot layout — fatal).
- Inlining a helper function (changes the call graph).
- Tightening a `require` guard (changes the reachable-state set
  that simulations have to mirror).
- ERC-7201 storage-location bump (the keccak inputs change, so the
  hardcoded storage slot changes).

OZ's release history shows multiple of these per point release.

## Drift detection

The cheapest detector is `pnpm-lock.yaml`. Two checks land it:

1. **CI hard-fail on lockfile change.** Any PR that touches
   `pnpm-lock.yaml` and bumps `@openzeppelin/contracts*` should
   require a manual ack and a re-run of:

       bash formal-verification/scripts/ir-rocq-coverage --include-oz
       # and once equivalence proofs land:
       bash formal-verification/scripts/rocq-build

2. **Periodic version-drift check.** Compare the resolved version
   against the registry's latest:

       npm view @openzeppelin/contracts version
       npm view @openzeppelin/contracts-upgradeable version

   If they differ from `5.4.0`, that's not a bug, but it's a
   reminder that the proof corpus is N point releases behind. The
   decision to upgrade is a deliberate one with a re-prove cost.

A heavier detector is to checksum `node_modules/@openzeppelin/`
after install and compare against a stored manifest. That's
overkill given pnpm's integrity hash already does the same job.

## When OZ moves: the playbook

Assume someone has decided to upgrade OZ (e.g. for a security fix).
Steps, in order:

1. **Re-sweep IR.** `pnpm install` to refresh `node_modules`, then
   `bash formal-verification/scripts/ir-rocq-coverage --include-oz`.
   If any file now fails that previously passed, the `--ir-rocq`
   stage of the new OZ release is broken on the patched solc-rocq
   fork — investigate before going further.

2. **Re-sweep shallow embed.** `bash formal-verification/scripts/
   shallow-embed-sweep` for the targets currently in
   `SHALLOW_TARGETS`. Failures here are likely new
   `shallow_embed.py` gaps (catalogued in
   `notes/shallow_embed_oz_gaps.md`).

3. **Re-run equivalence proofs.** `bash formal-verification/scripts/
   rocq-build`. Every `Qed` that breaks is either:
   - a benign formatting change (likely fixable with the same proof
     structure, maybe a different unify target), or
   - a behavioural change in OZ that the simulation now has to
     mirror. This is the expensive case — re-prove from scratch.

4. **Re-apply the upgradeable patch.** The
   `private` → `internal` widening lives at
   `patches/@openzeppelin__contracts-upgradeable.patch`. If the
   surrounding OZ code has shifted, the patch may not apply cleanly
   and will need to be ported. The patch hash in `pnpm-lock.yaml`
   gates whether pnpm believes the patch is still valid.

5. **Bump the pin in this note.** Update the "Current pin" table
   with the new resolved version, new integrity hash, and the new
   `npm view` value.

## What the pin does *not* protect against

- **Solidity compiler upgrades.** We're locked to the rocq-of-
  solidity fork's bundled solc. If that fork rebases on a newer
  upstream solc, codegen for OZ 5.4.0 sources can shift. The fork
  pin lives in `formal-verification/scripts/solc-rocq` (via
  `ROCQ_TREE`); the consequence is identical to an OZ bump.
- **`patches/`.** A change to the upgradeable patch is itself a
  drift event — the patched bytes are what proofs see.
- **Transitive ESM/dev deps.** OZ has a handful of dev dependencies
  (`solhint`, etc.) that don't reach the compile graph; their drift
  is irrelevant to equivalence proofs but may break local tooling.

## Risk model summary

A routine OZ point release (5.4.0 → 5.4.1) is a **proof-invalidating
event**, full stop. The Governor audit-relevant base (OZ
`GovernorUpgradeable`) is routinely updated; assume any equivalence
proof against it will need to be re-run on every OZ bump until
upstream OZ stabilises (it won't — security backports happen).

The mitigation is procedural, not architectural: keep the pin
explicit, keep the re-sweep cheap, and treat an OZ bump like a
schema migration — a deliberate event with a known re-prove cost,
not a `pnpm up`.
