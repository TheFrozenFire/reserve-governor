# Certora local-prover coverage

Certora Prover built from source — runs entirely on this machine, no
cloud account. Lives at `~/git/reserve/formal-verification/CertoraProver/`.

## Quick run

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/Guardian/Guardian.conf
```

Every `<Contract>/<Contract>.conf` in this directory runs the same way.

## Coverage matrix

| Contract | Spec dir | Rules VERIFIED |
|---|---|---|
| Guardian | `Guardian/` | 7 |
| UnstakingManager | `UnstakingManager/` | 10 |
| RewardTokenRegistry | `RewardTokenRegistry/` | 7 |
| OptimisticSelectorRegistry | `OptimisticSelectorRegistry/` | 10 |
| TimelockControllerOptimistic | `Timelock/` | 10 |
| VersionRegistry | `VersionRegistry/` | 7 |
| ReserveOptimisticGovernor | `Governor/` | 16 |
| StakingVault | `StakingVault/` | 17 |
| ThrottleLib (library) | `ThrottleLib/` | 7 |
| **Total** | | **91** |

Coverage shaped by two adversarial review passes:

- **First pass synthesis**: `notes/adversarial_synthesis.md` (five
  reports). Headline find: three of four angles flagged Guardian G6
  missing. P0 fixes landed G6a/G6b, UnstakingManager U8, and a
  VersionRegistry header disclosure.

- **Second pass** addressed all P1-P3 findings via six parallel
  sub-agents:
  - **P1**: Governor lifecycle rules (R13-R16) — `optimisticProposal-
    CannotBeQueued`, `acceptsOnlyAgainst`, `needsNoQueuing`,
    `cancelRequiresCancellerOrProposer`.
  - **P2 TC1**: ThrottleLib harness contract + 7 storage-delta /
    refill / capacity rules. Triple-confirmation with Rocq's
    `audit_throttle_consume_storage_delta` + CAS
    `charge_evolution.gp` INV-2.
  - **P2 TC2**: StakingVault rewards monotonicity (SV10-SV13).
    Triple-confirmation with Rocq's `audit_rewards_index_monotone`
    + CAS `multi_token_rewards.gp` INV-1.
  - **P2 TC3**: Timelock cross-id preservation (T8-T10).
    Triple-confirmation with Rocq's `audit_timelock_bypass_preserves_
    slow_path` + CAS `scheduling_ordering.gp` INV-5.
  - **P3 Governor**: R11-R12 added (upper-bound + persistence) plus
    ghost-backed `_.hasRole` fidelity upgrade.
  - **P3 misc**: SelectorRegistry +3 forbidden-target rules + R6 fix,
    UnstakingManager U9 (CEI re-entrancy half), StakingVault +4
    custom-error rules.

See `notes/exploration_rocq_cas_alignment.md` for the Rocq+CAS-
informed priority ranking that drove the P2 selections.

Plus `spike/Vault.{sol,spec,conf}` — a deliberately-broken-and-fixed
toy contract that proves the toolchain catches planted bugs (4 VERIFIED
+ 1 intentional VIOLATED).

## What's covered, by surface

- **Role gates** on every privileged setter and admin operation across
  all 8 contracts. Non-role callers are proven to revert.
- **Zero-address and zero-value rejections** at entry points that
  validate their inputs (deployer, reward token, account, deployer
  interface).
- **State invariants:** deprecation flag flip and isolation across
  hashes (VersionRegistry); registered/unregistered consistency
  (RewardTokenRegistry); deposit mints exact shares to receiver
  (StakingVault); convertTo{Shares,Assets}(0) == 0 (StakingVault).
- **Lifecycle properties:** lock cannot be claimed before unlock
  (UnstakingManager); double-claim reverts (UnstakingManager);
  scheduled op cannot be re-scheduled while pending (Timelock); revoke
  removes role (Timelock); cancel auth-gated (Guardian).
- **Single-shot:** bypass marks op done; bypass on existing op reverts
  (Timelock).
- **Parameter validation:** throttle capacity bounds, veto threshold
  bounds, veto delay/period minimums (Governor).
- **Update-timelock immutability:** Governor.updateTimelock always
  reverts.
- **Optimistic-delegation scope:** delegateOptimistic only changes the
  caller's delegate (StakingVault).

## What's NOT covered (deferred)

These are documented in the per-contract spec headers:

- **Full ERC4626 monotonicity** of `convertToShares` / `convertToAssets`
  across the whole uint256 range. OZ's `mulDiv` overflow boundary blows
  the solver budget. The zero edges are pinned; full-range needs
  bounded-state scoping or an explicit overflow invariant.
- **Set-membership cross-invariants** that depend on OZ's `EnumerableSet`
  internal `_positions` ↔ `_values` consistency. Certora's storage
  HAVOC treats those mappings as independent, so it can construct
  internally-inconsistent set states. Two contracts hit this
  (RewardTokenRegistry, OptimisticSelectorRegistry); the symmetric
  provable directions land, the inverse directions are deferred.
- **Full propose/queue/execute state machine** (Governor) — covered by
  Rocq simulation and proofs in `formal-verification/rocq/`.
- **Reward accrual math** (StakingVault) — `UD60x18.powu` is unbounded
  loop; covered by Rocq + PARI/GP CAS witness.
- **`getLatestVersion` reverts-when-unset** (VersionRegistry) — needs a
  ghost invariant tying `latestVersion` to `deployments[]`.
- **`delegateOptimisticBySig`** (StakingVault) — sig-recovery path.
- **`_authorizeUpgrade`** (StakingVault).

## Toolchain layout

```
~/git/reserve/
├── _tools/certora/
│   ├── env.sh                 # source me to activate the env
│   ├── bin/                   # cvc5, solc8.28, solc -> solc8.28
│   └── out/                   # $CERTORA — emv.jar, tac_optimizer, copied scripts
└── formal-verification/
    └── CertoraProver/         # cloned + built source
        ├── build/libs/        # emv.jar (-> shadow jar w/ deps)
        ├── fried-egg/         # Rust subproject -> tac_optimizer
        ├── scripts/           # certoraRun.py + sibling python packages
        └── .venv/             # python deps (activated by env.sh)
```

## Build reproducibility

The CertoraProver source assumes a Certora-published Docker image
(`public.ecr.aws/certora/cvt-image:...`). To build natively on macOS
arm64, the wrapper Gradle 7.2 had to be bumped to 8.5 (in
`gradle/wrapper/gradle-wrapper.properties`) so it can run on JDK 21.
That single edit is the only diff from upstream.

Versions used in this install:
- Gradle 8.5
- JDK 21 (Homebrew openjdk@21)
- Kotlin 1.9.20 (declared in gradle.properties)
- Z3 4.15.4 (Homebrew z3)
- CVC5 1.3.4 (downloaded macOS-arm64-static from cvc5/cvc5 releases)
- LLVM 22.1.6 (Homebrew llvm; for llvm-symbolizer / llvm-dwarfdump)
- Rust 1.93-nightly (cargo + rustfilt via cargo install)
- Graphviz 15 (Homebrew graphviz; for tac-report rendering)
- solc 0.8.28 (matches governor pragma)

## Conf template (use this as a starting point)

```json
{
    "files": ["contracts/path/to/File.sol:ContractName"],
    "verify": "ContractName:formal-verification/certora/ContractName/ContractName.spec",
    "solc": "solc8.28",
    "packages": [
        "@openzeppelin/contracts=node_modules/@openzeppelin/contracts",
        "@openzeppelin/contracts-upgradeable=node_modules/@openzeppelin/contracts-upgradeable",
        "@interfaces=contracts/interfaces",
        "@utils=contracts/utils",
        "@governance=contracts/governance"
    ],
    "optimistic_hashing": true,
    "optimistic_loop": true,
    "loop_iter": 3,
    "use_relpaths_for_solc_json": true,
    "msg": "Auth and state verification (ASCII only)"
}
```

Notes on the flags:
- `"files": ["File.sol:Contract"]` — required when filename and
  contract name differ (e.g., `VersionRegistry.sol` defines
  `ReserveOptimisticGovernanceVersionRegistry`).
- `"optimistic_hashing": true` — needed any time a function does
  `keccak256(abi.encodePacked(string))` or other variable-length hashes.
- `"optimistic_loop": true` + `"loop_iter": N` — needed for loops over
  dynamic arrays (e.g., Timelock's `_execute`, OZ Governor's
  `_executor()`).
- `"use_relpaths_for_solc_json": true` — needed for contracts not at
  `contracts/<Name>.sol`. Without it, Certora's path-matching fails on
  subdirectories like `governance/` and `staking/`.
- For deep inheritance (e.g., Governor's OZ chain), add
  `"disable_internal_function_instrumentation": true` to work around a
  path-normalization bug in Certora's autofinder recompile pass.

## Watch out

### Toolchain

- **Stale Kotlin daemon.** The Kotlin compile daemon has a 2-hour idle
  timeout and gets reused across Gradle invocations. If you change JDK
  versions and the build mysteriously fails with
  `UnsupportedClassVersionError`, run `pkill -f KotlinCompileDaemon`.

- **`emv.jar` vs `emv-0.4-jar-with-dependencies.jar`.** The slim
  `emv.jar` has no Main-Class manifest entry. The runnable one is the
  shadow jar. The env.sh setup symlinks `emv.jar` -> the shadow jar.

- **Non-ASCII in `msg` field.** The conf parser rejects em-dashes,
  plus signs, and other non-ASCII in string fields. ASCII only.

- **Cloud vs local.** `is_local()` in `Shared/certoraUtils.py` returns
  true iff `$CERTORA/emv.jar` exists and the conf doesn't pass
  `server`. Don't add a `server` field unless you want a cloud run.

### CVL footguns

- **`^` is XOR, not exponent.** `10^18 == 24` because XOR. Use the
  literal `1000000000000000000` for 1e18. If you see a rule "VERIFIED"
  on a condition that looked suspicious, sanity-check the constant.

- **Interface-typed parameters need address casts.** If a function
  takes an interface type (e.g., `IReserveOptimisticGovernorDeployer
  deployer`), `f(e, 0)` fails to typecheck. Pass an address-typed
  variable instead: `address zero; require zero == 0; f(e, zero);`.

- **CVL `external` summary on contract-self-call does NOT propagate.**
  If an OZ base contract internally calls `this.foo()` (or directly
  calls the contract's own external function via JUMP), the `external`
  summary you wrote on `foo()` is bypassed. Either summarize the
  internal helper directly, or restructure the rule.

- **Vacuity entries showing under "Failures summary" in stdout are not
  failures.** A vacuity check with `status=VERIFIED` and
  `nodeType=VIOLATED_ASSERT` is the *desired* state — it means the
  rule's preconditions are satisfiable. Read the JSON status report
  (`Reports/treeView/treeViewStatus_*.json`), not the stdout summary.

### Solidity-side footguns

- **EnumerableSet cross-slot HAVOC.** OZ's `EnumerableSet` uses
  `(_positions, _values)` where `_positions[v]` is a 1-indexed slot.
  Certora's storage exploration treats those two mappings as
  independent, so it can construct states where `_positions[v]=3` but
  `_values[2] != v`. Rules like "register adds to set" or "remove
  doesn't affect other elements" may VIOLATE on pathological initial
  states. Workaround: state symmetric provable directions, or use
  `requireInvariant` to encode the cross-slot consistency.

- **Initial-state assumptions.** Certora explores arbitrary storage
  states by default. Rules like "function reverts when storage is in
  its initial value" need explicit `require state == initial_value`
  preconditions; you cannot rely on `latestVersion == 0` just because
  Solidity zero-initializes storage.

## Per-contract status JSON dump

After any run, the per-rule status lives in
`<RUN_DIR>/Reports/treeView/treeViewStatus_*.json`. Quick extractor:

```sh
RUN_DIR=$(ls -dt emv-*-certora-* | head -1)
python3 -c "
import json, glob
files = sorted(glob.glob(f'$RUN_DIR/Reports/treeView/treeViewStatus_*.json'))
with open(files[-1]) as f: data = json.load(f)
def walk(n, d=0):
    if 'name' in n and 'status' in n:
        print(f'{\"  \"*d}{n[\"name\"][:55]:55} status={n.get(\"status\",\"?\")} type={n.get(\"nodeType\",\"\")}')
    for c in n.get('children', []): walk(c, d+1)
for r in data.get('rules', []): walk(r)
"
```

A clean run has every ROOT-type rule at `status=VERIFIED`. Vacuity
SANITY children with `nodeType=VIOLATED_ASSERT` and `status=VERIFIED`
are passing sanity checks.
