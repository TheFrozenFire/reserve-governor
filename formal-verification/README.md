# Triple-track verification: Rocq + CAS + Certora for Reserve Governor

The Reserve Governor implements a hybrid optimistic / standard
governance flow on top of an OpenZeppelin `Governor` foundation, a
custom ERC4626 `StakingVault` with dual delegation, a time-locked
`UnstakingManager`, and a single `TimelockControllerOptimistic` that
covers both proposal paths.

This directory holds the formal-verification scaffold: a Rocq 8.20.1
proof tree (`rocq/`), a PARI/GP CAS-witness layer (`cas/`), a Certora
CVL spec tree (`certora/`), and per-component audit notes (`notes/`).

## Why three layers

A formal verification effort has three distinct failure modes, each
attacked by a different layer:

1. **Logical unsoundness**: the proof has a hole, the lemma chain
   doesn't actually establish what it claims.
2. **Modeling error**: the proof is impeccable, but the abstract
   model the proof reasons about doesn't faithfully capture what the
   production code does.
3. **Source-vs-bytecode divergence**: the source-level model is
   faithful, but the compiled bytecode behaves differently due to
   solc lowering, optimizer interactions, or calldata-edge cases.

The three layers bracket the same property from three sides:

- The **Rocq layer** (`rocq/`) proves *logical soundness* on a
  hand-written Gallina simulation: under the assumptions of the
  model, the invariant holds for all inputs and all reachable
  traces. Strength: inductive reasoning over sequences of operations,
  conservation laws, telescoping bounds, no-double-spend across
  arbitrary call histories. Audit notations are re-exported in
  `rocq/Audit.v`.
- The **CAS layer** (`cas/`) validates *modeling faithfulness*: the
  claimed identities and bounds actually agree with concrete
  computation across calibrated parameters. Strength: rounding-
  direction sweeps, fixed-point math witnesses, numerical convergence.
- The **Certora layer** (`certora/`) confirms *source-vs-bytecode
  agreement*: the CVL rules verify properties against the TAC IR
  generated from solc output. Strength: per-method parametric rules,
  modifier-expansion ordering, calldata edges, TOCTOU patterns,
  bytecode-level confirmation that source-language theorems survive
  lowering.

These three failure modes are **orthogonal**. A property the team
needs to trust ought to be verified at every layer it can plausibly
be expressed at — the **triple-confirmation pattern** (Rocq proves
it, CAS witnesses it, Certora confirms it bytecode-side) gives the
highest-confidence guarantee.

The Rocq + CAS pattern is borrowed verbatim from the protocol repo's
`formal-verification/`. The Certora layer is new with the governor
work and was added after the Cantina contest surfaced a class of
*wrong-spec* bug that neither Rocq nor CAS could catch (see
`certora/notes/cantina_pr36_postmortem.md`).

## What each layer covers, governor-side

| Domain | Rocq | CAS | Certora | Why |
|---|---|---|---|---|
| StakingVault: exchange-rate evolution under deposit/redeem | ✓ | ✓ | ✓ | ERC4626 arithmetic with rounding; CAS sweeps the rounding boundary, Rocq pins monotonicity, Certora confirms zero-edge mapping bytecode-side. |
| StakingVault: dual-delegation checkpoint independence | ✓ | – | ✓ | OZ `ERC20Votes` checkpoint book over two ledgers (standard + optimistic). Certora `delegateOptimisticIsCallerScoped` confirms scope at the bytecode. |
| StakingVault: multi-token rewards accounting | ✓ | ✓ | ✓ | Triple-confirmation (`audit_rewards_index_monotone` + `multi_token_rewards.gp` INV-1 + Certora SV10-SV13). Conservation invariant remains Rocq-only — Certora cannot close it without a harness MockERC20 (see WISDOM C020). |
| UnstakingManager: time-locked withdrawal queue | ✓ | – | ✓ | Lifecycle U1–U9 in Certora; conservation under arbitrary sequences in Rocq. |
| ProposalLib: proposer throttle (12h sliding window) | ✓ | ✓ | ✓ | Triple-confirmation (`audit_throttle_consume_storage_delta` + `charge_evolution.gp` INV-2 + Certora ThrottleLib 7 rules + intent ThrottleBound 5 rules). Full 2*capacity bound captured in CVL via inductive decomposition (TB1+TB5+TB2). |
| OptimisticSelectorRegistry: `(target, selector)` whitelist | ✓ | – | ✓ | EnumerableSet-backed; Certora hits HAVOC pathology on the cross-slot consistency (see WISDOM C004) — symmetric provable directions covered. |
| ReserveOptimisticGovernor: fast-vote → slow-vote escalation | ✓ | – | ✓ | State machine R1–R16 in Certora; no-de-escalation theorem in Rocq. Channel separation explicitly partitioned in `intent/ChannelSeparation.spec` (CS1–CS4). |
| TimelockControllerOptimistic: bypass vs scheduleBatch ordering | ✓ | ✓ | ✓ | Triple-confirmation (`audit_timelock_bypass_preserves_slow_path` + `scheduling_ordering.gp` INV-5 + Certora T1–T10 plus boundary precision pair). |
| Veto-coalition reachability (Cantina-class) | – | – | ✓ | Intent-derived in Certora alone; the scenario rule + structural invariant pair caught the PR #36 wrong-supply-denominator on the pre-fix contract. |
| Reentrancy / access control | – | – | partial | Auth rules in Certora across all 9 contracts. Direct re-entry modeling not feasible under NONDET token summaries — captured indirectly via CEI rules (UnstakingManager U5+U9). |

(✓ = applies; – = doesn't apply yet, or out of scope)

## Where to start

| If you want to... | Read |
|---|---|
| See the Rocq headline theorems | [`rocq/Audit.v`](rocq/Audit.v) |
| See the Certora coverage matrix | [`certora/README.md`](certora/README.md) |
| Understand the intent-derived rule methodology | [`certora/notes/cantina_pr36_postmortem.md`](certora/notes/cantina_pr36_postmortem.md) |
| Browse the governance-shape bug catalog | [`certora/notes/governance_intent_and_shapes.md`](certora/notes/governance_intent_and_shapes.md) |
| See OWASP-2026 threat-category coverage | [`notes/owasp_2026_coverage.md`](notes/owasp_2026_coverage.md) |
| See Trace2Inv invariant-template coverage | [`notes/trace2inv_template_coverage.md`](notes/trace2inv_template_coverage.md) |
| See Trail of Bits maturity-framework positioning | section "Maturity classification" below |
| Understand a specific component's math | `rocq/simulations/<Component>.v` (e.g. `StakingVault.v` once added) |
| Audit the modeling fidelity | [`notes/simulation_fidelity_audit.md`](notes/simulation_fidelity_audit.md) |
| See `--ir-rocq` compile coverage of every contract | [`notes/ir_rocq_coverage.md`](notes/ir_rocq_coverage.md) |
| Read the Rocq / Certora footgun catalogs | [`rocq/WISDOM.md`](rocq/WISDOM.md), [`certora/WISDOM.md`](certora/WISDOM.md) |
| Reproduce the CAS sweeps | `bash cas/run-check.sh` |
| Build the whole Rocq tree | `bash scripts/rocq-build` |
| Run a single Certora spec | `source ~/git/reserve/_tools/certora/env.sh && certoraRun.py certora/<Contract>/<Contract>.conf` |
| Run the Halmos symbolic checks | `halmos --match-contract HalmosChecks` (governor checkout) |
| Regenerate `--ir-rocq` coverage matrix | `bash scripts/ir-rocq-coverage` |

## Maturity classification

The Reserve Governor's defense-in-depth posture against private-
key compromise sits at **Level 3** of the [Trail of Bits maturity
framework](https://blog.trailofbits.com/2025/06/25/maturing-your-smart-contracts-beyond-private-key-risk/),
with several paths backed by Level-4-adjacent immutability
theorems.

| Component | Maturity | Theorem(s) backing the claim |
|---|---|---|
| `ReserveOptimisticGovernor` | L3 — timelock + 4 distinct roles (proposer, executor, canceller, admin) + optimistic-vs-standard channel separation | `audit_governor_no_double_execution`, `audit_governor_optimistic_cannot_be_queued`, `audit_governor_execute_standard_requires_queued`; Certora S33 channel-separation, S31 veto-coalition reachability |
| `TimelockControllerOptimistic` | L3 — proposer/executor/canceller role split + scheduled-delay enforcement | `audit_timelock_no_double_execute`, `audit_timelock_op_done_persists`; Certora `Timelock.spec` |
| `StakingVault` | L3 — admin role for upgrades, gated by `VersionRegistry.deprecated`. L4-adjacent on upgrade authorization (the upgrade path is permission-checked structurally, not arbitrarily settable). | `audit_integration_upgrade_authorization` |
| `VersionRegistry` | L3 — `IRoleRegistry.isOwner` for register, `isOwnerOrEmergencyCouncil` for deprecate | `audit_version_register_requires_owner` |
| `UnstakingManager` | L4-adjacent — no admin functions post-deploy; lockup mechanics are pure-state-machine | `audit_unstaking_createLock_conservation`, `audit_unstaking_no_double_spend`, `audit_unstaking_total_active_bounded` |
| `Guardian` | L3 — two-tier (admin unrestricted + guardian conditional on proposal state) | `audit_guardian_cancel_with_state_admin_unrestricted`, `audit_guardian_cancel_with_state_guardian_path` |
| `RewardTokenRegistry` | L3 — `IRoleRegistry`-gated register/unregister | `audit_reward_token_register_not_owner_reverts`, `audit_reward_token_register_preserves_validity` |
| `OptimisticSelectorRegistry` | L3 — owner-gated add/remove with forbidden-target catalog | per-domain `audit_selector_registry_*` (NoDup invariants + forbidden-target rejection) |
| `ProposerThrottle` | structural rate-limit — not role-gated (anyone can call), but per-account state-machine bounded | `audit_throttle_consume_success_iff_available`, `audit_throttle_consume_storage_delta`, `audit_throttle_preserves_validity`, `audit_proposalsAvailable_le_capacity`; Halmos `check_Throttle*` symbolic confirmation |
| `ProposalLib` | L3 — proposer-role check + description-suffix proposer-binding | `audit_proposal_id_injective`, `audit_proposal_rejects_restricted_proposer`, `audit_proposal_optimistic_role_gate`; Certora `ProposalLib.spec` |
| Flash-loan resistance | L3 — vetoDelay > 0 separates snapshot from proposal-creation block; post-snapshot acquisitions are invisible | `audit_flash_loan_*` (3 theorems in `Flash_loan_resistance.v`) |
| Reentrancy guard | L3 — zero-first ordering in `claimRewards` machine-checked under outer-inner-outer interleaving | `audit_reentrancy_*` (5 theorems in `StakingVaultRewardsReentrancy.v`) |

The framework's L4 ("radical immutability") is unreachable for a
*governance* contract — the whole point is to be administrable by
the protocol's DAO. The closest L4-adjacent claims are
`UnstakingManager` (no post-deploy admin) and the upgrade-
authorization path (constrained by the version registry rather
than arbitrarily settable). Both have explicit theorems backing
the claim.

### Three framing axes

The corpus is cross-referenced against three external catalogs.
Each row of each catalog points at the same underlying artifacts;
the catalogs are different *views* of the coverage, not different
coverage:

1. **Threat catalog (attacks)** — [OWASP Smart Contract Top 10 (2026)](notes/owasp_2026_coverage.md): 10 of 10 categories addressed
2. **Defensive-pattern catalog (invariants)** — [Trace2Inv templates (FSE 2024)](notes/trace2inv_template_coverage.md): 14 of 14 applicable templates addressed
3. **Defense-in-depth catalog (architecture)** — Trail of Bits maturity framework: L3 with L4-adjacent paths documented above

When all three matrices read positive on overlapping rows, the
underlying proof is doing its job. When they disagree, the gap
points at either a missing theorem or a missing framing — both
are signals worth chasing.

## Toolchain

**Rocq + CAS side:**

- **Coq 8.20.1** (`coq-hammer-tactics`, `coq-coqutil`,
  `coq-record-update`)
- **rocq-of-solidity** at `$HOME/git/reserve/_tools/rocq-of-solidity`
  (shared with the protocol repo — single checkout, two consumers).
  Both the Rocq library and the `solc-rocq` solc fork are pre-built;
  the governor scripts reuse those artifacts via the `ROCQ_TREE` env
  var.
- **PARI/GP** (`gp` on PATH) for the CAS layer
- **GNU coreutils** for `timeout`/`gtimeout` (already required by the
  protocol repo's build script — same prereq)
- **colima** (`colima start rocq`) — required only when falling back
  to docker mode (`SOLC_ROCQ_MODE=docker`, or hosts without the patched
  native binary). The script defaults to the current Docker context;
  override via `DOCKER_CONTEXT`. On macOS arm64 with the patched
  native binary in place this fallback is unused.

**Certora side:**

- **Certora Prover (local build)** at
  `$HOME/git/reserve/formal-verification/CertoraProver`. Built from
  the open-sourced upstream with a single Gradle wrapper bump
  (7.2 → 8.5) to run on JDK 21. See `certora/WISDOM.md` C007 for the
  build-reproducibility notes.
- **JDK 21** (Homebrew `openjdk@21`)
- **Z3 4.15.4** (Homebrew `z3`) + **CVC5 1.3.4** (downloaded
  macOS-arm64-static from `cvc5/cvc5` releases)
- **LLVM** (Homebrew `llvm`) — for `llvm-symbolizer` and
  `llvm-dwarfdump` that the Certora native helpers need
- **Rust 1.81+** (1.93-nightly used here) + `rustfilt`
- **Graphviz** for TAC-report rendering
- **solc 0.8.28** matching the contracts' pragma

Toolchain activation:
```sh
source ~/git/reserve/_tools/certora/env.sh
```
That single source line sets `JAVA_HOME`, the `$CERTORA` env var, the
PATH for `certoraRun.py`, and activates the Python venv with the
Certora CLI's Python deps. See `certora/README.md` for the full
layout.

See the protocol repo's `formal-verification/README.md` for the
Rocq + CAS install steps; the governor repo uses the same toolchain
there. The Certora side is governor-specific (the protocol repo
doesn't currently have a Certora layer).

## Smoke test

A minimal end-to-end check of the toolchain lives at
`contracts/Smoke.sol` → `rocq/generated/Smoke.v`. After Colima is
running and rocq-of-solidity is built:

```sh
bash scripts/solc-rocq --ir-rocq formal-verification/contracts/Smoke.sol \
  > formal-verification/rocq/generated/Smoke.v
bash formal-verification/scripts/rocq-build generated/Smoke.v
```

The full build runs the smoke target by default (it's listed in
`rocq/_RocqProject`).

### Cost model and known limitations

`solc-rocq` picks the fastest available path:

- linux/x86_64 hosts: native solc, no container.
- macOS / arm64 hosts: native arm64 solc if
  `$ROCQ_TREE/build/solc/solc.macos-patched` exists (see the fork at
  `TheFrozenFire/rocq-of-solidity`, branch
  `fix/rocq-length-error-and-macos-build`), otherwise the upstream
  amd64 ELF run inside `coqorg/coq` under `--platform=linux/amd64` (slow:
  QEMU emulation costs ~1000×).
- Override with `SOLC_ROCQ_MODE=native|docker`.

Reference points on M-class native arm64 with the patched binary
(see `notes/ir_rocq_coverage.md` for the full matrix):

- `Smoke.sol`: ~10 ms.
- `Guardian.sol`: <1 s, 23 k-line Rocq IR.
- Heavy OZ-integrated contracts (`StakingVault` 107 k,
  `ReserveOptimisticGovernor`/`OptimisticSelectorRegistry`/`ProposalLib`
  ~194 k each, `Deployer` 325 k, `TimelockControllerOptimistic` 63 k):
  all compile cleanly in 1–2 s.

**All 22 governor contracts compile clean** through `--ir-rocq` with
the patched fork (re-run `scripts/ir-rocq-coverage` to verify). The
prior `std::length_error` crash on the long-name OZ-integrated set is
fixed at `Object::toRocq` in the fork.

One known cosmetic issue remains: when a single source file pulls in
multiple compilation units, the generated Rocq output appends a
top-level `Definition codes` per unit, so feeding that file straight
into `coqc` errors with `codes already exists`. This is harmless for
contract-by-contract IR inspection but blocks naively concatenated
builds; fix would be to scope each unit into its own module
(upstream-fork change, still parked).

The practical implication mirrors the protocol repo's experience:
**hand-written simulations in `rocq/simulations/` are the primary
verification path**, and `--ir-rocq` cross-checks are an
opportunistic parked workstream — useful when they work, but not
blocking.

## Build-script env vars

The build scripts pick up overrides from the environment:

| Var | Default | What it controls |
|---|---|---|
| `ROCQ_TREE` | `$HOME/git/reserve/_tools/rocq-of-solidity` | Where the shared rocq-of-solidity checkout lives. |
| `REPO_TREE` | self-located from script | The governor repo root (the parent of `formal-verification/`). |
| `OPAM_SWITCH` | unset | If set, `eval $(opam env --switch=$OPAM_SWITCH)` is run before `coqc`. |
| `RB_TIMEOUT` | `180` | Per-file `coqc` timeout in seconds. |
| `SOLC_ROCQ_MODE` | auto-detect | Force `native` or `docker`. Default picks native on linux/x86_64, and on macOS arm64 if `solc.macos-patched` exists; otherwise docker. |
| `DOCKER_CONTEXT` | current default | Which Docker context to use in docker mode. |
