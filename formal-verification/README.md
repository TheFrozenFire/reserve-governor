# Formal verification for the Reserve Governor

The Reserve Governor implements a hybrid optimistic / standard
governance flow on top of an OpenZeppelin `Governor` foundation, a
custom ERC4626 `StakingVault` with dual delegation, a time-locked
`UnstakingManager`, and a single `TimelockControllerOptimistic` that
covers both proposal paths.

This directory holds the formal-verification scaffold for that
system: a Rocq proof tree (`rocq/`), a PARI/GP CAS-witness layer
(`cas/`), a Certora CVL spec tree (`certora/`), and per-component
audit notes (`notes/`). A complementary Halmos symbolic-test file
(`test/HalmosChecks.t.sol`) lives alongside the Foundry suite in
the governor checkout's `test/`.

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

A fourth tool — **Halmos** — sits alongside (not at the same
tier as) the three primary layers. Halmos symbolically executes
Foundry test functions named `check_*`, reasoning about every
input within a bounded loop budget. It serves as a *spec-reuse
bridge*: a Foundry differential test can be re-expressed as a
symbolic check with minimal effort, promoting "passes on random
fuzz inputs" to "passes for every input the SMT solver can
enumerate within bound."

## What each layer covers, governor-side

| Domain | Rocq | CAS | Certora | Why |
|---|---|---|---|---|
| StakingVault: exchange-rate evolution under deposit/redeem | ✓ | ✓ | ✓ | ERC4626 arithmetic with rounding; CAS sweeps the rounding boundary, Rocq pins monotonicity, Certora confirms zero-edge mapping bytecode-side. |
| StakingVault: dual-delegation checkpoint independence | ✓ | – | ✓ | OZ `ERC20Votes` checkpoint book over two ledgers (standard + optimistic). Certora `delegateOptimisticIsCallerScoped` confirms scope at the bytecode. |
| StakingVault: multi-token rewards accounting | ✓ | ✓ | ✓ | Triple-confirmation on the reward-index monotone evolution. Conservation against the external ERC20 mock is the tightest form, bridging internal counters to actual on-chain balance. |
| UnstakingManager: time-locked withdrawal queue | ✓ | – | ✓ | Per-lock lifecycle and conservation across arbitrary sequences of create / cancel / claim. |
| ProposalLib: proposer throttle (12h sliding window) | ✓ | ✓ | ✓ | Triple-confirmation on charge replenishment, cap saturation, and consume-debits-unit. |
| OptimisticSelectorRegistry: `(target, selector)` whitelist | ✓ | – | ✓ | EnumerableSet-backed allowlist with forbidden-target rejection and cross-set consistency invariants. |
| ReserveOptimisticGovernor: fast-vote → slow-vote escalation | ✓ | – | ✓ | State-machine theorems in Rocq + Certora. Channel separation between optimistic and standard paths is explicitly partitioned. |
| TimelockControllerOptimistic: bypass vs scheduleBatch ordering | ✓ | ✓ | ✓ | Triple-confirmation on bypass preserving the slow-path operation-id discipline. |
| Veto-coalition reachability (Cantina-class) | – | – | ✓ | Intent-derived in Certora as a structural invariant over arbitrary parameters; refactor-resistant form of the audit-narrative claim. |
| Access control across all governance contracts | ✓ | – | ✓ | Per-domain role gates in Rocq + Certora auth rules across every contract. |
| Reentrancy on `claimRewards` (zero-first pattern) | ✓ | – | partial | Explicit outer-inner-outer interleaving model proves the inner reentrant call extracts zero. |
| Flash-loan resistance (snapshot-based voting) | ✓ | – | ✓ | Trace208 past-vote correctness plus `vetoDelay`-separates-blocks at the structural level. |
| EIP-712 signature delegation (`delegateOptimisticBySig`) | ✓ | – | – | ECDSA + Nonces mocks back signer-binding, replay-rejection, and cross-chain / cross-contract hash injectivity. Foundry differential tests cross-validate the axioms against the deployed implementations. |
| Pure-arithmetic state-machine bounds | ✓ | ✓ | ✓ | Halmos symbolic verification on throttle cap saturation, charge bound, and consume-debits-unit; complements the Rocq theorems at the EVM-arithmetic level. |
| Per-lock lifecycle state machine (UnstakingManager) | ✓ | – | – | Halmos symbolic checks on the lifecycle-subset harness: terminal states are absorbing (no-double-cancel / no-double-claim / no-claim-after-cancel / no-cancel-after-claim), premature claims revert, per-call structural transitions hold for every input. |

(✓ = applies; – = not applicable, or out of scope)

## Coverage by theorem type

The headline theorems re-exported in `rocq/Audit.v` fall into a
dozen distinct *kinds* of property, each targeting a specific
class of bug. A single contract surface is typically covered by
several theorem kinds; the overlap is what makes the corpus
robust against any single missing-spec failure.

| Theorem kind | What it proves | Why it matters |
|---|---|---|
| **Construction-boundary validation** | Every operator takes well-typed inputs (a `Valid.t` precondition) and produces well-typed outputs across both success and revert branches. | Closes "garbage in, undefined behavior out." Validates at the boundary; internal functions can trust their inputs unconditionally. The DDD discipline of "validate at boundaries, trust the interior" made formally explicit. |
| **Conservation laws** | Sum-preservation: total active stake, totalClaimed, balanceAccounted, vault asset balance — equal across any reachable sequence of operations. Includes the form that binds the internal counter to the external ERC20 balance directly, so conservation is stated against ground truth rather than an internal proxy. | Closes the canonical "value escapes" exploit shape. |
| **Adversarial unreachability (negative theorems)** | Certain state transitions cannot occur from certain states: no-double-execute, no-de-escalation post-sentinel, no-claim-after-cancel, no-double-spend across arbitrary sequences. | Closes liveness violations that aren't observable from individual operator correctness. These catch the "each step is fine, the composition isn't" class. |
| **Cross-domain integration** | Composed properties across boundaries: Governor + Timelock execution chain, StakingVault + UnstakingManager withdrawal conservation, VersionRegistry + StakingVault upgrade authorization, vault balance equals deposits + active locks. | Closes the most common audit-finding category: each piece is fine, the seams aren't. Bridges domain ownership boundaries with formal guarantees. |
| **End-to-end existence witnesses** | Constructive proofs that the happy path is reachable: optimistic lifecycle, standard lifecycle. Each constructs a concrete sequence of operations witnessing successful execution. | Confirms the model isn't vacuously safe by being unreachable. The structural dual of unreachability theorems — proves life-without-attack is possible. |
| **Intent-derived rules (Certora)** | Audit-narrative claims expressed as parametric structural invariants over all reachable states, not scenario tests over specific configurations. | Catches the *wrong-spec* bug class: errors where every layer's existing rules pass but the rules themselves don't capture what the narrative actually requires. The scenario form is fast for CI; the structural form is heavy but refactor-resistant. |
| **External-dependency mocks + axiomatic bindings** | Minimal Gallina models of the OpenZeppelin / PRBMath surfaces the governor depends on: AccessControl, ERC20, Trace208, PRBMath, ECDSA, Nonces. Each carries explicit `Valid.t` preconditions and theorem-level axioms. | Localizes trust surface: every theorem citing an external function must explicitly cite the axiom backing it. Trust assumptions are observable, not hidden. |
| **Differential validation of axioms** | Foundry tests that exercise each mock axiom against the deployed implementation across production-realistic ranges: PRBMath `powu` decay arithmetic, ECDSA recovery + EIP-712 hashing, ERC4626 share semantics. | Detects axiom-implementation drift before it propagates into proofs. The bridge between theorem-time assumptions and runtime behavior. |
| **Symbolic verification (Halmos)** | `check_*` functions reasoning about every input the SMT solver can enumerate within bound — used where the underlying arithmetic is shallow enough to be tractable (e.g. the proposer-throttle bounds). | Promotes "passes on random fuzz inputs" to "passes for every input the symbolic engine can decompose." Complements Rocq's unbounded proofs at the EVM-arithmetic level. |
| **Flash-loan resistance** | Past-vote correctness via the OZ-checkpoint mock (post-snapshot acquisitions are invisible at snapshot-time lookup) plus structural separation of the snapshot block from the proposal-creation block via positive `vetoDelay`. | Closes the flash-loan-amplified voting attack class. Converts the implicit "vetoDelay protects us" reviewer claim into machine-checked structural defense. |
| **Reentrancy via interleaving model** | Explicit outer-inner-outer call sequencing of `claimRewards` — the inner reentrant call observes the outer's `accruedRewards = 0` write and extracts zero. | Converts "this comment says the zero-first pattern is safe" into compile-time enforcement. Applies the "load-bearing comments must become theorems" discipline to the most-cited reentrancy defense. |
| **Triple-confirmation (Rocq + CAS + Certora)** | The same property proved logically (Rocq), witnessed numerically (CAS), and confirmed bytecode-side (Certora). The three failure modes (logical hole / modeling error / source-vs-bytecode divergence) are orthogonal. | The highest-confidence form of guarantee. Used for the load-bearing arithmetic — exchange rate evolution, multi-token rewards, throttle, timelock bypass — where any single layer's failure shape would silently corrupt downstream reasoning. |

The corpus is cross-referenced against three external catalogs
(see "Maturity classification" below): the OWASP smart-contract
threat taxonomy, the Trace2Inv invariant-template catalog, and
the Trail of Bits maturity framework. Each catalog row points
back to one or more of the kinds above. The catalogs are
different *views* of the same underlying theorems, not different
coverage.

## Where to start

| If you want to... | Read |
|---|---|
| See the Rocq headline theorems | [`rocq/Audit.v`](rocq/Audit.v) |
| See the Certora coverage matrix | [`certora/README.md`](certora/README.md) |
| Understand the intent-derived rule methodology | [`certora/notes/cantina_pr36_postmortem.md`](certora/notes/cantina_pr36_postmortem.md) |
| Browse the governance-shape bug catalog | [`certora/notes/governance_intent_and_shapes.md`](certora/notes/governance_intent_and_shapes.md) |
| See the OWASP threat-category cross-reference | [`notes/owasp_2026_coverage.md`](notes/owasp_2026_coverage.md) |
| See the Trace2Inv invariant-template cross-reference | [`notes/trace2inv_template_coverage.md`](notes/trace2inv_template_coverage.md) |
| See the Trail of Bits maturity positioning | section "Maturity classification" below |
| Understand a specific component's math | `rocq/simulations/<Component>.v` |
| Audit the modeling fidelity | [`notes/simulation_fidelity_audit.md`](notes/simulation_fidelity_audit.md) |
| See `--ir-rocq` compile coverage of every contract | [`notes/ir_rocq_coverage.md`](notes/ir_rocq_coverage.md) |
| Read the Rocq / Certora footgun catalogs | [`rocq/WISDOM.md`](rocq/WISDOM.md), [`certora/WISDOM.md`](certora/WISDOM.md) |

## Maturity classification

The Reserve Governor's defense-in-depth posture against private-
key compromise sits at **Level 3** of the Trail of Bits
smart-contract maturity framework, with several paths backed by
Level-4-adjacent immutability theorems.

| Component | Maturity | Backing |
|---|---|---|
| `ReserveOptimisticGovernor` | L3 — timelock + 4 distinct roles (proposer, executor, canceller, admin) + optimistic-vs-standard channel separation | Per-role authorization theorems in Rocq + Certora; channel-separation intent rule |
| `TimelockControllerOptimistic` | L3 — proposer/executor/canceller role split + scheduled-delay enforcement | Triple-confirmation on bypass / scheduling / single-shot execution |
| `StakingVault` | L3 — admin role for upgrades, gated by `VersionRegistry.deprecated`. L4-adjacent on upgrade authorization: the upgrade path is permission-checked structurally, not arbitrarily settable | Integration theorem bridging the registry to the vault's `_authorizeUpgrade` |
| `VersionRegistry` | L3 — `IRoleRegistry.isOwner` for register, `isOwnerOrEmergencyCouncil` for deprecate | Role-gated register / deprecate theorems |
| `UnstakingManager` | L4-adjacent — no admin functions post-deploy; lockup mechanics are pure-state-machine | Conservation, no-double-spend, total-active-bounded |
| `Guardian` | L3 — two-tier (admin unrestricted + guardian conditional on proposal state) | Role-discriminator theorems for the two-tier cancel path |
| `RewardTokenRegistry` | L3 — `IRoleRegistry`-gated register/unregister | Owner-required theorems on register and unregister |
| `OptimisticSelectorRegistry` | L3 — owner-gated add/remove with forbidden-target catalog | NoDup invariants + forbidden-target rejection theorems |
| `ProposerThrottle` | Structural rate-limit — not role-gated, but per-account state-machine bounded | Cap saturation, replenish monotone, consume-debits-unit; Halmos symbolic confirmation on the same properties |
| `ProposalLib` | L3 — proposer-role check + description-suffix proposer-binding | Proposal-id injectivity, restricted-proposer rejection, role-gate enforcement |
| Flash-loan resistance | L3 — `vetoDelay > 0` separates snapshot from proposal-creation block; post-snapshot acquisitions are invisible | Trace208 past-vote correctness + structural snapshot-separation theorems |
| Reentrancy guard on `claimRewards` | L3 — zero-first ordering machine-checked under outer-inner-outer interleaving | Explicit reentrancy-interleaving model + inner-extracts-zero theorem |

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

1. **Threat catalog (attacks)** — [OWASP Smart Contract Top 10](notes/owasp_2026_coverage.md), the canonical attack-class taxonomy
2. **Defensive-pattern catalog (invariants)** — [Trace2Inv templates](notes/trace2inv_template_coverage.md), the empirically-validated invariant catalog
3. **Defense-in-depth catalog (architecture)** — Trail of Bits maturity framework, the structural posture documented above

When the three matrices read positive on overlapping rows, the
underlying proof is doing its job. When they disagree, the gap
points at either a missing theorem or a missing framing — both
are signals worth chasing.

## Toolchain

Four toolchains support the four verification surfaces.

- **Rocq + opam** for the proof tree under `rocq/`. The build
  script (`scripts/rocq-build`) drives `coqc` over the files
  listed in `rocq/_RocqProject` and supports per-file timeouts
  via `RB_TIMEOUT` to guard against tactic-explosion hangs.
- **PARI/GP** for the CAS-witness layer under `cas/`. Each script
  prints `OK` / `FAIL` per probe; `cas/run-check.sh` runs the full
  set.
- **Certora Prover** (open-source upstream) for the CVL spec tree
  under `certora/`. Activated via a single sourced env script;
  individual specs run with `certoraRun.py certora/<Contract>/<Contract>.conf`.
- **Halmos** (`pipx install halmos` or `uv tool install halmos`)
  for the symbolic-test layer under `test/Halmos*.t.sol`
  (governor checkout). Run with `halmos --match-contract '^Halmos'`.
  The Foundry config emits Solidity AST in artifacts (`ast = true`),
  which Halmos parses to drive symbolic execution.

The Rocq fork of `solc` that emits `--ir-rocq` IR
(`rocq-of-solidity`) is shared across protocol and governor
repos; the governor's build scripts locate it via the `ROCQ_TREE`
environment variable.

Per-component install instructions live alongside each
toolchain's directory. Build-script environment variables
(`ROCQ_TREE`, `REPO_TREE`, `OPAM_SWITCH`, `RB_TIMEOUT`,
`SOLC_ROCQ_MODE`, `DOCKER_CONTEXT`) are documented at the top of
`scripts/rocq-build`.

## Running the verification

```sh
# Rocq + CAS — fast, local
bash formal-verification/scripts/rocq-build
bash formal-verification/cas/run-check.sh

# Foundry + Halmos — from the governor checkout root
forge test
halmos --match-contract '^Halmos'

# Certora — one spec at a time
source <certora env>
certoraRun.py formal-verification/certora/<Contract>/<Contract>.conf
```

`rocq/generated/` is the canonical landing path for `--ir-rocq`
output of every governor contract — the Rocq encoding of each
contract's Yul-translated semantics. The directory is checked in,
the outputs are gitignored: regenerate locally via

```sh
bash formal-verification/scripts/ir-rocq-coverage
```

The path being stable lets equivalence proofs under
`proofs/equivalence/` `Require` generated modules by name
(`ReserveGovernor.generated.<ContractName>`) without conditional
logic, while the outputs themselves remain local working artefacts
that don't decay the repository on every contract source change.

`solc-rocq` selects the fastest available path automatically
(native binary where one exists, container fallback otherwise);
the choice can be forced via `SOLC_ROCQ_MODE`.

## Print Assumptions snapshot (audit drift detector)

The equivalence-layer proofs in `rocq/proofs/equivalence/` close
against a small named set of trust axioms. The
[`scripts/print-assumptions-snapshot`](scripts/print-assumptions-snapshot)
script captures `Print Assumptions <Theorem>` for every milestone
Theorem in that tier, writes one `.txt` per milestone plus a
summary CSV / markdown table, and diffs against a checked-in
baseline.

```sh
# Run + diff (exit 1 on drift, 0 if matches baseline).
OPAM_SWITCH=rocq820 bash formal-verification/scripts/print-assumptions-snapshot

# Refresh the baseline after intentionally tightening or adding axioms.
OPAM_SWITCH=rocq820 bash formal-verification/scripts/print-assumptions-snapshot --refresh-baseline
```

The baseline lives at
[`rocq/print_assumptions_snapshot/baseline/`](rocq/print_assumptions_snapshot/baseline/)
— check it in. Per-run output goes to
`rocq/print_assumptions_snapshot/current/` (gitignored). See
[`rocq/print_assumptions_snapshot/README.md`](rocq/print_assumptions_snapshot/README.md)
for the full audit-value framing and refresh discipline.

This is local-runnable instrumentation, not CI-wired. Its value
is the human-readable diff that surfaces "did this commit add a
new trust axiom?" — the falsifiable form of Audit.v's Caveat-5
trust-budget claim.
