# Adversarial review synthesis — 2026-05-31

Six independent agents audited the equivalence-proof corpus from distinct
vantages. Their findings converge on a single core diagnosis: **the milestone
Qeds compile, but most of them constrain almost nothing about actual
contract behavior**. The vapor is concentrated at the equivalence-binding
layer; the mock and simulation layers are sound.

## Vantage summaries

| Vantage | File | Headline |
|---|---|---|
| Walker-completeness | `walker_completeness_auditor.md` | 25/45 composite walker axioms are DOUBTFUL or HAND-WAVING |
| Sim-vs-source | `sim_vs_source_auditor.md` | 3 CRITICAL semantic mismatches — ERC4626 formula bug is worst |
| Skolemization-soundness | `skolemization_soundness_auditor.md` | 18/25 milestones VACUOUS or VACUOUS² |
| Multi-base composition | `multi_base_composition_auditor.md` | ~43 no-op trust items across multi-base files |
| Wave-2-pending | `wave2_pending_auditor.md` | 5 files have stale claims; ROG never imports GovernorBase |
| Trust-axiom | `trust_axiom_auditor.md` | 8 CRITICAL + 8 HIGH + 12 MEDIUM = 28 findings; logical bug in cancel quantification |

## Cross-vantage convergence — high-confidence findings

These findings were flagged by ≥3 independent vantages. They are
high-confidence because multiple distinct review methodologies converged.

### CCV-1: Reflexive observational bridges (3 vantages: Skolemization, Wave-2, Multi-base, Trust-axiom)

The R070 "observational bridge axiom" pattern across StakingVault* and
ReserveOptimisticGovernor is implemented as

```coq
Axiom proj_post_<fn>_observes :
  storage_equiv (proj_post_<fn> ...) (proj_post_<fn> ...).
```

with `storage_equiv := eq` (or reflexive predicate). The same Skolem term
appears on both sides. The bridges are tautologies — they constrain
nothing about the post-state. Discovered by Skolemization, confirmed by
Wave-2-pending, mechanically catalogued by Multi-base (14 instances), and
verified by Trust-axiom via Print Assumptions.

**Affected files:** `StakingVaultExchange.v` (4), `StakingVaultAdmin.v` (7),
`ReserveOptimisticGovernor.v` (3), parts of `TimelockControllerOptimistic.v`.

**Severity: CRITICAL.** Until refactored, every milestone in these files
constrains only "some post-state exists" — not what it is.

### CCV-2: Section-bound milestone vapor (2 vantages: Wave-2, Multi-base, Skolemization)

`StakingVaultDelegation.v` wraps all four milestone theorems in
`Section StakingVaultDelegationSection` with `Variable`s for the walker,
state, projection, lens, and `Hypothesis` for the walker axiom. Section
closure universally quantifies these. **No inheritor instantiates the
Section.** `Print Assumptions` shows only `deployment_id` and
`Set is impredicative` because everything else gets universally quantified
away.

**Severity: CRITICAL.** The milestones are theorems about ANY walker /
ANY storage, not about StakingVault's specific implementation. They have
zero content against actual contract bytecode until the Section is
instantiated.

### CCV-3: Free-Parameter walker functions (2 vantages: Wave-2, Skolemization, Trust-axiom)

`StakingVaultExchange.v` declares `fun_<op>_op : U256.t -> ... -> M.t U256.t`
as opaque `Parameter`s rather than as `Notation`s aliasing the actual
shallow form's `fun_deposit_4312_inner` etc. The shallow form is wired in
`_RocqProject` but `StakingVaultExchange.v` doesn't `Require` it. Result:
the milestone Qeds are about an abstract function, not about the deployed
Yul body.

**Severity: CRITICAL.** Trivial to fix (uncomment the import, replace
Parameters with Notations) but currently rendering 4 milestones empty.

### CCV-4: ROG ↔ GovernorBase disconnection (2 vantages: Wave-2, Multi-base, Walker-completeness)

`ReserveOptimisticGovernor.v` was scaffolded as "Wave 2 binding pending
GOV-BASE", but GovernorBase landed BEFORE ROG. The file has 16 comment-
level references to GovernorBase and three "Wave 2 binding placeholder"
blocks. **It never `Require Import`s `GovernorBase`.** All four
`_isOptimistic` branch axioms (Section 7) assert
`storage_equiv (proj_post X) (proj_post X)` with the same Skolem on both
sides, so the optimistic-vs-pessimistic dispatch has zero proof content.

**Severity: CRITICAL.** GovernorBase is now landed at `e7a6909` — the
binding is mechanically tractable.

### CCV-5: Walker-axiom hand-waving for delegatecall + reentrancy + ERC4626 (1 vantage: Walker-completeness; corroborated by Multi-base for reentrancy)

10 composite walker axioms classified as HAND-WAVING: Governor
delegatecall (`propose/castVote/execute`), StakingVault ERC4626 mutators
(`deposit/mint/withdraw/redeem`), `claimRewards` reentrancy,
`upgradeToAndCall`. These are NOT amenable to walker-proof retirement
without architectural work: delegatecall bridge, ERC4626 equivalence
layer, reentrancy-aware Hoare-triple format.

**Severity: HIGH.** Documents as parametric-trust boundaries for now.
Each one is a multi-week framework-expressivity workstream.

## Single-vantage findings worth dispatching against immediately

### CRIT-Q: Logical bug in cancel walker axiom (Trust-axiom CRIT-1)

`run_fun_cancel_238_at_proj_sim_admin` and `_guardian` (Guardian.v lines
10209, 10266) universally quantify the Hoare-triple output `proposalId`,
making them logically inconsistent with the deterministic walker. This is
a logical bug, not a tightening deferral. Reshape to take
`proposalId := getProposalId_oracle key` as a hypothesis.

**Estimated effort:** 15 minutes.

### CRIT-E: ERC4626 formula mismatch (Sim-vs-source CRITICAL-1)

`simulations/StakingVaultExchange.v:71-76` uses naive
`assets * totalSupply / totalAssets` instead of OZ v5.4's
`assets * (totalSupply + 10^offset) / (totalAssets + 1)`. The two
headline share-rate theorems are proofs about the wrong mathematical
object. Direct economic impact: if those theorems were cited as evidence
that the inflation-attack defense holds, the citation would be wrong.

**Estimated effort:** 1-2 days (formula + proof refresh + audit doc).

### CRIT-G: ROG state() missing branch (Sim-vs-source CRITICAL-2)

`Governor.observe` does not model `ROG.sol:251-253`'s
`pastSupply == 0 → Canceled` exit. A proposal created when supply was
zero would be classified as Canceled on-chain but as something else by
the sim.

### CRIT-V: vetoThresholdTok live-vs-frozen (Sim-vs-source CRITICAL-3)

Contract recomputes `vetoThresholdTok` from current `pastSupply` on
every observation; sim freezes it at create time. Affects any theorem
about veto-counting correctness across delegation history.

### CRIT-A: ProposalLib helper-tier Admits (Wave-2 finding)

Lines 477, 510, 518 contain 3 helper-tier `Admitted` bodies that
`Audit.v` Caveat-5's "All 5 public functions Qed" framing masks. The
public-function milestones may still close, but they depend on helper
lemmas that don't.

## Trust-budget honest re-tally

| Category | Count | Notes |
|---|---|---|
| Genuinely TIGHT Qed milestones | 3 | Guardian grantRole, revokeRole, cancel |
| PROVABLE (closed-form post-storage) | 2 | VersionRegistry deprecate, register |
| Section-bound (content-free until instantiation) | 4 | StakingVaultDelegation |
| VACUOUS (free post-storage Parameter, reflexive bridge) | 14 | ROG×3, SVAdmin×7, SVRewards×3, +1 doubly-vacuous |
| VACUOUS² (function AND post-state both free) | 4 | StakingVaultExchange |
| WEAK (some constraint, but allows wrong instantiations) | 2 | RewardTokenRegistry |
| Logical bug (universally-quantified output) | 2 | Guardian cancel admin + guardian |
| Sim semantic mismatch | 3 | ERC4626 formula, ROG canceled-branch, vetoThresholdTok |

**Total milestone Qeds in corpus:** ~30
**Milestones with genuine semantic content right now:** ~5 (Guardian
grant/revoke/cancel + VersionRegistry deprecate/register).

## What is genuinely sound

Multi-base composition auditor: "**The mock layer is sound.**"

- `mocks/Votes.v` — `_delegate`, `_transferVotingUnits`, `_moveDelegateVotes`
  Qed against the mock's Valid.t invariants. 17 sim-level lemmas.
- `mocks/ERC20Votes.v` — dual-storage `update` composes cleanly. 14 spot-
  checked lemmas show only `Set is impredicative` in Print Assumptions.
- `simulations/StakingVaultRewardsReentrancy.v` — REN-1..5 are Qed against
  the hand-written `reentrancy_step` interleaving model.
- `simulations/Governor.v` — `propose_optimistic`, `add_veto_validated`,
  `execute_optimistic` Qed at sim level.
- The R059 set-equivalence pattern is consistently applied across all
  EnumerableSet-touching contracts (no R056-style regression).
- `Conventions.v` documented assumptions hold cross-cuttingly.
- All Foundry differential tests, CAS scripts, and Certora rules are
  unaffected — they bind to source / bytecode directly, not to the sim.

## Remediation plan (recommended)

### Tier 1 — Logical/factual corrections (15 min to 2 days each)

1. CRIT-Q: Fix Guardian cancel proposalId quantification (15 min).
2. CRIT-E: Replace ERC4626 formula in `simulations/StakingVaultExchange.v`
   (1-2 days including proof refresh).
3. CRIT-G + CRIT-V: Add missing ROG state() branches + dynamic
   vetoThresholdTok modeling (1-2 days).
4. CRIT-A: Close ProposalLib's 3 helper Admits (1 day).
5. Update Audit.v Caveat-5 to accurately reflect the per-file Qed-vs-
   scaffolded status (~1 hour).

**Total Tier 1:** ~1 week.

### Tier 2 — Equivalence-layer tightening (2-3 days each)

6. CCV-3: Wire `StakingVault_shallow` into `StakingVaultExchange.v` —
   replace `fun_<op>_op : Parameter` with `Notation` aliasing the actual
   shallow form (~30 min).
7. CCV-1: Promote reflexive `_observes` bridges to closed-form
   Definitions across SVAdmin / SVExchange / TLOCK (2-3 days).
8. CCV-4: Wire `GovernorBase` into `ReserveOptimisticGovernor.v` —
   instantiate the Section, supply concrete `proj_base` lens, discharge
   the three lens-correctness hypotheses by reflexivity (1 day).
9. CCV-2: Either (a) instantiate the StakingVaultDelegation Section at
   the concrete inheritor binding site, or (b) re-document the file's
   theorems as "abstract methodology, not concrete equivalence" and
   move them out of the milestone tier (1 day).

**Total Tier 2:** ~1-2 weeks.

### Tier 3 — Walker-proof retirements (1-2 days each, partially parallel)

10. Retire `run_fun_setUnstakingDelay_750_at_proj_sim` with real walker
    proof. Validates R067 template (1 day).
11. Retire `run_fun_deprecateVersion_187_at_proj_sim` with real walker
    proof. Validates R063 staticcall-bridge end-to-end (1 day).
12. Retire `run_fun__revokeRole_736_at_proj_sim_member`. Unblocks 4
    downstream axioms (2-3 days).

**Total Tier 3:** ~1 week.

### Tier 4 — Framework expressivity (multi-week each, parallel)

13. Delegatecall bridge in upstream rocq-of-solidity (2-4 weeks).
14. ERC4626 equivalence layer that closes the four mutators honestly
    (2-3 weeks; depends on Tier 1 CRIT-E for the sim alignment).
15. Reentrancy-aware Hoare-triple format (2-4 weeks).

**Total Tier 4:** parallel multi-month workstreams. Only pursue if the
audit objective is "every milestone closes against actual Yul".

### Tier 5 — Process hygiene (1 day each)

16. Add CI snapshot of every milestone's `Print Assumptions` (1 day).
17. Document the "Section-bound milestone" pattern in WISDOM as a
    warning — flagged Print Assumptions can hide content (1 hour).
18. Update Audit.v Caveat-5 with per-file granular status table
    (~2 hours).

## Honest framing for next audit

When this work is presented externally, the framing should be:

- ~5 contracts have GENUINE equivalence Qeds (Guardian, VersionRegistry,
  ThrottleLib at the small-target tier; the rest are scaffolded).
- The other heavyweight contracts (ROG, StakingVault×4) have walker-
  axiom-backed scaffolds that need either honest theorem-statement
  refresh (CCV-1, CCV-2, CCV-3) or honest theorem-content tightening
  (Tier 3).
- The sim-vs-source mismatches (CRIT-E most critically) must be fixed
  before any audit citation of share-rate / inflation-defense
  properties.

## Recommended next session direction

If user accepts the remediation plan: dispatch Tier 1 + Tier 2 in
parallel (8 agents). Tier 1 finishes in ~1 week, Tier 2 in ~2 weeks.
Tier 3 and Tier 4 are optional follow-ons depending on audit timeline.

If user prefers narrower focus: do CRIT-Q + CRIT-E + CCV-3 + CCV-4 in
one session each. That recovers four of the highest-confidence
critical-impact items in ~1 week.

If user wants to ship as-is: rewrite the Audit.v Caveat-5 to
accurately reflect the equivalence-binding-layer gaps. The corpus's
sim-level work, mock-level work, and Foundry/CAS/Certora layers all
stand independently of the equivalence layer's content.
