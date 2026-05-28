# Certora adversarial review — synthesis

Five independent review agents covered four adversarial angles plus an
exploration of how Rocq + CAS should inform next Certora priorities.
This memo synthesizes the convergent findings, ranks them by signal
strength (multi-angle convergence vs single-angle), and lays out the
fix plan.

Source reports:
- `adversarial_spec_correctness.md` — does each rule's assert match its
  comment?
- `adversarial_vapor_proofs.md` — trivially-true / under-constrained
  rules?
- `adversarial_summary_fidelity.md` — do NONDET/CONSTANT/ghost summaries
  faithfully represent reality?
- `adversarial_coverage_gaps.md` — what surfaces aren't covered?
- `exploration_rocq_cas_alignment.md` — how should Rocq + CAS inform
  next priorities?

## Headline: triple-convergence on Guardian G6

**Three of four adversarial agents independently flagged the same
defect**: `Guardian/Guardian.spec:10` advertises a rule G6 ("cancel by
non-admin requires the proposal be optimistic AND not Defeated") but
the rule body does not exist. G6 is the role-discriminator: it's the
only rule that would prove an OPTIMISTIC_GUARDIAN_ROLE caller can't
cancel a pessimistic or Defeated proposal — the core safety property
separating that role from DEFAULT_ADMIN_ROLE.

The summary-fidelity agent supplied the technical explanation: the
spec NONDET-summarizes `_.isOptimistic` and `_.state` (Guardian.spec:31-32),
which makes G6 unprovable as currently summarized — the prover can
pick arbitrary return values on each call. The fix requires
ghost-backed summaries (the same pattern OptimisticSelectorRegistry,
RewardTokenRegistry, and VersionRegistry already use), and is exactly
what the Rocq simulation already adopted in
`rocq/simulations/Guardian.v` via `cancel_with_governor_state` and the
`GovernorStateSnapshot` record.

## Same-class defects in two other contracts

**UnstakingManager U8** (`UnstakingManager.spec` header) and
**VersionRegistry V7/V8** (similar advertise-vs-deliver gap) follow
the identical pattern. The vapor-proof and spec-correctness agents
both flagged these. V7 is documented as deferred in the spec body
(needs an inductive invariant tying `latestVersion` to `deployments[]`)
but the header doesn't disclose that. U8 ("createLock increments
nextLockId by 1") has no rule body — and lock-ID uniqueness is the
load-bearing invariant for the no-double-spend Rocq proof.

## Coverage-gap headline finding

The coverage-gap agent's CG1 (HIGH) is the most uncomfortable single
finding:

> The ReserveOptimisticGovernor spec NONDET-summarizes the entire
> ProposalLib/ThrottleLib delegatecall surface plus the timelock
> interface (Governor.spec:42-67). The 10 "verified" rules are all
> setters plus the updateTimelock-always-reverts rule. **The
> optimistic propose/queue/execute/cancel/tally state machine — the
> contract's headline novelty — has no bytecode-level Certora
> coverage.**

Properties like `OptimisticProposalCannotBeQueued` and
`OptimisticProposalCanOnlyBeVetoed` are tractable single-rule
additions that would close this gap.

## Summary-fidelity HIGH findings

The summary-fidelity agent identified three HIGH-severity fidelity
gaps:

- **F1 Guardian two-read NONDET** (covered above)
- **F2 Governor `_.hasRole` NONDET** — Governor's onlyGovernance modifier
  reads the timelock's `hasRole` to determine executor authority. With
  that read NONDET, the auth gate is unconstrained for any non-direct
  call path.
- **F3 Governor library delegatecall NONDET** — `ProposalLib.*` and
  `ThrottleLib.*` are called via delegatecall and NONDET-summarized.
  Delegatecall executes the library code in Governor's storage
  context, so summarizing it away means none of the state mutations
  the libraries perform are visible to the prover.

## Exploration agent's biggest leverage point

> The highest-leverage Certora work is not new properties but
> converting existing Rocq-proved invariants into CVL invariants over
> the emitted bytecode — turning per-property single-method coverage
> into per-property double-coverage at low marginal cost.

Top three triple-confirmation candidates (Rocq proves it, CAS
witnesses it, Certora can express it):

- **TC1** ProposerThrottle consume storage delta is exact
  (`audit_throttle_consume_storage_delta` + `charge_evolution.gp` INV-2)
- **TC2** StakingVault rewardIndex monotone non-decreasing
  (`audit_rewards_index_monotone` + `multi_token_rewards.gp` INV-1)
- **TC3** Timelock bypass doesn't disturb other scheduled ops
  (`audit_timelock_bypass_preserves_slow_path` + `scheduling_ordering.gp` INV-5)

## Convergence map

| Finding | spec-correctness | vapor-proof | summary-fidelity | coverage-gap |
|---|:-:|:-:|:-:|:-:|
| Guardian G6 missing | F1 HIGH | F1 HIGH | F1 HIGH | (in Guardian section) |
| UnstakingManager U8 missing | F8 MED | F2 HIGH | F7 LOW | (in UM section) |
| VersionRegistry V7/V8 | F3 MED | F3 MED | F6 MED | (in VR section) |
| Governor library NONDET | (in Governor) | (in Governor) | F3 HIGH | CG1 HIGH |
| Governor R8 missing upper-bound | F2 MED | — | — | — |
| Governor missing optimistic-params persistence | F4 MED | — | — | — |
| Governor lifecycle state machine uncovered | — | — | F3 HIGH | CG1 HIGH |
| StakingVault all 9 custom errors uncovered | — | — | F5 MED | (in SV section) |
| UnstakingManager re-entrancy blindspot | — | — | F4 MED | (in UM section) |
| SelectorRegistry R6 no-op pre-state | — | F4 MED | — | — |

Convergent (HIGH-confidence) findings — appearing in 2+ angles:

1. **Guardian G6 missing** (4/4 angles where applicable)
2. **UnstakingManager U8 missing** (3/3 angles)
3. **VersionRegistry V7/V8 header overstates** (3/3 angles)
4. **Governor library delegatecall NONDET admits unrealistic states** (2/2 angles)
5. **Governor lifecycle state machine uncovered** (2/2 angles)

## Fix plan (severity-ordered)

### P0: address advertised-but-missing rules

These are the simplest defects to fix and the easiest to argue for:
the specs claim coverage they don't have.

1. **Guardian G6**: implement two ghost-backed rules
   (`cancelNonAdminRequiresOptimistic`, `cancelNonAdminRequiresNotDefeated`).
   Refactor the methods block to use ghost mappings for
   `isOptimistic`, `state`, and `getProposalId`. Pattern mirrors the
   `cancel_with_governor_state` snapshot threading in
   `rocq/simulations/Guardian.v`.

2. **UnstakingManager U8**: either implement
   `nextLockIdIncrementsByOne`, or remove from header. Implementation
   is straightforward; the contract literally does
   `lockId = nextLockId++;`.

3. **VersionRegistry V7**: remove the deferred V7 from the "Properties
   proved" header (it's correctly documented as deferred in the body
   but the header still lists it).

### P1: address Governor lifecycle gap (CG1)

Add at least two state-machine rules to Governor.spec:

- **`optimisticProposalCannotBeQueued`**: queue reverts with
  `OptimisticGovernor__OptimisticProposalCannotBeQueued` when the
  proposal id is optimistic. (Maps to the `audit_no_de_escalation`
  family of Rocq theorems.)
- **`optimisticProposalAcceptsOnlyAgainst`**: castVote reverts with
  `OptimisticGovernor__OptimisticProposalCanOnlyBeVetoed` when the
  proposal is optimistic and the support value isn't Against.

### P2: triple-confirmation rules

Convert the three TC candidates the exploration agent identified into
CVL rules. Estimated 1-2 hours each. These are high-confidence
because three independent verification methods will agree.

### P3: remaining single-angle findings

The Governor R8 upper-bound miss, the Governor setOptimisticParams
persistence gap, the SelectorRegistry R6 no-op pre-state, the
UnstakingManager re-entrancy blindspot, the StakingVault custom-error
coverage gap — all worth doing, lower urgency than the above.

## What this review changes about the coverage matrix

Current claim: 58 rules across 8 contracts.
True picture after this review:
- 57 rules with bodies (G6 is documented but doesn't exist).
- Of those 57, at least 4 are weakened by NONDET summaries on critical
  downstream state (Guardian G5, Governor R1-R10's reliance on
  delegatecall summaries, UnstakingManager re-entrancy hole).
- The Governor "10 rules VERIFIED" headline is technically accurate but
  conceals that none of those 10 touch the contract's optimistic
  state machine.

Action: the per-contract README and the spec headers need a
"Limitations" subsection that's honest about what each NONDET wall
hides, in the style of `Audit.v`'s `Caveat-N` notes.
