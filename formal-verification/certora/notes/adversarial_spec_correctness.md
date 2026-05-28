# Spec correctness adversarial review

## Summary

The Certora specs are well-scoped and self-aware about CVL footguns
(EnumerableSet HAVOC, internal-summary propagation, `^` vs `**`, etc.),
but the spec **headers oversell coverage**: several enumerated properties
are listed but never implemented as rules, including the
**single most important Guardian safety property** (an optimistic
guardian cannot cancel a pessimistic proposal). Almost every
"only X can Y" rule is verified in the negative (non-X reverts) without
a paired positive (X-with-good-input succeeds), so a contract that
accidentally reverts for *everyone* would silently pass. Several
multi-clause `require`s in the contracts are checked only on the
boundary explicitly named in the rule comment, leaving the other
clauses unverified.

## Findings (severity-ordered)

### F1 [HIGH]: Guardian's core safety property (G6) is listed but not implemented (Guardian)

**Where:** `formal-verification/certora/Guardian/Guardian.spec:10` (spec header), no rule
**Issue:** The spec header advertises:
> G6 cancel by non-admin requires the proposal be optimistic AND not Defeated

…but no rule encodes G6. Only `G1`–`G5` (rules `onlyManagerCanGrant`,
`grantRejectsZero`, `grantAddsRole`, `onlyAdminCanRevoke`,
`cancelRequiresAuth`) exist. G5 only proves that a caller with
**neither** admin nor guardian role reverts (`Guardian.spec:86–100`);
it says nothing about what an `OPTIMISTIC_GUARDIAN_ROLE` holder can
actually cancel.

Reading `Guardian.sol:72–97`, the contract has two distinct revert
clauses for a non-admin cancel path:

```solidity
require(managedGovernor.isOptimistic(proposalId), Guardian__NotOptimisticProposal(proposalId));
require(IGovernor(governor).state(proposalId) != IGovernor.ProposalState.Defeated, Guardian__DefeatedProposal(proposalId));
```

Both are summarized as `NONDET` in the spec methods block
(`Guardian.spec:31, 32`), so the prover has total freedom over their
return values — exactly the surface where a missing rule matters most.
A buggy refactor that swapped `!=` for `==` on the Defeated check,
or dropped the `isOptimistic` guard entirely, would change nothing
that the current spec measures.

**Why it matters:** The optimistic guardian's authority is supposed
to be strictly limited to *active optimistic* proposals; this is the
contract's headline safety invariant per the NatSpec
(`Guardian.sol:18–25`). The Certora coverage as it stands proves
only "you need *some* role to cancel," not "the optimistic guardian
cannot cancel a pessimistic proposal."

**Suggested fix:** Add two rules using ghost-backed summaries for
`isOptimistic` and `state` (analogous to the `ghostIsOwner` pattern
in `RewardTokenRegistry.spec`):

```cvl
ghost mapping(uint256 => bool) ghostIsOptimistic;
ghost mapping(uint256 => uint8) ghostState;  // ProposalState

// G6a: non-admin guardian cannot cancel non-optimistic
rule guardianCannotCancelPessimistic {
    env e; ...
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require  hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);
    require !ghostIsOptimistic[id];  // pessimistic
    cancel@withrevert(e, ...);
    assert lastReverted;
}

// G6b: non-admin guardian cannot cancel a Defeated optimistic proposal
rule guardianCannotCancelDefeated { ...
    require ghostIsOptimistic[id];
    require ghostState[id] == 4 /* Defeated */;
    ...
    assert lastReverted;
}
```

---

### F2 [HIGH]: Governor R8 only tests vetoDelay lower bound; upper bound unverified (Governor)

**Where:** `formal-verification/certora/Governor/Governor.spec:188–201` (rule `setOptimisticParamsRejectsZeroVetoDelay`)
**Issue:** `ReserveOptimisticGovernor._setOptimisticParams`
(`ReserveOptimisticGovernor.sol:491–500`) enforces a **conjunction**:

```solidity
require(
    params.vetoDelay >= MIN_OPTIMISTIC_VETO_DELAY
 && params.vetoDelay <  MAX_OPTIMISTIC_DELAY
 && params.vetoPeriod >= MIN_OPTIMISTIC_VETO_PERIOD
 && params.vetoThreshold != 0
 && params.vetoThreshold <= 1e18,
    OptimisticGovernor__InvalidOptimisticParameters()
);
```

The spec covers `vetoDelay == 0` (R8), `vetoPeriod < 300` (R9),
`vetoThreshold == 0` (R6), `vetoThreshold > 1e18` (R7). It does **not**
cover `vetoDelay >= MAX_OPTIMISTIC_DELAY` (≈ `2^47`). Since
`MIN_OPTIMISTIC_VETO_DELAY == 1 second`, the only value rejected by the
lower bound is `0`; the much larger surface — anything `>= 2^47` — is
silently accepted by the spec. The contract correctly rejects it; the
*spec* doesn't.

Same omission for `vetoPeriod`: the contract has only a lower bound
(no upper bound), so R9 is complete there. The asymmetry is real for
`vetoDelay`.

**Why it matters:** A refactor that drops the `< MAX_OPTIMISTIC_DELAY`
clause would still satisfy every rule in this spec. The bound matters
because `vetoDelay` is later cast to `uint48` in OZ Governor's
`uint48 voteStart = clock() + uint48(vetoDelay)` (or the analogue
inside `ProposalLib.proposeOptimistic`); a too-large value would
wrap or overflow.

**Suggested fix:** Add a rule symmetric to R8:

```cvl
rule setOptimisticParamsRejectsTooLargeVetoDelay {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoDelay >= 140737488355327;  // MAX_OPTIMISTIC_DELAY = type(uint48).max / 2
    setOptimisticParams@withrevert(e, params);
    assert lastReverted, "accepted vetoDelay >= MAX_OPTIMISTIC_DELAY";
}
```

---

### F3 [MED]: UnstakingManager U8 advertised but absent; `nextLockId` is private, so even claiming it is misleading (UnstakingManager)

**Where:** `formal-verification/certora/UnstakingManager/UnstakingManager.spec:21` (header), no rule
**Issue:** The header lists:
> U8 createLock increments nextLockId by 1

…but only `U1`–`U7` are implemented as rules. Worse, the storage slot
`nextLockId` is declared `private` in `UnstakingManager.sol:22`, so
even if a rule existed, CVL has no envfree getter to observe it
(the spec's methods block at `UnstakingManager.spec:35–37` only exposes
`locks(uint256)`, `vault()`, `targetToken()`). The current spec
silently drops U8 without acknowledging that it isn't tractable as-is.

**Why it matters:** `nextLockId` monotonicity is what makes the
contract free of lock-id collisions (no two calls produce the same
`lockId`). The companion Rocq proof
(`formal-verification/rocq/simulations/UnstakingManager.v`) covers
conservation but not this. The Certora spec advertising the property
while not delivering it leaves a reader who trusts the header in the
dark.

**Suggested fix:** Either
- expose `nextLockId` via a public getter and add a rule
  `nextLockIdBefore + 1 == nextLockIdAfter` for successful `createLock`,
  with appropriate auth preconditions; **or**
- delete U8 from the spec header (`UnstakingManager.spec:21`) and add
  one line noting the property lives in Rocq.

The first is preferred; a contract change is small and the property
is a real safety property.

---

### F4 [MED]: Governor has no `setOptimisticParams` persistence rule, only the `setProposalThrottle` one (Governor)

**Where:** `formal-verification/certora/Governor/Governor.spec:218–235` (`setProposalThrottlePersistsCapacity` is R10; no R11 for params)
**Issue:** R10 verifies that `setProposalThrottle` actually writes
`newCapacity` to `proposalThrottle.capacity`. There is no analogous
rule for `setOptimisticParams`: the spec verifies *which inputs are
rejected* (R6/R7/R8/R9) but not that a valid input is *persisted to
storage*. The contract writes `optimisticParams = params;` at
`ReserveOptimisticGovernor.sol:498`, but a buggy refactor (e.g.,
assigning to a shadowed local, or writing only one struct field) would
satisfy every existing rule.

**Why it matters:** `optimisticParams` is the source of truth for the
veto window of every future optimistic proposal. If a write regression
ever shipped, the spec wouldn't catch it.

**Suggested fix:** Add (with the same self-timelock precondition
pattern as R10):

```cvl
methods {
    function optimisticParams() external returns (
        uint256, uint256, uint256
    ) envfree;  // vetoDelay, vetoPeriod, vetoThreshold
}

rule setOptimisticParamsPersists {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoDelay >= 1
         && params.vetoDelay < 140737488355327
         && params.vetoPeriod >= 300
         && params.vetoThreshold != 0
         && params.vetoThreshold <= 1000000000000000000;
    setOptimisticParams(e, params);
    // Read back and compare each field
    uint256 d; uint256 p; uint256 t;
    d, p, t = optimisticParams();
    assert d == params.vetoDelay && p == params.vetoPeriod && t == params.vetoThreshold;
}
```

---

### F5 [MED]: Timelock spec runs with `rule_sanity: "none"`; vacuous rules pass silently (Timelock)

**Where:** `formal-verification/certora/Timelock/Timelock.conf:11` (`"rule_sanity": "none"`) interacts with `formal-verification/certora/Timelock/Timelock.spec:149–177` (rule `bypassMarksOpDone`) and lines 187–210 (rule `bypassRejectsExistingOp`)
**Issue:** The spec header at `Timelock.spec:23–32` openly explains
why sanity is disabled (OOM on the bypass rules under the inherited
OZ storage layout). The trade-off is real, but it means:
- T6/T7 have heavyweight preconditions (`targets.length == 0`,
  `values.length == 0`, `payloads.length == 0`, `predecessor == 0`,
  `block.timestamp > 1`, both `PROPOSER_ROLE` and `EXECUTOR_ROLE`,
  pre-state on `getTimestamp(id)`). If *any* of these makes the
  successful path unreachable for the prover, the rule passes
  vacuously and no one notices.
- Even T1–T5 (which the header says "would pass sanity too") are
  given the uniform `"none"` setting "for consistency."

The header argues sanity OOMs only on T6/T7. The defensible move is
**per-rule** sanity opt-out for those, leaving T1–T5 with
`rule_sanity: "basic"` so the easy revert-only auth rules still get
the non-vacuity guard. CVL supports per-rule sanity via
`@withrevert`-pattern witnessing rules.

**Why it matters:** Half the value of a revert-only auth rule is the
sanity check confirming that there *exists* a setup where the function
is callable. Without it, every "X reverts" rule could be vacuously
true.

**Suggested fix:** Re-enable `rule_sanity: "basic"` globally; add a
companion witness rule for each bypass rule that constructs a
non-reverting trace (e.g., `bypassSucceedsOnEmptyOp`) and lets the
prover learn the precondition is satisfiable without the OOM-trigger
path. If that proves infeasible, split the conf into two files (one
with sanity for T1–T5, one without for T6/T7).

---

### F6 [MED]: Governor R2/R3 over-constrain `msg.sender`, hiding the self-timelock edge (Governor)

**Where:** `formal-verification/certora/Governor/Governor.spec:92–115` (rules `setProposalThrottleOnlyGovernance` and `setOptimisticParamsOnlyGovernance`)
**Issue:** OZ's `_checkGovernance` (in
`GovernorUpgradeable.sol:242–252`) reverts when
`_executor() != _msgSender()`. Since
`GovernorTimelockControlUpgradeable._executor()` returns
`address($._timelock)`, the *only* address that can pass is
`timelock()`. The rules require **both**:

```cvl
require e.msg.sender != timelock();
require e.msg.sender != currentContract;
```

The second clause is unnecessary in the normal case (`timelock() !=
currentContract`), and it actively *hides* the degenerate case where
`timelock() == currentContract`: there, only senders distinct from
`currentContract` get to attempt; the rule never exercises `msg.sender
== currentContract` against a function that, in this self-timelock
config, would actually succeed (because then `_executor() == address(this)`,
which makes the deque-pop branch active, where R4–R10 already require
this self-timelock setup to test inner validation).

**Why it matters:** The two halves of the spec (R2/R3 vs R4–R10)
implicitly assume different deployment configurations. The auth check
that R2/R3 verifies is the auth check against a `timelock() !=
currentContract` deployment; R4–R10 verify validation logic only
under `timelock() == currentContract`. There is no rule that
exercises the *normal* deployment's success path — that the timelock
caller can update params on a non-self-timelock contract. The spec is
correct for what it checks, but the surface labeled "R2/R3 +
R4–R10" doesn't compose into "auth + validation under realistic
deployment."

**Suggested fix:** Drop `require e.msg.sender != currentContract;` in
R2/R3 — the OZ contract has no special case for self-calls (except
inside `_checkGovernance` itself, which is already gated on
`_executor() == _msgSender()`). Then add a positive-direction rule
that exercises a realistic deployment: `require e.msg.sender ==
timelock() && timelock() != currentContract`, then call the setter
with valid inputs and assert no revert. This requires summarising
the deque-pop branch (e.g., `_governanceCall.popFront() => NONDET`
via ghost or an axiom that the deque holds the expected operation).

---

### F7 [LOW]: StakingVault SV9 is tautological (StakingVault)

**Where:** `formal-verification/certora/StakingVault/StakingVault.spec:186–194` (rule `delegateOptimisticSetsCallerDelegate`)
**Issue:** The rule reads:
```cvl
delegateOptimistic(e, newDelegate);
assert optimisticDelegates(e.msg.sender) == newDelegate;
```
The contract function literally writes
`optimisticDelegatees[msg.sender] = delegatee;` at
`StakingVault.sol:545`. Reading the same slot immediately after
asserts only that the Solidity language correctly performs storage
writes — which is not a property of the contract under test.

The rule has some value as a regression-prevention canary (against a
refactor that, e.g., writes the *wrong* mapping), but it cannot
discriminate any correctness-relevant variant of the implementation
that touches the right slot.

**Why it matters:** Low. The rule is cheap to run; it just inflates
the "verified properties" count without adding semantic coverage.

**Suggested fix:** Either delete it, or strengthen to "the **previous**
delegate of the caller has been emitted in the
`OptimisticDelegateChanged` event" (which would require Certora event
support; probably not worth it). The more useful property — that the
**checkpoint** for the new delegate increased by `balanceOf(caller)` —
is what the contract's safety story actually depends on. Pursuing that
is more work but more honest coverage.

---

### F8 [LOW]: VersionRegistry V7 is documented as deferred but the header still lists it under "Properties proved" (VersionRegistry)

**Where:** `formal-verification/certora/VersionRegistry/VersionRegistry.spec:12–13` (header) vs `:124–131` (V7 explicitly deferred)
**Issue:** The spec header lists:
> V7 getLatestVersion reverts when no version has ever been
>    registered (latestVersion -> address(0))

…then at the end of the file, a multi-line comment says V7 is
"deferred" because `latestVersion` is private and CVL cannot observe
it without a contract change or a ghost-tracked inductive invariant.
Same dual-listing pattern as the Guardian G6 issue (F1) and
UnstakingManager U8 (F3): the "Properties proved" header is
aspirational, not actual.

**Why it matters:** A reader auditing what is verified will assume
all entries in the header are covered. Three of the eight specs
overstate their coverage in headers; the pattern is repeated enough
to call out as a discipline issue.

**Suggested fix:** Adopt a uniform header convention — either
"Properties proved" (only what is actually a rule) plus a separate
"Deferred" subsection, or move deferred entries out of the
enumerated list. Apply across all eight specs.

---

### F9 [LOW]: OptimisticSelectorRegistry R5 still vulnerable to EnumerableSet HAVOC at initial state (OptimisticSelectorRegistry)

**Where:** `formal-verification/certora/OptimisticSelectorRegistry/OptimisticSelectorRegistry.spec:141–164` (rule `registerSucceedsOnValidInput`)
**Issue:** R5 asserts `!lastReverted` after a single-element
registerSelectors with a non-zero selector and non-forbidden target.
The internal `_add` calls `_allowedSelectors[target].add(...)` and
then `_targets.add(target)`. Both are OZ EnumerableSet.add, which —
per WISDOM C004, and acknowledged in the spec header
(`OptimisticSelectorRegistry.spec:33–40`) — can be in an initial
state where `_values.length == type(uint256).max`, in which case the
internal `_values.push(...)` reverts (Solidity 0.8 overflow on
`length += 1`).

The spec header argues that R5/R6 are "the complementary direction"
that avoids the HAVOC, but R5's `assert !lastReverted` is the side
that can still tip over for this same reason. A passing R5 implicitly
relies on the prover not exploring the full-set initial state, which
is a property of the solver, not of the contract.

**Why it matters:** Low. The Rocq simulation
(`formal-verification/rocq/simulations/SelectorRegistry.v`) handles
this. The risk is that R5 is reported as VERIFIED for the wrong
reason (solver didn't find the pathology, not because it doesn't
exist).

**Suggested fix:** Add `requireInvariant` over the EnumerableSet
position/length consistency at the top of R5 (the heavyweight option
in WISDOM C004), or document explicitly that R5 is only sound modulo
the `_targets.values.length < 2^256 − 1` precondition the spec relies
on implicitly. The latter is cheap and fits the spec's documentary
style.

---

### F10 [LOW]: Most "auth-only" rules verify revert-on-negative without a companion success-on-positive (multiple specs)

**Where:** Pattern across `Guardian.spec:40–48,73–83`,
`UnstakingManager.spec:51–61,64–78`,
`RewardTokenRegistry.spec:54–73`,
`OptimisticSelectorRegistry.spec:68–89`,
`Timelock.spec:61–113`,
`StakingVault.spec:125–166`,
`Governor.spec:92–115`
**Issue:** Almost every "only X can do Y" rule is encoded as
"non-X reverts." None of these rules have a companion rule asserting
that **X with valid inputs does NOT revert**. A pathological refactor
that makes the function unconditionally revert (or revert under
realistic inputs but not under the prover's chosen state) would
satisfy every existing auth rule. Default `rule_sanity: "basic"` on
most confs partially mitigates this (sanity confirms the precondition
is satisfiable for the negative case), but a satisfiable
non-X-precondition is much weaker than a witness that X-with-good-input
succeeds.

The OptimisticSelectorRegistry spec is the only one that pairs the
negative revert (R1/R2) with a positive success rule (R5) — and the
header explicitly explains this is the right pattern. The other
specs do not follow suit.

**Why it matters:** Low to medium individually, but the pattern
compounds: a regression that turned `cancel` into a no-op
(`function cancel(...) { return; }`) would not be caught by any
existing rule on Guardian, Timelock, or UnstakingManager.

**Suggested fix:** For each auth-only rule, add a paired witness rule
of the form:
```cvl
rule fooSucceedsForAuthorized {
    env e;
    require hasRole(THE_ROLE, e.msg.sender);
    // valid inputs ...
    foo@withrevert(e, ...);
    assert !lastReverted;
}
```
Use NONDET-summarised dependencies so the witness rule isn't
contaminated by downstream behavior. R5 in
OptimisticSelectorRegistry is the model.
