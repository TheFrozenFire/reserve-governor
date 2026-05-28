# Vapor-proof / vacuity adversarial review

## Summary

The 8 production specs (Guardian, UnstakingManager, RewardTokenRegistry,
OptimisticSelectorRegistry, Timelock, VersionRegistry, Governor,
StakingVault) total ~60 rules. The bulk of them are tight one-line
auth-gate proofs of the form `require !hasRole(R, sender);
f@withrevert(...); assert lastReverted` — those are short, focused, and
not vapor. The state-effect rules are mostly also tight, with explicit
preconditions tying the ghost-modeled RoleRegistry to the auth branch
under test.

The substantive vapor-shaped issues this review found are:

  - Two rules are listed in spec-header docstrings but the rule body is
    absent (Guardian G6, UnstakingManager U8). These are vapor by
    omission: the documented property is not verified anywhere.
  - One rule's header advertises a stronger property than the rule body
    actually verifies (VersionRegistry V8).
  - One rule pair on the OptimisticSelectorRegistry is satisfied by the
    no-op pre-state (SelectorRegistry R6).
  - Several auth-shielded "validation" properties (Guardian G5, Timelock
    T2/T3) leave the downstream branch entirely untested under NONDET
    summaries on the called-into views.

Below, findings are ordered by severity. Where a spec is genuinely
tight under its declared scope, I say so.

## Findings (severity-ordered)

### F1 [HIGH]: Guardian G6 is documented but never verified

**Rule:** `formal-verification/certora/Guardian/Guardian.spec` —
Guardian.spec:10 (header) vs Guardian.spec:21-100 (rule bodies).

**The rule claims:** The header docstring at Guardian.spec:10 lists G6:
"cancel by non-admin requires the proposal be optimistic AND not
Defeated." This is the *core* non-admin invariant in
`Guardian.cancel` — the post-auth-check business logic at
`contracts/Guardian.sol:88-94`.

**What it actually verifies:** Nothing. Only G1-G5 have rule bodies. G6
is in the docstring but no `rule g6...` exists. Compounding this, the
spec summarizes `_.isOptimistic` and `_.state` as NONDET
(Guardian.spec:31-32), so even the existing G5 ("non-(admin|guardian)
callers cannot cancel") proves only the first-revert path; the
optimistic/Defeated gate is entirely outside the Certora coverage.

**Why this is weaker:** The whole point of OPTIMISTIC_GUARDIAN_ROLE
(vs. DEFAULT_ADMIN_ROLE) is that a guardian's cancel powers are
limited to the optimistic/non-Defeated subset. Without G6 verified,
the contract's defining authorization invariant is unproved by Certora.
The Rocq simulation at `formal-verification/rocq/simulations/Guardian.v`
may or may not cover this — but the Certora docstring lies about it.

**Suggested fix:** Either (a) implement G6 as:
```
rule guardianRequiresOptimisticAndNotDefeated {
    env e; address governor; ... bytes32 descriptionHash;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);
    // Force the post-auth NONDET branches via ghosts (replace the
    // NONDET summaries on _.isOptimistic / _.state with ghost-backed
    // readers, mirroring RewardTokenRegistry.spec ghostIsOwner).
    require ghostIsOptimistic[proposalId] == false ||
            ghostState[proposalId] == Defeated;
    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);
    assert lastReverted;
}
```
or (b) remove G6 from the header and document the gap explicitly.

---

### F2 [HIGH]: UnstakingManager U8 is documented but never verified

**Rule:** `formal-verification/certora/UnstakingManager/UnstakingManager.spec`
— header at UnstakingManager.spec:21 vs. rule bodies at lines 51-165.

**The rule claims:** Header U8: "createLock increments nextLockId by 1."
This is a core sequencing invariant — if `nextLockId` is not strictly
incremented per call, two createLock calls collide and overwrite each
other's Lock storage.

**What it actually verifies:** Nothing. The spec has exactly 7 rule
bodies (`onlyVaultCanCreateLock`, `onlyLockUserCanCancel`,
`claimRevertsBeforeUnlock`, `claimRevertsOnUninitializedSlot`,
`doubleClaimReverts`, `cancelAfterClaimReverts`, `claimStampsTimestamp`).
U8 is absent. Furthermore, `nextLockId` is `private`
(`contracts/staking/UnstakingManager.sol:22`), so even adding the rule
requires either a public getter or a CVL ghost tracker.

**Why this is weaker:** Lock-ID uniqueness is the *only* defense against
lock-slot collision. Without it, a Solidity refactor that, say,
accidentally read `nextLockId` without `++` would let one lock
overwrite another's `amount` and `unlockTime`. The conservation
invariant (sum of active lock amounts == contract balance) proved in
Rocq depends on this uniqueness.

**Suggested fix:** Add a public getter for `nextLockId` (or expose it
via a CVL `using` ghost). Then:
```
rule createLockIncrementsId {
    env e; address user; uint256 amount; uint256 unlockTime;
    require e.msg.sender == vault();
    uint256 before = nextLockId();
    createLock(e, user, amount, unlockTime);
    assert nextLockId() == before + 1;
}
```

---

### F3 [MED]: VersionRegistry V8 header overstates the rule body

**Rule:** `formal-verification/certora/VersionRegistry/VersionRegistry.spec:14`
(header) vs `formal-verification/certora/VersionRegistry/VersionRegistry.spec:143-156`
(rule `registerDoesNotOverwriteExisting`).

**The rule claims:** Header V8: "registerVersion rejects re-registration
of a versionHash that already maps to a non-zero deployer."

**What it actually verifies:** A *weaker* property: "for an arbitrary
hash h with `deployments(h) != 0`, after a successful registerVersion,
`deployments(h)` is unchanged." Together with the NONDET summary on
`_.version()` (VersionRegistry.spec:42), the prover is allowed to
re-pick versionHash on each call; the rule passes as long as the
adversarial prover can find a versionHash != h on which to write. The
rule does not exhibit a counterexample if the contract overwrote
`deployments[h]` for any h-specific case the prover doesn't pick.

Actually — re-reading: the prover IS adversarial and WILL pick
versionHash == h to break the rule if such a trace exists. So the
rule *does* implicitly cover re-registration. But it does so only
under the assumption that NONDET picks include versionHash == h,
which it does. The verbal claim ("rejects re-registration") and
the rule body ("does not overwrite") are equivalent IF the
NONDET model fully covers the keccak preimage space — a non-obvious
chain of reasoning that should be in the spec.

**Why this is weaker:** The rule name `registerDoesNotOverwriteExisting`
is precise; the docstring claim "rejects re-registration" is a stronger
verbal claim that obscures the indirection. The bigger gap: the rule
does NOT prove that calling `registerVersion(deployer)` with the
*same* deployer twice in a row reverts. That requires modeling the
deterministic version() return for a given deployer, which NONDET
discards.

**Suggested fix:** Either tighten the rule by replacing the NONDET
summary on `_.version()` with a deterministic ghost (`ghost version()
returns string`), or update the header to read "no slot overwrite"
and explicitly note that "rejects re-registration of the same
deployer" is a corollary contingent on `version()` being a pure
function — which it is, but the spec doesn't currently see it.

---

### F4 [MED]: SelectorRegistry R6 is satisfied by the no-op pre-state

**Rule:** `formal-verification/certora/OptimisticSelectorRegistry/OptimisticSelectorRegistry.spec:170-186`
(`isAllowedAfterUnregister`).

**The rule claims:** "after a successful single-selector
unregisterSelectors, isAllowed is false. Proxy: removal is reflected in
the public view." (OptimisticSelectorRegistry.spec:166-169)

**What it actually verifies:** "post-call, isAllowed(target, selector)
== false." The rule does NOT require `isAllowed(target, selector) ==
true` in the pre-state. If the prover picks an initial state where the
selector was already absent (isAllowed=false), `_remove` is a no-op
(EnumerableSet.remove returns false silently when the value isn't
present — see contracts/governance/OptimisticSelectorRegistry.sol:108),
and the postcondition trivially holds because the pre-state already
satisfied it.

**Why this is weaker:** The rule's *intent* is to prove that
unregisterSelectors actually removes a present selector. The current
formulation also accepts the case "unregister a never-registered
selector and read isAllowed=false." A buggy `_remove` that did nothing
at all would still satisfy this rule for any pre-state with the
selector already absent.

**Suggested fix:**
```
rule isAllowedAfterUnregister {
    // ... existing setup ...
    require isAllowed(target, selector);  // <-- add this
    unregisterSelectors(e, data);
    assert !isAllowed(target, selector);
}
```
Without it, R6 is true for any function that doesn't add the selector —
which is a much wider class than "actually removes it."

---

### F5 [MED]: Guardian G5 only proves first-revert; the entire post-auth NONDET branch is unconstrained

**Rule:** `formal-verification/certora/Guardian/Guardian.spec:86-100`
(`cancelRequiresAuth`).

**The rule claims:** Header G5: "cancel reverts if caller has neither
admin nor guardian role."

**What it actually verifies:** Under `!hasRole(admin) && !hasRole(guardian)`,
calling cancel reverts. This is technically true: `contracts/Guardian.sol:79-83`
trips the `Guardian__UnauthorizedCaller` revert as the first check.

**Why this is weaker:** The spec summarizes `_.isOptimistic`, `_.state`,
`_.getProposalId`, `_.cancel`, `_.timelock` all as NONDET
(Guardian.spec:31-36). That means there is *no* downstream coverage of
the rest of cancel's logic — the admin-bypass case, the
non-admin-checks-optimistic case, the non-admin-checks-state case. G5
proves what amounts to "the first `if` works"; everything past line 84
of Guardian.sol is in the symbolic void. Combined with the missing G6,
the Guardian's substantive authorization invariant is barely covered.

**Suggested fix:** As in F1, replace NONDET on `_.isOptimistic` and
`_.state` with ghost-backed readers, and add rules covering:
- admin can cancel arbitrary proposals (skip optimistic/Defeated check)
- guardian cannot cancel non-optimistic proposals
- guardian cannot cancel Defeated proposals
This isn't extra work — it's the work G6 was already supposed to be.

---

### F6 [LOW]: Timelock T6/T7 bypass coverage is tight only on the empty-batch trace

**Rule:** `formal-verification/certora/Timelock/Timelock.spec:149-210`
(rules `bypassMarksOpDone` and `bypassRejectsExistingOp`).

**The rule claims:** Header T6/T7: bypass marks ops Done; bypass rejects
already-scheduled ops.

**What it actually verifies:** Both rules pin
`targets.length == values.length == payloads.length == 0`
(Timelock.spec:157-159, 195-197), so the inner `_execute` dispatch loop
runs zero times. The OperationConflict guard at
`contracts/governance/TimelockControllerOptimistic.sol:88` is exercised,
but the meaningful execution path with at least one external call is
not.

**Why this is weaker:** A bug in `executeBatchBypass` that affected the
*non*-empty-batch path (e.g., wrong `_DONE_TIMESTAMP` placement when
the dispatch loop ran) would slip past T6/T7. The spec acknowledges this
is intentional to avoid forking on external HAVOC. Acceptable, but the
property name "executeBatchBypass on a fresh op leaves the OZ Done
marker" suggests a generality the rule does not deliver.

**Suggested fix:** Add a companion rule with `targets.length == 1` and
the target summarized as a no-op contract (a stub address with NONDET
`call`), to cover the dispatch path. Alternatively, document in the
spec header that the bypass rules cover ONLY the zero-payload case and
that the dispatch-loop semantics are covered in the Rocq
`simulations/Timelock.v`.

---

### F7 [LOW]: Governor R7 hardcodes the 1e18 threshold (correct, but trap-shaped)

**Rule:** `formal-verification/certora/Governor/Governor.spec:171-186`
(`setOptimisticParamsRejectsTooLargeVetoThreshold`).

**The rule claims:** R7: rejects `vetoThreshold > 1e18`.

**What it actually verifies:** `require params.vetoThreshold >
1000000000000000000` (Governor.spec:181). Contract:
`params.vetoThreshold <= 1e18` (ReserveOptimisticGovernor.sol:495). So
strictly-greater-than-1e18 is the correct boundary. **No actual bug**;
flagging for completeness because hardcoded `1000000000000000000`
without a named constant is exactly the off-by-one trap WISDOM.md
warns about. A future refactor that bumps the contract to `1e18 + 1`
won't break the spec, masking the change.

**Suggested fix:** Replace the literal with `to_uint256(1000000000000000000)`
plus a comment cross-referencing
`ReserveOptimisticGovernor.sol:494-495`, or expose `1e18` as a constant
in the contract (e.g., `MAX_VETO_THRESHOLD`) and reference it. R5's
`newCapacity > 12` (Governor.spec:145) has the same shape — also
hardcoded.

---

### F8 [INFO]: Tight specs (no findings)

The following are tight under their stated scope:

- **RewardTokenRegistry**: R1-R7 are all clean. R6 (unregisterRemovesToken)
  has a real pre-state requirement (`require isRegistered(token)`);
  R7 (no cross-token bleed) tests the asymmetric direction correctly.
  The deferred direction (register flips to true) is honestly flagged
  in the docstring as needing EnumerableSet invariants.

- **StakingVault** SV1/SV2/SV8/SV9: zero-preserving conversions and
  the two delegateOptimistic rules are tight. SV8 in particular
  catches the side-effect frame ("call doesn't touch a non-caller's
  delegate") which is a non-trivial property even under NONDET
  summaries.

- **Timelock T1-T5**: standard auth-gate format, no issues.

- **Governor R1-R10** (apart from F7's cosmetic): the locked-timelock
  rule R1, the onlyGovernance gates R2/R3, and the parameter-validation
  rules R4-R10 are all well-formed. The `disable_internal_function_instrumentation`
  flag and the NONDET wall around OZ internals are deliberate scoping
  choices documented in the spec header.

- **OptimisticSelectorRegistry** R1-R5: tight. The deterministic
  ghost-backed `timelockAddr()` is a particularly good pattern (called
  out in the docstring) — it prevents two reads of `governor.timelock()`
  in the same transaction from returning different values, which would
  silently break the auth modifier.
