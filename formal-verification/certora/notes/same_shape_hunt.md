# Hunt: same-shape opportunities

Read-only audit for further instances of the Cantina PR #36 shape:
a function computes a quantity (threshold, bound, decision, target,
auth) from input X where multiple plausible sources exist and the
chosen X is wrong relative to the function's documented intent.

## Methodology

Read the postmortem (`cantina_pr36_postmortem.md`), the priority
framework (`exploration_rocq_cas_alignment.md`), and the prior
adversarial synthesis. Then read every contract in scope end to end
(`contracts/Guardian.sol`, `contracts/VersionRegistry.sol`,
`contracts/Deployer.sol`, `contracts/governance/*.sol`,
`contracts/governance/lib/*.sol`, `contracts/staking/*.sol`).
Cross-referenced the OZ Governor / Votes upstream
(`emv-*/inputs/.certora_sources/.../GovernorUpgradeable.sol`,
`VotesUpgradeable.sol`) to see what each downstream method returns
and which alternative sources exist for the same quantity. Scanned
Rocq simulations for opaque-parameter signals (`grep Parameter
*.v`) and the Foundry test suite for hints about non-obvious intent
(e.g. `test_optimisticProposal_autoCancelsWhenPastSupplyIsZero`).

Note on framing: the Cantina headline bug itself
(`ReserveOptimisticGovernor.sol:249`) is still present on this
branch — the postmortem describes the forthcoming fix, not a
landed one. The hunt below excludes that exact line and looks for
**other** wrong-source choices in the same codebase.

## Findings (ranked by likelihood-of-bug x impact)

### F1 [HIGH]: `proposalThreshold()` measures proposer's voting power against TOTAL supply, but only DELEGATED supply can actually meet it

**Location:** `contracts/governance/ReserveOptimisticGovernor.sol:302-315`

**Pattern type:** Wrong-population denominator (same family as Cantina).

**The code:**

```solidity
function proposalThreshold() public view override(...) returns (uint256) {
    uint256 proposalThresholdRatio = super.proposalThreshold(); // D18{1}

    // {tok}
    uint256 supply = Math.max(1, token().getPastTotalSupply(block.timestamp - 1));

    // CEIL to make sure thresholds near 0% don't get rounded down to 0 tokens
    return (proposalThresholdRatio * supply + (1e18 - 1)) / 1e18;
}
```

The threshold is then compared against the proposer's *delegated*
voting weight in `ProposalLib.proposePessimistic`
(`contracts/governance/lib/ProposalLib.sol:82-88`):

```solidity
uint256 votesThreshold = governor.proposalThreshold();
uint256 proposerVotes = governor.getVotes(proposal.proposer, block.timestamp - 1);
require(proposerVotes >= votesThreshold, ...);
```

**The plausible-but-wrong source:** `getPastTotalSupply` — includes
every minted StakingVault share, including shares whose holder has
never delegated.

**The semantically-correct source:** The supply of *delegated* votes
(`Σ getVotes(d, t)` across delegates `d`) — i.e., the population
whose voting weight is comparable to `getVotes(proposer, t)`.

**Why it might be wrong:** Per OZ's own warning in
`VotesUpgradeable.sol:126-128`:

> NOTE: This value is the sum of all available votes, which is not
> necessarily the sum of all delegated votes. Votes that have not
> been delegated are still part of total supply, even though they
> would not participate in a vote.

The contract docs at `ReserveOptimisticGovernor.sol:87` say
"proposalThreshold D18{1} Fraction of tok supply required to
propose". The word "fraction" implies a comparison against the
**reachable** voting population. If 70% of StakingVault shares are
held by users who never called `delegate()`, the proposer must hold
≥ `proposalThresholdRatio * totalSupply` in *delegated* votes — a
larger absolute amount than the spec implies. In the limit, if a
single whale holds the entire delegated supply but only 30% of total
supply, **the threshold may be unreachable by any single voter even
though the design intent ("a fraction of the voting population")
treats them as the de facto majority**. This is exactly the Cantina
shape: numerator and denominator drawn from different populations.

The StakingVault does NOT auto-self-delegate (see `_delegate` usage
in `depositAndDelegate` is opt-in; the bare `deposit` does not
delegate). So undelegated supply is the **default** state, not a
corner case.

**Why it might be correct:** This mirrors OZ's standard Governor
pattern. The intent may be that proposers should be required to
hold a fraction-of-total-supply level of delegated weight, even if
that's structurally harder to reach. The CEIL rounding suggests
this was thought-through (errs toward "thresholds near 0% don't
round to 0"). One could read the spec as deliberately "1% of total
supply" rather than "1% of delegated votes" — a more conservative
gate that scales with the underlying token, not with delegation
participation.

**Intent-derived rule sketch:**

```cvl
rule proposalThresholdReachableByDelegates(env e) {
    uint256 threshold = proposalThreshold(e);
    uint256 supplyAtT = sumDelegatedVotesAt(e.block.timestamp - 1);
    // Reachable: the entire delegated voting supply must be >= threshold
    assert threshold <= supplyAtT,
        "proposalThreshold exceeds the supply that could meet it";
}
```

**Confidence:** Medium-high that this is a same-shape *risk*; lower
that the team would treat it as a bug rather than as-designed.
The Cantina bug had the *exact same defense* available ("we picked
total supply on purpose"), and the fix overrode that defense. This
is the strongest candidate for the same treatment.

---

### F2 [HIGH]: `state()` auto-cancel uses TOTAL supply but the threshold below it uses TOTAL supply — both wrong relative to the optimistic-voting population

**Location:** `contracts/governance/ReserveOptimisticGovernor.sol:249-258`

**Pattern type:** Wrong-population denominator, second instance of
the same shape as the headline.

**The code:**

```solidity
// {tok}
uint256 pastSupply = token().getPastTotalSupply(snapshot);

if (pastSupply == 0) {
    return ProposalState.Canceled;
}

// {tok} = D18{1} * {tok} / D18{1}
uint256 vetoThresholdTok = (_vetoThreshold * pastSupply) / 1e18;
vetoThresholdTok = Math.max(vetoThresholdTok, 1);
```

**The plausible-but-wrong source:** `getPastTotalSupply(snapshot)`.

**The semantically-correct source:** The aggregate `getPastOptimisticVotes`
across all optimistic delegates at `snapshot` — i.e., the supply
whose veto weight can actually accumulate against this proposal.
Per the postmortem, the PR-#36 fix adds
`getPastOptimisticVotingSupply()` for exactly this read.

**Why it might be wrong:** This is the EXACT line the Cantina
postmortem identifies (line 249). It is included as a
finding-against-this-branch because the fix has not landed on
this branch — the postmortem documents the fix that's coming. The
adjacent line 251 auto-cancel decision is the **secondary
manifestation of the same bug**: it triggers auto-cancel when total
supply is zero, but the intended trigger is when optimistic-voting
supply is zero. A proposal with non-zero total supply but zero
optimistic-delegated supply has an unreachable veto and should
also auto-cancel; the current logic lets it proceed and either
Succeed by deadline or fail vacuously.

**Why it might be correct:** It's the headline bug, included only
because reviewers reading this branch in isolation will land here
first. Stated correctness: zero total supply is a strictly weaker
trigger than zero optimistic supply, and total-supply == 0 is the
edge case the test
(`test_optimisticProposal_autoCancelsWhenPastSupplyIsZero`) was
written to validate. The fix should change both lines together.

**Intent-derived rule sketch:**

```cvl
rule autoCancelWhenNoOptimisticSupply(env e) {
    uint256 pid;
    require isOptimistic(pid);
    require getPastOptimisticVotingSupply(snapshot(pid)) == 0;
    require !proposalExecuted(pid) && !proposalCanceled(pid);
    require snapshot(pid) < e.block.timestamp;
    assert state(e, pid) == ProposalState.Canceled;
}
```

**Confidence:** High — this is the Cantina pair-bug. Listed
separately from F-headline because line 251's auto-cancel branch
is its own decision point that future audits should test, not
just the threshold formula at 256.

---

### F3 [MED]: `_validateCancel` lets an optimistic proposer cancel their own ACTIVE proposal, enabling snapshot-refresh evasion

**Location:** `contracts/governance/ReserveOptimisticGovernor.sol:374-388`

**Pattern type:** Wrong-precondition propagation / Wrong-actor-set
check on the cancel surface.

**The code:**

```solidity
function _validateCancel(uint256 proposalId, address caller) internal view override returns (bool) {
    TimelockControllerOptimistic t = _timelock();
    if (t.hasRole(CANCELLER_ROLE, caller)) return true;
    if (caller != proposalProposer(proposalId)) return false;

    ProposalState s = state(proposalId);
    return _isOptimistic(proposalId) ? s != ProposalState.Defeated : s == ProposalState.Pending;
}
```

**The plausible-but-wrong source:** `s != ProposalState.Defeated`
for the optimistic case — the most permissive set possible
(Pending ∪ Active ∪ Succeeded). The pessimistic branch by contrast
uses the most restrictive set (`Pending` only).

**The semantically-correct source:** The intent for both flavors
is "let the proposer abandon the proposal before it commits to a
vote". Pessimistic uses Pending. Optimistic should likely use
Pending too, or at most `Pending ∪ Active-without-vetoes`.

**Why it might be wrong:** With the current rule, an optimistic
proposer can watch the veto tally accumulate in Active state and
cancel **before** the threshold is crossed. They can then re-propose
the same calldata, which (a) consumes throttle but (b) resets the
voteStart to a new timestamp, forcing vetoers to re-discover the
proposal and re-vote against. Looping this is bounded by the
throttle but it grinds vetoers down on signaling cost. The
asymmetry with the pessimistic branch (which is correctly
restricted to `Pending`) suggests the optimistic branch's permissive
set was a copy-paste-divergence error, not a deliberate distinction.

The same applies to `Succeeded`: optimistic proposer cancelling a
*succeeded* proposal between deadline-passing and
queue/bypass-execution is a unilateral last-second veto by the
proposer themselves. Probably not intended.

**Why it might be correct:** The OPTIMISTIC_PROPOSER_ROLE is a
**trusted** role, granted by timelock vote. The intent may be
"trusted proposer should be able to retract at any pre-execution
phase". The Defeated exclusion is then the load-bearing rule (so a
proposer can't undo a successful veto). Pessimistic proposers
aren't trusted (permissionless), hence the tighter `Pending`
restriction.

**Intent-derived rule sketch:**

```cvl
rule optimisticProposerCannotCancelActive {
    uint256 pid; address caller;
    require isOptimistic(pid);
    require caller == proposalProposer(pid);
    require !timelockHasCancellerRole(caller);
    require state(pid) == ProposalState.Active;
    assert !_validateCancel(pid, caller);  // expected: cancel rejected
}
```

**Confidence:** Medium. The asymmetry against the pessimistic
branch is the strongest signal; the steelman (trusted role) is
plausible but the spec does NOT document the asymmetry.

---

### F4 [MED]: `transitionToPessimistic` carries forward the original proposer without re-validating proposalThreshold or OPTIMISTIC_PROPOSER_ROLE

**Location:** `contracts/governance/lib/ProposalLib.sol:109-143`,
in particular line 135: `governor.proposalProposer(proposalId)`.

**Pattern type:** Wrong-precondition propagation.

**The code:**

```solidity
ProposalData memory proposalData = ProposalData(
    newProposalId,
    governor.proposalProposer(proposalId),  // <-- carries forward original optimistic proposer
    optimisticProposal.targets,
    optimisticProposal.values,
    optimisticProposal.calldatas,
    newDescription
);

_saveProposal(proposalData, proposalCores[newProposalId], governor.votingDelay(), governor.votingPeriod());
```

**The plausible-but-wrong source:** The original-proposal proposer
address, unconditionally.

**The semantically-correct source:** Either (a) the same address
**only if** they still meet the threshold that a fresh pessimistic
proposal would require, or (b) a sentinel `address(this)` /
`address(0)` so the post-transition proposal has no privileged
proposer.

**Why it might be wrong:** When `proposePessimistic` is called
the normal way, OZ requires `proposerVotes >= votesThreshold`
(`ProposalLib.sol:85`). The transition path **skips this check
entirely** — `_saveProposal` is called directly. The original
proposer may not satisfy the standard threshold (optimistic
proposers don't need stake; they're role-gated). The fresh
pessimistic proposal is then "owned" by an address that, in normal
circumstances, could not have created it.

Downstream impact: that proposer can `cancel()` the new pessimistic
proposal in its Pending state per `_validateCancel`'s permissive
branch for the proposer-equals-caller case. They can also call any
proposer-only governor hooks. The OPTIMISTIC_PROPOSER_ROLE may
have been revoked between the original propose and the transition
(`TimelockControllerOptimistic.revokeOptimisticProposer`), so a
*formerly* trusted account can wind up controlling a pessimistic
proposal that the rest of the system trusts.

**Why it might be correct:** The design intent of
`transitionToPessimistic` may be "preserve all original attribution
so the new vote re-litigates the same calldata under the same
sponsor". Skipping the threshold makes sense if the optimistic
proposal already had de-facto threshold (it was role-gated). The
risk is bounded because the transitioned proposal can be cancelled
by anyone with CANCELLER_ROLE (Guardian, timelock).

**Intent-derived rule sketch:**

```cvl
rule transitionedProposalProposerMeetsThreshold {
    uint256 oldPid; uint256 newPid;
    require transitionsTo(oldPid, newPid);
    address proposer = proposalProposer(newPid);
    uint256 proposerVotes = getVotes(proposer, snapshot(newPid));
    assert proposerVotes >= proposalThreshold(),
        "transitioned proposal's carried-over proposer lacks threshold";
}
```

**Confidence:** Medium. The intent here is ambiguous in the spec.
The Rocq sim (`Governor.v`) does model the transition but doesn't
encode any post-transition proposer constraint, which is itself a
signal — the simulation is encoding the implementation, not the
intent.

---

### F5 [MED]: `UnstakingManager.claimLock` has no auth check, allowing any caller to force-claim someone else's lock

**Location:** `contracts/staking/UnstakingManager.sol:72-82`

**Pattern type:** Wrong-actor-set check — missing auth, and the
missing check is exactly the one that exists on the sibling
function `cancelLock`.

**The code:**

```solidity
function claimLock(uint256 lockId) external {
    Lock storage lock = locks[lockId];

    require(lock.unlockTime <= block.timestamp && lock.unlockTime != 0, UnstakingManager__NotUnlockedYet());
    require(lock.claimedAt == 0, UnstakingManager__AlreadyClaimed());

    lock.claimedAt = block.timestamp;
    SafeERC20.safeTransfer(targetToken, lock.user, lock.amount);

    emit LockClaimed(lockId);
}
```

Contrast with `cancelLock` (line 55-70) which DOES have
`require(user == msg.sender, UnstakingManager__Unauthorized())`.

**The plausible-but-wrong source:** "anyone" (no auth) versus
`cancelLock`'s `lock.user == msg.sender`.

**The semantically-correct source:** `lock.user == msg.sender`
(consistent with the sibling).

**Why it might be wrong:** Funds aren't stealable — `safeTransfer`
targets `lock.user`. But the side effect is real: a griefer can
front-run a user's `cancelLock` with a `claimLock`, irreversibly
ending the lock at the unlock time. The user loses the option to
re-stake during the unlock window. This is a wrong-actor-set
choice because the function's *intent* per its naming
("`claim` the lock") implies the lock owner is the actor; the
**implementation** lets anyone push the action through.

**Why it might be correct:** A common idiom is "claims are
permissionless — they only ever transfer funds to the rightful
owner". Auto-claiming via a relayer is convenient. The decision
might be deliberate to support keepers / claim-bots. The asymmetry
with `cancelLock` is justifiable: cancel changes intent
(re-deposit), so the user must opt in; claim just realizes the
already-intended transfer.

**Intent-derived rule sketch:**

```cvl
rule onlyOwnerCanClaim {
    uint256 lockId; env e;
    address user = getLockUser(lockId);
    require e.msg.sender != user;
    require getLockClaimedAt(lockId) == 0;
    claimLock@withrevert(e, lockId);
    assert lastReverted, "non-owner could claim";
}
```

**Confidence:** Medium. This is the classic "claim is permissionless,
cancel is permissioned" idiom. Worth confirming the team's
intent — the asymmetry with `cancelLock` is the only signal.

---

### F6 [MED]: `StakingVault._authorizeUpgrade` checks deprecation of the LATEST version, not the SPECIFIC target version

**Location:** `contracts/staking/StakingVault.sol:530-541`

**Pattern type:** Wrong-snapshot read (subtle): the deprecation
bool returned by `getLatestVersion()` is for the latest entry, not
for the `stakingVaultImpl` being authorized.

**The code:**

```solidity
function _authorizeUpgrade(address stakingVaultImpl) internal view override onlyRole(DEFAULT_ADMIN_ROLE) {
    bytes32 versionHash = keccak256(abi.encodePacked(Versioned(stakingVaultImpl).version()));

    // RoleRegistry SHOULD maintain fresh latest versions

    (bytes32 latestVersionHash,,, bool deprecated) = versionRegistry.getLatestVersion();
    require(!deprecated, Vault__VersionDeprecated(versionHash));
    require(versionHash == latestVersionHash, Vault__NotLatestStakingVault(stakingVaultImpl));

    (address latestStakingVaultImpl,,) = versionRegistry.getImplementationsForVersion(versionHash);
    require(latestStakingVaultImpl == stakingVaultImpl, Vault__NotLatestStakingVault(stakingVaultImpl));
}
```

**The plausible-but-wrong source:** `versionRegistry.getLatestVersion()`
returns `deprecated` for the latest registered version, then the
code separately requires `versionHash == latestVersionHash`. The
two checks together happen to be correct (if target == latest AND
latest not deprecated, allow). But the deprecation read is from a
function tied to the *registry's latest*, not from a per-hash
deprecation read.

**The semantically-correct source:**
`versionRegistry.isDeprecated[versionHash]` — the deprecation flag
for the specific target.

**Why it might be wrong:** The current code works **by accident**.
If `getLatestVersion()` is ever refactored to return deprecation
status for a different version (e.g., previous-latest, or
target-of-an-upgrade-pointer), this contract silently allows or
silently rejects based on the wrong version's flag. The
documentation hint at line 533 ("RoleRegistry SHOULD maintain fresh
latest versions") suggests the team is aware the read is delicate.

Also: `VersionRegistry.deprecateVersion` (`contracts/VersionRegistry.sol:53-61`)
does **not** require `deployments[versionHash] != address(0)` — you
can flag-deprecate a never-registered hash. If `latestVersion`
points to a hash whose deprecation was set *before* registration,
then a future re-registration of the same hash leaves it
permanently deprecated, and the upgrade gate locks out the *only*
non-deprecated implementation. The wrong-source read here couples
to that missing constructor check at VersionRegistry.

**Why it might be correct:** As of today the two checks together
(latest + deprecated-on-latest) are equivalent to (target ==
latest && target-not-deprecated). The code is a single-source-of-
truth simplification. The maintenance hazard is real but the
current behavior is correct.

**Intent-derived rule sketch:**

```cvl
rule upgradeRejectsDeprecatedTarget {
    address impl; bytes32 hash;
    require versionHashOf(impl) == hash;
    require versionRegistry.isDeprecated(hash);
    _authorizeUpgrade@withrevert(impl);
    assert lastReverted, "deprecated target was authorized";
}
```

**Confidence:** Medium. The bug is latent — the existing two-check
pattern is correct today. The risk is "this is a shape-mismatch
between the intent ('reject deprecated target') and the
implementation ('reject if latest is deprecated AND target ==
latest')". A small refactor of `getLatestVersion` could flip the
behavior silently.

---

### F7 [LOW]: `proposalThreshold` and `vetoThreshold` use opposite rounding directions for analogous formulas

**Location:**
- `contracts/governance/ReserveOptimisticGovernor.sol:314` (CEIL,
  pessimistic): `(proposalThresholdRatio * supply + (1e18 - 1)) / 1e18`
- `contracts/governance/ReserveOptimisticGovernor.sol:256-257` (FLOOR + max(1),
  optimistic): `(_vetoThreshold * pastSupply) / 1e18` then `Math.max(.., 1)`

**Pattern type:** Wrong-direction rounding / saturation.

**The code:**

```solidity
// proposalThreshold (CEIL)
return (proposalThresholdRatio * supply + (1e18 - 1)) / 1e18;

// vetoThreshold (FLOOR + max(1))
uint256 vetoThresholdTok = (_vetoThreshold * pastSupply) / 1e18;
vetoThresholdTok = Math.max(vetoThresholdTok, 1);
```

**The plausible-but-wrong source:** FLOOR + max(1) for veto.

**The semantically-correct source:** Same rounding direction for
both — typically CEIL for both ("never round down such that the
threshold accidentally drops below the intent").

**Why it might be wrong:** The asymmetry has no documented
justification. CEIL prevents rounding-to-zero for tiny fractions.
FLOOR+max(1) also prevents zero but lets every other case round
**down**, making the veto threshold strictly easier to clear (by
up to 1e18 - 1 tokens worth). For a vetoThreshold of, say, 0.10e18
on a supply of 1.5e18 tokens, FLOOR gives `(0.1e18 * 1.5e18) / 1e18
= 0.15e18` exactly. No drift. But for arbitrary `_vetoThreshold *
pastSupply` not divisible by 1e18, the veto path rounds in favor of
the vetoer; the propose path rounds against the proposer. Whether
that's the intended directionality is unclear.

**Why it might be correct:** The asymmetry could be intentional —
the veto threshold should be "as low as possible without being
zero" (favor vetoers, since vetoes are a safety mechanism). The
propose threshold should be "as high as possible without being
zero" (favor caution, since proposing is a privilege). If so,
this is by-design.

**Intent-derived rule sketch:**

```cvl
rule thresholdRoundingConsistency {
    uint256 ratio; uint256 supply;
    uint256 ceiled = ceilDiv(ratio * supply, 1e18);
    uint256 floored = (ratio * supply) / 1e18;
    // Whichever the team intends, assert it explicitly.
    assert vetoThresholdTokOf(ratio, supply) == ceiled, "veto threshold rounds the wrong way";
}
```

**Confidence:** Low. The asymmetry is real but plausibly intent.

---

### F8 [LOW]: `_moveOptimisticDelegateVotes` uses `latest()` while `_authorizeUpgrade` uses a structured registry read — neither is wrong, but the pattern reuse is brittle

**Location:** `contracts/staking/StakingVault.sol:551-571`

**Pattern type:** Wrong-checkpoint lookup (potential — flagging
for monitoring not as a bug).

**The code:**

```solidity
Checkpoints.Trace208 storage fromCheckpoints = optimisticDelegateCheckpoints[from];
uint256 oldValue = fromCheckpoints.latest();
uint256 newValue = oldValue - amount;
fromCheckpoints.push(clock(), SafeCast.toUint208(newValue));
```

**The plausible-but-wrong source:** `latest()` for the current
balance.

**The semantically-correct source:** `latest()` IS correct here —
the invariant is that the LATEST checkpoint reflects the current
delegated supply for that delegate. `upperLookupRecent(clock())`
would be wrong because clock() might match an older checkpoint key
within the same block.

**Why it might be wrong:** It isn't, under the standard
Checkpoints semantics. Flagged because:
- The amount-underflow protection here relies on the invariant
  `latest() >= amount`. If a re-entrancy or out-of-order
  `_delegateOptimistic` call inflated `optimisticDelegatees` without
  a corresponding `_moveOptimisticDelegateVotes`, the latest() value
  could be lower than `amount`, causing a silent underflow.
- The pre-PR-36 codebase did not have a `_totalCheckpoints`
  mirror for optimistic supply; per the postmortem PR #36 adds
  one. Until that lands, **there's no way to read aggregate
  optimistic-voting supply at a past snapshot** — making F1 and F2
  literally unfixable on this branch with the current contract
  surface. The patches will need to add the `VotesStorage`-style
  mirror.

**Why it might be correct:** Standard pattern, identical to OZ
ERC20Votes' `_moveVotingPower`. Nothing wrong here in isolation.

**Intent-derived rule sketch:**

```cvl
invariant optimisticLatestMatchesDelegated(address d)
    optimisticDelegateCheckpoints[d].latest() == sum(balanceOf[a] for a where optimisticDelegatees[a] == d);
```

**Confidence:** Low — diagnostic finding, not a bug.

---

## Cross-contract / out-of-scope observations

A few things I noticed in passing that aren't quite the Cantina
shape but are worth recording:

- **`OptimisticSelectorRegistry._add`**
  (`contracts/governance/OptimisticSelectorRegistry.sol:84-104`)
  checks `target != address(governor.token())`. The token is
  fixed-at-init in OZ Governor, but a future refactor that adds a
  setter would silently change which target gets blacklisted. Wrong-
  source-via-future-mutation. Low risk today.

- **`VersionRegistry.deprecateVersion`**
  (`contracts/VersionRegistry.sol:53-61`) does not require the
  versionHash to be registered. Couples to F6 as a hazard
  multiplier.

- **`Guardian.cancel`** (`contracts/Guardian.sol:88-94`) calls
  `IGovernor(governor).state(proposalId) != Defeated` before
  cancelling. For an optimistic proposal that has TRANSITIONED to
  pessimistic, `vetoThreshold == TRANSITIONED_VETO_THRESHOLD` and
  `state()` returns Defeated, blocking guardian cancel. That's
  correct, but the implicit dependency on `state()` doing the
  TRANSITIONED special-case is fragile — a refactor that moves
  the "transitioned == Defeated" logic elsewhere would let the
  guardian cancel a post-transition optimistic proposal.

## Patterns-not-instances

Risk classes future audits in this codebase should focus on:

1. **External-vote-read alternatives.** Any read from
   `IOptimisticVotes` or `IVotes` with multiple plausible methods
   (`getPastTotalSupply` vs `getPastVotes` vs the forthcoming
   `getPastOptimisticVotingSupply`) is a Cantina-shape risk. In this
   codebase the relevant reads are at
   `ReserveOptimisticGovernor.sol:249` (state), `:311` (proposalThreshold),
   `:413` (castVote), `:509` (_getOptimisticVotes), and `ProposalLib.sol:83`
   (proposePessimistic). F1, F2, and the Cantina headline are three
   of those five sharing the same shape.

2. **Carried-forward identities through state-machine transitions.**
   Anywhere a value (proposer, timestamp, hash) is read once and
   carried into a fresh entity (transitioned proposal, replayed
   id, cloned lock), the original validity context is dropped. F4
   is the explicit case (proposer carries forward without
   re-validation). Auditors should walk every cross-entity copy:
   `ProposalLib.transitionToPessimistic`, `getProposalId` aliasing,
   and the `executeBatchBypass` salt mixing
   (`ReserveOptimisticGovernor.sol:356`).

3. **Asymmetric cousin functions.** When two functions guard the
   same resource with different rules (`cancelLock` requires owner,
   `claimLock` does not — F5; `_validateCancel`'s
   optimistic-vs-pessimistic branches — F3; veto-vs-propose rounding
   — F7), the asymmetry is either a deliberate distinction
   (should be in the spec) or a copy-paste-drift (should be a
   finding). Default to skepticism.

4. **Reading aggregate state via a "latest" pointer when the
   intent is per-target.** F6 reads deprecation via
   `getLatestVersion()` because today latest-deprecation and
   target-deprecation coincide. Anywhere a contract uses
   "X.getLatest()" instead of "X.getFor(key)", a future
   refactor of "getLatest" can silently change the semantics.

5. **Rocq simulations with opaque parameters.** Per the postmortem,
   anywhere `rocq/simulations/*.v` takes a `Parameter` or opaque
   argument is a place the production contract picks a concrete
   source and could pick wrong. Highest-risk in this codebase:
   `Governor.v` (`pastSupply`), `ProposalLib.v` (proposer suffix
   parsing), `VersionRegistry.v` (`is_owner` predicate — opaque
   in Rocq, concrete `roleRegistry.isOwner` in Solidity). Each is
   a meta-rule candidate: "the production contract MUST pass the
   X corresponding to the Y in the invariant."
