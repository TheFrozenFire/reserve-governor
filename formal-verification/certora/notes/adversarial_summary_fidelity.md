# Summary-fidelity adversarial review

## Summary

Across the 8 specs under `formal-verification/certora/`, the dominant
abstraction technique is wildcard external NONDET summaries. The
auth-gate rules tend to remain sound because the auth check executes
before any summarized call. The fidelity gaps cluster in three
places: (1) Guardian's two-read decision logic uses NONDET for both
reads, which is the same TOCTOU shape the prior adversarial review
flagged; (2) several library `external` summaries that are actually
delegatecalls writing to the calling contract's storage are
NONDET'd, so the prover sees the side effects vanish; (3) the spec
docstrings advertise properties (G6, U8) that have no corresponding
rule because the abstraction is too loose to express them. About
half the summaries are appropriately tight (gh ost-backed deterministic
readers in OptimisticSelectorRegistry, RewardTokenRegistry,
VersionRegistry); about half are too loose for the surface the
specs claim to cover.

Of the 7 findings below, the single most fidelity-relaxing summary
is **Guardian.spec NONDET on `_.isOptimistic(uint256)` and
`_.state(uint256)`** — the spec's docstring promises a rule (G6)
that requires the two reads to come from one consistent Governor
state, but the NONDET summary lets the prover pick different
answers for each call. The corresponding Rocq simulation
(`formal-verification/rocq/simulations/Guardian.v:351-391`)
explicitly threads a `GovernorStateSnapshot` through the
`cancel_with_governor_state` function specifically because of
this issue, then says the racing-cancel attack vector becomes
expressible only with that snapshot. The Certora spec does not
adopt the same discipline.

## Findings (severity-ordered)

### F1 [HIGH]: Guardian NONDET on the two-read cancel decision

**Where:** `formal-verification/certora/Guardian/Guardian.spec:31-32`

```cvl
function _.isOptimistic(uint256) external => NONDET;
function _.state(uint256) external => NONDET;
```

**Reality:** In `contracts/Guardian.sol:88-94`, the non-admin
branch of `cancel` reads the governor's view of the proposal
twice: `managedGovernor.isOptimistic(proposalId)` and
`IGovernor(governor).state(proposalId)`. In production, both
reads observe the SAME Governor storage in the SAME call frame:
they must agree about the same proposal.

**The summary admits:** The prover can pick `isOptimistic = true`
on the first call and then pick any `state` (including `Defeated`
== 3) on the second — or it can pick `isOptimistic = false` to
revert the first check entirely. Two reads of the same logical
state are treated as independent, which is the exact TOCTOU
shape the WISDOM C015 entry warns about.

**Impact on which rule(s):** The spec docstring promises a rule
**G6 "cancel by non-admin requires the proposal be optimistic AND
not Defeated"** at `Guardian.spec:10-11`, but there is no `rule G6`
in the file — `grep -n "^rule" Guardian.spec` shows only G1-G5.
The spec advertises a property it cannot prove because the
summary is too loose. G1-G5 themselves are sound (the auth check
happens before the summarized calls), but the cancel-decision
surface the docstring claims to cover is verifiably out of reach
under the current abstraction.

**Suggested fix:** Replace NONDET with per-proposalId ghost mappings:

```cvl
ghost mapping(uint256 => bool) ghostIsOptimistic;
ghost mapping(uint256 => uint8) ghostProposalState;

methods {
    function _.isOptimistic(uint256 pid) external
        => ghostIsOptimistic[pid] expect bool;
    function _.state(uint256 pid) external
        => ghostProposalState[pid] expect uint8;
}
```

Each rule can then `require` consistent values for the proposalId
under test, and a G6-shape rule becomes provable. Match the
shape of the existing OptimisticSelectorRegistry ghost summaries
at `OptimisticSelectorRegistry.spec:58-65`.

### F2 [HIGH]: Governor `_.hasRole` NONDET allows split decisions on the same role

**Where:** `formal-verification/certora/Governor/Governor.spec:56`

```cvl
function _.hasRole(bytes32, address) external => NONDET;
```

**Reality:** `contracts/governance/ReserveOptimisticGovernor.sol:377`:
`_validateCancel` calls `t.hasRole(CANCELLER_ROLE, caller)` against
the timelock. `contracts/governance/lib/ProposalLib.sol:44-46` also
calls `AccessControl(governor.timelock()).hasRole(OPTIMISTIC_PROPOSER_ROLE,
proposal.proposer)`. The timelock's AccessControl mapping is a
deterministic storage function — the same (role, account) pair
yields the same answer every time within a transaction.

**The summary admits:** Two `hasRole(CANCELLER_ROLE, alice)` calls
in one transaction can return `true` then `false`. A future rule
that proves a cancel-flow property by `require hasRole(...) = true`
would not be enforceable: the actual contract execution can call
`hasRole` and get `false` even when the rule's precondition asserts
otherwise.

**Impact on which rule(s):** The current R1-R10 do not exercise the
`_validateCancel` path nor `proposeOptimistic` (the latter is
NONDET'd at line 44). So no currently-VERIFIED rule is invalidated.
But the spec's auth-surface coverage is **incomplete** by exactly
the surface where `_.hasRole` matters; extending coverage to
cancel / propose / vote auth would require fixing this first.

**Suggested fix:** Ghost-back the `hasRole` summary keyed by
(role, account):

```cvl
ghost mapping(bytes32 => mapping(address => bool)) ghostHasRole;

methods {
    function _.hasRole(bytes32 r, address a) external
        => ghostHasRole[r][a] expect bool;
}
```

This matches `RewardTokenRegistry.spec:48-50` and
`VersionRegistry.spec:36-38`.

### F3 [HIGH]: Library delegatecall NONDETs erase storage mutation

**Where:** `formal-verification/certora/Governor/Governor.spec:42-46`

```cvl
function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
function _.getProposalsAvailable(...) external => NONDET;
function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, ...) external => NONDET;
function _.proposePessimistic(...) external => NONDET;
function _.transitionToPessimistic(...) external => NONDET;
```

**Reality:** These are `external` library functions taking `storage`
references — Solidity compiles them as `delegatecall`, so the
library code runs in the calling Governor's storage context and
**writes the Governor's own storage**: `consumeProposalCharge`
decrements `proposalThrottle.charges`,
`proposeOptimistic`/`proposePessimistic` writes
`GovernorUpgradeable._proposals[proposalId]` (the ProposalCore
struct passed by storage ref), `transitionToPessimistic` mutates
`optimisticProposalDetails[proposalId]`. See
`contracts/governance/lib/ThrottleLib.sol:18` and
`contracts/governance/lib/ProposalLib.sol:33-37`.

**The summary admits:** Certora's `NONDET` on an external function
returns an arbitrary value and **does not havoc the calling
contract's storage**. The prover therefore sees these calls as
no-ops on Governor storage. Any rule that asserts a storage
post-condition after a propose/transition call would be unsound
in the direction "Governor storage is unchanged".

**Impact on which rule(s):** R10 (`setProposalThrottlePersistsCapacity`)
is sound because `setProposalThrottle` does not transit
through any of these library functions (it writes
`proposalThrottle.capacity` directly inline). However, a natural
follow-up rule like "after a successful `proposeOptimistic`, the
proposalCore for that id has non-zero `voteStart`" would be
unprovable — the NONDET makes the storage write disappear and
the prover would observe `voteStart == 0` after the call.

**Suggested fix:** For delegatecalled libraries, summarize them
with `HAVOC_ALL` if the rule does not need their behavior, or
inline them via `DISPATCHER(true)` if the rule needs the storage
mutation. The current NONDET is the only summary that is both
"call disappears" and "no havoc" — too strong for what these
delegatecalls actually do.

### F4 [MED]: UnstakingManager NONDET on `_.transfer` ignores re-entrancy

**Where:** `formal-verification/certora/UnstakingManager/UnstakingManager.spec:42-46`

```cvl
function _.transfer(address, uint256) external => NONDET;
function _.transferFrom(address, address, uint256) external => NONDET;
function _.deposit(uint256, address) external => NONDET;
```

**Reality:** `claimLock` (contracts/staking/UnstakingManager.sol:78-79):

```solidity
lock.claimedAt = block.timestamp;
SafeERC20.safeTransfer(targetToken, lock.user, lock.amount);
```

The transfer call is to an external token contract. A non-trivial
ERC20 (a hook-enabled token, ERC777, or an upgradeable token whose
implementation calls back) can re-enter UnstakingManager during
the transfer.

**The summary admits:** NONDET returns an arbitrary `bool` but
does **not** havoc UnstakingManager's storage. The prover
therefore assumes the transfer cannot affect `locks[lockId]` or
any other state. U7's assertion `claimedAtAfter == block.timestamp`
holds trivially under this assumption: the storage write at
line 78 cannot be undone by anything during line 79.

In reality, a re-entrant token transfer could call
`claimLock(lockId)` again. The contract would `require
lock.claimedAt == 0` and revert — so the property is in fact
preserved by the contract's own logic. But the **spec does not
exercise that logic**: it just trusts that NONDET behaves like
a pure return.

**Impact on which rule(s):** U7 (`claimStampsTimestamp`) is true
in practice but proved under an abstraction that does not stress
the re-entrancy boundary. If `safeTransfer` is later changed in
a way that affects re-entrancy guarantees (or `targetToken` is a
malicious token in production), the rule's "proven" status would
not catch the regression.

**Suggested fix:** Where re-entrancy matters, either model the
transfer with `HAVOC_ECF` (havoc external contracts but not the
calling one) plus an explicit re-entrancy guard precondition, or
add a separate rule that proves the re-entrancy guard itself
(here: `require lock.claimedAt == 0` is the guard).

### F5 [MED]: StakingVault `_calculateHandout` CONSTANT erases input dependence

**Where:** `formal-verification/certora/StakingVault/StakingVault.spec:52`

```cvl
function _calculateHandout(uint256, uint256) internal returns (uint256) => CONSTANT;
```

**Reality:** `contracts/staking/StakingVault.sol:480-494`:

```solidity
function _calculateHandout(uint256 balanceAvailable, uint256 elapsed)
    internal view returns (uint256) {
    if (balanceAvailable == 0 || elapsed == 0 || totalSupply() == 0) {
        return 0;
    }
    // ...
}
```

The function explicitly returns 0 when any of its three guards
hit. `_currentAccountedNativeRewards` calls it with
`(nativeBalanceLastKnown - totalDeposited, elapsed)`. The
function is called multiple times per transaction with
**different** argument values.

**The summary admits:** CONSTANT picks ONE uint256 value at the
start of the rule and returns it for every call regardless of
inputs. A call site with `balanceAvailable == 0` (which reality
returns 0 for) will get the same non-zero value as a call site
with a real balance. Worse, `_currentAccountedNativeRewards`
computes `nativeBalanceLastKnown - totalDeposited` which can
underflow — but the prover never sees the call body, so the
underflow path is invisible.

**Impact on which rule(s):** SV1/SV2 (convertToShares/Assets of 0
== 0) are sound because the formula `0 * X / Y = 0` doesn't
depend on totalAssets, regardless of what the handout is. SV3
(deposit mints exactly `shares`) is also sound for the same
reason — shares is the return value of `_convertToShares` inside
deposit, and the mint amount is whatever `super._deposit` mints.
The CONSTANT summary is therefore appropriate **for the chosen
rules**, but the spec header at line 47-52 claims it's sound
"since they do not depend on the specific handout value, only
that it is consistent across the rule." That's true for the
selected rules but the docstring should not be read as a
general statement: any future rule that needs the zero-input
branch (e.g., "totalAssets == totalDeposited when block.timestamp
== nativeRewardsLastPaid") would silently fail to enforce it.

**Suggested fix:** When extending to rules that depend on the
zero-input behavior of `_calculateHandout`, replace CONSTANT
with a per-input ghost or with a CVL function summary that
encodes the early-return guards explicitly. The
`MIN_REWARD_HALF_LIFE` / `MAX_REWARD_HALF_LIFE` constraints
also do not appear in the spec — they're guards on
`rewardRatio` that the CONSTANT model bypasses.

### F6 [MED]: VersionRegistry `_.version()` NONDET feeds keccak256, breaks injective deployer->hash

**Where:** `formal-verification/certora/VersionRegistry/VersionRegistry.spec:42`

```cvl
function _.version() external => NONDET;
```

**Reality:** `contracts/VersionRegistry.sol:42-43`:

```solidity
string memory version = Versioned(address(deployer)).version();
bytes32 versionHash = keccak256(abi.encodePacked(version));
```

In production, each deployer's `version()` returns a deterministic
string baked in at deployment. Two distinct deployer addresses
return distinct strings only if their code differs — but the
deduplication check at line 45 ensures the same versionHash
cannot be re-registered.

**The summary admits:** NONDET lets `version()` return arbitrary
strings of arbitrary length. With `optimistic_hashing: true`
(conf line 5), Certora assumes hashes are collision-free on
constant-length inputs, but the NONDET'd string has
prover-chosen length. The prover can make two different deployer
addresses produce the same string -> the same versionHash, which
the contract's `require` at line 45 will then catch as a
duplicate registration.

**Impact on which rule(s):** V8 (`registerDoesNotOverwriteExisting`)
calls `registerVersion(e, newDeployer)` without `@withrevert`,
so a NONDET-induced collision causes the call to revert
inside `registerVersion`, making the rule vacuously hold. The
rule is provable but provides weaker assurance than its
docstring suggests: it does not actually establish that
distinct deployers yield distinct hashes, only that the require
catches collisions when they happen.

**Suggested fix:** If the docstring intent is "distinct deployers
yield distinct hashes by injectivity of `version`," that needs
an explicit assumption — either a ghost
`address -> bytes32` that the spec requires to be injective, or
an axiom relating `version()` to the deployer address. The
current setup proves something weaker than the docstring
implies.

### F7 [LOW]: UnstakingManager docstring promises U8 that has no rule

**Where:** `formal-verification/certora/UnstakingManager/UnstakingManager.spec:22`

The spec header lists:

```
U8   createLock increments nextLockId by 1
```

**Reality:** `nextLockId` in `contracts/staking/UnstakingManager.sol:22`
is a `private` storage variable, with no public getter. The
contract definitely does `uint256 lockId = nextLockId++;` at
line 45 — that is observable post-condition.

**The summary admits:** Nothing — there is no summary issue here
per se. The fidelity gap is that the spec **does not declare a
reader** for `nextLockId` in its `methods` block (only `locks`,
`vault`, `targetToken`). The U8 rule cannot be written without
either a getter on the contract or a ghost shadowing nextLockId.

**Impact on which rule(s):** U8 is advertised in the docstring but
no `rule` exists for it (`grep -n "^rule" UnstakingManager.spec`
shows U1-U7). The spec's coverage claim is weaker than the
docstring implies.

**Suggested fix:** Either add a public getter for `nextLockId` on
the contract (lowest cost), or ghost-shadow it in the spec by
hooking on the SSTORE at the relevant slot. Or, more cheaply
honest, remove U8 from the docstring header.
