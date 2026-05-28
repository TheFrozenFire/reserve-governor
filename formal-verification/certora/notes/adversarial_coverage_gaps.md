# Coverage-gap adversarial review

Adversarial review of the Certora specs under `formal-verification/certora/`.
Read-only audit. Each contract's external/public surface, custom errors,
and validation `require`s were enumerated and compared against the rules in
the corresponding spec. Items already deferred in spec headers, covered by
Rocq proofs, or excluded by the conf summarisation strategy (NONDET) are
noted as such and not double-counted. Citations are `file:line`.

## Summary

| Contract | Public/external fns | Custom errors | Spec rules | Gap profile |
|---|---|---|---|---|
| Guardian | 4 + ctor | 6 | 5 | Medium — `revokeOptimisticProposer` happy path unchecked; G6 documented but not implemented |
| UnstakingManager | 3 + ctor | 3 | 7 | Low — `createLock` happy-path state mutations not asserted |
| RewardTokenRegistry | 4 + ctor | 4 | 7 | Low — strong; positive-direction `register` membership deferred (HAVOC) |
| OptimisticSelectorRegistry | 4 + ctor + init | 3 | 6 | **Medium-High** — `initialize` entirely uncovered; three of four `_add`-forbidden targets untested |
| TimelockControllerOptimistic | 4 + ctor + init | 2 | 7 | Medium — `_authorizeUpgrade` (UUPS) untested; `executeBatchBypass` value-forwarding only covered with empty arrays |
| VersionRegistry | 4 + ctor | 5 | 7 | Low-Medium — `getLatestVersion` revert deferred (V7); `getImplementationsForVersion` revert-on-unknown uncovered |
| ReserveOptimisticGovernor | 11 public/external + 10 internal overrides | 7 | 10 | **High** — every actual proposal-lifecycle mutation (`proposeOptimistic`, `propose`, `cancel`, `_queueOperations`, `_executeOperations`, `_validateCancel`, `_countVote`, `_tallyUpdated`) is NONDET'd; only setters proved |
| StakingVault | 16 public/external | 9 | 9 | **High** — only auth gates + ERC4626 zero-edges; `addRewardToken`/`removeRewardToken` reverts (5 distinct paths), `_authorizeUpgrade` version-pinning, `delegateOptimisticBySig`, withdraw/rewards-accrual happy paths all uncovered |

**Biggest gap:** ReserveOptimisticGovernor (Governor.spec). The headline
optimistic-overlay logic — the entire `proposeOptimistic`/`propose`/`cancel`
state machine, the `_validateCancel` role-vs-proposer split, the
optimistic-vs-pessimistic `_executeOperations` fork, and the
`_tallyUpdated` transition-to-pessimistic — is summarised as NONDET in the
spec. Only setters and `updateTimelock`-reverts are actually proved
against bytecode. The spec header explicitly says this is deferred to
Rocq, but that means there is **no bytecode-level Certora coverage** of
the contract's core function, which is the contract's biggest risk
surface in deployment.

**Best-covered:** RewardTokenRegistry and VersionRegistry — every
documented error path and every documented setter mutation has a rule;
the only gaps are EnumerableSet HAVOC limitations (CG2) and the
private-slot precondition for `getLatestVersion` (deferred V7).

## Per-contract findings

### Guardian

**Functions:** 4 external + ctor (`grantOptimisticGuardian`, `revokeOptimisticProposer`, `cancel`, plus the role-constant getters). Spec asserts auth on three; `cancel`'s downstream effect (the actual cancellation through the governor) is NONDET'd as expected.

**Custom errors (6):** `Guardian__UnauthorizedCaller`, `Guardian__ZeroAddress`, `Guardian__InvalidGovernor`, `Guardian__InvalidTimelock`, `Guardian__NotOptimisticProposal`, `Guardian__DefeatedProposal`. Two covered explicitly (G2, G5). Four uncovered.

**Gaps:**
- **G6 documented in header but not implemented as a rule** (`Guardian.spec:9-10`). The header lists "cancel by non-admin requires the proposal be optimistic AND not Defeated" — but rule `cancelRequiresAuth` only asserts `lastReverted` for a caller with neither role. There is no rule that says "non-admin guardian caller, proposal not optimistic, reverts with `NotOptimisticProposal`" nor "non-admin guardian caller, proposal Defeated, reverts with `DefeatedProposal`". (`Guardian.sol:88-94`)
- **`revokeOptimisticProposer` happy-path mutation unverified.** G4 proves a non-admin reverts; there is no symmetric rule asserting that an admin caller succeeds and the downstream `timelock.revokeOptimisticProposer(account)` is invoked with the right account. (Acceptable given timelock is NONDET'd, but worth flagging.)
- **`Guardian__InvalidGovernor` / `Guardian__InvalidTimelock` uncovered.** `_governor()` and `_timelock()` revert on `address(0)` or `code.length == 0` (`Guardian.sol:101-115`). No rule asserts cancel reverts when `governor == 0`, nor when `governor.code.length == 0`. Reachable on every external entry that calls `_governor` (i.e. both `revokeOptimisticProposer` and `cancel`).
- **Constructor invariants unchecked.** The constructor calls `_requireNonZero(initialAdmin)` (`Guardian.sol:44,47`) and iterates `initialOptimisticGuardians` enforcing `_requireNonZero` (`Guardian.sol:53-54`). No rule asserts construction with `initialAdmin == 0` reverts, nor with a zero-address element in `initialOptimisticGuardians`. (Constructors are admittedly awkward in CVL; flag as a "should consider".)

### UnstakingManager

**Functions:** 3 external + ctor (`createLock`, `cancelLock`, `claimLock`, plus public storage getters `locks`, `targetToken`, `vault`, `nextLockId` is private).

**Custom errors (3):** `UnstakingManager__Unauthorized`, `UnstakingManager__NotUnlockedYet`, `UnstakingManager__AlreadyClaimed`. All three covered (U1, U2, U3, U5, U6).

**Gaps:**
- **`createLock` happy-path mutations unverified.** U8 asserts `nextLockId++`, but no rule asserts that on successful `createLock(user, amount, unlockTime)` the storage at `locks[lockId]` ends up with the right `user`, `amount`, `unlockTime`, and `claimedAt == 0` (`UnstakingManager.sol:48-52`). The conservation theorem is in Rocq (`UnstakingManager_conservation.v` — `cancelLock_conservation`, `claimLock_conservation`, `createLock_conservation`); flag as "should be proven against bytecode too" but not net-new.
- **`cancelLock` happy-path mutations unverified.** No rule asserts that on success the lock is `delete`d (slot zeroed) and `vault.deposit(amount, user)` is invoked (`UnstakingManager.sol:64-68`). The Rocq side proves the conservation half.
- **`claimLock` transfer side-effect unchecked.** U7 verifies the timestamp stamp, but the assertion that `safeTransfer(targetToken, lock.user, lock.amount)` is the only state mutation outside of `claimedAt` is not made. (NONDET'd ERC20 calls make this OK but worth flagging.)
- **No rule asserts `cancelLock` reverts when `lockId` is uninitialised** (`user == 0` slot). `cancelLock` requires `user == msg.sender` — if `msg.sender != 0` and the slot is zero, this reverts via U2 trivially, but if a caller is `address(0)` it bypasses. This is hypothetical (`msg.sender == 0` is not reachable in production), so flag as low.

### RewardTokenRegistry

**Functions:** 4 external + ctor (`registerRewardToken`, `unregisterRewardToken`, `rewardTokens`, `isRegistered`, plus immutable `roleRegistry`).

**Custom errors (4):** `RewardTokenRegistry__InvalidCaller`, `RewardTokenRegistry__ZeroAddress`, `RewardTokenRegistry__RewardAlreadyRegistered`, `RewardTokenRegistry__RewardNotRegistered`. All covered (R1, R2, R3, R4, R5).

**Gaps:**
- **Constructor zero-address reject uncovered.** The ctor requires `address(_roleRegistry) != 0` (`RewardTokenRegistry.sol:30`). No constructor-level rule.
- **`unregisterRewardToken` reject-on-zero uncovered.** The contract has `_rewardTokens.remove(rewardToken)` which fails on an unknown token; for the zero address `_rewardTokens.contains(0)` is false so it reverts with `RewardNotRegistered`. There is no zero-address `require` on unregister. This is fine semantically but flag — adversarial would ask "what if someone unregisters 0?", and the answer is "it reverts because 0 was never registered", which is implicit, not explicit.
- **Positive-direction `register` membership deferred (R7 is the inverse).** Header acknowledges this — "successful register flips `isRegistered(token) == true`" is not provable in Certora due to EnumerableSet HAVOC (C004 in WISDOM.md). Tracked in Rocq (`RewardTokenRegistry_validity.v`). Flag as cross-cutting (CG2).

### OptimisticSelectorRegistry

**Functions:** 4 external + ctor + `initialize` (`registerSelectors`, `unregisterSelectors`, `targets`, `isAllowed`, `selectorsAllowed`).

**Custom errors (3):** `SelectorRegistry__OnlyOwner`, `SelectorRegistry__InvalidTarget`, `SelectorRegistry__InvalidSelector`. Two covered (R3 covers `InvalidTarget` for self; R4 covers `InvalidSelector`).

**Gaps:**
- **`initialize` entirely uncovered.** The `initialize` function validates the governor by calling `governor.timelock()` and `governor.token()` (`OptimisticSelectorRegistry.sol:32-34`), then iterates `selectorData` calling `_add` (which has its own validations). No rule asserts that:
  - calling `initialize` after a successful initial init reverts (Initializable's `initializer` modifier),
  - `initialize` reverts if `_governor` is a non-contract (the implicit `governor.timelock()` call would fail),
  - `initialize` correctly persists the `governor` storage slot.
- **`SelectorRegistry__InvalidTarget` only covered for `target == self`.** The contract rejects four forbidden targets (`OptimisticSelectorRegistry.sol:86-90`): `self`, `governor`, `governor.timelock()`, `governor.token()`. R3 covers `self` only. The three other forbidden-target branches are untested. The adversarial case "selector registered for target == timelock" or "target == token" is the more dangerous one because those calls would let a proposer self-grant via the timelock or self-transfer via the staking token.
- **`unregisterSelectors` `_remove` branch with empty-set side-effect unchecked.** R6 verifies `isAllowed(target, selector) == false` after unregister — but does not verify that when `_allowedSelectors[target].length() == 0` the `_targets` set is updated (`OptimisticSelectorRegistry.sol:111-113`). Means `targets()` could leak a target whose selector set is empty.
- **No rule asserts `_targets` is populated on successful add.** Symmetric to the HAVOC limitation (CG2).

### TimelockControllerOptimistic

**Functions:** 4 directly defined (`initialize`, `supportsInterface`, `revokeOptimisticProposer`, `executeBatchBypass`) + UUPS `_authorizeUpgrade` internal. Inherits massive OZ Timelock + AccessControl surface (`schedule`, `scheduleBatch`, `execute`, `executeBatch`, `cancel`, `grantRole`, `revokeRole`, ...).

**Custom errors (2):** `TimelockControllerOptimistic__OperationConflict`, `TimelockControllerOptimistic__UnauthorizedUpgrade`. One covered (T7 = OperationConflict). The other (UnauthorizedUpgrade) is NOT covered.

**Gaps:**
- **`_authorizeUpgrade` not verified.** The contract has `require(msg.sender == address(this), TimelockControllerOptimistic__UnauthorizedUpgrade())` (`TimelockControllerOptimistic.sol:96-98`). No rule asserts `upgradeTo` / `upgradeToAndCall` revert when `msg.sender != address(this)`. The UUPS upgrade gate is **the** safety boundary for this upgradeable contract.
- **`executeBatchBypass` only proven against empty `targets`.** T6 and T7 require `targets.length == 0` to keep the SMT tractable. A real adversarial property — "bypass with non-empty `targets` still requires PROPOSER_ROLE AND EXECUTOR_ROLE on the caller" — is not proven against bytecode. The single-shot property (`bypassRejectsExistingOp`) does suffice to rule out re-execution of an already-Done op, but the spec does not assert "bypass with PROPOSER but not EXECUTOR reverts".
- **Inherited `OperationCancelled`/`OperationNotReady` reverts on inherited `executeBatch` unchecked.** The bypass path calls `executeBatch`, which internally walks `_beforeCall` checks. Those are OZ-tested; flag as deferred only because the spec doesn't claim to cover them.
- **`initialize` initialization gate uncovered.** No rule asserts `initialize` cannot be called twice.
- **`supportsInterface` correctness unchecked** (low priority; this is OZ glue).

### VersionRegistry (ReserveOptimisticGovernanceVersionRegistry)

**Functions:** 4 external + ctor + public auto-getter `deployments`, `isDeprecated`, `roleRegistry`.

**Custom errors (5):** `VersionRegistry__InvalidCaller`, `VersionRegistry__ZeroAddress`, `VersionRegistry__InvalidRegistration`, `VersionRegistry__AlreadyDeprecated`, `VersionRegistry__NotConfigured`. Covered: `InvalidCaller` (V1, V3), `ZeroAddress` (V2), `InvalidRegistration` (V8 — re-registration), `AlreadyDeprecated` (V4). Uncovered: `NotConfigured`.

**Gaps:**
- **V7 deferred — `getLatestVersion` revert-when-unset.** Header acknowledges; cannot observe private `latestVersion`. Documented limitation (C006 in WISDOM.md).
- **`getImplementationsForVersion` revert-on-unknown uncovered.** `deployments[versionHash].stakingVaultImpl()` (`VersionRegistry.sol:87-91`) reverts on a zero deployer; no rule asserts this. Lower-priority than V7 because it's a view function and only callers using a stale versionHash hit it.
- **`registerVersion` happy-path storage commit unverified.** No rule asserts that on success `deployments[versionHash] == deployer` and `latestVersion = versionHash`. V8 shows `deployments[h]` is unchanged when `h != newHash`, but does not show the new slot is populated correctly.
- **Constructor zero-address uncovered.** `VersionRegistry.sol:32` — same flag as the other ctors.

### ReserveOptimisticGovernor

**Functions:** Many. External/public (own): `initialize`, `setProposalThrottle`, `setOptimisticParams`, `proposalThrottleCapacity`, `proposalThrottleCharges`, `quorumDenominator`, `vetoThreshold`, `isOptimistic`, `proposeOptimistic`, `propose` (override), `cancel` (override), `quorum`, `getOptimisticVotes`, `state` (override), `proposalDeadline`, `proposalNeedsQueuing`, `proposalThreshold`, `timelock`, `updateTimelock`, `version`. Plus internal overrides: `_queueOperations`, `_executeOperations`, `_cancel`, `_validateCancel`, `_countVote`, `_castVote`, `_tallyUpdated`, `_executor`, `_authorizeUpgrade`, `_setProposalThreshold`, `_setVotingDelay`, `_setLateQuorumVoteExtension`.

**Custom errors (7):** `OptimisticGovernor__TimelockCannotBeUpdated`, `OptimisticGovernor__OptimisticProposalCannotBeQueued`, `OptimisticGovernor__OptimisticProposalCanOnlyBeVetoed`, `OptimisticGovernor__InvalidProposalThreshold`, `OptimisticGovernor__InvalidProposalThrottle`, `OptimisticGovernor__InvalidDelay`, `OptimisticGovernor__InvalidOptimisticParameters`. Covered: `TimelockCannotBeUpdated` (R1), `InvalidProposalThrottle` (R4, R5), `InvalidOptimisticParameters` (R6, R7, R8, R9). Uncovered: `OptimisticProposalCannotBeQueued`, `OptimisticProposalCanOnlyBeVetoed`, `InvalidProposalThreshold`, `InvalidDelay`.

**Gaps:**
- **`proposeOptimistic` entirely NONDET'd.** `Governor.spec:44` — `ProposalLib.proposeOptimistic` and `ThrottleLib.consumeProposalCharge` are summarised as NONDET. Therefore:
  - The auth check "non-OPTIMISTIC_PROPOSER caller reverts" is not proven at the Certora layer.
  - The throttle revert (`OptimisticGovernor__ProposalThrottleExceeded` defined on `IReserveOptimisticGovernor`, raised in `ThrottleLib`) is not exercised.
  - The selector-allowlist check in `proposeOptimistic` (via `selectorRegistry.isAllowed`) is not exercised.
  - The proposal-storage commit (`optimisticProposalDetails[proposalId] = ...` at `ReserveOptimisticGovernor.sol:161-167`) is unverified.
- **`propose` (pessimistic path) entirely NONDET'd.** Same shape — `ProposalLib.proposePessimistic` is NONDET'd; no assertion that the proposer-votes-threshold check fires.
- **`cancel` (override) NONDET'd downstream.** No rule asserts `cancel` invokes `_validateCancel` correctly or that the cancellation flag is set.
- **`_queueOperations` revert path uncovered.** `OptimisticGovernor__OptimisticProposalCannotBeQueued` (`ReserveOptimisticGovernor.sol:340`) is not exercised. An optimistic proposal must NEVER be queued; this is a core safety property.
- **`_executeOperations` fork uncovered.** The optimistic/pessimistic fork at `ReserveOptimisticGovernor.sol:352-362` decides whether to call `_timelock().executeBatchBypass` or `super._executeOperations`. No rule asserts this branches correctly.
- **`_validateCancel` 3-way logic uncovered.** `ReserveOptimisticGovernor.sol:374-388` — CANCELLER_ROLE | proposer-and-active | proposer-and-optimistic-not-defeated. None of the three branches is exercised against bytecode.
- **`_countVote` optimistic-only-Against uncovered.** `OptimisticGovernor__OptimisticProposalCanOnlyBeVetoed` (`ReserveOptimisticGovernor.sol:395-398`) is not exercised. Adversarial property: a For-vote on an optimistic proposal must revert.
- **`_tallyUpdated` transition-to-pessimistic uncovered.** `ReserveOptimisticGovernor.sol:439-443` — the state-machine transition is a NONDET'd library call.
- **`state(proposalId)` correctness uncovered.** `ReserveOptimisticGovernor.sol:216-277` — this is the most complex view function in the contract (60+ lines, branching on `executed`, `canceled`, `voteStart`, `pastSupply`, `vetoThresholdTok`, `againstVotes`, `deadline`). No rule asserts any of its branches.
- **`proposalThreshold` rounding correctness uncovered.** `ReserveOptimisticGovernor.sol:302-315` — ceiling division to avoid zero. No rule.
- **`vetoThreshold(proposalId)` mapping read uncovered.** Used by `_isOptimistic`; covered transitively.
- **`_setProposalThreshold` validation uncovered.** `OptimisticGovernor__InvalidProposalThreshold` (`ReserveOptimisticGovernor.sol:460-466`) — `newProposalThreshold != 0 && <= 1e18`. Not exercised.
- **`_setVotingDelay` / `_setLateQuorumVoteExtension` validation uncovered.** `OptimisticGovernor__InvalidDelay` (`ReserveOptimisticGovernor.sol:479-489`) — these are reachable via OZ Governor's `setVotingDelay` and `setLateQuorumVoteExtension` external functions.
- **`_authorizeUpgrade` `onlyGovernance` uncovered.** `ReserveOptimisticGovernor.sol:456` — UUPS upgrade gate.

The spec header explicitly says "Heavy NONDET summarisation is used for OZ Governor inherited internals and for the external ProposalLib / ThrottleLib delegatecalls. We're proving the optimistic-overlay logic, not OZ's internals." This is a deliberate scoping decision and the Rocq side carries most of the load. But the **bytecode-level Certora coverage** of this contract is **setters only**. Anyone reading the README's "Governor: 10 rules" line should know that those 10 rules are all setters and `updateTimelock`-reverts — none cover the propose/queue/execute/cancel/tally state machine.

### StakingVault

**Functions:** 16 own external/public + many inherited (ERC4626 `deposit`, `mint`, `withdraw`, `redeem`; ERC20 `transfer`, `transferFrom`, `approve`; ERC20Votes `delegate`, `delegateBySig`; AccessControl `grantRole`, `revokeRole`, `renounceRole`; UUPS `upgradeTo`, `upgradeToAndCall`; plus the OPTIMISTIC delegation overlay).

Own external/public:
- `initialize`, `depositAndDelegate` (2 overloads), `delegateOptimistic`, `delegateOptimisticBySig`, `optimisticDelegates`, `getOptimisticVotes`, `numOptimisticCheckpoints`, `optimisticCheckpoints`, `getPastOptimisticVotes`, `totalAssets`, `setUnstakingDelay`, `addRewardToken`, `removeRewardToken`, `claimRewards`, `getAllRewardTokens`, `setRewardRatio`, `poke`, `nonces`, `decimals`, `clock`, `CLOCK_MODE`.

**Custom errors (9):** `Vault__InvalidRewardToken`, `Vault__DisallowedRewardToken`, `Vault__RewardAlreadyRegistered`, `Vault__RewardNotRegistered`, `Vault__MaxRewardTokensReached`, `Vault__InvalidUnstakingDelay`, `Vault__InvalidRewardsHalfLife`, `Vault__InvalidAdmin`, `Vault__VersionDeprecated`, `Vault__NotLatestStakingVault`. 

Plus `VotesExpiredSignature` from IVotes used by `delegateOptimisticBySig`.

**Covered:** Four `onlyRole(DEFAULT_ADMIN_ROLE)` gates (SV4-SV7), `delegateOptimistic` scope/effect (SV8-SV9), `convertTo{Shares,Assets}(0) == 0` (SV1-SV2), deposit-mints-exact-shares (SV3). **None of the 9 custom errors are exercised.**

**Gaps:**
- **`addRewardToken` 4 revert paths uncovered.** `StakingVault.sol:312-317`:
  - `_rewardToken == address(this) || _rewardToken == asset()` → `InvalidRewardToken`.
  - `disallowedRewardTokens[_rewardToken]` → `DisallowedRewardToken`.
  - `!rewardTokenRegistry.isRegistered(_rewardToken)` → `RewardNotRegistered`.
  - `rewardTokens.length() >= MAX_REWARD_TOKENS` → `MaxRewardTokensReached`.
  - `!rewardTokens.add(_rewardToken)` (duplicate) → `RewardAlreadyRegistered`.
  
  All five are documented invariants. None tested. The "self-as-reward" and "asset-as-reward" cases are particularly worth pinning because they would corrupt accounting if not blocked.
- **`removeRewardToken` `RewardNotRegistered` revert uncovered.** `StakingVault.sol:332`.
- **`removeRewardToken` `disallowedRewardTokens[_rewardToken] = true` side-effect unverified.** The disallow-list is supposed to be sticky (`StakingVault.sol:330`).
- **`setUnstakingDelay` `Vault__InvalidUnstakingDelay` revert uncovered.** `StakingVault.sol:302` — `_delay <= MAX_UNSTAKING_DELAY`. No rule.
- **`setRewardRatio` `Vault__InvalidRewardsHalfLife` revert uncovered.** `StakingVault.sol:383-386`. The min/max half-life is a documented invariant.
- **`initialize` `Vault__InvalidAdmin` revert uncovered.** `StakingVault.sol:152`.
- **`_authorizeUpgrade` version-pinning uncovered.** `StakingVault.sol:530-541` — this is the **upgrade authorization gate** for the staking vault. Three reverts (`Vault__VersionDeprecated`, `Vault__NotLatestStakingVault` twice). None tested. Deferred in README.
- **`delegateOptimisticBySig` signature-recovery uncovered.** `StakingVault.sol:202-214` — `VotesExpiredSignature` revert at `block.timestamp > expiry` and ECDSA + nonce checks. Deferred in README.
- **`depositAndDelegate` (both overloads) only covered transitively.** SV3 covers `deposit`; the delegate-side effects of `depositAndDelegate` (i.e. that the delegate AND optimistic delegate are both updated) are not asserted.
- **`claimRewards` accruedRewards-zeroing unverified.** `StakingVault.sol:341-366` — the most security-critical function in the rewards subsystem (token transfer of caller-claimable balance). No rule asserts that `accruedRewards == 0` after a successful claim, nor that double-claim is impossible.
- **`_update` (ERC20 transfer override) optimistic-delegate move uncovered.** `StakingVault.sol:499-506` — every share transfer moves optimistic delegate votes. This is the **dual-delegation invariant**. Not tested.
- **`_withdraw` immediate-vs-lockup fork uncovered.** `StakingVault.sol:266-293` — `unstakingDelay == 0` branches between `super._withdraw` and the lockup-creating branch. No rule. (Rocq covers the conservation side; flag as cross-cutting.)
- **`getOptimisticVotes` / `getPastOptimisticVotes` consistency uncovered.** No invariant asserts that `sum(getOptimisticVotes(d) for all d) == totalSupply()`.

## Cross-cutting gaps

### CG1 [HIGH]: Proposal-lifecycle state machine has no Certora coverage

**Where:** `ReserveOptimisticGovernor.spec` summarises every library call (`ProposalLib.proposeOptimistic`, `ProposalLib.proposePessimistic`, `ProposalLib.transitionToPessimistic`, `ThrottleLib.consumeProposalCharge`) as NONDET (`Governor.spec:44-47`). Combined with NONDET on the timelock interface (`Governor.spec:56-67`), the entire propose/queue/execute/cancel/tally surface is unverified at the bytecode level by Certora.

**Why it matters:** This is the contract's core function. The optimistic flow is the codebase's headline novelty. Adversarial properties the spec does NOT pin:
- "An optimistic proposal cannot be queued" (`OptimisticProposalCannotBeQueued`).
- "An optimistic proposal can only receive Against votes" (`OptimisticProposalCanOnlyBeVetoed`).
- "An optimistic proposal that goes Defeated transitions to a pessimistic confirmation proposal" (the `_tallyUpdated` branch).
- "Cancel auth obeys the 3-way `_validateCancel` rule (CANCELLER role | proposer-Pending | proposer-optimistic-not-Defeated)".
- "A non-OPTIMISTIC_PROPOSER cannot call `proposeOptimistic`".
- "The throttle is consumed on every `proposeOptimistic` call".

**Suggested fix:** Add a focused spec covering at least:
- A rule that calls `proposeOptimistic` with msg.sender lacking OPTIMISTIC_PROPOSER_ROLE on the timelock and asserts revert. Requires modelling the library call rather than NONDET'ing it — could replace `ProposalLib.proposeOptimistic` NONDET with an `ALWAYS(revert)` summary keyed on the role-check, or inline a small CVL model of the proposer-validation.
- A rule that calls `_queueOperations` (via the public `queue` route) on a proposal whose `vetoThreshold != 0` and asserts revert with `OptimisticProposalCannotBeQueued`. This one is tractable because `_queueOperations` only checks `_isOptimistic(proposalId)` before delegating; the library call can stay NONDET.
- A rule that calls `_countVote` with `support != Against` for an optimistic proposal and asserts revert.

The third in particular is small and very high-value.

### CG2 [MED]: EnumerableSet HAVOC blocks positive-direction invariants in two contracts

**Where:** `RewardTokenRegistry.spec` header (R7's complement deferred), `OptimisticSelectorRegistry.spec` (R5/R6 pair only — the "add succeeds → contains = true" direction is missing), `StakingVault` (`addRewardToken` mutations also EnumerableSet-backed; even if a rule were added, it would hit the same HAVOC).

**Why it matters:** Documented in `WISDOM.md:C004` as an acknowledged tool limitation. The Rocq side covers these — `RewardTokenRegistry_validity.v`, `SelectorRegistry_validity.v`, etc. — but the bytecode-vs-source gap remains. If the OZ `EnumerableSet` implementation were ever swapped or modified, the bytecode would silently violate the invariant without a Certora red flag.

**Suggested fix:** Encode the cross-slot consistency as a `requireInvariant` (one-off, expensive but airtight). Alternative: drop EnumerableSet entirely in favor of a simpler mapping-based set in the contracts where the enumeration is rarely used (none, currently — but this is a possibility worth recording).

### CG3 [MED]: UUPS `_authorizeUpgrade` untested for 3 of 4 upgradeable contracts

**Where:**
- `TimelockControllerOptimistic._authorizeUpgrade` — `msg.sender == address(this)` (`TimelockControllerOptimistic.sol:96-98`). Not tested.
- `ReserveOptimisticGovernor._authorizeUpgrade` — `onlyGovernance` (`ReserveOptimisticGovernor.sol:456`). Not tested.
- `StakingVault._authorizeUpgrade` — `onlyRole(DEFAULT_ADMIN_ROLE)` plus version-pinning against the registry (`StakingVault.sol:530-541`). Not tested. (Header acknowledges deferred.)

The OZ `UUPSUpgradeable.upgradeToAndCall` external surface is what an attacker would target; the `_authorizeUpgrade` hook is the only gate.

**Why it matters:** Three of the four upgradeable contracts in this codebase have unverified upgrade gates. The version-pinning in `StakingVault._authorizeUpgrade` is particularly interesting because it has bespoke logic (version-registry roundtrip, deprecation check, impl-pinning) that goes well beyond a role check.

**Suggested fix:** For each, a small rule:
```
rule cannotUpgradeWithoutAuth {
    env e;
    address newImpl;
    require <not authorised>;
    upgradeToAndCall@withrevert(e, newImpl, "");
    assert lastReverted;
}
```
For StakingVault, additionally a rule that calls `_authorizeUpgrade` (or `upgradeToAndCall`) with a deprecated version and asserts `Vault__VersionDeprecated` revert; same for non-latest impl asserting `Vault__NotLatestStakingVault`. NONDET the `versionRegistry.getLatestVersion()` / `getImplementationsForVersion` calls via ghost-backed summaries so the rule can pin the "deprecated" or "non-matching" branch.

### CG4 [MED]: Initialization gates and constructors uncovered across the board

**Where:** Every upgradeable contract has an `initialize` function with constructor-style invariants:
- `TimelockControllerOptimistic.initialize` (`TimelockControllerOptimistic.sol:28-37`) — chains 4 OZ init calls.
- `ReserveOptimisticGovernor.initialize` (`ReserveOptimisticGovernor.sol:91-114`) — chains 8 OZ init calls plus throttle and optimistic-params setup.
- `OptimisticSelectorRegistry.initialize` (`OptimisticSelectorRegistry.sol:29-39`) — chains `governor.timelock()`, `governor.token()`, then iterates `selectorData`.
- `StakingVault.initialize` (`StakingVault.sol:144-179`) — chains 7 OZ init calls plus the deployer-callback to fetch registries.

Plus the non-upgradeable contracts have ctor `require`s:
- `Guardian` (`Guardian.sol:38-56`) — zero-address checks on three role assignees.
- `RewardTokenRegistry` (`RewardTokenRegistry.sol:29-33`) — zero-address on `_roleRegistry`.
- `VersionRegistry` (`VersionRegistry.sol:31-35`) — zero-address on `_roleRegistry`.
- `UnstakingManager` (`UnstakingManager.sol:33-36`) — captures `msg.sender` as vault.

**Why it matters:** None of these have any Certora rule. The `initializer` modifier from OZ prevents re-init, but no rule asserts that a second `initialize` call reverts. The `UnstakingManager` ctor in particular permanently encodes the vault address from `msg.sender` — if a misconfigured deployer transaction set this wrong, every subsequent `createLock` would revert. That's worth pinning.

**Suggested fix:** One rule per contract along the lines of "calling `initialize` after a successful initial init reverts", which exercises the OZ `Initializable._checkInitializing` gate; plus per-parameter validation rules where the spec already structures them (e.g. `StakingVault.initialize(_, _, _, 0, _, _)` reverts with `Vault__InvalidAdmin`).

### CG5 [LOW]: View-function happy paths under-asserted

**Where:** `StakingVault`'s `totalAssets`, `getOptimisticVotes`, `getPastOptimisticVotes`, `numOptimisticCheckpoints`, `optimisticCheckpoints`; Governor's `proposalThreshold`, `state`, `vetoThreshold`, `proposalDeadline`, `proposalNeedsQueuing`, `quorum`; VersionRegistry's `getLatestVersion`, `getImplementationsForVersion`.

**Why it matters:** Most are simple wrappers, but a few have meaningful logic (Governor.state is 60+ lines; StakingVault.totalAssets accrues native rewards; proposalThreshold does ceiling division). Adversarial review treats "no rule" as "could silently return wrong value after a refactor". Lower priority than mutating functions but worth a sweep.

**Suggested fix:** Per-function "view does not revert" + "view returns documented sentinel on documented inputs" sanity rules, prioritised by complexity (Governor.state first).

### CG6 [LOW]: Conservation invariants only proved in Rocq

**Where:** `UnstakingManager` conservation (sum of active lock amounts == contract balance) is in `rocq/proofs/UnstakingManager_conservation.v`. `StakingVault` rewards conservation in `rocq/proofs/StakingVaultRewards_conservation.v`. Vault balance conservation in `rocq/proofs/Integration_vault_balance_conservation.v`.

**Why it matters:** Spec headers acknowledge "CVL is not the right tool for that global predicate" (e.g. `UnstakingManager.spec:26-29`). This is true today but worth recording because if the conservation invariant ever moves into a more locally-expressible form (e.g. via an internal sum-tracked storage slot), it would become a Certora candidate. Not net-new, but should appear in this audit so the gap doesn't get forgotten.

---

**File map (referenced in this report):**
- Contracts: `contracts/Guardian.sol`, `contracts/VersionRegistry.sol`, `contracts/staking/UnstakingManager.sol`, `contracts/staking/StakingVault.sol`, `contracts/staking/RewardTokenRegistry.sol`, `contracts/governance/TimelockControllerOptimistic.sol`, `contracts/governance/OptimisticSelectorRegistry.sol`, `contracts/governance/ReserveOptimisticGovernor.sol`, `contracts/governance/lib/ProposalLib.sol`, `contracts/governance/lib/ThrottleLib.sol`.
- Specs: `formal-verification/certora/<Contract>/<Contract>.{spec,conf}`.
- Rocq cross-reference: `formal-verification/rocq/proofs/`.
