# External dependencies — Reserve Governor

## Introduction

This audit enumerates every contract or library that the Reserve Governor
system calls into or is called by, that lies outside the governor's own
codebase (`contracts/`). The purpose is to identify what the formal
verification effort must model, abstract, or declare as a trust assumption
for proofs to be transferable to production.

**What "external" means here.** A dependency is external if it is (a)
imported from a package (`@openzeppelin/*`, `@prb/math`) rather than from
within `contracts/`, and (b) instantiated at a *different contract address*
at runtime, meaning its behavior cannot be inlined into the governor's own
simulation. Pure utility libraries that are inlined by the compiler (e.g.
`SafeCast`, `Math`, `Strings`) are treated separately from interface calls
that cross address boundaries.

**Modeling spectrum.** The formal-verification effort has four stances:

| Label | Meaning |
|---|---|
| **Abstract** | The function is axiomatized: the proof takes its properties as hypotheses rather than deriving them. Suitable when the behavior is provably sound (e.g. ECDSA recovery is injective on valid signatures) or when the property used is a weaker invariant the governor relies on without caring about internal mechanics. |
| **Mock** | A minimal Gallina model captures only the side-effects the governor depends on. ERC20 is the canonical example: the simulation maintains a `balances : address -> Z` map and `transfer` updates two entries. |
| **Full simulation** | The dependency's entire logic gets its own simulation module (expensive; justified only when the property set is large or interactions are subtle). |
| **Trust assumption** | Declared out of scope. A named axiom or a hypothesis in the relevant `Valid.t` predicate documents what is assumed. Justified when the dependency is a well-audited, widely-used primitive whose formal model already exists in the literature. |

---

## At a glance

| Dependency | Import path | Direction | Depth of trust | Recommended modeling |
|---|---|---|---|---|
| OZ `AccessControl` / `AccessControlEnumerable` | `@openzeppelin/contracts/access/...` | Both (governor inherits; Guardian calls into governor) | Role-state correctness | Mock: `roles : role -> AddressSet` map |
| OZ `GovernorUpgradeable` (+ extensions) | `@openzeppelin/contracts-upgradeable/governance/...` | Ingress (external callers invoke governor) + egress (governor calls token) | Proposal-state machine, vote counting | Full simulation — *already in progress* |
| OZ `TimelockControllerUpgradeable` | `@openzeppelin/contracts-upgradeable/governance/TimelockControllerUpgradeable.sol` | Both (inherited by `TimelockControllerOptimistic`; governor calls `executeBatchBypass`) | Scheduling, delay enforcement | Full simulation — *already in progress* |
| OZ `ERC20Upgradeable` / `ERC4626Upgradeable` / `ERC20VotesUpgradeable` | `@openzeppelin/contracts-upgradeable/token/ERC20/...` | Inherited by `StakingVault` | Token balance + vote accounting | Mock (balance map); `ERC20VotesUpgradeable` needs checkpoint model |
| OZ `UUPSUpgradeable` / `ERC1967Proxy` / `Clones` | `@openzeppelin/contracts-upgradeable/proxy/utils/...` | Egress (deployer creates proxies) | Proxy storage layout, upgrade auth | Trust assumption (proxy correctness is OZ-audited) |
| OZ `ECDSA` | `@openzeppelin/contracts/utils/cryptography/ECDSA.sol` | Egress (StakingVault calls `recover`) | Signature recovery for optimistic delegation | Abstract (injectivity axiom) |
| OZ `SafeERC20` | `@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol` | Egress (StakingVault transfers tokens; UnstakingManager transfers tokens) | Token transfer correctness | Mock (same balance map as ERC20) |
| OZ `Math` | `@openzeppelin/contracts/utils/math/Math.sol` | Egress (governor, staking vault call `mulDiv`, `max`) | Arithmetic correctness | Abstract (proven exact over Z, no overflow) |
| OZ `SafeCast` | `@openzeppelin/contracts/utils/math/SafeCast.sol` | Egress (StakingVault, ProposalLib) | Overflow-detecting downcasts | Abstract (trivial: `toUintN` = identity on bounded Z) |
| OZ `Checkpoints` | `@openzeppelin/contracts/utils/structs/Checkpoints.sol` | Egress (StakingVault uses `Trace208`) | Binary-search checkpoint lookups | Mock: sorted timestamp-value list with `upperLookupRecent` |
| OZ `EnumerableSet` | `@openzeppelin/contracts/utils/structs/EnumerableSet.sol` | Egress (StakingVault, SelectorRegistry, RewardTokenRegistry) | Set membership, ordered iteration | Mock: list-with-no-duplicates |
| OZ `Time` | `@openzeppelin/contracts/utils/types/Time.sol` | Egress (StakingVault clock) | `block.timestamp` as `uint48` | Abstract (`Time.timestamp()` = explicit `now : U256.t` arg) |
| OZ `Strings` | `@openzeppelin/contracts/utils/Strings.sol` | Egress (ProposalLib `tryParseAddress`) | Address suffix validation in description | Abstract (total-function specification) |
| `@prb/math` `UD60x18.powu` | `@prb/math/src/UD60x18.sol` | Egress (StakingVault `_calculateHandout`) | Exponential decay kernel | Abstract: CAS-validated axiom `(1-r)^n` |
| `IRoleRegistry` (Reserve-owned) | `contracts/interfaces/IRoleRegistry.sol` | Egress (VersionRegistry, RewardTokenRegistry call `isOwner`) | Authorization gate | Trust assumption (out-of-scope singleton) |
| `ReserveOptimisticGovernanceVersionRegistry` (Reserve-owned) | `contracts/VersionRegistry.sol` | Egress (StakingVault `_authorizeUpgrade` calls `getLatestVersion`) | Upgrade safety gate | Mock: `(latestHash, deprecated)` map |
| Arbitrary reward token ERC20s | Runtime — any `address` in `rewardTokens` set | Egress (StakingVault `balanceOf`, `safeTransfer`) | Balance reads, transfer side effects | Mock (balance map); token behavior trusted |
| Arbitrary proposal targets | Runtime — any `address[]` in a proposal | Egress (timelock executes calldata against targets) | Any side effect possible | Trust assumption (target behavior is governance-controlled) |

---

## OpenZeppelin: AccessControl / AccessControlEnumerable

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import paths:**
- `contracts/Guardian.sol:4` — `AccessControlEnumerable`
- `contracts/governance/lib/ProposalLib.sol:4` — non-upgradeable `AccessControl`
- `contracts/staking/StakingVault.sol:15` — `AccessControlEnumerableUpgradeable`
- `contracts/governance/TimelockControllerOptimistic.sol:5` — `AccessControlEnumerableUpgradeable`

**Direction of trust:** Both. The governor *inherits* `AccessControl` (so it *is* the access-controlled object), and it *calls into* `AccessControl(governor.timelock()).hasRole(...)` (ProposalLib line 45) to validate the proposer role.

**State the governor reads:**
- `hasRole(role, account)` — ProposalLib checks `OPTIMISTIC_PROPOSER_ROLE` on the timelock (ProposalLib.sol:45).
- `hasRole(CANCELLER_ROLE, caller)` — `ReserveOptimisticGovernor._validateCancel` (ReserveOptimisticGovernor.sol:377).
- `hasRole(DEFAULT_ADMIN_ROLE, msg.sender)` — Guardian.sol:79.

**State the governor writes via this dependency:**
- `_grantRole`, `_revokeRole`, `renounceRole` — Deployer configures the timelock role set at deploy time. Guardian grants/revokes OPTIMISTIC_GUARDIAN_ROLE and OPTIMISTIC_PROPOSER_ROLE.

**Returned values the governor relies on:**
- `hasRole(role, account) → bool` — the ProposalLib `proposeOptimistic` check is a hard gating condition. If this returns wrong data, any address can make an optimistic proposal.

**Failure modes:**
- Revert: `hasRole` is a pure view; it does not revert in any documented path.
- Wrong data: If the role mapping is corrupted (e.g. via a storage collision in the UUPS proxy), `proposeOptimistic` could be called by unauthorized addresses, or cancellation could be blocked for guardians.
- Reentrancy: `hasRole` is non-reentrant by construction. `grantRole`/`revokeRole` can be called from a malicious target proposal callback if the timelock has been configured to allow it; that is a governance-path risk, not a code bug.

**Modeling recommendation: Mock.**
Represent the role store as `roles : bytes32 -> AddressSet`. The mock's `hasRole`, `grantRole`, `revokeRole`, `renounceRole` update that map. The critical theorem is: `grantRole(r, a) ; hasRole(r, a) = true`. The protocol-repo effort uses no dedicated AccessControl simulation, but all proofs that touch roles take `hasRole` as a precondition via `Valid.t` hypotheses. The governor proofs should follow the same pattern for the role-gate properties (e.g. `proposeOptimistic_requires_optimistic_proposer_role`).

**Protocol-repo precedent:** No dedicated simulation. Role checks are asserted as `Valid.t` conditions in the Throttle and Distributor simulations. Reuse the same pattern here.

---

## OpenZeppelin: Governor (Upgradeable suite)

**Source:** `@openzeppelin/contracts-upgradeable ^5.4.0`
**Import paths (ReserveOptimisticGovernor.sol):**
- `GovernorUpgradeable` (line 7)
- `TimelockControllerUpgradeable` (line 9)
- `GovernorCountingSimpleUpgradeable` (line 12)
- `GovernorPreventLateQuorumUpgradeable` (line 15)
- `GovernorSettingsUpgradeable` (line 18)
- `GovernorTimelockControlUpgradeable` (line 21)
- `GovernorVotesQuorumFractionUpgradeable` (line 24)
- `GovernorVotesUpgradeable` (line 27)

**Direction of trust:** Ingress. External callers (`propose`, `vote`, `execute`, `queue`, `cancel`) enter the governor through the OZ base-contract dispatch. Egress: the governor calls `token().getPastTotalSupply(snapshot)` (line 249, 311) and `token().getVotes(proposer, block.timestamp - 1)` (ProposalLib.sol:83).

**State the governor reads:**
- `token().getPastTotalSupply(snapshot)` — used to compute `vetoThresholdTok` and `proposalThreshold` (ReserveOptimisticGovernor.sol:249, 311).
- `token().getVotes(proposer, ts)` — vote-weight for pessimistic proposer gate (ProposalLib.sol:83).
- `IOptimisticVotes(token()).getPastOptimisticVotes(account, timepoint)` — weight for optimistic veto counting (ReserveOptimisticGovernor.sol:509).

**State the governor writes via this dependency:**
- Vote counts (`_countVote`) are written into the OZ `_proposals` mapping via `GovernorCountingSimpleUpgradeable`.
- Proposal lifecycle fields (`voteStart`, `voteDuration`, `executed`, `canceled`) are written by `proposeOptimistic`/`proposePessimistic` and the execution/cancel paths.

**Returned values the governor relies on:**
- `getPastTotalSupply(snapshot)` — correctness determines whether optimistic proposals can be vetoed.
- `getPastVotes` / `getPastOptimisticVotes` — correctness determines per-account vote weight.
- `_proposalCore(proposalId).voteStart` — ProposalLib reads this to detect duplicate proposals.

**Failure modes:**
- Revert in `getPastTotalSupply`: this would freeze the `state()` function for that proposal. An optimistic proposal would appear permanently Pending.
- Stale/wrong total supply: vetoThresholdTok computed from wrong supply; a proposal could be harder or easier to veto than intended.
- Stale/wrong past votes: vote fraud — an account could veto with more weight than it actually held at snapshot.
- Reentrancy into governor via `_castVote`: OZ Governor uses a reentrancy guard for `execute` but not for `castVote` directly. A malicious token could reenter `castVote` during `getPastVotes`. The `_tallyUpdated` hook (which triggers `transitionToPessimistic`) would then operate on partially-updated state.

**Modeling recommendation: Full simulation — already in progress (tasks #77, #78).**
The `ProposalLib.v` and `ReserveOptimisticGovernor.v` Rocq simulations are the primary vehicles. The OZ base-class state (`_proposals`, `_proposalVotes`) should be modeled as storage records passed into the simulation functions, exactly as the protocol-repo's StRSR simulation passes `totalStRSR` and `draftRSR` as storage fields.

The token read (`getPastTotalSupply`, `getPastVotes`) should be **abstracted**: add a `Valid.t` hypothesis `supply_correct : past_supply = actual_supply_at_snapshot` and prove the governor's invariants *conditional on that hypothesis*. This is the same pattern the protocol StRSR simulation uses for `rewardsPool` (taken as an explicit argument rather than reading the live RSR balance).

---

## OpenZeppelin: TimelockControllerUpgradeable

**Source:** `@openzeppelin/contracts-upgradeable ^5.4.0`
**Import paths:**
- `contracts/governance/TimelockControllerOptimistic.sol:9`
- `contracts/governance/ReserveOptimisticGovernor.sol:9`

**Direction of trust:** Both. `TimelockControllerOptimistic` inherits from it. `ReserveOptimisticGovernor._executeOperations` calls `_timelock().executeBatchBypass(...)` (line 355) and `super._executeOperations(...)` (line 361) which calls through to the OZ timelock.

**State the governor reads:**
- `TimelockController.hashOperationBatch(...)` — used inside `executeBatchBypass` to derive the operation ID (TimelockControllerOptimistic.sol:83).
- `$._timestamps[id]` — checked for conflict in `executeBatchBypass` (line 88).
- `hasRole(PROPOSER_ROLE, caller)` — gates `executeBatchBypass`.

**State the governor writes via this dependency:**
- `$._timestamps[id] = block.timestamp` — marks the operation as Ready in the bypass path (line 89).
- Execution of target calls (`executeBatch`) — these are the actual proposal calls, so all external-state changes go through here.

**Returned values the governor relies on:**
- `hashOperationBatch` return value — determines the operation ID. Collision would allow two proposals to conflict.

**Failure modes:**
- Revert in `executeBatch` due to any target reverting — the entire optimistic or pessimistic execution reverts. No partial execution.
- Wrong `_timestamps` state — if the bypass sets `_timestamps[id] = 0` or already-set, the conflict check fails / succeeds incorrectly.
- Reentrancy via target calls: an executed target could call back into the governor or timelock. The timelock has no reentrancy guard on `executeBatch`. The governor relies on proposal state (`executed` flag) to prevent double-execution.

**Modeling recommendation: Full simulation — already in progress (task #79).**
The key property to prove is that `executeBatchBypass` is equivalent to `scheduleBatch + immediate execute` for the governor's operation-ID space, and that the `_timestamps[id] == 0` pre-check prevents replay. The OZ `hashOperationBatch` should be **abstract** (injective on its five inputs).

---

## OpenZeppelin: ERC20/ERC4626/ERC20Votes (StakingVault base classes)

**Source:** `@openzeppelin/contracts-upgradeable ^5.4.0`
**Import paths (StakingVault.sol):**
- `ERC20Upgradeable` (line 18), `ERC20PermitUpgradeable` (line 20), `ERC20VotesUpgradeable` (line 23), `ERC4626Upgradeable` (line 25), `NoncesUpgradeable` (line 26)

**Direction of trust:** Both. StakingVault inherits all of these and so *is* the ERC20/ERC4626 object. External actors (depositors, delegators) call `deposit`, `withdraw`, `transfer`, `delegate`, and `delegateBySig` against it.

**State the governor reads:**
- `balanceOf(user)` — used in `_accrueUser` (StakingVault.sol:469) and `_delegateOptimistic` (line 548).
- `totalSupply()` — used in `_accrueRewards` delta-index computation (line 445).
- `IERC20(asset()).balanceOf(address(this))` — StakingVault reads its own underlying balance to compute `nativeBalanceLastKnown` (lines 292, 429, 437).
- `IERC20(_rewardToken).balanceOf(address(this))` — same pattern for each reward token (line 322, 437).

**State the governor writes via this dependency:**
- `_mint(receiver, shares)` on deposit.
- `_burn(owner, shares)` on withdraw.
- `_transfer` / `_update` — the `accrueRewards` modifier fires on every ERC20 transfer.

**Returned values the governor relies on:**
- `IERC20(asset()).balanceOf(address(this))` — correctness determines `nativeBalanceLastKnown` and thus the reward accrual rate. A lying token would misstate the vault's asset balance.
- `IERC20(_rewardToken).balanceOf(address(this))` — determines `balanceLastKnown`, the input to the reward index.

**Failure modes:**
- Underlying token reverts on `balanceOf`: `_accrueRewards` would revert; any deposit/withdraw/transfer/claim would be bricked while that token is active.
- Underlying token lies on `balanceOf`: rewards would be computed incorrectly. This is a "malicious token" threat.
- Underlying token reverts on `safeTransfer` in `claimRewards`: single-token claim fails; other reward tokens unaffected (the loop would revert on that index, losing the rest of the batch unless the caller chooses tokens carefully).
- `forceApprove` fails on `asset()`: the `_withdraw` path with `unstakingDelay > 0` would revert, bricking all unstaking for the vault.
- ERC20 reentrancy via `safeTransfer` in `claimRewards` (line 361): a malicious reward token could reenter `claimRewards` before the `accruedRewards = 0` write... but that line fires before the external call (line 359–360), so this is NOT a vulnerability. The zero-first pattern is safe.

**Modeling recommendation: Mock.**
For the `StakingVaultExchange.v` and `StakingVaultRewards.v` simulations (already written), the underlying token balance is already abstracted as an explicit `balanceOfThis : U256.t` argument. For the StakingVaultDelegation simulation (task #84), `balanceOf(user)` is used directly in `_delegateOptimistic` and `_moveOptimisticDelegateVotes`. Model it as a `shares : Address -> U256.t` map. The critical property: `_mint(addr, n)` adds `n` to `shares[addr]` and to `totalSupply`.

For reward tokens and the underlying token, document the trust assumption:
> **Trust assumption T-ERC20:** All registered reward tokens and the vault's `asset()` token behave as honest ERC20s: `balanceOf` is non-decreasing except via `transferFrom`, `transfer`, and `burn`; it does not revert; and it returns the true balance.

This mirrors the protocol-repo pattern exactly: the StRSR simulation takes `rewardsPool` (the live RSR balance) as an explicit argument, with no simulation of the RSR token itself.

---

## OpenZeppelin: UUPS proxy / ERC1967Proxy / Clones

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import paths:**
- `contracts/Deployer.sol:6` — `ERC1967Proxy` (used to deploy StakingVault, Timelock, Governor proxies)
- `contracts/Deployer.sol:5` — `Clones.cloneDeterministic` (used for OptimisticSelectorRegistry)
- `contracts/staking/StakingVault.sol:17`, `contracts/governance/TimelockControllerOptimistic.sol:11`, `contracts/governance/ReserveOptimisticGovernor.sol:29` — `UUPSUpgradeable`

**Direction of trust:** Egress only. Deployer calls `new ERC1967Proxy(impl, data)` and `Clones.cloneDeterministic(impl, salt)`.

**State the governor reads:** None at runtime. Proxy infrastructure is deployment-time only.

**State the governor writes via this dependency:**
- UUPS upgrade: `_authorizeUpgrade` gates upgrades to `onlyGovernance` (Governor) or `DEFAULT_ADMIN_ROLE` (StakingVault) or self (Timelock). The proxy slot `_IMPLEMENTATION_SLOT` is updated.

**Returned values the governor relies on:**
- `ERC1967Proxy` constructor result — the deployed proxy address. Used to wire up the governance system during `_deployOptimisticGovernance`.
- `Clones.cloneDeterministic` address — the selector registry's address is known at deployment.

**Failure modes:**
- Proxy deployment reverts (out-of-gas, address collision): the whole deployment transaction reverts. No partial state.
- Wrong implementation address in proxy: any function call would execute against the wrong logic. This is a deployment error, not a runtime attack.
- Storage collision between proxy admin slot and implementation storage: OZ ERC1967 uses the EIP-1967 storage slot to avoid this; the governor contracts use `UUPSUpgradeable`, which is the standard safe pattern.

**Modeling recommendation: Trust assumption.**
The OZ proxy infrastructure is out of scope. The formal proofs should assume:
> **Trust assumption T-PROXY:** The UUPS proxy correctly delegates all non-upgrade calls to the current implementation, and the upgrade slot is only writable via `_authorizeUpgrade`. Implementation address after `new ERC1967Proxy(impl, data)` is `impl`.

---

## OpenZeppelin: ECDSA

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import path:** `contracts/staking/StakingVault.sol:7`
**Usage:** `ECDSA.recover(hash, v, r, s)` called in `delegateOptimisticBySig` (StakingVault.sol:209).

**Direction of trust:** Egress.

**State the governor reads:** None. `ECDSA.recover` is a pure computation.

**Returned values the governor relies on:**
- `signer : address` — the recovered signing address. If wrong, a signature from any key would be accepted as delegation from any other account. The governor then calls `_delegateOptimistic(signer, delegatee)`, setting optimistic voting delegation based on the recovered address.

**Failure modes:**
- Signature malleability: OZ ECDSA v5 rejects high-s signatures. Safe.
- Hash preimage: `_hashTypedDataV4` uses EIP-712. If the domain separator is wrong (upgrade changed the contract address?), replay from other chains is possible but bounded to the same `block.chainid`.
- `ECDSA.recover` returns `address(0)` on invalid signatures: OZ v5 reverts in this case. The governor never sees a zero signer.

**Modeling recommendation: Abstract.**
Treat `ECDSA.recover(hash, sig) = addr` as a pure function with the axiom: `recover(hash, sign(key, hash)) = publicAddress(key)` (injective; outputs are in range `[1, 2^160 - 1]`). The nonce check (`_useCheckedNonce`) provides replay protection and should be modeled as a `nonces : Address -> U256.t` map with the increment invariant.

**Protocol-repo precedent:** No ECDSA simulation exists. The EIP-712 pattern in StRSR (`permit`) is noted as "ERC20 surface — None" in the simulation header, consistent with treating it as abstract.

---

## OpenZeppelin: Math (mulDiv / max)

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import paths:**
- `contracts/governance/ReserveOptimisticGovernor.sol:5` — `Math.max`
- `contracts/staking/StakingVault.sol:8` — `Math.mulDiv`

**Usage:**
- `Math.max(1, super.quorum(timepoint))` — ensures quorum is at least 1 (line 208).
- `Math.max(1, token().getPastTotalSupply(...))` — ensures supply is at least 1 in proposalThreshold (line 311).
- `Math.mulDiv(tokensToHandout, SCALAR * 10**decimals(), totalSupply())` — reward index delta (StakingVault.sol:445).
- `Math.mulDiv(balanceOf(_user), deltaIndex, 10**decimals() * SCALAR)` — per-user reward accrual (line 469).

**Direction of trust:** Egress.

**Failure modes:**
- `Math.mulDiv` reverts on division by zero: StakingVault calls it only when `totalSupply() > 0` (line 443 `if (tokensToHandout != 0)` implies supply > 0 was checked at line 486); and line 469 is only reached within `_accrueUser` which skips `address(0)`.
- Overflow in `mulDiv`: OZ v5 `Math.mulDiv` uses 512-bit multiplication internally; it does not overflow on uint256 inputs.

**Modeling recommendation: Abstract.**
Model `mulDiv(a, b, c)` as `(a * b) / c` over `Z` (exact integer division, floor). The key theorems about reward index correctness are already in `StakingVaultRewards.v`; they rely on the exact identity. Add a `mulDiv_correct` lemma: `mulDiv(a, b, c) = Z.div (a * b) c` (for `c > 0`). Similarly `max(a, b) = Z.max a b`.

**Protocol-repo precedent:** `simulations/Fixed.v` models `FixLib.mul` etc. as Z-arithmetic. The `Math.mulDiv` calls in the governor are simpler (not uint192-boxed); the same Z-over-integer approach applies.

---

## OpenZeppelin: SafeCast

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import paths:**
- `contracts/staking/StakingVault.sol:9`
- `contracts/governance/lib/ProposalLib.sol:7`

**Usage:**
- `SafeCast.toUint32(...)` — voteDuration cast in ProposalLib.sol:185.
- `SafeCast.toUint48(...)` — voteStart cast in ProposalLib.sol:184.
- `SafeCast.toUint208(...)` — optimistic checkpoint value in StakingVault.sol:561, 568.
- `SafeCast.toUint32(...)` — checkpoint count in StakingVault.sol:225.

**Direction of trust:** Egress.

**Failure modes:**
- Revert on overflow: `toUint48` would revert if `block.timestamp + voteDelay > 2^48 - 1`. Given `voteDelay < MAX_OPTIMISTIC_DELAY = type(uint48).max / 2` and `block.timestamp` is uint48 at max ~140,000 years, this is not reachable in practice.
- `toUint208` revert: checkpoint values are vote-weight sums. If total optimistic delegation exceeds `type(uint208).max`, the push would revert. Given StakingVault total supply is a uint256, this is theoretically possible if a staking vault accumulates more than `2^208` shares.

**Modeling recommendation: Abstract.**
In the simulation, treat `SafeCast.toUintN(x)` as the identity on values in `[0, 2^N - 1]` and as `Result.Revert` outside that range. The `Valid.t` predicate for the proposal-core state should assert `0 <= voteStart <= UINT48_MAX` (matching the protocol-repo's `lastPayout_uint48` pattern for Furnace and StRSR).

**Protocol-repo precedent:** The protocol sims use `U256.t` (unbounded Z) and carry `UINT48_MAX` bounds in `Valid.t` rather than modeling SafeCast directly. Follow the same convention.

---

## OpenZeppelin: Checkpoints (Trace208)

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import path:** `contracts/staking/StakingVault.sol:10`
**Usage:**
- `Checkpoints.Trace208` — `optimisticDelegateCheckpoints[delegatee]` stores (timestamp, uint208) pairs.
- `push(clock(), newValue)` — on every delegation change (StakingVault.sol:560, 567).
- `latest()` — returns the most-recent value (line 222, 559, 566).
- `upperLookupRecent(timepoint)` — binary-search past value (line 237).

**Direction of trust:** Egress.

**State the governor reads:**
- `checkpoints.upperLookupRecent(timepoint)` — called in `getPastOptimisticVotes` (line 237), which is used by the governor to count veto weight at snapshot.

**Returned values the governor relies on:**
- `upperLookupRecent(t)` — correctness determines the optimistic vote weight attributed to a delegate at a past time. If wrong, an account could retroactively gain or lose veto power.

**Failure modes:**
- `push` with a clock value less than or equal to the last push: OZ v5 Checkpoints reverts with `CheckpointUnorderedInsertion`. The governor calls `push(clock(), ...)` where `clock() = Time.timestamp()`. If `block.timestamp` is non-monotonic (impossible in EVM) this would revert. In practice this is safe.
- Binary search on an empty array: `upperLookupRecent` returns 0. The governor treats 0 past-optimistic-votes as zero weight, which is correct.

**Modeling recommendation: Mock.**
Model `Trace208` as a sorted list of `(timestamp, value)` pairs. `push(t, v)` appends; `latest()` returns the last; `upperLookupRecent(t)` returns the `value` of the last entry with `timestamp <= t`, or 0 if none. This is the essential invariant that must hold for the dual-delegation proof (task #84).

The key theorem: `push(t, v); upperLookupRecent(t') = v` when `t' >= t` and `t` is strictly greater than all prior timestamps. This should be proved in the `StakingVaultDelegation.v` simulation.

---

## OpenZeppelin: EnumerableSet

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import paths:**
- `contracts/staking/StakingVault.sol:11` — `EnumerableSet.AddressSet` for reward tokens
- `contracts/governance/OptimisticSelectorRegistry.sol:4` — `AddressSet` (targets), `Bytes32Set` (selectors)
- `contracts/staking/RewardTokenRegistry.sol:4` — `AddressSet` for registered tokens

**State the governor reads:**
- `rewardTokens.values()` — iterated in `_accrueRewards` (line 403).
- `rewardTokens.length()` — cap check in `addRewardToken` (line 316).
- `_allowedSelectors[target].contains(bytes32(selector))` — gating check in `OptimisticSelectorRegistry.isAllowed` (line 69).
- `_rewardTokens.contains(rewardToken)` — in `RewardTokenRegistry.isRegistered` (line 55).

**Failure modes:**
- `values()` iterates in insertion order (OZ EnumerableSet guarantees this). If order were non-deterministic, reward accrual order would be non-deterministic. Not a safety issue since accrual commutes over independent tokens.
- `add`/`remove` on a set that already contains/lacks the element: OZ v5 returns false rather than reverting; the governor checks the return value only in some cases.

**Modeling recommendation: Mock.**
Model as a list with no duplicates. Key properties: `add(s, x); contains(s, x) = true`; `remove(s, x); contains(s, x) = false`; `length(s) = List.length(s)`. The ordering guarantee (`values()` returns insertion order) should be modeled as `values(s) = s` (identity on the list). This is sufficient for the reward-token iteration and selector-registry proofs.

**Protocol-repo precedent:** The Distributor simulation uses `list (U256.t * RevenueShare.t)` as a plain list, acknowledging that "EnumerableSet ordering guarantee" is treated as an invariant of the caller, not the set. Follow the same approach.

---

## OpenZeppelin: Time (clock)

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import path:** `contracts/staking/StakingVault.sol:12`
**Usage:** `Time.timestamp()` in `clock()` (line 521). This is called by OZ Governor base to map block timestamps to checkpoint lookup keys.

**Direction of trust:** Egress.

**Modeling recommendation: Abstract.**
`Time.timestamp()` = `block.timestamp` cast to uint48. In all simulations, pass `now : U256.t` as an explicit argument with the precondition `0 <= now <= UINT48_MAX`. This is the convention already established across the governor simulations.

---

## OpenZeppelin: Strings (tryParseAddress)

**Source:** `@openzeppelin/contracts ^5.4.0`
**Import path:** `contracts/governance/lib/ProposalLib.sol:6`
**Usage:** `Strings.tryParseAddress(description, start, end)` at ProposalLib.sol:219 — extracts the address suffix from a proposal description to enforce the proposer-restriction convention.

**Direction of trust:** Egress.

**Returned values the governor relies on:**
- `(bool success, address recovered)` — if success=false or recovered=proposer, the description is valid. If success=true and recovered≠proposer, the proposal is rejected.

**Failure modes:**
- None. If `tryParseAddress` returns garbage (e.g. due to a bug), the proposal description check is wrong. A malicious proposer could craft a description that passes the check when it should fail, allowing them to front-run a different proposer's proposal ID.

**Modeling recommendation: Abstract.**
Axiomatize `tryParseAddress` as a pure function: `tryParseAddress(desc, start, end) = (true, addr)` iff the substring `desc[start..end]` is a checksummed 42-character Ethereum address string for `addr`; otherwise `(false, _)`. The governor's invariant is `_isValidDescriptionForProposer`, which should be proved assuming this axiom.

---

## @prb/math: UD60x18.powu

**Source:** `@prb/math ^4.1.0`
**Import path:** `contracts/staking/StakingVault.sol:28`
**Usage:** One call site:

```solidity
// StakingVault.sol:490
uint256 handoutPercentage = 1e18 - UD60x18.wrap(1e18 - rewardRatio).powu(elapsed).unwrap() - 1;
```

This is the discrete exponential decay kernel: `handoutPct = 1 - (1 - r)^n` where `r = rewardRatio / 1e18` (D18 fraction) and `n = elapsed` (seconds).

**Direction of trust:** Egress. `UD60x18.wrap(x).powu(n)` is a pure computation over the UD60x18 type.

**State the governor reads:** None. Pure computation.

**Returned values the governor relies on:**
- `handoutPercentage` — determines how much of the unaccounted reward balance is handed out this period. If `powu` is wrong, the reward emission rate is wrong.
- The `-1` at the end rounds down: `handoutPercentage = 1e18 - (1-r)^n * 1e18 - 1`. This intentional rounding ensures the vault never pays out more than it received.

**Failure modes:**
- `powu(0)` = 1 (identity): `elapsed = 0` implies `handoutPercentage = 0`, so no reward. Correct.
- Revert: UD60x18 reverts on overflow. `rewardRatio < 1e18` always (it is `ln(2) / halfLife` with halfLife bounded below), so `1e18 - rewardRatio > 0` and `wrap` succeeds. `powu` on a value in `[0, 1e18)` cannot overflow (result approaches 0, never exceeds the input).
- Rounding error accumulation: `powu` uses repeated squaring in UD60x18 arithmetic with floor rounding. Small rounding errors accumulate, causing the vault to hand out slightly less than the theoretical continuous rate. This is expected and safe — the vault accrues slightly more over time.

**Modeling recommendation: Abstract (CAS-validated axiom).**
The CAS corpus in `cas/staking_vault/` already validates the decay formula separately (see `StakingVaultExchange.v` header, line 9). The formal proofs should treat `calculateHandout(bal, elapsed, ratio)` as an opaque function with the following axioms:
1. `calculateHandout(0, _, _) = 0`
2. `calculateHandout(_, 0, _) = 0`
3. `calculateHandout(bal, elapsed, ratio) <= bal` (no overpayment)
4. `calculateHandout(bal, elapsed, ratio) >= 0` (no negative payout)

These four properties are sufficient for the reward-accounting correctness proofs in `StakingVaultRewards.v`. The exact closed-form `1 - (1-r)^n` is a CAS concern, not a Rocq proof concern.

**Protocol-repo precedent:** The StRSR simulation uses `FixLib.powu` (from `simulations/Fixed.v`) for its compound decay. The governor uses `UD60x18.powu` from a different library but the mathematical structure is identical: `(1-r)^n` in D18 arithmetic. The approach should mirror Fixed.v's `powu` modeling — provide a `powu_safe`-style lemma asserting the key monotone bound (`result <= input`) without trying to prove the full arithmetic identity in Rocq.

---

## IRoleRegistry (Reserve-owned singleton)

**Source:** `contracts/interfaces/IRoleRegistry.sol`
**Import paths:**
- `contracts/VersionRegistry.sol:5`
- `contracts/staking/RewardTokenRegistry.sol:7`

**Direction of trust:** Egress. `VersionRegistry` and `RewardTokenRegistry` call `roleRegistry.isOwner(msg.sender)` and `roleRegistry.isOwnerOrEmergencyCouncil(msg.sender)` to gate governance writes.

**State the governor reads:**
- `isOwner(account) → bool` — gates `registerVersion` in VersionRegistry and `registerRewardToken` in RewardTokenRegistry.
- `isOwnerOrEmergencyCouncil(account) → bool` — gates `deprecateVersion` and `unregisterRewardToken`.

**Returned values the governor relies on:**
- Correctness of these booleans determines who can register/deprecate governor versions and reward tokens.

**Failure modes:**
- If `isOwner` returns `true` for an adversary, they can register a deprecated or malicious version, then trick a StakingVault upgrade into accepting a compromised implementation (via `_authorizeUpgrade`).
- If `isOwner` always returns `false` (stuck), the protocol cannot register new versions. All StakingVaults would be bricked at upgrade time.

**Modeling recommendation: Trust assumption.**
The `IRoleRegistry` is an external governance contract outside the governor's own domain. Declare:
> **Trust assumption T-ROLEREG:** `roleRegistry.isOwner(addr)` returns `true` iff `addr` is the current owner of the Reserve protocol. `isOwnerOrEmergencyCouncil` includes the emergency council subset. These booleans are correct with respect to Reserve's off-chain governance.

In proofs that touch `VersionRegistry.registerVersion` or `RewardTokenRegistry.registerRewardToken`, assert the auth condition as a `Valid.t` hypothesis rather than modeling the RoleRegistry internals.

---

## ReserveOptimisticGovernanceVersionRegistry (Reserve-owned)

**Source:** `contracts/VersionRegistry.sol`
**Usage:** Called from `StakingVault._authorizeUpgrade` (lines 535, 539):
```solidity
(bytes32 latestVersionHash,,, bool deprecated) = versionRegistry.getLatestVersion();
(address latestStakingVaultImpl,,) = versionRegistry.getImplementationsForVersion(versionHash);
```

**Direction of trust:** Egress.

**State the governor reads:**
- `getLatestVersion() → (versionHash, version, deployer, deprecated)` — the current canonical version.
- `getImplementationsForVersion(hash) → (stakingVaultImpl, governorImpl, timelockImpl)` — implementation addresses for a given version.

**Returned values the governor relies on:**
- `deprecated` flag — if `true`, StakingVault refuses the upgrade (safety gate).
- `latestVersionHash` — determines which implementation is acceptable. Mismatch reverts upgrade.
- `latestStakingVaultImpl` — the accepted implementation address. If this points to a compromised address, the vault accepts a malicious upgrade.

**Failure modes:**
- Wrong `deprecated = false` when it should be `true`: allows upgrading to a deprecated (potentially vulnerable) implementation.
- Registry returns the wrong `stakingVaultImpl`: vault upgrades to wrong code.
- Registry reverts (e.g. `VersionRegistry__NotConfigured`): upgrade is permanently blocked until registry is configured.

**Modeling recommendation: Mock.**
Represent as `registry : versionHash -> (stakingVaultImpl * bool)` where the bool is `deprecated`. The `_authorizeUpgrade` invariant to prove: the vault only accepts upgrades to `(hash, impl)` pairs where `deprecated = false` and `impl = proposed_impl`. This is the core safety property for the StakingVault upgrade path.

---

## Arbitrary reward token ERC20s

**Source:** Runtime — any address in `StakingVault.rewardTokens`
**Direction of trust:** Egress. StakingVault calls:
- `IERC20(_rewardToken).balanceOf(address(this))` — in `addRewardToken` (line 322), `_accrueRewards` (line 437).
- `SafeERC20.safeTransfer(IERC20(_rewardToken), msg.sender, amount)` — in `claimRewards` (line 361).

**Failure modes:**
- Revert on `balanceOf`: `_accrueRewards` is called from the `accrueRewards` modifier, which wraps every deposit/withdraw/transfer. A reverting reward token bricks the entire vault.
- Revert on `safeTransfer`: claim fails for that token; the loop reverts, losing the remainder of the batch.
- Reentrancy via `safeTransfer` in `claimRewards`: the accrued amount is zeroed before the call (line 359), so reentrancy cannot double-claim. However, a reentrant call could trigger another deposit/withdraw and thus another `_accrueRewards` pass. This would operate on already-zeroed `accruedRewards` and should be safe.
- Lying `balanceOf`: reward index is computed from a false balance. Honest stakers would see incorrect reward accrual.
- Fee-on-transfer tokens: `safeTransfer(amount)` sends less than `amount`; the vault treats `totalClaimed` as increasing by `amount`. Overstated `balanceLastKnown` would accrue phantom rewards on next call.

**Modeling recommendation: Trust assumption + Valid hypothesis.**
Declare:
> **Trust assumption T-REWARDTOKEN:** Each registered reward token is an honest ERC20: `balanceOf` is accurate, `safeTransfer` delivers exactly the requested amount, and `balanceOf` does not revert.

In the `StakingVaultRewards.v` simulation, `balanceLastKnown` is already taken as an explicit argument. The trust assumption formalizes the precondition that this argument equals the true on-chain balance.

---

## Arbitrary proposal target contracts

**Source:** Runtime — `targets[]` array in any proposal
**Direction of trust:** Egress. The timelock executes arbitrary calldata against arbitrary targets via `executeBatch` (standard) and `executeBatchBypass` (optimistic).

**State the governor reads:** None (the governor does not read state from target calls).

**Side effects:** Any state change to any external contract is possible. Governance controls what calls are permitted via `OptimisticSelectorRegistry` (for optimistic proposals) and via the `targets[i].code.length != 0` check (for pessimistic proposals, ProposalLib.sol:96).

**Failure modes:**
- Target reverts: entire batch reverts. The proposal does not transition to Executed; it remains Queued (pessimistic) or re-executable (optimistic, once).
- Target reentrancy: a target could call back into the governor. The governor's `executed` flag and the timelock's operation-id uniqueness prevent double-execution.
- Malicious target approved by `OptimisticSelectorRegistry`: an optimistic proposer could execute arbitrary calls to a target that the selector registry allows. The registry is the only defense; proofs about the governor should include the invariant "selectors in the registry are safe by construction" as a `Valid.t` condition.

**Modeling recommendation: Trust assumption.**
> **Trust assumption T-TARGET:** The behavior of any external target called via `executeBatch` or `executeBatchBypass` is outside the scope of these proofs. Proofs about governor safety treat target calls as opaque operations that may succeed or revert but do not observe or modify governor-internal storage.

---

## Threat surface summary

### Highest severity (wrong data corrupts a core safety invariant)

1. **Voting token (`IOptimisticVotes.getPastOptimisticVotes`, `IERC5805.getPastTotalSupply`):** Incorrect past supply or vote weight directly corrupts the veto threshold computation and the pessimistic-proposal proposal-threshold. A lying or rounding-buggy token would allow vetoes to be suppressed or proposals to pass without sufficient stake.

2. **UD60x18.powu (reward decay):** A systematic error here would cause the vault to over- or under-pay rewards. Over-payment could drain the vault; under-payment silently harms stakers. The `-1` rounding term in `_calculateHandout` provides a thin buffer against over-payment but not a formal proof.

3. **AccessControl.hasRole (proposer gating):** If `hasRole(OPTIMISTIC_PROPOSER_ROLE, ...)` returns wrong values, unauthorized addresses can make optimistic proposals. This is the entry gate for the optimistic governance path.

### Medium severity (wrong data causes incorrect behavior but not direct fund loss)

4. **Checkpoints.Trace208.upperLookupRecent:** A bug here would give stale optimistic vote weights. Since these are only used for veto-counting in the optimistic path, the impact is bounded to the current veto window.

5. **ReserveOptimisticGovernanceVersionRegistry:** An incorrect `deprecated` flag could allow or block vault upgrades. This is critical during an active upgrade event but has no effect otherwise.

6. **Reward token balanceOf:** Incorrect balance readings cause wrong reward index deltas. Accrued reward debt could be inflated (phantom rewards) or deflated (lost rewards).

### Low severity (bounded or deployment-time only)

7. **EnumerableSet:** Iteration order change would reshuffle accrual order, but since accrual commutes across tokens, this has no semantic effect.

8. **ERC1967Proxy / Clones:** Deployment-time only. Errors are one-time and immediately observable.

9. **IRoleRegistry:** Governance-path authorization. Compromise requires the Reserve owner key to be compromised, which is outside the threat model.

---

## Modeling recommendations — ordered by priority

*Priority is determined by: (1) whether the dependency blocks an in-flight proof task, (2) severity of the threat it guards, and (3) whether the model already exists.*

### Priority 1: Checkpoints.Trace208 mock (blocks task #84)

The `StakingVaultDelegation.v` simulation (task #84) needs a model of `Trace208.push` and `upperLookupRecent` to prove the dual-delegation independence invariant. This is the most immediate blocker.

**Recommended model:** A `list (U256.t * U256.t)` (timestamp × value pairs), sorted by timestamp. `push(t, v)` appends; `upperLookupRecent(t)` returns `value` of the rightmost entry with `timestamp <= t`. The key theorem: `upperLookupRecent(t, push(t, v, checkpoints)) = v` when `t >= last_timestamp(checkpoints)`.

### Priority 2: ERC20 balance map mock (blocks StakingVaultRewards reward-conservation proof)

The `claimRewards` correctness theorem — `sum(claimable) = totalClaimed - totalClaimed_pre` — requires modeling the `safeTransfer` side effect. Currently `StakingVaultRewards.v` takes `claimable` as an abstract value. Adding a `balances : Address -> U256.t` map with `safeTransfer(token, recipient, amount)` updating it makes the claim-is-faithful theorem statable.

**Recommended model:** `(balances : Address -> U256.t)` with `transfer_updates : balances[to]' = balances[to] + amount /\ balances[vault]' = balances[vault] - amount`. This is a minimal mock — no total-supply tracking needed, since the vault only reads its own balance via `balanceOf(this)`.

### Priority 3: UD60x18.powu abstract axioms (needed for StakingVaultExchange integration)

The `_calculateHandout` function is currently out of scope in `StakingVaultExchange.v` (the caller supplies `accumulatedNativeRewards` as an argument). For integration proofs that couple the exchange-rate surface with the rewards surface, the CAS-validated bound `0 <= calculateHandout(bal, elapsed, ratio) <= bal` needs to be an explicit Rocq hypothesis rather than an implicit assumption.

**Recommended action:** Add an `Axiom calculateHandout_bounded` to `StakingVaultRewards.v` or a shared `Axioms.v` file, stating the four properties listed in the `@prb/math` section above. Gate all downstream lemmas on this axiom.

### Priority 4: IRoleRegistry trust assumption (blocks VersionRegistry proofs)

The `StakingVault._authorizeUpgrade` proof depends on `versionRegistry.getLatestVersion()` returning the correct `deprecated` flag. Before that proof is attempted, add a formal `Trust_T_ROLEREG` hypothesis to the `Valid.t` record for the VersionRegistry mock.

### Priority 5: ECDSA abstract axiom (needed for delegateOptimisticBySig proofs)

When the delegation proof tree reaches `delegateOptimisticBySig`, it needs an `ECDSA.recover_correct` axiom. This is low urgency since delegation-by-sig is a secondary path; the primary delegation path (`delegateOptimistic`) does not use ECDSA.

### Priority 6 (can stay abstract indefinitely):

- **ERC1967Proxy / Clones / UUPSUpgradeable** — deployment-time only; the proof tree does not model contract deployment.
- **SafeCast** — trivial downcast; modeled as identity on bounded inputs throughout.
- **Math.max / Math.mulDiv** — already effectively abstracted in the StakingVaultRewards simulation; just state the Z-arithmetic equality explicitly when needed.
- **Strings.tryParseAddress** — the `_isValidDescriptionForProposer` check is a pessimistic-proposal guard. It affects proposer enumeration, not fund safety. Abstract axiom is sufficient when the pessimistic-proposal proof is eventually attempted.
- **Time.timestamp()** — already resolved: pass `now : U256.t` everywhere.
- **Arbitrary proposal targets** — out of scope by design.
- **IRoleRegistry** — out of scope governance singleton.

---

## Mocks landed

The three highest-priority external-dependency mocks identified above are now landed under `rocq/mocks/`. Each is wired into `_RocqProject` in a `# --- Mocks of external dependencies ---` block ahead of the per-domain entries, so all simulations and proofs can consume them.

### `rocq/mocks/Trace208.v` — OpenZeppelin `Checkpoints.Trace208`

Sorted list of `(key, value)` checkpoints with `empty`, `push`, `latest`, `upperLookupRecent`. `push` appends on strictly-larger key and updates in place otherwise (in lieu of the OZ "revert on out-of-order" path, which the Governor never triggers since it pushes monotone `Time.timestamp()`).

Proven lemmas:
- `latest_after_push` — pushing a strictly larger key updates `latest`
- `upperLookupRecent_returns_0_below_first` — query below first key yields 0 (under sortedness)
- `latest_eq_upperLookup_at_last_key` — `upperLookupRecent` at the last key returns `latest`
- `push_preserves_sortedness` — `Module Valid` sortedness invariant is preserved by push

Plus a `Module Examples` exercising `vm_compute` on a three-push trace, an in-place-update trace, and the empty trace.

**Existing proof candidates for adoption:** `proofs/StakingVaultDelegation.v` currently abstracts the optimistic-vote checkpoint store down to a `votes` map (last value only). When the dual-delegation independence theorem extends to past-vote correctness (`getPastOptimisticVotes`), it can replace that abstraction with `Trace208.upperLookupRecent` on a per-delegate `Trace208.t` field.

### `rocq/mocks/ERC20.v` — Balance-map IERC20 / SafeERC20

`Record State := { balances : list (Address * U256.t); totalSupply : U256.t }` with `balanceOf`, `transfer`, `transferFrom` (the latter taking allowance as an explicit argument). Reverts on insufficient balance or insufficient allowance.

Proven lemmas:
- `transfer_preserves_total_supply` — supply invariant across `transfer`
- `transfer_decreases_sender_increases_receiver_by_amount` — exact-debit/exact-credit, no fees
- `transfer_zero_to_self_noop` — zero-amount and self-transfer paths are no-ops

`Module Valid` carries `sum balances = totalSupply` and `all_nonneg balances`, plus `U256.Valid.t totalSupply`. `Module Examples` exercises `vm_compute` on successful and reverting transfers and `transferFrom`s.

**Existing proof candidates for adoption:** `proofs/StakingVaultRewards.v` currently states the claim-faithfulness theorem in terms of an abstract `claimable` argument. With this mock available, the theorem can be sharpened to: "for every reward token, the change in `ERC20.balanceOf(vault)` equals `-totalClaimedDelta`" — the conservation theorem named in the audit's Priority 2.

### `rocq/mocks/PRBMath.v` — `UD60x18.powu` axiomatic interface

`Parameter powu : U256.t -> U256.t -> U256.t` with five axioms:
- `powu_zero_exp` — `powu base 0 = 10^18` (identity)
- `powu_zero_base` — `0 < n -> powu 0 n = 0` (zero passthrough)
- `powu_bounded` — `base <= 10^18 -> powu base n <= 10^18`
- `powu_monotone_in_exp` — sub-one base, decay shape in elapsed
- `powu_one_base` — `powu (10^18) n = 10^18` (rewardRatio=0 corner)

Plus two derived corollaries (`powu_nonneg`, `powu_zero_exp_eq_one_d18`) and a `Module Valid.decay_base` predicate capturing `0 < b <= 10^18` (the production invariant on `1e18 - rewardRatio`).

**Axioms considered but rejected as too strong:**
- *Strict monotonicity* (`n1 < n2 -> powu base n1 > powu base n2`) — false on the rounded D18 implementation: small inputs can produce equal outputs after floor rounding. Sticking with `>=` keeps the axiom faithful.
- *Multiplicativity* (`powu base (n1 + n2) = powu base n1 * powu base n2 / ONE_D18`) — would be nice but cannot be proved equationally on rounded D18 arithmetic; the rounding error is precisely what the CAS witnesses pin numerically rather than algebraically.
- *Explicit value at small inputs* (`powu base 1 = base`) — true on the real-number kernel but the D18 floor-rounding could in principle introduce off-by-one (it does not in practice for `base <= ONE_D18`; CAS-validated). Left out to keep the axiom set minimal.

**Existing proof candidates for adoption:** `simulations/StakingVaultExchange.v` (the "exchange rate" surface) currently takes `accumulatedNativeRewards` as an opaque argument. With `PRBMath.powu` available, the `_calculateHandout` formula can be inlined verbatim and the "handout <= balance" invariant proved against `powu_bounded`. Similarly the "handout = 0 at elapsed = 0" lemma against `powu_zero_exp`.

