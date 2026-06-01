# Sim-vs-source fidelity audit (2026-05-31)

Adversarial review pass focused on whether the Coq simulation files
faithfully model the actual Solidity sources. Baseline:
`thefrozenfire/feature/formal-verification` @ `dbf4844`. Read-only audit.

Each finding cites:
- the contract location (file:line),
- the sim definition (file:line),
- the disposition (CRITICAL / MEDIUM / LOW / INFO),
- whether it is gated by a `Valid` predicate, a precondition in the
  equivalence proof, or otherwise.

R056 (OZ EnumerableSet swap-and-pop vs order-preserving sim `remove_role`)
is the canonical pattern. The audit looked for both R056-style structural
divergences and other classes of mismatch.

---

## Per-contract findings

### ProposalLib

Sim: `simulations/ProposalLib.v`. Contract: `contracts/governance/lib/ProposalLib.sol`.

- **LOW (P1)** — sim's `saveProposal` does not model `SafeCast.toUint48` /
  `SafeCast.toUint32`.
  - Contract `_saveProposal` (`ProposalLib.sol:182-186`):
    ```
    proposalCore.voteStart = SafeCast.toUint48(block.timestamp + voteDelay);
    proposalCore.voteDuration = SafeCast.toUint32(voteDuration);
    ```
    `SafeCast.toUintN` reverts when the value exceeds 2^N - 1.
  - Sim `saveProposal` (`ProposalLib.v:270-277`) stores `now + voteDelay`
    and `voteDuration` as raw `U256.t` without truncation or revert.
  - Effect: `block.timestamp + voteDelay > type(uint48).max` reverts on
    chain, succeeds in the sim. Likewise `voteDuration > type(uint32).max`.
    The sim's `Valid.well_formed_proposal` does not bound either field.
  - Disposition: caller-side preconditions (`voteDelay < MAX_OPTIMISTIC_DELAY`
    from `ReserveOptimisticGovernor._setVotingDelay` at ROG.sol:480) keep
    this off the realistic edge, but the sim's invariant is broader than
    the contract's reachable set. Audit-clarification.

- **INFO** — `_isValidDescriptionForProposer` parser collapses two
  contract paths.
  - Contract returns true if (a) length < 52, (b) marker mismatch,
    (c) `!success` on `Strings.tryParseAddress`, OR (d) the parsed
    address equals proposer (`ProposalLib.sol:200-221`).
  - Sim folds (a)+(b)+(c) into a single `None` case of
    `description_proposer : Desc -> option Address`
    (`ProposalLib.v:120, 231-236`). Sound (the parameter is abstract),
    but auditors should know the sim doesn't distinguish the three
    failure modes.

- **INFO** — `transitionToPessimistic` does NOT model overwrite of an
  existing `proposalCores[newProposalId]` slot. The contract calls
  `_saveProposal(proposalData, proposalCores[newProposalId], ...)` —
  if that slot already has `voteStart != 0` from a prior call, it is
  silently overwritten. Sim's `transitionToPessimistic`
  (`ProposalLib.v:422-457`) returns the new core record but doesn't
  cross-check the fresh-slot invariant. Matches contract behavior
  (so faithful), but is a contract-side audit point distinct from
  the sim/source equivalence.

### ReserveOptimisticGovernor

Sim: `simulations/Governor.v`. Contract: `contracts/governance/ReserveOptimisticGovernor.sol`.

- **CRITICAL** — `state()` does NOT model the `pastSupply == 0 ->
  Canceled` branch.
  - Contract `state(proposalId)` (`ROG.sol:249-253`):
    ```
    uint256 pastSupply = token().getPastTotalSupply(snapshot);
    if (pastSupply == 0) {
        return ProposalState.Canceled;
    }
    ```
    A proposal observed with `pastSupply == 0` at its snapshot is
    Canceled, NOT Defeated, NOT Succeeded, regardless of veto votes
    or deadline.
  - Sim `observe` (`Governor.v:198-219`) has no equivalent branch.
    `pastSupply` isn't even a field of `Proposal.t`; the sim freezes
    `vetoThresholdTok` at creation time.
  - Effect: a proposal that the contract would observe as Canceled
    can be observed as PhaseDefeated / PhaseSucceeded / PhaseActive
    by the sim. Downstream: `_tallyUpdated`'s transition trigger
    (`ROG.sol:439-443`) only fires on `state == Defeated` — under
    the sim's model, transitions can be triggered when the contract
    would refuse them.
  - Disposition: load-bearing for ANY claim about reachability of
    PhaseDefeated -> PhaseStdPending. Recommend documenting as a
    Caveat or extending `Proposal.t` with a `pastSupply` field.

- **CRITICAL** — `state()` recomputes `vetoThresholdTok` LIVE from
  current `pastSupply` and current `vetoThreshold` at observation
  time; sim freezes both at creation time.
  - Contract `state()` (`ROG.sol:241, 256-257`):
    ```
    uint256 _vetoThreshold = vetoThreshold(proposalId);  // can be UINT256_MAX!
    ...
    uint256 vetoThresholdTok = (_vetoThreshold * pastSupply) / 1e18;
    vetoThresholdTok = Math.max(vetoThresholdTok, 1);
    ```
    Both `_vetoThreshold` (sentinel-bumpable to `UINT256_MAX`) and
    `pastSupply` (live token().getPastTotalSupply) are re-read each
    call.
  - Sim freezes `vetoThresholdTok` at `propose_optimistic` time
    (`Governor.v:273`, see `vetoThresholdTokOf`). The sentinel-bump
    on transition is modeled by phase=PhaseDefeated only, not by a
    runtime change of the threshold value.
  - Effect: any change in token supply between creation and
    observation (mint, burn) shifts the contract's threshold-tok
    while the sim's stays frozen. A proposal that's "ready to be
    Defeated" under the sim's model may still be Active on chain
    (or vice versa).

- **MEDIUM** — `proposalThreshold()` modeled abstractly; CEIL division
  in contract not captured.
  - Contract (`ROG.sol:308-315`):
    ```
    uint256 supply = Math.max(1, token().getPastTotalSupply(block.timestamp - 1));
    return (proposalThresholdRatio * supply + (1e18 - 1)) / 1e18;
    ```
    CEIL division; floor would round small thresholds to 0.
  - Sim has no equivalent — the pessimistic-track propose path is
    abstracted out per the sim's "Not modeled" list (`Governor.v:56-58`).
    Caller (ProposalLib) reads `governor.proposalThreshold()` as an
    opaque `U256.t`. As long as the sim accepts the value the contract
    returns, fidelity holds. Note inline.

- **LOW** — `_validateCancel` proposer-cancel path: sim's
  `cancel_validated` approximates the contract's `state()`-based
  decision with phase comparison (`Governor.v:528-540`). The
  contract checks `state(proposalId) != Defeated` for optimistic
  and `state(proposalId) == Pending` for standard; the sim
  pattern-matches on `phase`. Already documented (`Caveat-11 SV3`)
  and known.

### TimelockControllerOptimistic + base

Sim: `simulations/Timelock.v`. Contracts:
`contracts/governance/TimelockControllerOptimistic.sol` +
OZ `TimelockControllerUpgradeable.sol`.

- **MEDIUM** — `executeBatch` does not model the `onlyRoleOrOpenRole`
  "open role" branch.
  - OZ contract (`TimelockControllerUpgradeable.sol:167-172, 415`):
    ```
    modifier onlyRoleOrOpenRole(bytes32 role) {
        if (!hasRole(role, address(0))) {
            _checkRole(role, _msgSender());
        }
        _;
    }
    ```
    If `hasRole(EXECUTOR_ROLE, address(0))` is true, ANY caller can
    execute — the explicit caller-role check is skipped.
  - Sim `executeBatch` (`Timelock.v:199-206`) takes a boolean
    `hasExecutor` and reverts unconditionally if false.
  - The equivalence file (`TimelockControllerBase.v:433+`) uses
    `has_role_or_open` correctly for the abstract base, but the
    `TimelockControllerOptimistic.v` equivalence file binds via
    `has_EXECUTOR_ROLE : Address -> bool` directly
    (`TimelockControllerOptimistic.v:133, 148-151`), without an
    explicit alternative path for the open-role case.
  - Effect: if the deployment grants `EXECUTOR_ROLE` to `address(0)`,
    the contract allows anyone to execute; the sim/equivalence
    requires the caller to hold the role. Sim/equivalence is
    SOUND (any `hasExecutor=true` is reachable by holders), but
    INCOMPLETE on the open-role case.
  - Disposition: matters only for deployments that use the open-role
    pattern — this codebase's Deployer does not, by inspection.
    Document the assumption.

- **INFO** — sim `executeBatch` doesn't model the predecessor chain
  (`_beforeCall` predecessor check) or the `_execute` calls
  themselves. Documented (`Timelock.v:73-77`).

### OptimisticSelectorRegistry

Sim: `simulations/SelectorRegistry.v`. Contract:
`contracts/governance/OptimisticSelectorRegistry.sol`.

- **INFO** — `addSelector`'s forbidden-target check is per-selector
  in the sim (`SelectorRegistry.v:112-132`), per-call in the contract
  (`OSR.sol:84-104` — check is outside the inner per-selector loop).
  Both refuse the same inputs; the divergence is only in *what
  reverts the operation*. Equivalence proof must thread the forbidden
  list through correctly.

- **INFO** — R059-style `set_eq_at_role` (per WISDOM) IS used in the
  equivalence proof (`SelectorRegistry.v:21-26`), so the OZ
  EnumerableSet swap-and-pop divergence is correctly abstracted.

### Guardian

Sim: `simulations/Guardian.v`. Contract: `contracts/Guardian.sol`.

- **MEDIUM** — TOCTOU is acknowledged but the racing-cancel attack
  vector is documented as out-of-model.
  - The sim provides BOTH a `cancel` (`Guardian.v:313-344`) using
    pure oracle reads AND a `cancel_with_governor_state`
    (`Guardian.v:387-416`) using a single snapshot.
  - Contract `cancel` (`Guardian.sol:72-97`) does the two reads
    (`isOptimistic` + `state`) across two SLOAD-bridged external
    calls, racing with `_tallyUpdated`'s sentinel-bump.
  - Even the snapshot variant doesn't model the on-chain TOCTOU
    between the Guardian's hasRole check and the downstream
    `managedGovernor.cancel(...)`. Acknowledged in the sim
    (`Guardian.v:346-374`). Audit-clarification.

- **LOW** — `renounceRole` doesn't model the
  `callerConfirmation == _msgSender()` requirement that OZ
  AccessControl 5+ enforces (`Guardian.v:469-491`). The sim's
  `renounceRole(s, role, caller)` removes `caller` from the role
  unconditionally. The contract's `renounceRole(role, callerConfirmation)`
  reverts if `callerConfirmation != _msgSender()`. Sim is more
  permissive than the contract. Sound (a call that revokes self is
  reachable), incomplete (the contract's revert path isn't modeled).

### VersionRegistry

Sim: `simulations/VersionRegistry.v`. Contract:
`contracts/VersionRegistry.sol`.

- **MEDIUM** — Sim FREEZES the impl triple at registration time;
  contract reads it LIVE from the deployer each call to
  `getImplementationsForVersion`.
  - Contract (`VersionRegistry.sol:82-92`):
    ```
    return (
        deployments[versionHash].stakingVaultImpl(),
        deployments[versionHash].governorImpl(),
        deployments[versionHash].timelockImpl()
    );
    ```
    Three live external calls, each reading the deployer's storage
    (or function return) at view time.
  - Sim (`VersionRegistry.v:219-227`) stores
    `(stakingVaultImpl, governorImpl, timelockImpl)` in `VersionEntry.t`
    at `registerVersion` time. Later `getImplementationsForVersion`
    reads the frozen triple (`VersionRegistry.v:304-314`).
  - Effect: under the realistic assumption that deployers are
    immutable, the sim and contract agree. If a deployer's
    `stakingVaultImpl()` (etc.) is upgradeable or returns different
    values at different times, they diverge. The sim's behavior
    is a model assumption that the contract does NOT enforce.

- **INFO** — `deprecateVersion` for unregistered hashes: sim
  returns Success with state unchanged (`VersionRegistry.v:241-255`);
  contract sets `isDeprecated[h] = true` for the unregistered hash
  (a write that has no effect on anything else because the
  upgrade path requires a registered hash). Documented in the sim
  as a known divergence safe-for-upgrade-authorization.

### RewardTokenRegistry

Sim: `simulations/RewardTokenRegistry.v`. Contract:
`contracts/staking/RewardTokenRegistry.sol`.

- **INFO** — Sim's `list_remove` (`RewardTokenRegistry.v:86-90`)
  preserves order; contract's `_rewardTokens.remove(...)` uses OZ
  EnumerableSet swap-and-pop. R059-style `set_eq_in_registry` IS
  used in the equivalence (`RewardTokenRegistry.v:837+`), so this
  is correctly abstracted. R056 pattern applied.

- **INFO** — `unregisterRewardToken` and `registerRewardToken` revert
  on no-op (already-registered / not-registered) — sim matches
  (`RewardTokenRegistry.v:102-129`). Note the order: contract checks
  role gate first (require), THEN attempts add/remove. Sim does the
  same (negb is_owner first, then `list_contains` check). Match.

### ThrottleLib

Sim: `simulations/ProposerThrottle.v`. Contract:
`contracts/governance/lib/ThrottleLib.sol`.

- **LOW** — `_getProposalsAvailable` computes
  `elapsed = block.timestamp - throttle.lastUpdated` (`ThrottleLib.sol:48`).
  The sim uses `now - lastUpdated` (`ProposerThrottle.v:78`). Both
  underflow when `lastUpdated > now` (impossible on real chains
  under monotone block.timestamp, but the sim's `Valid` predicate
  doesn't enforce `lastUpdated <= now`). The sim's `Valid` should
  carry a `lastUpdated <= now` precondition if any proof depends on
  no-underflow.

- **INFO** — Rounding-leak discussion is documented in the sim header
  (`ProposerThrottle.v:30-36`); INV-6 in CAS witnesses validates
  the divergence between "exact one-slot consumption" and floor-
  divided slot.

### UnstakingManager

Sim: `simulations/UnstakingManager.v`. Contract:
`contracts/staking/UnstakingManager.sol`.

- **INFO** — `cancelLock` order of checks: contract checks
  `user == msg.sender` first, then `claimedAt == 0`
  (`UnstakingManager.sol:55-62`). Sim matches exactly
  (`UnstakingManager.v:151-160`).

- **INFO** — `claimLock` is permissionless (no caller check) on both
  sides. Match.

- **INFO** — Default-zero lock slot for unset lockId is handled by
  Solidity's mapping default (returns zero struct); sim's `lock_at`
  returns `default_lock` for out-of-range index (`UnstakingManager.v:111-112`).
  Match.

### StakingVault (multiple sims)

#### StakingVaultExchange

Sim: `simulations/StakingVaultExchange.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **CRITICAL** — Sim's `convertToShares` / `convertToAssets` use
  the WRONG formula vs OZ ERC4626 v5.4.
  - OZ contract (`ERC4626Upgradeable.sol:247-256`):
    ```
    function _convertToShares(uint256 assets, Math.Rounding rounding) ... {
        return assets.mulDiv(totalSupply() + 10 ** _decimalsOffset(), totalAssets() + 1, rounding);
    }
    function _convertToAssets(uint256 shares, Math.Rounding rounding) ... {
        return shares.mulDiv(totalAssets() + 1, totalSupply() + 10 ** _decimalsOffset(), rounding);
    }
    ```
    Inflation-defense `+1` on `totalAssets` denominator and
    `10^offset` on `totalSupply` numerator. StakingVault does NOT
    override `_decimalsOffset()` so offset = 0 (`10^0 = 1`), but
    the `+1` on the denominator and the `+1` on the numerator are
    still applied.
  - Sim `convertToShares` (`StakingVaultExchange.v:71-76`):
    ```
    if s.(State.totalSupply) =? 0 then assets
    else (assets * s.(State.totalSupply)) / ta.
    ```
    No `+1` on either side. The supply-zero case returns `assets`
    1:1, which AGREES with the contract (since `(assets * 1) / 1 = assets`),
    but the supply-nonzero case differs.
  - Effect: any sim-level lemma about
    "round-trip rounding bound" or "share-value monotonicity" is
    a theorem about the WRONG mathematical object. The downstream
    equivalence proof binds via the ERC4626 abstract base
    (`equivalence/ERC4626.v:152-154, 426-455` model the correct
    formula), so the end-to-end Qed depends on that binding being
    actually completed.
  - The sim's file header
    (`StakingVaultExchange.v:13-19, 53-58`) advertises
    "share-value monotonicity" and "round-trip rounding bound" as
    headline theorems — but those properties are proved against
    the sim's formula, not the contract's.
  - **This is the single most concerning mismatch found in the audit.**

- **MEDIUM** — Sim models accumulated native rewards as a separate
  stored field `accumulatedNativeRewards`; contract has no such
  field (rewards are folded into `totalDeposited` via
  `_accrueRewards` at line 428 — `totalDeposited += _currentAccountedNativeRewards()`).
  The sim's `totalAssets = totalDeposited + accumulatedNativeRewards`
  matches the contract's `totalAssets = totalDeposited + _currentAccountedNativeRewards()`
  at any observation point IF the accrual is computed at the same
  block.timestamp. The sim treats the rewards as a pre-settled
  scalar; the contract computes them live from
  `nativeBalanceLastKnown - totalDeposited` and elapsed time.
  Sound under the binding assumption.

- **INFO** — `withdraw` `unstakingDelay != 0` branch (UnstakingManager-
  routed) is not separately modeled at the StakingVaultExchange sim
  level. The sim collapses both branches into one
  share-decrement + asset-decrement. The actual asset transfer to
  UnstakingManager.createLock vs receiver is the difference. This
  is fine for share-rate reasoning but the equivalence proof must
  not over-claim "receiver got assets directly."

#### StakingVaultDelegation

Sim: `simulations/StakingVaultDelegation.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **INFO** — Sim's `transfer` (`StakingVaultDelegation.v:158-172`)
  reads `oFrom`/`oTo` (optimistic delegates) from the PRE-state.
  Contract `_update` (`StakingVault.sol:499-506`) reads
  `optimisticDelegatees[from]` and `optimisticDelegatees[to]` AFTER
  `super._update` (which doesn't touch the optimistic delegate map).
  Observationally equivalent, since `super._update` only mutates
  balances, std votes, std delegates, NOT optimistic delegates.

- **INFO** — Sim's `transfer` does balance-then-votes-pointwise.
  Contract's order is balance (via super._update) then sequential
  std-then-opt votes moves. Both std and opt move_votes use the SAME
  `value` and disjoint ledgers, so sequential vs parallel doesn't
  matter.

- **INFO** — accrueRewards modifier prefix (`StakingVault.sol:502`)
  isn't part of `transfer`'s sim definition. The sim handles the
  delegation/vote layer in isolation; reward accrual is owned by
  StakingVaultRewards.v. Equivalence proof must compose them
  correctly.

#### StakingVaultDelegationCheckpointed

Sim: `simulations/StakingVaultDelegationCheckpointed.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **MEDIUM** — Sim's `set_opt_delegate_checkpointed`
  (`StakingVaultDelegationCheckpointed.v:107-136`) PUSHES to both
  old/new traces whenever `old_d != new_d` AND each address is
  non-zero — regardless of `balanceOf(account)`.
  - Contract `_delegateOptimistic` (`StakingVault.sol:543-549`) calls
    `_moveOptimisticDelegateVotes(oldDelegate, delegatee, balanceOf(account))`,
    which short-circuits on `from == to || amount == 0`
    (`StakingVault.sol:551-554`). When `balanceOf(account) == 0`,
    NO checkpoint push happens on either trace.
  - Sim has no equivalent short-circuit on amount==0 — it always
    pushes (with the unchanged value, since `move_votes` did
    no-op).
  - Effect: zero-balance delegate changes produce an extra
    checkpoint entry per call in the sim vs the contract. The
    Trace208 `push` mock overwrites entries at the same key
    (`mocks/Trace208.v:94-103`), so when `now` happens to equal an
    existing key, the redundant push collapses; otherwise the trace
    accumulates extra entries. Observable via
    `numOptimisticCheckpoints()` (`StakingVault.sol:224-226`).
    `latest()` and `getPastOptimisticVotes()` are unaffected (the
    value pushed equals the existing latest), but the array length
    differs.

#### StakingVaultDelegationBySig

Sim: `simulations/StakingVaultDelegationBySig.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **INFO** — Sim's expiry check `Z.ltb expiry now`
  (`StakingVaultDelegationBySig.v:110`) matches the contract's
  `block.timestamp > expiry` (`StakingVault.sol:205`) — both
  permit signatures AT expiry (equal). Match.

- **INFO** — Sim threads the EIP-712 domain through correctly via
  `ECDSA.typed_data_hash`. Nonce + signer recovery follow OZ's
  standard pattern; no divergence observed.

#### StakingVaultRewards

Sim: `simulations/StakingVaultRewards.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **INFO** — Sim drops two of five fields from `RewardInfo`:
  `payoutLastPaid` and `balanceLastKnown` are not in the sim's
  `RewardInfo.t` (`StakingVaultRewards.v:51-57`). These fields are
  used to compute the `tokensToHandout` delta in the contract
  (`StakingVault.sol:439-441`). The sim takes `balanceDelta` as an
  opaque parameter (documented at `StakingVaultRewards.v:35-40`).
  Sound abstraction; the binding equivalence proof
  (`equivalence/StakingVaultRewards.v` GlobalRewardState) tracks
  the full 5-field shape.

- **LOW** — Sim's `set_reward_ratio_sim` early-returns the unchanged
  state when `halfLife == 0` (`equivalence/StakingVaultRewards.v:232-243`).
  Contract `_setRewardRatio` (`StakingVault.sol:382-392`) reverts
  via `require(_rewardHalfLife >= MIN_REWARD_HALF_LIFE)`, then
  computes `LN_2 / _rewardHalfLife`. If `_rewardHalfLife == 0` did
  reach the division, it would also revert. The sim's silent no-op
  is precondition-gated by `wf_halfLife` in the equivalence file
  (`equivalence/StakingVaultRewards.v:889-890`). Sim should arguably
  surface a revert; documented gate is sufficient.

#### StakingVaultRewardsReentrancy

Sim: `simulations/StakingVaultRewardsReentrancy.v`. Contract:
`contracts/staking/StakingVault.sol`.

- **INFO** — Pattern correctly mirrors the zero-first invariant at
  `claimRewards` (`StakingVault.sol:359` zeroes accrued BEFORE
  `safeTransfer`). WISDOM R079 documents this. No divergence
  observed.

---

## Cross-cutting patterns

### 1. Modifier composition is consistently lifted to the equivalence layer

The sims uniformly skip modeling Solidity modifiers
(`accrueRewards`, `onlyRole`, `onlyTimelock`, `initializer`,
`nonReentrant`). The composite walker axioms in the equivalence
layer bind them via per-modifier wrapper axioms (R045 `with_nonReentrant`,
R055 grantRole, R063 staticcall). This is sound and consistent.

Where it fails: `_update`'s `accrueRewards` modifier IS the entry
point for native-reward accrual (line 428 of StakingVault.sol):
`totalDeposited += _currentAccountedNativeRewards()`. The sim's
`transfer` doesn't reflect this; cross-sim composition between
`StakingVaultDelegation`, `StakingVaultRewards`, and
`StakingVaultExchange` must thread the accrual side-effect manually
in the equivalence proof.

### 2. Live oracle reads vs frozen storage

A recurring pattern: the contract reads external state LIVE at
observation time, while the sim FREEZES it at write time.

- `ReserveOptimisticGovernor.state()` reads `pastSupply` LIVE; sim
  freezes `vetoThresholdTok` at create. (CRITICAL)
- `VersionRegistry.getImplementationsForVersion()` reads the impl
  triple LIVE from the deployer; sim freezes at register. (MEDIUM)

In both cases the "live" read introduces TOCTOU-style sensitivity
to events between read points that the sim cannot detect. Audit
implications differ by contract.

### 3. R059 set-equivalence pattern IS consistently applied

SelectorRegistry, RewardTokenRegistry, Guardian (admins / managers /
guardians) all use R059-style `set_eq_*` predicates correctly to
bridge OZ EnumerableSet swap-and-pop vs sim's order-preserving
deletion. R056's lesson appears to have been absorbed across the
corpus.

### 4. OZ inflation-defense `+1` in ERC4626

The StakingVaultExchange sim does NOT model the OZ inflation defense
(+1 denominator). The equivalence file delegates to an abstract
ERC4626 module that DOES model it. The sim-level theorems about
share-rate properties are not theorems about the contract until that
binding is concretized. **CRITICAL** finding.

### 5. Trace208 push on zero-amount delegate changes

OZ's vote-move helpers short-circuit on `amount == 0` and SKIP the
checkpoint push. The sim's `set_opt_delegate_checkpointed`
unconditionally pushes (writing the unchanged value). Observable
via checkpoint-count queries. Affects `numOptimisticCheckpoints()`,
not `latest()` or `getPastOptimisticVotes()`. **MEDIUM**.

---

## CRITICAL findings

Three findings rise to the CRITICAL level:

1. **StakingVaultExchange uses the wrong ERC4626 formula.**
   `simulations/StakingVaultExchange.v:71-76` computes
   `convertToShares = assets * totalSupply / totalAssets` (no `+1`,
   no `10^offset`). The contract via OZ ERC4626 v5.4 uses
   `assets * (totalSupply + 10^offset) / (totalAssets + 1)`. Any
   sim-level proof of round-trip rounding or share-rate
   monotonicity is over the wrong object. The equivalence path
   binds to `equivalence/ERC4626.v` which has the correct formula,
   so the end-to-end equivalence Qed depends on that binding being
   completed.

2. **ReserveOptimisticGovernor's `state()` is missing the
   `pastSupply == 0 -> Canceled` branch.** Contract `ROG.sol:251-253`;
   sim `Governor.v:198-219` has no model of this case.

3. **ReserveOptimisticGovernor's `state()` re-evaluates threshold
   live; sim freezes at create time.** Contract `ROG.sol:241, 256-257`;
   sim `Governor.v:273` stores `vetoThresholdTok` once.

(1) is the single most concerning mismatch — it touches the core
share-asset math of the staking vault, which has direct economic
impact, and the sim ships with two headline theorems that are
*not* theorems about the contract until the ERC4626 abstract base
binding is concretely instantiated.

(2) and (3) together undermine sim-level reachability claims for
the optimistic-to-pessimistic transition state machine. Any proof
that says "Defeated is reachable iff X" or "transition triggers
when Y" needs explicit acknowledgment that pastSupply-dependent
edge cases are not modeled.

## MEDIUM / LOW findings

(See per-contract sections above for the full list.) Recurring
medium-grade items:

- VersionRegistry: live-vs-frozen impl triple (MEDIUM).
- Timelock executor: open-role path not modeled (MEDIUM).
- StakingVaultDelegationCheckpointed: zero-amount push divergence (MEDIUM).
- Guardian: TOCTOU on cancel cross-call (MEDIUM; already documented).
- Guardian: renounceRole caller-confirmation not modeled (LOW).
- ProposalLib: SafeCast.toUint48 / toUint32 not modeled (LOW).
- ProposerThrottle: lastUpdated <= now not bound in Valid (LOW).
- StakingVaultRewards: halfLife==0 silent no-op (LOW; gated by precondition).

## Recommendations

### Audit-side (no code changes)

1. **Add a Caveat to `Audit.v`** noting that the
   `ReserveOptimisticGovernor.state()` sim does not model the
   `pastSupply == 0` branch nor the live-recomputed
   `vetoThresholdTok`. Any audit claim about state-machine
   reachability for optimistic proposals MUST flag this.

2. **Document the ERC4626 sim/source divergence**: the
   `simulations/StakingVaultExchange.v` formula is a strict
   sub-shape of the contract's OZ inflation-defended formula. The
   sim's lemmas are proofs of properties of the simplified formula
   only.

3. **Document open-role assumption for Timelock**: the audit
   assumes `EXECUTOR_ROLE` is NOT granted to `address(0)`. Verify
   via deployment-script inspection (Deployer.sol) and add an
   explicit non-open-role invariant to the audit.

### Sim-side (low-cost edits)

4. Add `Valid.t` precondition `lastUpdated <= now` to
   `ProposerThrottle.Valid.throttle`.

5. Add a `Valid.t` bound on `voteDelay <= type(uint48).max` and
   `voteDuration <= type(uint32).max` to ProposalLib's
   `well_formed_proposal`. Until then, sim's `saveProposal` is
   more permissive than the contract.

6. In `StakingVaultDelegationCheckpointed.set_opt_delegate_checkpointed`,
   add the `amount == 0` short-circuit to match the contract. This
   is a one-line change and removes the checkpoint-count
   divergence.

### Sim-side (heavier)

7. Extend `Governor.Proposal.t` with a `vetoThresholdRatioD18` field
   (the un-snapped, pre-`vetoThresholdTokOf` value) and have
   `observe` recompute the threshold from supply at observation
   time. Add a `pastSupply` parameter to `observe` so the
   `pastSupply == 0 -> Canceled` branch can be modeled.

8. Replace `StakingVaultExchange.convertToShares` and
   `convertToAssets` with the OZ inflation-defended formulas, OR
   parameterize the sim over the formula and let the equivalence
   layer bind concretely. The current state is "two correct
   formulas, only one of which is in the sim, and the audit-quality
   claim is over the wrong one."

### Equivalence-proof gap

9. The `StakingVaultExchange` equivalence proof's ERC4626 abstract
   binding (`StakingVaultExchange.v` references `ERC4626.v` Wave 2
   markers but the concrete instantiation is incomplete) should
   close before the share-rate audit claims promote to "vs
   bytecode" status. Until then, the audit claim level is "vs sim
   formula, which is not the same as the contract's formula."
