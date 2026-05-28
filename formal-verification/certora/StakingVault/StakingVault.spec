/* StakingVault.sol Certora spec - covers a tight slice of the
   ERC4626 + multi-token rewards + dual-delegation contract.

   Properties proved:
     SV1   convertToShares(0) == 0 (zero-asset edge of the ER curve)
     SV2   convertToAssets(0) == 0 (zero-share edge of the ER curve)
     SV3   deposit() mints exactly the returned `shares` to the receiver
     SV4   addRewardToken requires DEFAULT_ADMIN_ROLE
     SV5   removeRewardToken requires DEFAULT_ADMIN_ROLE
     SV6   setRewardRatio requires DEFAULT_ADMIN_ROLE
     SV7   setUnstakingDelay requires DEFAULT_ADMIN_ROLE
     SV8   delegateOptimistic only changes the caller's delegate
     SV9   delegateOptimistic on success sets caller's delegate
     SV10  rewardIndex is monotone non-decreasing across any method call
           (P2 TC2; mirrors Rocq `updateRewardIndex_monotone` /
           audit_rewards_index_monotone)
     SV11  totalClaimed is monotone non-decreasing across any method call
           (mirrors Rocq `claimUser_totalClaimed_monotone`)
     SV12  user.accruedRewards is monotone non-decreasing across any
           non-claim method (mirrors Rocq
           `accrueUser_accrued_monotone`)
     SV13  claimRewards zeroes the claimed user's accruedRewards for
           the (single-token) calldata array (mirrors Rocq
           `claimUser_zeroes_accrued`)

   Deferred:
   - The per-user lastRewardIndex sync property
     (`accrueUser_no_op_when_index_stable`) is exercised through the
     Rocq simulation but not pinned at CVL: the property depends on
     the token being currently present in the `rewardTokens`
     EnumerableSet, and the WISDOM C004 cross-slot HAVOC pathology
     makes membership reasoning unreliable from arbitrary initial
     states.

   Scoping decisions:
   - All IERC20 calls (balanceOf, transfer, transferFrom, approve) and the
     IRewardTokenRegistry.isRegistered call are summarized as wildcard
     NONDET. That gives the prover maximum freedom for downstream
     contracts and keeps the rules about *this* contract's logic.
   - The UnstakingManager.createLock external call is also NONDET.
   - The ERC20Votes side of dual delegation is covered by OZ's own
     audits; we focus on the optimistic overlay where the bookkeeping
     is contract-owned.
   - Reentrancy / signature paths (delegateOptimisticBySig) deferred.

   Note on `_calculateHandout` summary:
   The helper computes the time-decayed handout via `UD60x18.powu`
   which is an unbounded loop the prover cannot close. We summarize
   the internal helper as CONSTANT - the prover picks one uint256
   value per rule. Crucially, CONSTANT picks a uint256, which is
   non-negative by type, and the downstream usage is
       rewardIndex += mulDiv(tokensToHandout, SCALAR * 10**decimals, totalSupply)
   so deltaIndex is non-negative whenever totalSupply > 0. That is
   exactly the precondition we need for `rewardIndexMonotone`.
   The same property carries through to `totalClaimedMonotone`
   (claim increments by `claimable >= 0`) and to
   `userAccruedMonotoneExceptClaim` (`_accrueUser` adds a
   non-negative `supplierDelta`).
*/

// Ghost backing the IRewardTokenRegistry.isRegistered summary so two
// reads within the same rule (the contract reads it inside both
// `_accrueRewards(_caller,_receiver)` and `addRewardToken`) agree on
// the registration status of a given token.
ghost mapping(address => bool) ghostIsRegistered;

methods {
    // Envfree views on StakingVault state.
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function unstakingDelay() external returns (uint256) envfree;
    function rewardRatio() external returns (uint256) envfree;
    function optimisticDelegates(address) external returns (address) envfree;

    // Auto-generated getters for the public reward-tracker mappings.
    // `rewardTrackers(token)` returns the RewardInfo tuple:
    //   (payoutLastPaid, rewardIndex, balanceAccounted,
    //    balanceLastKnown, totalClaimed)
    // `userRewardTrackers(token, user)` returns the UserRewardInfo tuple:
    //   (lastRewardIndex, accruedRewards)
    function rewardTrackers(address) external
        returns (uint256, uint256, uint256, uint256, uint256) envfree;
    function userRewardTrackers(address, address) external
        returns (uint256, uint256) envfree;

    // ERC4626 conversion views - not envfree because totalAssets() reads
    // block.timestamp via _currentAccountedNativeRewards.
    function convertToShares(uint256) external returns (uint256);
    function convertToAssets(uint256) external returns (uint256);

    // _calculateHandout walks UD60x18.powu which is a long loop the
    // prover cannot close in reasonable time. Summarize the internal
    // helper as CONSTANT: the prover picks one uint256 and returns it
    // for every call within a single rule. Sound for every property
    // in this spec - including the rewardIndex / totalClaimed / user
    // accruedRewards monotonicity rules - because the return type is
    // uint256, hence the picked value is non-negative, and the
    // downstream usage only ever *adds* a value derived from
    // `tokensToHandout` to the relevant monotone slot.
    function _calculateHandout(uint256, uint256) internal returns (uint256) => CONSTANT;

    // Wildcard summaries for all external calls into other contracts.
    // The leading `_.` matches any function with that signature on any
    // external address. NONDET lets the prover pick any return value
    // (the strongest abstraction).
    function _.balanceOf(address) external => NONDET;
    function _.transfer(address, uint256) external => NONDET;
    function _.transferFrom(address, address, uint256) external => NONDET;
    function _.approve(address, uint256) external => NONDET;
    function _.allowance(address, address) external => NONDET;
    function _.totalSupply() external => NONDET;

    // RewardTokenRegistry: ghost-backed so two reads within a rule
    // for the same token return the same answer. NONDET would let the
    // prover flip the registration status between reads of the same
    // token, making any rule that pins on registration vacuously
    // unprovable (per WISDOM C015).
    function _.isRegistered(address t) external => ghostIsRegistered[t] expect bool;

    // UnstakingManager.createLock (called from _withdraw delay branch).
    function _.createLock(address, uint256, uint256) external => NONDET;
}

/* ----- SV1: convertToShares zero maps to zero -----
   The OZ formula a * (totalSupply + 10^offset) / (totalAssets + 1) with
   floor rounding necessarily yields zero shares for zero assets, since
   the denominator is at least 1 and the numerator is exactly 0.

   We pin this rather than the full monotonicity statement because the
   full-range monotonicity rule (forall a <= b: convertToShares(a) <=
   convertToShares(b)) generates a 256-bit mulDiv reasoning problem
   that the prover does not close inside our 5-min budget. Zero
   preservation captures the most actionable corner of the exchange-
   rate surface. */
rule convertToSharesZeroMapsToZero {
    env e;
    uint256 shares = convertToShares(e, 0);

    assert shares == 0, "convertToShares(0) != 0";
}

/* ----- SV2: convertToAssets zero maps to zero -----
   Symmetric to SV1. Same rationale on scoping: full monotonicity is
   provable in principle but explodes solver time on this contract. */
rule convertToAssetsZeroMapsToZero {
    env e;
    uint256 assets = convertToAssets(e, 0);

    assert assets == 0, "convertToAssets(0) != 0";
}

/* ----- SV3: deposit mints exactly `shares` to receiver -----
   Pinned to the case where caller != receiver so we observe the
   receiver-side mint without confounding from msg.sender bookkeeping. */
rule depositMintsSharesToReceiver {
    env e;
    uint256 assets;
    address receiver;

    require receiver != 0;
    require receiver != currentContract;
    require e.msg.sender != receiver;
    require e.msg.sender != currentContract;

    uint256 balBefore = balanceOf(receiver);

    uint256 shares = deposit(e, assets, receiver);

    // No overflow: balanceOf increase fits in uint256 (totalSupply <= max).
    require balBefore + shares <= max_uint256;

    assert balanceOf(receiver) == balBefore + shares,
        "deposit did not mint exactly `shares` to receiver";
}

/* ----- SV4: addRewardToken requires DEFAULT_ADMIN_ROLE ----- */
rule addRewardTokenRequiresAdmin {
    env e;
    address token;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);

    addRewardToken@withrevert(e, token);

    assert lastReverted, "non-admin succeeded in addRewardToken";
}

/* ----- SV5: removeRewardToken requires DEFAULT_ADMIN_ROLE ----- */
rule removeRewardTokenRequiresAdmin {
    env e;
    address token;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);

    removeRewardToken@withrevert(e, token);

    assert lastReverted, "non-admin succeeded in removeRewardToken";
}

/* ----- SV6: setRewardRatio requires DEFAULT_ADMIN_ROLE ----- */
rule setRewardRatioRequiresAdmin {
    env e;
    uint256 halfLife;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);

    setRewardRatio@withrevert(e, halfLife);

    assert lastReverted, "non-admin succeeded in setRewardRatio";
}

/* ----- SV7: setUnstakingDelay requires DEFAULT_ADMIN_ROLE ----- */
rule setUnstakingDelayRequiresAdmin {
    env e;
    uint256 delay;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);

    setUnstakingDelay@withrevert(e, delay);

    assert lastReverted, "non-admin succeeded in setUnstakingDelay";
}

/* ----- SV8: delegateOptimistic only changes the caller's delegate -----
   A third party's optimistic delegate is unaffected by msg.sender's
   call to delegateOptimistic. */
rule delegateOptimisticIsCallerScoped {
    env e;
    address newDelegate;
    address other;
    require other != e.msg.sender;

    address otherBefore = optimisticDelegates(other);

    delegateOptimistic(e, newDelegate);

    assert optimisticDelegates(other) == otherBefore,
        "delegateOptimistic changed a non-caller's delegate";
}

/* ----- SV9: delegateOptimistic sets caller's delegate on success ----- */
rule delegateOptimisticSetsCallerDelegate {
    env e;
    address newDelegate;

    delegateOptimistic(e, newDelegate);

    assert optimisticDelegates(e.msg.sender) == newDelegate,
        "delegateOptimistic did not set caller's delegate";
}

/* ----- SV10: rewardIndex monotone non-decreasing -----
   Triple-confirmation of audit_rewards_index_monotone:
     Rocq simulations/StakingVaultRewards.v        (mechanized proof)
     CAS  cas/staking_vault/multi_token_rewards.gp (INV-1 witness)
     CVL  this rule                                (bytecode level)

   Quantifies over an arbitrary reward `token` and an arbitrary
   external method `f`. Snapshots `rewardIndex` before and after
   the call; asserts non-decrease.

   Soundness of the `_calculateHandout => CONSTANT` summary for
   this rule: the only writer of `rewardIndex` in the contract is
   `_accrueRewards(address)` which does
       rewardIndex += deltaIndex
   where `deltaIndex = mulDiv(tokensToHandout, _, _)`. CONSTANT
   makes the prover pick a uint256 (non-negative) for the handout
   value; mulDiv of non-negatives with a non-zero denominator is
   non-negative; therefore `rewardIndex` only grows. */
rule rewardIndexMonotone(method f)
    filtered {
        // UUPS upgradeToAndCall is an arbitrary delegatecall; storage
        // semantics after upgrade are out of scope (the new
        // implementation can map slots however it likes). Authorisation
        // for that path is covered by VersionRegistry/Upgrade specs.
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;

    uint256 idxBefore;
    uint256 a; uint256 b; uint256 c; uint256 d;
    a, idxBefore, b, c, d = rewardTrackers(token);

    f(e, args);

    uint256 idxAfter;
    uint256 a2; uint256 b2; uint256 c2; uint256 d2;
    a2, idxAfter, b2, c2, d2 = rewardTrackers(token);

    assert idxAfter >= idxBefore,
        "rewardIndex decreased across method call";
}

/* ----- SV11: totalClaimed monotone non-decreasing -----
   Mirrors Rocq `claimUser_totalClaimed_monotone`. The only writer
   is the `+= claimableRewards[i]` in `claimRewards`, where
   `claimableRewards[i]` is a uint256 (non-negative). Quantified
   over all methods to catch any future code path that touches
   the slot. */
rule totalClaimedMonotone(method f)
    filtered {
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;

    uint256 claimedBefore;
    uint256 a; uint256 b; uint256 c; uint256 d;
    a, b, c, d, claimedBefore = rewardTrackers(token);

    f(e, args);

    uint256 claimedAfter;
    uint256 a2; uint256 b2; uint256 c2; uint256 d2;
    a2, b2, c2, d2, claimedAfter = rewardTrackers(token);

    assert claimedAfter >= claimedBefore,
        "totalClaimed decreased across method call";
}

/* ----- SV12: user.accruedRewards monotone except across claim -----
   `claimRewards` is the only method that zeroes accruedRewards;
   every other path either leaves it untouched or extends it by a
   non-negative `supplierDelta` in `_accrueUser`. The rule
   quantifies over all methods and filters claimRewards out. */
rule userAccruedMonotoneExceptClaim(method f)
    filtered {
        f -> f.selector != sig:claimRewards(address[]).selector
          && f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;
    address user;

    uint256 lastIdxBefore; uint256 accruedBefore;
    lastIdxBefore, accruedBefore = userRewardTrackers(token, user);

    f(e, args);

    uint256 lastIdxAfter; uint256 accruedAfter;
    lastIdxAfter, accruedAfter = userRewardTrackers(token, user);

    assert accruedAfter >= accruedBefore,
        "accruedRewards decreased across non-claim method";
}

/* ----- SV13: claimRewards zeroes the caller's accruedRewards -----
   The contract zeroes `userRewardTracker.accruedRewards` inside
   the `claimableRewards[i] != 0` branch, but after the
   `accrueRewards(msg.sender, msg.sender)` modifier has already
   run. The modifier picks up the latest global index and folds
   any pending payout into the user's accrued slot; the claim then
   transfers that exact amount and zeroes the slot.

   We pin the single-token shape (length-1 calldata array) - the
   loop-iteration bound is 3 in the conf, but a single-element
   shape captures the essential property without inviting the
   prover to chase the cross-element interleaving. */
rule claimZeroesAccrued {
    env e;
    address token;
    address[] tokens;

    require tokens.length == 1;
    require tokens[0] == token;

    claimRewards(e, tokens);

    uint256 lastIdxAfter; uint256 accruedAfter;
    lastIdxAfter, accruedAfter = userRewardTrackers(token, e.msg.sender);

    assert accruedAfter == 0,
        "claimRewards did not zero the caller's accruedRewards";
}

/* ----- SV10: setUnstakingDelay rejects delay > MAX_UNSTAKING_DELAY -----
   Pins the Vault__InvalidUnstakingDelay custom-error revert path.
   MAX_UNSTAKING_DELAY = 4 weeks = 4 * 7 * 24 * 3600 = 2419200 seconds.
   We require the caller has admin so the only revert reason is the
   bound check (admin auth is covered by SV7). */
rule setUnstakingDelayRejectsAboveMax {
    env e;
    uint256 delay;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require e.msg.value == 0;
    require delay > 2419200;  // MAX_UNSTAKING_DELAY

    setUnstakingDelay@withrevert(e, delay);

    assert lastReverted,
        "setUnstakingDelay accepted delay > MAX_UNSTAKING_DELAY";
}

/* ----- SV11a: setRewardRatio rejects half-life > MAX_REWARD_HALF_LIFE -----
   MAX_REWARD_HALF_LIFE = 2 weeks = 2 * 7 * 24 * 3600 = 1209600 seconds.
   Admin auth covered by SV6. */
rule setRewardRatioRejectsAboveMax {
    env e;
    uint256 halfLife;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require e.msg.value == 0;
    require halfLife > 1209600;  // MAX_REWARD_HALF_LIFE

    setRewardRatio@withrevert(e, halfLife);

    assert lastReverted,
        "setRewardRatio accepted halfLife > MAX_REWARD_HALF_LIFE";
}

/* ----- SV11b: setRewardRatio rejects half-life < MIN_REWARD_HALF_LIFE -----
   MIN_REWARD_HALF_LIFE = 1 day = 86400 seconds. */
rule setRewardRatioRejectsBelowMin {
    env e;
    uint256 halfLife;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require e.msg.value == 0;
    require halfLife < 86400;  // MIN_REWARD_HALF_LIFE

    setRewardRatio@withrevert(e, halfLife);

    assert lastReverted,
        "setRewardRatio accepted halfLife < MIN_REWARD_HALF_LIFE";
}

/* ----- SV12: addRewardToken rejects self as reward token -----
   Pins the Vault__InvalidRewardToken self-branch. The function has
   five revert conditions; we focus on the `_rewardToken !=
   address(this)` check by setting the candidate token to the vault
   itself. Admin auth is covered by SV4. */
rule addRewardTokenRejectsSelf {
    env e;
    address token;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require e.msg.value == 0;
    require token == currentContract;

    addRewardToken@withrevert(e, token);

    assert lastReverted,
        "addRewardToken accepted address(this) as reward token";
}
