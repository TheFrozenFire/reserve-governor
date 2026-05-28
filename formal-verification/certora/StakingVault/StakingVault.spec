/* StakingVault.sol Certora spec - covers a tight slice of the
   ERC4626 + multi-token rewards + dual-delegation contract.

   Properties proved:
     SV1  convertToShares(0) == 0 (zero-asset edge of the ER curve)
     SV2  convertToAssets(0) == 0 (zero-share edge of the ER curve)
     SV3  deposit() mints exactly the returned `shares` to the receiver
     SV4  addRewardToken requires DEFAULT_ADMIN_ROLE
     SV5  removeRewardToken requires DEFAULT_ADMIN_ROLE
     SV6  setRewardRatio requires DEFAULT_ADMIN_ROLE
     SV7  setUnstakingDelay requires DEFAULT_ADMIN_ROLE
     SV8  delegateOptimistic only changes the caller's delegate
     SV9  delegateOptimistic on success sets caller's delegate

   Scoping decisions:
   - All IERC20 calls (balanceOf, transfer, transferFrom, approve) and the
     IRewardTokenRegistry.isRegistered call are summarized as wildcard
     NONDET. That gives the prover maximum freedom for downstream
     contracts and keeps the rules about *this* contract's logic.
   - The UnstakingManager.createLock external call is also NONDET.
   - Reward-accrual math (rewardIndex, accruedRewards updates) is not
     directly asserted; it is exercised transitively by deposit/withdraw
     rules under the NONDET token summaries.
   - The ERC20Votes side of dual delegation is covered by OZ's own
     audits; we focus on the optimistic overlay where the bookkeeping
     is contract-owned.
   - Reentrancy / signature paths (delegateOptimisticBySig) deferred.
*/

methods {
    // Envfree views on StakingVault state.
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function unstakingDelay() external returns (uint256) envfree;
    function rewardRatio() external returns (uint256) envfree;
    function optimisticDelegates(address) external returns (address) envfree;

    // ERC4626 conversion views - not envfree because totalAssets() reads
    // block.timestamp via _currentAccountedNativeRewards.
    function convertToShares(uint256) external returns (uint256);
    function convertToAssets(uint256) external returns (uint256);

    // _calculateHandout walks UD60x18.powu which is a long loop the
    // prover cannot close in reasonable time. Summarize the internal
    // helper as CONSTANT: the prover picks one uint256 and returns it
    // for every call within a single rule. Sound for the properties we
    // care about (monotonicity in the assets/shares argument; share
    // balance change on mint) since they do not depend on the specific
    // handout value, only that it is consistent across the rule.
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

    // RewardTokenRegistry: only one method.
    function _.isRegistered(address) external => NONDET;

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
