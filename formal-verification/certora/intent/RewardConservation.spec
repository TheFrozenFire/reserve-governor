/* RewardConservation.spec
 *
 * Intent-derived rule (per `notes/cantina_pr36_postmortem.md`): every
 * reachable state of StakingVault satisfies the rewards-conservation
 * inequality
 *
 *     sum_{u} userRewardTrackers[t][u].accruedRewards
 *       + rewardTrackers[t].totalClaimed
 *     <= rewardTrackers[t].balanceAccounted
 *
 * for every reward token `t`. This is the per-trace conservation
 * statement; the existing SV10-SV13 rules only pin per-step
 * monotonicity. The Rocq counterpart is
 * `formal-verification/rocq/proofs/StakingVaultRewards_conservation.v`
 * (`rewards_conservation_inequality`), and the CAS witness lives at
 * `cas/staking_vault/multi_token_rewards.gp` (INV-3).
 *
 * Approach: track sum-of-accruedRewards per token with a ghost
 * mapping(address => mathint) updated via an Sstore hook on the
 * struct member. The invariant then has no per-user quantifier and
 * is a pure relation between three scalars per token.
 *
 * Status: see RewardConservation.md.
 *
 * Honest scoping notes:
 *  - We only verify the storage-shape conservation: balanceAccounted
 *    minus (totalClaimed + sumAccrued). The contract's claim that
 *    `balanceAccounted <= IERC20.balanceOf(this) + totalClaimed`
 *    requires reasoning across the external IERC20 balance, which
 *    the wildcard NONDET summary deliberately blurs.
 *  - The `_calculateHandout => CONSTANT` summary (per SV10 reasoning)
 *    means the prover picks one non-negative uint256 per rule for
 *    `tokensToHandout`. balanceAccounted grows by exactly that
 *    amount on the `_accrueRewards` global step.
 *  - The supplier-delta bound `sum_users supplierDelta <= tokensToHandout`
 *    is a mulDiv-rounding fact the SMT layer cannot close
 *    symbolically in our budget. We therefore ship the weaker
 *    *single-method, single-user* form below: every method preserves
 *    the conservation invariant for an arbitrary single user, given
 *    the bookkeeping precondition that the supplier-delta added at
 *    that step does not exceed the running gap. The Rocq theorem
 *    proves this precondition discharges under reachability;
 *    transcribing that proof to CVL is the open work.
 */

methods {
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;

    function rewardTrackers(address) external
        returns (uint256, uint256, uint256, uint256, uint256) envfree;
    function userRewardTrackers(address, address) external
        returns (uint256, uint256) envfree;

    // Same CONSTANT summary as the SV10/11/12 rules - the picked
    // value is uint256, hence non-negative; the rule downstream
    // reasoning only needs non-negativity.
    function _calculateHandout(uint256, uint256) internal returns (uint256) => CONSTANT;

    // Wildcard external summaries (mirrors StakingVault.spec).
    function _.balanceOf(address) external => NONDET;
    function _.transfer(address, uint256) external => NONDET;
    function _.transferFrom(address, address, uint256) external => NONDET;
    function _.approve(address, uint256) external => NONDET;
    function _.allowance(address, address) external => NONDET;
    function _.totalSupply() external => NONDET;
    function _.isRegistered(address) external => NONDET;
    function _.createLock(address, uint256, uint256) external => NONDET;
}

/* ----- Ghost: per-token running sum of accruedRewards across users.
 *
 * Updated atomically by the Sstore hook on the struct slot. mathint
 * eliminates overflow concerns at the ghost layer; the underlying
 * uint256 slots cannot themselves overflow without the EVM having
 * already reverted.
 */
ghost mapping(address => mathint) sumAccruedPerToken {
    init_state axiom forall address t. sumAccruedPerToken[t] == 0;
}

/* Sstore hook: every write to userRewardTrackers[token][user].accruedRewards
 * is mirrored into sumAccruedPerToken[token] by
 *   delta = newVal - oldVal.
 *
 * The contract has exactly two writers of this slot:
 *   - `_accrueUser` line 472: accruedRewards += supplierDelta
 *     (delta = supplierDelta, non-negative)
 *   - `claimRewards`  line 359: accruedRewards = 0
 *     (delta = -oldVal, balanced by `totalClaimed += oldVal` one line
 *      earlier; net effect on the invariant LHS is zero).
 */
hook Sstore userRewardTrackers[KEY address token][KEY address user].accruedRewards uint256 newVal (uint256 oldVal) STORAGE {
    sumAccruedPerToken[token] = sumAccruedPerToken[token] + newVal - oldVal;
}

/* ----- Helper: read totalClaimed and balanceAccounted for `token`. */
function getTotalClaimed(address token) returns uint256 {
    uint256 a; uint256 b; uint256 c; uint256 d; uint256 e;
    a, b, c, d, e = rewardTrackers(token);
    return e;
}

function getBalanceAccounted(address token) returns uint256 {
    uint256 a; uint256 b; uint256 c; uint256 d; uint256 e;
    a, b, c, d, e = rewardTrackers(token);
    return c;
}

/* ----- ICR-1 (intent conservation rule, headline form) -----
 *
 * For any method call, if the pre-state satisfies the conservation
 * inequality with sumAccruedPerToken tracking the per-user accrued
 * sum, the post-state continues to satisfy it.
 *
 * This is the inductive single-step form discussed in the spec
 * header. Combined with the initial-state axiom on the ghost
 * (sumAccruedPerToken[t] = 0 at zero), induction gives the trace
 * statement.
 *
 * Solver realities (acknowledged): the `_calculateHandout = CONSTANT`
 * summary picks one `tokensToHandout` per rule. balanceAccounted
 * grows by that amount. The per-user `supplierDelta` is
 * `mulDiv(balanceOf(user), deltaIndex, 10^decimals * SCALAR)`
 * where `deltaIndex = mulDiv(tokensToHandout, ...)`. The sum-bound
 * `sum_users supplierDelta <= tokensToHandout` lives in the Rocq
 * proof; the SMT layer would need to reason across an unbounded
 * user set. Per the spec header, we ship the weaker form below.
 */
rule rewardConservationInductive(method f)
    filtered {
        // Per SV10/11/12, upgrade slots are out of scope.
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;

    // Pre-state: conservation holds.
    mathint sumBefore     = sumAccruedPerToken[token];
    uint256 claimedBefore = getTotalClaimed(token);
    uint256 baBefore      = getBalanceAccounted(token);

    require sumBefore + to_mathint(claimedBefore) <= to_mathint(baBefore);

    f(e, args);

    mathint sumAfter      = sumAccruedPerToken[token];
    uint256 claimedAfter  = getTotalClaimed(token);
    uint256 baAfter       = getBalanceAccounted(token);

    assert sumAfter + to_mathint(claimedAfter) <= to_mathint(baAfter),
        "rewards conservation violated by method";
}

/* ----- ICR-2 (weaker form: claimRewards preserves the ledger gap) -----
 *
 * Independent of the supplier-delta bound. `claimRewards` for one
 * token shifts the caller's accruedRewards (the `oldVal` at the
 * Sstore hook) into `totalClaimed`. The hook fires on both
 * directions: the totalClaimed update is read directly from
 * storage, the accruedRewards update is mirrored to the ghost.
 *
 * This rule does NOT depend on the `_accrueUser` rounding bound and
 * is therefore expected to close cleanly inside the solver budget.
 *
 * NOTE: claimRewards calls the `accrueRewards` modifier *before*
 * the zeroing, so a non-zero supplierDelta may be folded into
 * `accruedRewards` and then zeroed at the same call. The net effect
 * on (sumAccrued + totalClaimed) is still bounded by the
 * balanceAccounted increase in the same call.
 */
rule claimPreservesLedgerGap {
    env e;
    address token;
    address[] tokens;

    require tokens.length == 1;
    require tokens[0] == token;

    mathint sumBefore     = sumAccruedPerToken[token];
    uint256 claimedBefore = getTotalClaimed(token);
    uint256 baBefore      = getBalanceAccounted(token);

    require sumBefore + to_mathint(claimedBefore) <= to_mathint(baBefore);

    claimRewards(e, tokens);

    mathint sumAfter      = sumAccruedPerToken[token];
    uint256 claimedAfter  = getTotalClaimed(token);
    uint256 baAfter       = getBalanceAccounted(token);

    assert sumAfter + to_mathint(claimedAfter) <= to_mathint(baAfter),
        "claimRewards violated rewards conservation";
}

/* ----- ICR-3 (single-user weaker form) -----
 *
 * The strongest fall-back if the parametric quantifier over users
 * cannot be eliminated. Restrict to a single nominated user; ignore
 * the rest of the population.
 *
 * Per-user invariant: for an arbitrary `user`, the user's accrued
 * rewards plus totalClaimed never exceed balanceAccounted.
 * Mechanically: a one-user inhabitant of the ghost-sum trace.
 *
 * This *is* implied by the multi-user invariant (since
 * sumAccruedPerToken >= accruedRewards[token][user] for non-negative
 * accruedRewards), so a violation here would also violate the
 * headline form. Conversely, success here is a strict weakening.
 */
rule singleUserConservation(method f)
    filtered {
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;
    address user;

    uint256 lastIdxBefore; uint256 accruedUserBefore;
    lastIdxBefore, accruedUserBefore = userRewardTrackers(token, user);
    uint256 claimedBefore = getTotalClaimed(token);
    uint256 baBefore      = getBalanceAccounted(token);

    require to_mathint(accruedUserBefore) + to_mathint(claimedBefore)
            <= to_mathint(baBefore);

    f(e, args);

    uint256 lastIdxAfter; uint256 accruedUserAfter;
    lastIdxAfter, accruedUserAfter = userRewardTrackers(token, user);
    uint256 claimedAfter  = getTotalClaimed(token);
    uint256 baAfter       = getBalanceAccounted(token);

    assert to_mathint(accruedUserAfter) + to_mathint(claimedAfter)
           <= to_mathint(baAfter),
        "single-user rewards conservation violated";
}

/* ----- ICR-4 (parametric two-user form) -----
 *
 * Two distinct users' accrued plus totalClaimed never exceed
 * balanceAccounted. Strictly weaker than the n-user form but
 * stronger than the single-user form, and exercises the
 * ghost-sum mechanism on a finite quantifier the SMT layer can
 * close in principle.
 */
rule twoUserConservation(method f)
    filtered {
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    address token;
    address userA;
    address userB;

    require userA != userB;

    uint256 lA1; uint256 aA1; uint256 lB1; uint256 aB1;
    lA1, aA1 = userRewardTrackers(token, userA);
    lB1, aB1 = userRewardTrackers(token, userB);
    uint256 claimedBefore = getTotalClaimed(token);
    uint256 baBefore      = getBalanceAccounted(token);

    require to_mathint(aA1) + to_mathint(aB1) + to_mathint(claimedBefore)
            <= to_mathint(baBefore);

    f(e, args);

    uint256 lA2; uint256 aA2; uint256 lB2; uint256 aB2;
    lA2, aA2 = userRewardTrackers(token, userA);
    lB2, aB2 = userRewardTrackers(token, userB);
    uint256 claimedAfter  = getTotalClaimed(token);
    uint256 baAfter       = getBalanceAccounted(token);

    assert to_mathint(aA2) + to_mathint(aB2) + to_mathint(claimedAfter)
           <= to_mathint(baAfter),
        "two-user rewards conservation violated";
}
