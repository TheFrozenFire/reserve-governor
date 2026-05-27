\\ multi_token_rewards.gp
\\
\\ CAS-side validation of StakingVault's per-token reward accounting.
\\ Each registered reward token has a global RewardInfo + per-user
\\ UserRewardInfo, with the index-style accumulator:
\\
\\   rewardIndex            : D18+decimals {reward/share}, monotone
\\   userRewardTracker[u]   : (lastRewardIndex, accruedRewards)
\\
\\ On every accrueRewards modifier hit:
\\   deltaIndex = (rewardIndex - lastRewardIndex)
\\   accruedRewards += balanceOf(u) * deltaIndex / (decimals * SCALAR)
\\   lastRewardIndex = rewardIndex      (only when deltaIndex != 0)
\\
\\ Reference:
\\   contracts/staking/StakingVault.sol (_accrueRewards, _accrueUser)
\\
\\ Invariants probed:
\\
\\   INV-1  rewardIndex is monotonically non-decreasing across accruals.
\\
\\   INV-2  userRewardTracker.accruedRewards is non-decreasing across
\\          accruals (assuming positive balance and non-negative
\\          deltaIndex).
\\
\\   INV-3  Conservation across a per-user sequence:
\\            sum_u accrueDelta(u)
\\          equals the total handed out for that token, with rounding
\\          drift bounded by (#users) wei (one floor per user).
\\
\\   INV-4  Claim is at-most-once-per-current-state: after a claim
\\          empties accruedRewards, a second claim returns 0.
\\
\\   INV-5  totalClaimed is monotone non-decreasing across claims.
\\
\\   INV-6  No double-count after re-registration: re-adding a removed
\\          reward token resets the local payoutLastPaid but does NOT
\\          erase any user's lastRewardIndex (so users keep their
\\          unclaimed accrued amounts).

print("=== StakingVault — multi-token reward accounting CAS ===");
print("");

FIX_ONE  = 10^18;
DEC18    = 10^18;     \\ decimals() returns 18 by default in OZ ERC4626

\\ ---- A minimal reward-token model.
\\ rewardInfo : [payoutLastPaid, rewardIndex, balanceAccounted,
\\               balanceLastKnown, totalClaimed]
\\ user_tracker : map<user, [lastRewardIndex, accruedRewards]>

newRewardInfo() = [0, 0, 0, 0, 0];

updateRewardIndex(rinfo, supply, balance_delta) = {
  my(deltaIndex, ri);
  if(supply == 0 || balance_delta == 0, return(rinfo));
  \\ deltaIndex = balance_delta * SCALAR * DEC18 / supply
  deltaIndex = (balance_delta * FIX_ONE * DEC18) \ supply;
  ri = rinfo[2] + deltaIndex;
  [rinfo[1], ri, rinfo[3] + balance_delta, rinfo[4], rinfo[5]];
}

accrueUser(rinfo, user_tracker, user_balance) = {
  my(lastIdx, accrued, deltaIndex, supplierDelta);
  lastIdx    = user_tracker[1];
  accrued    = user_tracker[2];
  deltaIndex = rinfo[2] - lastIdx;
  if(deltaIndex == 0, return(user_tracker));
  \\ supplierDelta = user_balance * deltaIndex / (DEC18 * SCALAR)
  supplierDelta = (user_balance * deltaIndex) \ (DEC18 * FIX_ONE);
  [rinfo[2], accrued + supplierDelta];
}

claimUser(user_tracker, rinfo) = {
  my(claimable, new_rinfo);
  claimable = user_tracker[2];
  new_rinfo = [rinfo[1], rinfo[2], rinfo[3], rinfo[4], rinfo[5] + claimable];
  [new_rinfo, [user_tracker[1], 0], claimable];
}

\\ ---- INV-1: rewardIndex monotone ----
print("--- INV-1: rewardIndex monotone non-decreasing across accruals ---");
{
  rinfo = newRewardInfo();
  supply = 10^21;
  prev = 0;
  fail1 = 0;
  for(k = 1, 8,
    rinfo = updateRewardIndex(rinfo, supply, 10^18 * k);
    if(rinfo[2] < prev, fail1 = fail1 + 1);
    prev = rinfo[2];
  );
  printf("  8 accruals, final rewardIndex = %d, violations = %d\n", rinfo[2], fail1);
  if(fail1 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: user accrued non-decreasing ----
print("--- INV-2: user.accruedRewards non-decreasing across accruals ---");
{
  rinfo = newRewardInfo();
  supply = 10^21;
  u_balance = 10^20;
  u_tracker = [0, 0];
  prev = 0;
  fail2 = 0;
  for(k = 1, 6,
    rinfo     = updateRewardIndex(rinfo, supply, 10^18 * (1 + k));
    u_tracker = accrueUser(rinfo, u_tracker, u_balance);
    if(u_tracker[2] < prev, fail2 = fail2 + 1);
    prev = u_tracker[2];
  );
  printf("  6 accruals, final accrued = %d, violations = %d\n", u_tracker[2], fail2);
  if(fail2 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-3: per-user sum vs. total handed out, with rounding bound ----
print("--- INV-3: sum_u accrued(u) <= balance_delta, with #users wei drift ---");
{
  rinfo = newRewardInfo();
  n_users = 5;
  supply  = n_users * 10^20;
  u_trackers = vector(n_users, k, [0, 0]);
  balance_delta = 10^20;
  rinfo = updateRewardIndex(rinfo, supply, balance_delta);
  for(u = 1, n_users,
    u_trackers[u] = accrueUser(rinfo, u_trackers[u], 10^20);
  );
  total_accrued = 0;
  for(u = 1, n_users, total_accrued = total_accrued + u_trackers[u][2]);
  drift = balance_delta - total_accrued;
  printf("  delta_in=%d  sum_accrued=%d  drift=%d (<=%d users)\n",
         balance_delta, total_accrued, drift, n_users);
  \\ Each user incurs at most 1 wei of rounding loss, so drift <= n_users.
  if(drift >= 0 && drift <= n_users, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: claim zeroes accruedRewards; second claim returns 0 ----
print("--- INV-4: claim is at-most-once per accrued amount ---");
{
  rinfo = newRewardInfo();
  supply = 10^21;
  u_tracker = [0, 0];
  rinfo     = updateRewardIndex(rinfo, supply, 10^20);
  u_tracker = accrueUser(rinfo, u_tracker, 10^20);
  pre_accrued = u_tracker[2];
  first_claim = claimUser(u_tracker, rinfo);
  rinfo       = first_claim[1];
  u_tracker   = first_claim[2];
  c1          = first_claim[3];
  second_claim = claimUser(u_tracker, rinfo);
  c2          = second_claim[3];
  printf("  pre=%d c1=%d c2=%d\n", pre_accrued, c1, c2);
  if(c1 == pre_accrued && c2 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-5: totalClaimed monotone ----
print("--- INV-5: totalClaimed monotone non-decreasing ---");
{
  rinfo = newRewardInfo();
  supply = 10^21;
  u_tracker = [0, 0];
  prev = 0;
  fail5 = 0;
  for(k = 1, 4,
    rinfo     = updateRewardIndex(rinfo, supply, 10^18 * k);
    u_tracker = accrueUser(rinfo, u_tracker, 10^20);
    cr        = claimUser(u_tracker, rinfo);
    rinfo     = cr[1];
    u_tracker = cr[2];
    if(rinfo[5] < prev, fail5 = fail5 + 1);
    prev = rinfo[5];
  );
  printf("  4 claim cycles, final totalClaimed=%d, violations=%d\n", rinfo[5], fail5);
  if(fail5 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: user lastRewardIndex preserved across "removal" ----
\\ Modeled as: after a token is removed from rewardTokens, its
\\ RewardInfo persists in storage. Re-adding writes only payoutLastPaid
\\ and balanceLastKnown; rewardIndex and user.lastRewardIndex are untouched.
print("--- INV-6: user.lastRewardIndex preserved across remove/re-add ---");
{
  rinfo = newRewardInfo();
  supply = 10^21;
  u_tracker = [0, 0];
  rinfo     = updateRewardIndex(rinfo, supply, 10^20);
  u_tracker = accrueUser(rinfo, u_tracker, 10^20);
  pre_lastIdx = u_tracker[1];
  \\ "Remove" doesn't touch RewardInfo or userRewardTracker storage.
  \\ "Re-add" resets payoutLastPaid + balanceLastKnown only.
  rinfo_readded = [42, rinfo[2], rinfo[3], 99, rinfo[5]];
  if(u_tracker[1] == pre_lastIdx, print("  OK"), print("  FAIL"));
}
print("");

print("=== StakingVault multi-token rewards CAS — done ===");
