\\ exchange_rate.gp
\\
\\ CAS-side validation of StakingVault's ERC4626 exchange-rate
\\ surface. The vault overrides `totalAssets()` to add native-asset
\\ rewards that have accrued since the last accrual point:
\\
\\   totalAssets() = totalDeposited + _currentAccountedNativeRewards()
\\
\\ which feeds into the OZ convertToShares / convertToAssets
\\ machinery. The custom contribution is the
\\ `_calculateHandout(balance, elapsed)` formula:
\\
\\   handoutPct = 1e18 - (1e18 - rewardRatio)^elapsed - 1     [D18]
\\   handout    = balance * handoutPct / 1e18
\\
\\ Note the trailing "- 1": the contract subtracts 1 to make
\\ rounding strictly conservative. We probe that subtraction.
\\
\\ Reference:
\\   contracts/staking/StakingVault.sol (_calculateHandout,
\\   _currentAccountedNativeRewards, totalAssets)
\\
\\ Invariants probed:
\\
\\   INV-1  handout(0, _) = 0  and  handout(_, 0) = 0.
\\
\\   INV-2  handout(b, t) <= b for any (b >= 0, t >= 0). The decay
\\          handoutPct is in [0, 1e18) so handout cannot exceed balance.
\\
\\   INV-3  handout is monotone non-decreasing in elapsed [t]:
\\          handout(b, t1) <= handout(b, t2) when t1 <= t2.
\\
\\   INV-4  Round-trip: convertToAssets(convertToShares(a, S, A), S, A) <= a.
\\          (OZ ERC4626 floors everywhere, so round-trips are sub-identity.)
\\
\\   INV-5  Share value is non-decreasing under reward accrual:
\\          totalAssets/supply at t2 >= totalAssets/supply at t1
\\          whenever t1 <= t2 (and no withdrawals).
\\
\\   INV-6  Half-life calibration: rewardRatio = LN_2 / halfLife implies
\\          that handout over `halfLife` seconds on balance `b` is
\\          approximately b/2 (off by the conservative "- 1" wei).

print("=== StakingVault — exchange-rate / native rewards CAS ===");
print("");

LN_2    = 693147180559945309;          \\ D18 ln(2)
FIX_ONE = 10^18;
SCALAR  = FIX_ONE;

\\ ---- handout helper, with exact rational discrete exponential ----
\\ The Solidity code uses UD60x18.powu — exact integer power, then
\\ a D18-scaled formula. We mirror this exactly.
\\
\\   handoutPct = FIX_ONE - (FIX_ONE - rewardRatio)^elapsed / FIX_ONE^(elapsed-1) - 1
\\
\\ where the powu is in D18 with the convention that
\\   ud60x18_pow(x, n) = x^n / FIX_ONE^(n-1)
\\ (each subsequent multiply divides by FIX_ONE).

ud_powu(x, n) = {
  my(acc, k);
  acc = FIX_ONE;
  for(k = 1, n, acc = (acc * x) \ FIX_ONE);
  acc;
}

handout(balance, elapsed, rewardRatio, supply) = {
  my(pct, base);
  if(balance == 0 || elapsed == 0 || supply == 0, return(0));
  base = FIX_ONE - rewardRatio;
  pct  = FIX_ONE - ud_powu(base, elapsed) - 1;   \\ "- 1" matches contract
  if(pct < 0, pct = 0);
  (balance * pct) \ FIX_ONE;
}

\\ ---- INV-1: handout(0, _) and handout(_, 0) are zero ----
print("--- INV-1: handout(0, _) = 0 and handout(_, 0) = 0 ---");
{
  rr = LN_2 \ 86400;          \\ 1-day half-life rewardRatio
  fail1 = 0;
  if(handout(0, 1000, rr, 10^21) != 0,   fail1 = 1);
  if(handout(10^20, 0, rr, 10^21) != 0,  fail1 = 1);
  if(handout(0, 0, rr, 10^21) != 0,      fail1 = 1);
  printf("  three zero-edge probes: %d failures\n", fail1);
  if(fail1 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: handout(b, t) <= b ----
print("--- INV-2: handout(b, t) <= b across sweep ---");
{
  rr = LN_2 \ 86400;
  supply = 10^21;
  fail2 = 0;
  for(b_idx = 1, 5,
    balances = [0, 1, 10^9, 10^15, 10^24];
    b = balances[b_idx];
    for(t_idx = 1, 6,
      times = [0, 1, 1000, 86400, 86400 * 7, 86400 * 365];
      t = times[t_idx];
      h = handout(b, t, rr, supply);
      if(h < 0 || h > b, fail2 = fail2 + 1);
    );
  );
  printf("  violations across 5 bal * 6 elapsed combos: %d\n", fail2);
  if(fail2 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-3: monotone in elapsed ----
print("--- INV-3: handout(b, t) non-decreasing in t ---");
{
  rr = LN_2 \ 86400;
  b = 10^21;
  supply = 10^21;
  prev = handout(b, 0, rr, supply);
  fail3 = 0;
  for(k = 1, 12,
    t = k * 3600;
    cur = handout(b, t, rr, supply);
    if(cur < prev, fail3 = fail3 + 1);
    prev = cur;
  );
  printf("  violations across 12 step increases: %d\n", fail3);
  if(fail3 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: round-trip rounding via OZ ERC4626 floor everywhere ----
\\
\\ previewDeposit(assets) = assets * supply / totalAssets    (floor)
\\ previewRedeem(shares)  = shares * totalAssets / supply    (floor)
\\
\\ Round trip: previewRedeem(previewDeposit(a)) <= a.
print("--- INV-4: convertToAssets(convertToShares(a)) <= a ---");
{
  fail4 = 0;
  for(probe = 1, 12,
    \\ Vary supply, totalAssets, and the test amount.
    supply       = 10^18 * probe;
    totalAssets  = 10^18 * (probe + 7);   \\ rate > 1
    a            = 10^17 * (probe + 3);
    shares       = (a * supply) \ totalAssets;
    a_back       = (shares * totalAssets) \ supply;
    if(a_back > a, fail4 = fail4 + 1);
  );
  printf("  violations across 12 probes: %d\n", fail4);
  if(fail4 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-5: share value is non-decreasing under reward accrual ----
print("--- INV-5: totalAssets/supply non-decreasing during reward accrual ---");
{
  rr = LN_2 \ 86400;
  totalDeposited = 10^21;
  reward_balance = 10^20;
  supply = totalDeposited;
  fail5 = 0;
  prev_rate_num = totalDeposited;
  prev_rate_den = supply;
  for(k = 1, 10,
    t = k * 3600;
    accrued = handout(reward_balance, t, rr, supply);
    new_assets = totalDeposited + accrued;
    \\ Compare rate as cross-multiply: a/b >= c/d iff a*d >= c*b.
    if(new_assets * prev_rate_den < prev_rate_num * supply, fail5 = fail5 + 1);
    prev_rate_num = new_assets;
    prev_rate_den = supply;
  );
  printf("  violations across 10 hourly steps: %d\n", fail5);
  if(fail5 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: half-life calibration sanity ----
\\
\\ Discrete compounding (1 - r)^t slightly overshoots exp(-r*t) for
\\ small r, so handout after one halfLife is fractionally above b/2.
\\ Tolerance is set to 10ppm of b — the actual error at 86400 1-second
\\ steps with r = ln(2)/86400 is ~2.8ppm.
print("--- INV-6: handout over halfLife is approximately balance / 2 ---");
{
  halfLife = 86400;
  rr = LN_2 \ halfLife;
  b = 10^24;
  supply = 10^21;
  h = handout(b, halfLife, rr, supply);
  diff = 2 * h - b;
  printf("  handout(b=1e24, halfLife=86400) = %d  (b/2 = %d)\n", h, b \ 2);
  printf("  2*handout - b = %d  (= %.4f ppm of b)\n", diff, abs(diff) * 1.0e6 / b);
  if(abs(diff) < b \ (10^5), print("  OK"), print("  FAIL"));
}
print("");

print("=== StakingVault exchange-rate CAS — done ===");
