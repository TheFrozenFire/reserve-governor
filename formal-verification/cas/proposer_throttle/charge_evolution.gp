\\ charge_evolution.gp
\\
\\ CAS-side validation of ProposerThrottle (contracts/governance/lib/
\\ ThrottleLib.sol) — a per-account, D18-normalized charge accumulator
\\ with a 12-hour full-recovery period and an integer slot count of
\\ `capacity` proposals per account per 12h.
\\
\\ Reference:
\\   contracts/governance/lib/ThrottleLib.sol
\\   contracts/utils/Constants.sol (PROPOSAL_THROTTLE_PERIOD = 12 hours)
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  proposalsAvailable(t, account, now) <= capacity
\\          (cap holds across all (now, lastUpdated, currentCharge) probes)
\\
\\   INV-2  After consumeProposalCharge succeeds at time [now]:
\\            t'.lastUpdated  = now
\\            t'.currentCharge = old_charge - (1e18 \ capacity)
\\          where old_charge is the capped read-side charge at [now].
\\
\\   INV-3  Refill linearity in the uncapped regime:
\\          charge(now1) - charge(now0)
\\            = (now1 - now0) * 1e18 \ PROPOSAL_THROTTLE_PERIOD
\\          whenever the accumulator never reaches the 1e18 ceiling
\\          across [now0, now1].
\\
\\   INV-4  Full-recovery time: starting from currentCharge = 0,
\\          after PROPOSAL_THROTTLE_PERIOD seconds the read-side
\\          charge equals exactly 1e18 (i.e. one full capacity refill).
\\
\\   INV-5  Consumption with proposalsAvailable < 1 reverts. (Tested
\\          as: probe returns ["revert"] vs ["ok", ...].)
\\
\\   INV-6  Per-consume rounding leak: with integer division on
\\          (1e18 \ capacity), each consume removes `floor(1e18/capacity)`
\\          rather than `1e18/capacity`. The discarded remainder must
\\          satisfy 0 <= leak < capacity per consume.
\\
\\ Overflow analysis:
\\   The dangerous product is (elapsed * 1e18). uint256 = 2^256-1
\\   accommodates elapsed up to ~10^59 seconds — many orders of magnitude
\\   above any plausible block.timestamp horizon. No overflow risk.

print("=== ProposerThrottle (ThrottleLib) — CAS invariant validation ===");
print("");

PROPOSAL_THROTTLE_PERIOD = 12 * 3600;  \\ 12 hours, seconds
FIX_ONE                   = 10^18;
UINT256_MAX               = 2^256 - 1;

\\ ---- Solidity-faithful read model ----
\\
\\ _getProposalsAvailable(throttle, account) computes
\\   elapsed = now - throttle.lastUpdated
\\   charge  = throttle.currentCharge + (elapsed * 1e18) \ PERIOD
\\   if charge > 1e18: charge = 1e18
\\   proposalsAvailable = (capacity * charge) \ 1e18

readCharge(currentCharge, lastUpdated, now) = {
  my(elapsed, c);
  elapsed = now - lastUpdated;
  c = currentCharge + (elapsed * FIX_ONE) \ PROPOSAL_THROTTLE_PERIOD;
  if(c > FIX_ONE, c = FIX_ONE);
  c;
}

proposalsAvailable(capacity, currentCharge, lastUpdated, now) = {
  my(c);
  c = readCharge(currentCharge, lastUpdated, now);
  (capacity * c) \ FIX_ONE;
}

\\ consumeProposalCharge returns ["revert"] if proposalsAvailable < 1,
\\ else ["ok", newCurrentCharge, newLastUpdated].
consume(capacity, currentCharge, lastUpdated, now) = {
  my(c, avail, slot);
  c = readCharge(currentCharge, lastUpdated, now);
  avail = (capacity * c) \ FIX_ONE;
  if(avail < 1, return(["revert"]));
  slot = FIX_ONE \ capacity;   \\ <-- integer division: INV-6 leak source
  ["ok", c - slot, now];
}

\\ ---- INV-1: proposalsAvailable <= capacity, sweep ----
print("--- INV-1: proposalsAvailable <= capacity ---");
viol_inv1 = 0;
{
  caps = [1, 2, 3, 5, 7, 10, 100];
  ts_offsets = [0, 1, 100, 3599, 3600, 7199, 43199, 43200, 43201, 86400, 10^9];
  charges = [0, 1, FIX_ONE \ 3, FIX_ONE \ 2, FIX_ONE - 1, FIX_ONE];
  for(ci = 1, length(caps),
    capacity = caps[ci];
    for(ti = 1, length(ts_offsets),
      now = ts_offsets[ti];
      for(chi = 1, length(charges),
        cc = charges[chi];
        a = proposalsAvailable(capacity, cc, 0, now);
        if(a > capacity, viol_inv1 = viol_inv1 + 1);
      );
    );
  );
}
{ printf("  violations across %d cap*ts*charge combos: %d\n", 7 * 11 * 6, viol_inv1); }
if(viol_inv1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-2: consume sets lastUpdated:=now and currentCharge:=charge-slot ----
print("--- INV-2: consume's storage delta is exact ---");
viol_inv2 = 0;
{
  for(ci = 1, length(caps),
    capacity = caps[ci];
    \\ Use a state with enough charge that consume succeeds.
    cc0 = FIX_ONE;       \\ full
    lu0 = 0;
    now = 5000;
    res = consume(capacity, cc0, lu0, now);
    if(res[1] != "ok", viol_inv2 = viol_inv2 + 1; next);
    cc1 = res[2]; lu1 = res[3];
    if(lu1 != now, viol_inv2 = viol_inv2 + 1);
    \\ Expected new charge: read-side charge at now minus floor(1e18/capacity)
    c_read = readCharge(cc0, lu0, now);
    expected = c_read - (FIX_ONE \ capacity);
    if(cc1 != expected, viol_inv2 = viol_inv2 + 1);
  );
}
printf("  violations across %d capacities: %d\n", length(caps), viol_inv2);
if(viol_inv2 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-3: uncapped refill linearity ----
print("--- INV-3: charge refills linearly while < 1e18 ---");
viol_inv3 = 0;
{
  cc0 = 0;
  lu0 = 0;
  \\ A step that stays under 1e18: delta = PERIOD/4 -> charge = 0.25e18.
  step = PROPOSAL_THROTTLE_PERIOD \ 4;
  expected_per_step = (step * FIX_ONE) \ PROPOSAL_THROTTLE_PERIOD;
  prev = cc0;
  for(k = 1, 3,
    now = k * step;
    c = readCharge(cc0, lu0, now);
    if(c - prev != expected_per_step, viol_inv3 = viol_inv3 + 1);
    prev = c;
  );
  printf("  expected refill per quarter-period: %d (= 0.25e18 = %d)\n", expected_per_step, FIX_ONE \ 4);
}
if(viol_inv3 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-4: full recovery in exactly PERIOD seconds ----
print("--- INV-4: charge(0) over PERIOD seconds = 1e18 ---");
viol_inv4 = 0;
{
  c_at_period = readCharge(0, 0, PROPOSAL_THROTTLE_PERIOD);
  printf("  readCharge(0, 0, PERIOD) = %d  (expected %d)\n", c_at_period, FIX_ONE);
  if(c_at_period != FIX_ONE, viol_inv4 = viol_inv4 + 1);
  \\ One second short should leave us strictly under 1e18.
  c_short = readCharge(0, 0, PROPOSAL_THROTTLE_PERIOD - 1);
  if(c_short >= FIX_ONE, viol_inv4 = viol_inv4 + 1);
  \\ One second long is still capped to 1e18.
  c_over = readCharge(0, 0, PROPOSAL_THROTTLE_PERIOD + 1);
  if(c_over != FIX_ONE, viol_inv4 = viol_inv4 + 1);
}
if(viol_inv4 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-5: consume reverts iff proposalsAvailable < 1 ----
print("--- INV-5: consume reverts iff no proposal available ---");
viol_inv5 = 0;
{
  capacity = 5;
  \\ Just below the floor for "1 proposal available": charge must hit
  \\ 1e18 / capacity for proposalsAvailable to reach 1.
  threshold = FIX_ONE \ capacity;
  res_below = consume(capacity, threshold - 1, 0, 0);  \\ no elapsed time
  res_at    = consume(capacity, threshold,     0, 0);
  if(res_below[1] != "revert", viol_inv5 = viol_inv5 + 1);
  if(res_at[1]    != "ok",     viol_inv5 = viol_inv5 + 1);
  printf("  at threshold-1: %s ; at threshold: %s\n", res_below[1], res_at[1]);
}
if(viol_inv5 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-6: per-consume rounding leak is bounded ----
print("--- INV-6: rounding leak per consume = 1e18 mod capacity ---");
viol_inv6 = 0;
{
  for(ci = 1, length(caps),
    capacity = caps[ci];
    slot_floor = FIX_ONE \ capacity;
    leak = FIX_ONE - slot_floor * capacity;   \\ = 1e18 mod capacity
    if(leak < 0 || leak >= capacity, viol_inv6 = viol_inv6 + 1);
    printf("  capacity=%-4d  slot=%-22d  leak/consume=%d (%.6f%% of slot)\n", capacity, slot_floor, leak, if(slot_floor > 0, leak * 100.0 / slot_floor, 0.0));
  );
}
if(viol_inv6 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- Overflow witness ----
print("--- Overflow: (elapsed * 1e18) for plausible block.timestamp ---");
{
  dt_max = 2^63;
  acc = dt_max * FIX_ONE;
  printf("  (2^63) * 1e18 = %d   (fits in uint256? %s)\n", acc, if(acc < 2^256, "yes", "no"));
}
print("");

print("=== ProposerThrottle CAS — done ===");
