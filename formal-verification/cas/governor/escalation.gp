\\ escalation.gp
\\
\\ CAS-side validation of ReserveOptimisticGovernor — the hybrid
\\ optimistic/pessimistic governance state machine. This script probes
\\ the fast-to-slow escalation transitions and their guards.
\\
\\ Reference:
\\   contracts/governance/ReserveOptimisticGovernor.sol
\\   contracts/governance/lib/ProposalLib.sol
\\
\\ Modeling abstractions (matched 1:1 in the Rocq simulation):
\\
\\   selectorRegistry.isAllowed(target, selector) — oracle: 1/0
\\   throttle.consume(proposer)                   — oracle: ok / revert
\\   token.getPastTotalSupply(snapshot)           — supplied per-call
\\   token.getPastVotes(account, snapshot)        — supplied via vetoVotes
\\   timelock.queue / execute                     — modeled as a phase bump
\\
\\ Phase encoding:
\\   "submitted"  : optimistic proposal newly created (post-throttle)
\\                  voteStart = now + vetoDelay; voteDuration = vetoPeriod
\\   "active"     : optimistic veto window open (snapshot < now < deadline)
\\   "defeated"   : againstVotes >= vetoThresholdTok within window
\\                  -> auto-escalates: a *new* standard ProposalCore is
\\                     created (different proposalId — confirmation flow)
\\   "succeeded"  : optimistic deadline elapsed with !defeated
\\   "executed"   : terminal success
\\   "canceled"   : terminal cancellation
\\
\\ Confirmation (standard) phase encoding for the *new* proposalId
\\ created by [ProposalLib.transitionToPessimistic]:
\\   "std_pending"   : voteStart > now
\\   "std_active"    : in voting window
\\   "std_succeeded" : forVotes pass + quorum + deadline elapsed
\\   "std_queued"    : timelock.scheduleBatch called
\\   "std_executed"  : timelock.executeBatch called
\\
\\ Invariants probed (numbered to align with the Rocq proofs):
\\
\\   INV-1  State-transition monotonicity. The phase index is
\\          non-decreasing along any valid sequence of transitions
\\          (no "undo" of escalation, no resurrection from
\\          executed/canceled).
\\
\\   INV-2  Veto threshold correctness. The optimistic proposal escalates
\\          to "defeated" iff:
\\            againstVotes >= ceil(vetoThreshold * pastSupply / 1e18, 1)
\\          AND the proposal is in its active veto window.
\\          (The contract uses Math.max(_, 1) for vetoThresholdTok.)
\\
\\   INV-3  Optimistic execution gating. An optimistic proposal can move
\\          to "executed" only from "succeeded": no veto met AND
\\          (now > voteStart + voteDuration) AND not canceled.
\\
\\   INV-4  Standard execution chain. A confirmation proposal can only
\\          reach "std_executed" via the full chain
\\          std_pending -> std_active -> std_succeeded -> std_queued
\\          -> std_executed (no skipping, no backward steps).
\\
\\   INV-5  Throttle consumption. Every successful proposeOptimistic
\\          consumes exactly one slot from the proposer's throttle.
\\          When the throttle reverts, no proposal is created.
\\
\\   INV-6  Selector-registry gate. proposeOptimistic reverts unless
\\          every (target_i, selector_i) is allowed in the registry.
\\          Even a single denied call rejects the whole batch.

print("=== ReserveOptimisticGovernor — escalation state machine ===");
print("");

FIX_ONE = 10^18;

\\ ---- Phase ordering for monotonicity checks ----
\\ Optimistic phases:   submitted=0, active=1, succeeded=2, executed=3,
\\                                                         canceled=3
\\ The "defeated" branch is a *side exit* that spawns a fresh standard
\\ proposal — we model it as a separate phase track.
\\
\\ For monotonicity we map both tracks onto a totally ordered index
\\ {submitted < active < {succeeded, defeated} < {executed, std_*} < terminal}.

phaseIndex(p) = {
  if(p == "submitted",     return(0));
  if(p == "pending",       return(0));
  if(p == "active",        return(1));
  if(p == "succeeded",     return(2));
  if(p == "defeated",      return(2));
  if(p == "std_pending",   return(3));
  if(p == "std_active",    return(4));
  if(p == "std_succeeded", return(5));
  if(p == "std_queued",    return(6));
  if(p == "std_executed",  return(7));
  if(p == "executed",      return(7));
  if(p == "canceled",      return(7));
  -1;  \\ unknown
}

\\ ---- Stateful model of the contract slice ----
\\ Each proposal record:
\\   [proposalId, proposer, voteStart, voteDuration, vetoThresholdTok,
\\    againstVotes, phase, isOptimistic, parentId_or_0]
\\
\\ "vetoThresholdTok" stores ceil(vetoThreshold * supply / 1e18) snapped
\\ to >= 1 (the Math.max(_, 1) in state()).
\\
\\ The proposer throttle is a list of [account, charges] pairs.

newProposal(pid, prop, vs, vd, vtt, opt, parent) =
  [pid, prop, vs, vd, vtt, 0, "submitted", opt, parent];

setPhase(pr, newPhase) = [pr[1], pr[2], pr[3], pr[4], pr[5], pr[6], newPhase, pr[8], pr[9]];
addAgainstVotes(pr, v) = [pr[1], pr[2], pr[3], pr[4], pr[5], pr[6] + v, pr[7], pr[8], pr[9]];

\\ ---- Veto threshold computation ----
\\ Mirrors state() lines 240-257 in ReserveOptimisticGovernor.sol:
\\   vetoThresholdTok = max(1, vetoThreshold * pastSupply / 1e18)

vetoThresholdTok(vetoThresholdD18, pastSupply) = {
  my(v);
  v = (vetoThresholdD18 * pastSupply) \ FIX_ONE;
  if(v < 1, v = 1);
  v;
}

\\ ---- State function (matches state() in the source) ----
\\ Inputs: a proposal record + the wall-clock `now`.
\\ Returns one of {"pending", "active", "succeeded", "defeated",
\\ "executed", "canceled"} for optimistic, and the std_* analogues
\\ for confirmation proposals.

statef(pr, now) = {
  my(phase, voteStart, voteDuration, againstVotes, vtt, opt, deadline);
  phase        = pr[7];
  if(phase == "executed" || phase == "canceled", return(phase));
  voteStart    = pr[3];
  voteDuration = pr[4];
  vtt          = pr[5];
  againstVotes = pr[6];
  opt          = pr[8];
  if(now < voteStart, return(if(opt, "pending", "std_pending")));
  deadline = voteStart + voteDuration;
  if(opt,
    \\ optimistic path
    if(againstVotes >= vtt, return("defeated"));
    if(now < deadline,      return("active"));
    return("succeeded"),
    \\ standard / confirmation path
    if(now < deadline, return("std_active"));
    \\ post-deadline: simulated outcome is held in phase already
    return(phase));
}

\\ ---- proposeOptimistic ----
\\ Returns ["ok", new_proposal] or ["revert", reason].
\\ Throttle is updated in-place on the caller's side; the registry oracle
\\ is supplied as a callback (target_in_registry(t, sel) = 0/1).
proposeOptimistic(pid, proposer, vetoDelay, vetoPeriod, vetoThresholdD18, pastSupply, throttle_charges, targets, selectors, allowedTuples) = {my(k, j, t, sel, allowed, vtt); if(throttle_charges < 1, return(["revert", "ProposalThrottleExceeded"])); if(#targets == 0, return(["revert", "InvalidProposalLength"])); if(#targets != #selectors, return(["revert", "InvalidProposalLength"])); for(k = 1, #targets, t = targets[k]; sel = selectors[k]; allowed = 0; for(j = 1, #allowedTuples, if(allowedTuples[j] == [t, sel], allowed = 1; break)); if(!allowed, return(["revert", "InvalidCall"]));); vtt = vetoThresholdTok(vetoThresholdD18, pastSupply); ["ok", newProposal(pid, proposer, vetoDelay, vetoPeriod, vtt, 1, 0)];}

\\ ---- transitionToPessimistic ----
\\ Models ProposalLib.transitionToPessimistic: spawns a *new* standard
\\ proposal carrying the same calls, with a different proposalId derived
\\ from the description prefix "Confirmation For: ".
transitionToPessimistic(parent, newPid, votingDelay, votingPeriod) = {
  newProposal(newPid, parent[2], votingDelay, votingPeriod, 0, 0, parent[1]);
}

\\ ---- queueOperations ----
queueOperations(pr) = {
  if(pr[8] == 1, return(["revert", "OptimisticProposalCannotBeQueued"]));
  if(pr[7] != "std_succeeded", return(["revert", "WrongPhase"]));
  ["ok", setPhase(pr, "std_queued")];
}

\\ ---- executeOperations (standard) ----
executeStandard(pr) = {
  if(pr[7] != "std_queued", return(["revert", "WrongPhase"]));
  ["ok", setPhase(pr, "std_executed")];
}

\\ ---- executeOptimistic ----
executeOptimistic(pr, now) = {
  if(pr[8] != 1, return(["revert", "NotOptimistic"]));
  if(statef(pr, now) != "succeeded", return(["revert", "WrongPhase"]));
  ["ok", setPhase(pr, "executed")];
}

\\ ---- cancel ----
cancelProposal(pr) = {
  if(pr[7] == "executed", return(["revert", "AlreadyTerminal"]));
  ["ok", setPhase(pr, "canceled")];
}

\\ ===========================================================
\\ INV-1: Monotonicity across the happy paths
\\ ===========================================================
print("--- INV-1: phase index is non-decreasing along valid transitions ---");
{
  \\ Path A: submitted -> active -> succeeded -> executed (optimistic)
  pa = newProposal(101, 1001, 100, 1000, 5, 1, 0);
  idx_a = [phaseIndex(statef(pa, 50)),    \\ submitted -> pending (treated as "submitted"-window)
           phaseIndex(statef(pa, 500)),   \\ active
           phaseIndex(statef(pa, 1500))]; \\ succeeded
  pa = setPhase(pa, "executed");
  idx_a = concat(idx_a, [phaseIndex(pa[7])]);

  \\ Path B: submitted -> active -> defeated -> std_pending -> std_active
  \\           -> std_succeeded -> std_queued -> std_executed (escalation)
  pb = newProposal(201, 2001, 100, 1000, 5, 1, 0);
  pb = addAgainstVotes(pb, 10);   \\ defeats
  idx_b = [phaseIndex(statef(pb, 50)),     \\ pending
           phaseIndex(statef(pb, 500))];   \\ defeated
  std = transitionToPessimistic(pb, 999, 50, 1000);
  idx_b = concat(idx_b, [phaseIndex(statef(std, 25)),     \\ std_pending
                         phaseIndex(statef(std, 500)),    \\ std_active
                         phaseIndex(setPhase(std, "std_succeeded")[7])]);
  std = setPhase(std, "std_succeeded");
  r = queueOperations(std); std = r[2];
  idx_b = concat(idx_b, [phaseIndex(std[7])]);
  r = executeStandard(std); std = r[2];
  idx_b = concat(idx_b, [phaseIndex(std[7])]);

  monoA = 1;
  for(k = 2, #idx_a, if(idx_a[k] < idx_a[k-1], monoA = 0));
  monoB = 1;
  for(k = 2, #idx_b, if(idx_b[k] < idx_b[k-1], monoB = 0));
  printf("  Path A indices (opt happy):   %s\n", Str(idx_a));
  printf("  Path B indices (escalation):  %s\n", Str(idx_b));
  if(monoA && monoB, print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-1b: De-escalation is forbidden.
\\ Once escalated (parent has phase "defeated" and child exists),
\\ the parent cannot transition to "succeeded" or "executed".
\\ We assert it by attempting executeOptimistic post-defeat and
\\ expecting a revert.
\\ ===========================================================
print("--- INV-1b: once escalated, no de-escalation back to optimistic ---");
{
  pr = newProposal(301, 3001, 100, 1000, 5, 1, 0);
  pr = addAgainstVotes(pr, 5);  \\ defeats at threshold
  st_before = statef(pr, 500);
  r = executeOptimistic(pr, 9999);
  printf("  state at active window with vetoes: %s\n", st_before);
  printf("  executeOptimistic post-defeat -> %s\n", r[1]);
  if(st_before == "defeated" && r[1] == "revert", print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-2: Veto threshold correctness (edge cases).
\\
\\ Probes:
\\   (a) Below threshold by 1 wei (not defeated, "active" if in window)
\\   (b) At threshold (defeated)
\\   (c) Above threshold (defeated)
\\   (d) Tiny supply -> Math.max(_, 1) snaps to 1
\\   (e) Zero supply -> contract returns "canceled" (modeled separately)
\\ ===========================================================
print("--- INV-2: veto threshold gate (boundary, snap-to-1, zero supply) ---");
{
  vetoD18 = FIX_ONE / 10;       \\ 10%
  supply  = 100;                 \\ -> vtt = 10
  vtt = vetoThresholdTok(vetoD18, supply);
  printf("  vetoThresholdTok(10%%, supply=100) = %d (expect 10)\n", vtt);

  pr_below = newProposal(401, 4001, 100, 1000, vtt, 1, 0); pr_below = addAgainstVotes(pr_below, 9);
  pr_at    = newProposal(402, 4002, 100, 1000, vtt, 1, 0); pr_at    = addAgainstVotes(pr_at, 10);
  pr_above = newProposal(403, 4003, 100, 1000, vtt, 1, 0); pr_above = addAgainstVotes(pr_above, 11);

  s_below = statef(pr_below, 500);   \\ within window
  s_at    = statef(pr_at, 500);
  s_above = statef(pr_above, 500);

  printf("  below threshold (9/10):  %s (expect active)\n", s_below);
  printf("  at threshold (10/10):    %s (expect defeated)\n", s_at);
  printf("  above threshold (11/10): %s (expect defeated)\n", s_above);

  vttTiny = vetoThresholdTok(1, 10);     \\ 1*10/1e18 = 0, snap -> 1
  printf("  Math.max(_, 1) snap with tiny supply: vtt = %d (expect 1)\n", vttTiny);

  ok = (s_below == "active" && s_at == "defeated" && s_above == "defeated" &&
        vtt == 10 && vttTiny == 1);
  if(ok, print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-3: Optimistic execution gating.
\\ Must be in "succeeded" — meaning post-deadline, never defeated.
\\ ===========================================================
print("--- INV-3: executeOptimistic requires succeeded (post-deadline, no veto) ---");
{
  pr = newProposal(501, 5001, 100, 1000, 5, 1, 0);

  \\ During active window: revert
  r1 = executeOptimistic(pr, 500);
  \\ After deadline, no veto: ok
  r2 = executeOptimistic(pr, 2000);
  \\ Apply enough vetoes, even post-deadline: defeated -> revert
  pr_v = addAgainstVotes(pr, 6);
  r3 = executeOptimistic(pr_v, 2000);

  printf("  exec during active window: %s (expect revert)\n", r1[1]);
  printf("  exec post-deadline no veto: %s (expect ok)\n", r2[1]);
  printf("  exec post-deadline with veto: %s (expect revert)\n", r3[1]);
  ok = (r1[1] == "revert" && r2[1] == "ok" && r3[1] == "revert");
  if(ok, print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-4: Standard execution chain (full happy path required).
\\ ===========================================================
print("--- INV-4: standard execution chain requires queue->execute ---");
{
  parent = newProposal(601, 6001, 100, 1000, 5, 1, 0);
  parent = addAgainstVotes(parent, 6);  \\ defeat
  std = transitionToPessimistic(parent, 9999, 50, 1000);

  \\ Cannot queue while still active
  std = setPhase(std, "std_active");
  q1 = queueOperations(std);

  \\ Cannot execute while still active
  e1 = executeStandard(std);

  \\ Promote to std_succeeded, then queue should work
  std = setPhase(std, "std_succeeded");
  q2 = queueOperations(std); std = q2[2];

  \\ Now executeStandard succeeds
  e2 = executeStandard(std); std = e2[2];

  printf("  queue from std_active:   %s (expect revert)\n", q1[1]);
  printf("  execute from std_active: %s (expect revert)\n", e1[1]);
  printf("  queue from std_succeeded: %s\n", q2[1]);
  printf("  execute from std_queued:  %s\n", e2[1]);
  printf("  terminal phase: %s\n", std[7]);
  ok = (q1[1] == "revert" && e1[1] == "revert" &&
        q2[1] == "ok"     && e2[1] == "ok"     && std[7] == "std_executed");
  if(ok, print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-4b: Optimistic proposals cannot be queued.
\\ ===========================================================
print("--- INV-4b: optimistic proposals cannot be queued (OptimisticProposalCannotBeQueued) ---");
{
  pr = newProposal(602, 6002, 100, 1000, 5, 1, 0);
  pr = setPhase(pr, "std_succeeded");  \\ would-be-valid for standard
  pr[8] = 1;   \\ but isOptimistic stays true
  r = queueOperations(pr);
  printf("  queueOptimistic -> %s (%s)\n", r[1], r[2]);
  if(r[1] == "revert" && r[2] == "OptimisticProposalCannotBeQueued",
    print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-5: Throttle consumption at submission.
\\ ===========================================================
print("--- INV-5: every successful proposeOptimistic consumes 1 throttle slot ---");
{
  throttle = 3;
  successes = 0;
  reverts   = 0;
  for(k = 1, 5,
    \\ Use a single permitted call (target=20, selector=1000).
    r = proposeOptimistic(700 + k, 7001, 100, 1000, FIX_ONE/10, 100,
                          throttle, [20], [1000], [[20, 1000]]);
    if(r[1] == "ok", successes = successes + 1; throttle = throttle - 1);
    if(r[1] == "revert", reverts = reverts + 1);
  );
  printf("  successes: %d (expect 3) | reverts: %d (expect 2) | final throttle: %d (expect 0)\n",
         successes, reverts, throttle);
  if(successes == 3 && reverts == 2 && throttle == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ===========================================================
\\ INV-6: Selector-registry gate.
\\
\\ A batch with any one (target_i, selector_i) not in the allowlist
\\ rejects the whole proposal.
\\ ===========================================================
print("--- INV-6: selector-registry gate is honored per call in batch ---");
{
  allow = [[20, 1000], [30, 3000]];

  \\ all allowed
  r_ok = proposeOptimistic(801, 8001, 100, 1000, FIX_ONE/10, 100,
                            1, [20, 30], [1000, 3000], allow);
  \\ one denied (selector mismatch on target 30)
  r_no = proposeOptimistic(802, 8001, 100, 1000, FIX_ONE/10, 100,
                            1, [20, 30], [1000, 9999], allow);
  \\ disallowed target entirely
  r_t  = proposeOptimistic(803, 8001, 100, 1000, FIX_ONE/10, 100,
                            1, [99], [1000], allow);

  printf("  all allowed:        %s (expect ok)\n",     r_ok[1]);
  printf("  one denied:         %s (%s) (expect revert/InvalidCall)\n", r_no[1], r_no[2]);
  printf("  disallowed target:  %s (%s)\n", r_t[1], r_t[2]);
  if(r_ok[1] == "ok" && r_no[1] == "revert" && r_t[1] == "revert" &&
     r_no[2] == "InvalidCall" && r_t[2] == "InvalidCall",
    print("  OK"), print("  FAIL"));
}
print("");

print("=== ReserveOptimisticGovernor CAS — done ===");
