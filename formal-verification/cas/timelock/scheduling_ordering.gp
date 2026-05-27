\\ scheduling_ordering.gp
\\
\\ CAS-side validation of TimelockControllerOptimistic. The contract
\\ inherits the OZ TimelockControllerUpgradeable model:
\\
\\   operation id = keccak256(targets, values, payloads, predecessor, salt)
\\   state[id]    in {Unset, Waiting, Ready, Done}   (encoded as a
\\                                                    single uint256
\\                                                    timestamp)
\\
\\ encoded as:
\\   timestamps[id] = 0    -> Unset
\\   timestamps[id] = 1    -> Done    (the magic _DONE_TIMESTAMP)
\\   timestamps[id] > 1, > now -> Waiting
\\   timestamps[id] > 1, <= now -> Ready
\\
\\ Operations:
\\   scheduleBatch(id, delay)    -- only PROPOSER_ROLE
\\                                  requires timestamps[id] == 0 and
\\                                  delay >= minDelay; writes
\\                                  timestamps[id] = now + delay
\\   executeBatch(id)            -- only EXECUTOR_ROLE
\\                                  requires Ready (timestamps[id] != 0
\\                                  and != 1 and <= now); marks Done
\\                                  by writing timestamps[id] = 1
\\   cancel(id)                  -- only CANCELLER_ROLE
\\                                  requires Pending (Waiting or Ready);
\\                                  clears timestamps[id] = 0
\\   executeBatchBypass(id)      -- only PROPOSER_ROLE (must also hold
\\                                  EXECUTOR_ROLE for the inner exec)
\\                                  requires Unset (timestamps[id] == 0);
\\                                  sets timestamps[id] = now and then
\\                                  immediately runs executeBatch which
\\                                  transitions it to Done
\\
\\ Reference:
\\   contracts/governance/TimelockControllerOptimistic.sol
\\   node_modules/.../governance/TimelockControllerUpgradeable.sol
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  No operation executes before its executableAt timestamp:
\\          executeBatch on a Waiting operation reverts NotReady.
\\
\\   INV-2  No double execute: a second executeBatch after Done reverts
\\          NotReady (the second observes timestamps[id] = 1, neither
\\          0 nor a real future timestamp, so it's not Ready either).
\\
\\   INV-3  Cancel removes from queue: after cancel, executeBatch
\\          reverts NotReady (timestamps[id] = 0, Unset).
\\
\\   INV-4  Bypass requires PROPOSER_ROLE: caller without role reverts
\\          Unauthorized.
\\
\\   INV-5  Bypass preserves slow-path queue ordering: after
\\          scheduleBatch(A, delay); bypass(B); the queued A's
\\          executableAt is unchanged and A is still Waiting until its
\\          original maturity. Only B has transitioned Unset -> Done.
\\
\\   INV-6  Bypass cannot run on an already-scheduled op: bypass on an
\\          id with timestamps[id] != 0 reverts OperationConflict.

print("=== TimelockControllerOptimistic --- CAS invariant validation ===");
print("");

\\ ---- Solidity-faithful semantics, computed exactly ----
\\
\\ State = [timestamps_map, minDelay] where timestamps_map is a list of
\\ [id, ts] pairs. We probe with small integer ids standing in for the
\\ keccak digests.

DONE_TS = 1;

\\ ---- helpers ----

lookupTs(state, id) = {
  my(m, j);
  m = state[1];
  for(j = 1, #m,
    if(m[j][1] == id, return(m[j][2]));
  );
  0;
}

setTs(state, id, ts) = {
  my(m, j, found);
  m = state[1];
  found = 0;
  for(j = 1, #m,
    if(m[j][1] == id,
      m[j] = [id, ts];
      found = 1;
    );
  );
  if(found == 0,
    m = concat(m, [[id, ts]]);
  );
  [m, state[2]];
}

opState(state, id, now) = {
  my(t);
  t = lookupTs(state, id);
  if(t == 0,        return("Unset"));
  if(t == DONE_TS,  return("Done"));
  if(t > now,       return("Waiting"));
  "Ready";
}

\\ ---- operations ----

scheduleBatch(state, id, delay, now, hasProposer) = {
  my(minDelay);
  if(hasProposer == 0, return(["revert", "Unauthorized"]));
  if(lookupTs(state, id) != 0, return(["revert", "OperationConflict"]));
  minDelay = state[2];
  if(delay < minDelay, return(["revert", "InsufficientDelay"]));
  ["ok", setTs(state, id, now + delay)];
}

executeBatch(state, id, now, hasExecutor) = {
  my(st);
  if(hasExecutor == 0, return(["revert", "Unauthorized"]));
  st = opState(state, id, now);
  if(st != "Ready", return(["revert", "NotReady"]));
  ["ok", setTs(state, id, DONE_TS)];
}

cancel(state, id, now, hasCanceller) = {
  my(st);
  if(hasCanceller == 0, return(["revert", "Unauthorized"]));
  st = opState(state, id, now);
  if(st != "Waiting" && st != "Ready", return(["revert", "NotPending"]));
  ["ok", setTs(state, id, 0)];
}

\\ executeBatchBypass: in the production contract, the function checks
\\ that timestamps[id] == 0 (OperationConflict otherwise), then sets
\\ timestamps[id] = now, then immediately calls executeBatch which
\\ requires Ready. Since timestamps[id] = now passes the Ready check
\\ (t != 0 && t != 1 && t <= now), executeBatch then marks it Done.
\\ The combined effect: Unset -> Done in one transaction, modulo the
\\ EXECUTOR_ROLE check inside executeBatch.
executeBatchBypass(state, id, now, hasProposer, hasExecutor) = {
  my(s2, r);
  if(hasProposer == 0, return(["revert", "Unauthorized"]));
  if(lookupTs(state, id) != 0, return(["revert", "OperationConflict"]));
  s2 = setTs(state, id, now);
  r = executeBatch(s2, id, now, hasExecutor);
  r;
}

\\ ---- INV-1: no operation executes before its executableAt ----
print("--- INV-1: execute before executableAt reverts NotReady ---");
{
  s = [[], 100];   \\ empty timestamps, minDelay = 100
  s = scheduleBatch(s, 42, 200, 1000, 1)[2];   \\ scheduled at now=1000, delay=200 -> ready at 1200
  viol = 0;
  fornows = [1000, 1100, 1199, 1200, 1201];
  for(i = 1, 5,
    n = fornows[i];
    r = executeBatch(s, 42, n, 1);
    if(n < 1200 && r[1] != "revert",                  viol = viol + 1);
    if(n < 1200 && r[1] == "revert" && r[2] != "NotReady", viol = viol + 1);
    if(n >= 1200 && r[1] != "ok",                      viol = viol + 1);
  );
  printf("  violations across now in {1000,1100,1199,1200,1201}: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: no double execute ----
print("--- INV-2: re-execute after Done reverts NotReady ---");
{
  s = [[], 100];
  s = scheduleBatch(s, 7, 100, 500, 1)[2];   \\ ready at 600
  r1 = executeBatch(s, 7, 700, 1);
  if(r1[1] != "ok", error("setup: first execute should succeed"));
  s = r1[2];
  r2 = executeBatch(s, 7, 800, 1);
  printf("  first execute: %s ; second execute: %s (%s)\n", r1[1], r2[1], r2[2]);
  if(r2[1] != "revert" || r2[2] != "NotReady", print("  FAIL"), print("  OK"));
}
print("");

\\ ---- INV-3: cancel removes operation from queue ----
print("--- INV-3: execute after cancel reverts NotReady ---");
{
  s = [[], 100];
  s = scheduleBatch(s, 9, 100, 500, 1)[2];   \\ ready at 600
  r1 = cancel(s, 9, 550, 1);                  \\ cancel while Waiting
  if(r1[1] != "ok", error("setup: cancel should succeed"));
  s = r1[2];
  r2 = executeBatch(s, 9, 9999, 1);
  printf("  cancel: %s ; execute after cancel: %s (%s)\n", r1[1], r2[1], r2[2]);
  if(r2[1] != "revert" || r2[2] != "NotReady", print("  FAIL"), print("  OK"));
}
print("");

\\ ---- INV-4: bypass requires PROPOSER_ROLE ----
print("--- INV-4: bypass without PROPOSER_ROLE reverts Unauthorized ---");
{
  s = [[], 100];
  r = executeBatchBypass(s, 11, 1000, 0, 1);   \\ no PROPOSER_ROLE
  printf("  bypass (no proposer):  %s (%s)\n", r[1], r[2]);
  if(r[1] != "revert" || r[2] != "Unauthorized", print("  FAIL"), print("  OK"));
}
print("");

\\ ---- INV-5: bypass preserves slow-path queue ordering ----
print("--- INV-5: scheduleBatch(A,delay); bypass(B) leaves A unchanged and Waiting ---");
{
  s = [[], 100];
  idA = 100; idB = 200;
  delay = 500;
  nowSched = 1000;
  s = scheduleBatch(s, idA, delay, nowSched, 1)[2];   \\ A waiting until 1500
  tsA_before = lookupTs(s, idA);
  nowBypass = 1100;
  r = executeBatchBypass(s, idB, nowBypass, 1, 1);
  if(r[1] != "ok", error("setup: bypass should succeed"));
  s = r[2];
  tsA_after = lookupTs(s, idA);
  tsB_after = lookupTs(s, idB);
  printf("  A.executableAt: before=%d after=%d   B status=%s\n",
         tsA_before, tsA_after, opState(s, idB, nowBypass));
  \\ INV-5 checks: A still has same executableAt; A is still Waiting at nowBypass;
  \\               B is Done; A is not Ready until original maturity.
  fail5 = 0;
  if(tsA_before != tsA_after,                      fail5 = 1);
  if(tsA_after  != nowSched + delay,               fail5 = 1);
  if(opState(s, idA, nowBypass) != "Waiting",      fail5 = 1);
  if(opState(s, idB, nowBypass) != "Done",         fail5 = 1);
  if(opState(s, idA, nowSched + delay) != "Ready", fail5 = 1);
  \\ Attempting to execute A early (before its delay matures) reverts.
  rExecA_early = executeBatch(s, idA, nowBypass, 1);
  if(rExecA_early[1] != "revert" || rExecA_early[2] != "NotReady", fail5 = 1);
  if(fail5 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: bypass collides with already-scheduled op ----
print("--- INV-6: bypass on an already-scheduled op reverts OperationConflict ---");
{
  s = [[], 100];
  id = 77;
  s = scheduleBatch(s, id, 200, 1000, 1)[2];
  r = executeBatchBypass(s, id, 1100, 1, 1);
  printf("  bypass collide: %s (%s)\n", r[1], r[2]);
  if(r[1] != "revert" || r[2] != "OperationConflict", print("  FAIL"), print("  OK"));
}
print("");

print("=== TimelockControllerOptimistic CAS --- done ===");
