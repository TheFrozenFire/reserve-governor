\\ lock_lifecycle.gp
\\
\\ CAS-side validation of UnstakingManager — a per-lockId time-locked
\\ withdrawal queue. Each lock is a 4-tuple:
\\
\\   Lock = {user, amount, unlockTime, claimedAt}
\\
\\ With three operations:
\\
\\   createLock(user, amount, unlockTime)    -- only vault may call
\\   cancelLock(lockId)                       -- only lock.user
\\   claimLock(lockId)                        -- anyone, once matured
\\
\\ Reference:
\\   contracts/staking/UnstakingManager.sol
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  Once claimed (claimedAt != 0), claim again reverts.
\\          Equivalently: claimedAt is monotonic 0 -> now (one-way).
\\
\\   INV-2  After cancel, the slot is zeroed -- subsequent claim
\\          observes unlockTime = 0 and reverts with NotUnlockedYet.
\\
\\   INV-3  Time-lock honoring: claim before unlockTime reverts.
\\          (Tested as: at every probed (now, unlockTime) with
\\          now < unlockTime, claim returns "revert(NotUnlockedYet)".)
\\
\\   INV-4  Default-zero slot is unclaimable: claim on a lockId that
\\          was never created reverts (unlockTime = 0).
\\
\\   INV-5  Conservation: contract's targetToken balance equals the
\\          sum of `amount` over locks where claimedAt == 0 AND
\\          unlockTime != 0. Probed via a finite event log replay.
\\
\\   INV-6  Re-cancel after cancel reverts: after cancelLock the slot
\\          is wiped; the next cancelLock observes user = 0 != msg.sender
\\          and reverts Unauthorized.

print("=== UnstakingManager — CAS invariant validation ===");
print("");

\\ ---- Solidity-faithful semantics, computed exactly ----
\\
\\ Locks are represented as 4-tuples [user, amount, unlockTime, claimedAt].
\\ A "deleted" slot is [0, 0, 0, 0].

emptyLock = [0, 0, 0, 0];

createLock(state, vault, user, amount, unlockTime, caller) = {
  my(nextId, locks, newLock);
  if(caller != vault, return(["revert", "Unauthorized"]));
  nextId = state[1];
  locks  = state[2];
  newLock = [user, amount, unlockTime, 0];
  locks  = concat(locks, [newLock]);
  ["ok", [nextId + 1, locks]];
}

cancelLock(state, lockId, caller) = {
  my(locks, lock, user);
  locks = state[2];
  if(lockId < 0 || lockId >= #locks, return(["revert", "OOB"]));
  lock = locks[lockId + 1];   \\ PARI vectors are 1-indexed
  user = lock[1];
  if(user != caller, return(["revert", "Unauthorized"]));
  if(lock[4] != 0,  return(["revert", "AlreadyClaimed"]));
  locks[lockId + 1] = emptyLock;
  ["ok", [state[1], locks]];
}

claimLock(state, lockId, now) = {
  my(locks, lock);
  locks = state[2];
  if(lockId < 0 || lockId >= #locks, return(["revert", "OOB"]));
  lock = locks[lockId + 1];
  if(!(lock[3] != 0 && lock[3] <= now), return(["revert", "NotUnlockedYet"]));
  if(lock[4] != 0,                       return(["revert", "AlreadyClaimed"]));
  locks[lockId + 1] = [lock[1], lock[2], lock[3], now];
  ["ok", [state[1], locks]];
}

\\ ---- INV-1: claim is idempotent (second claim reverts) ----
print("--- INV-1: re-claim after claim reverts AlreadyClaimed ---");
{
  vault = 100;
  s = [0, []];
  s = createLock(s, vault, 200, 1000, 50, vault)[2];   \\ lock 0: user=200, amt=1000, t=50
  r1 = claimLock(s, 0, 100);                           \\ at now=100 (>= 50)
  if(r1[1] != "ok", error("setup: first claim should succeed"));
  s = r1[2];
  r2 = claimLock(s, 0, 200);                           \\ second claim
  printf("  first claim:  %s ; second claim: %s (%s)\n", r1[1], r2[1], r2[2]);
  if(r2[1] != "revert" || r2[2] != "AlreadyClaimed", print("  FAIL"), print("  OK"));
}
print("");

\\ ---- INV-2: cancel zeroes the slot; subsequent claim reverts NotUnlockedYet ----
print("--- INV-2: claim after cancel reverts NotUnlockedYet ---");
{
  vault = 100;
  user = 200;
  s = [0, []];
  s = createLock(s, vault, user, 1000, 50, vault)[2];
  r1 = cancelLock(s, 0, user);
  if(r1[1] != "ok", error("setup: cancel should succeed"));
  s = r1[2];
  r2 = claimLock(s, 0, 9999);
  printf("  after cancel, claim:  %s (%s)\n", r2[1], r2[2]);
  if(r2[1] != "revert" || r2[2] != "NotUnlockedYet", print("  FAIL"), print("  OK"));
}
print("");

\\ ---- INV-3: time-lock honoring (claim before unlockTime reverts) ----
print("--- INV-3: claim before unlockTime reverts ---");
{
  vault = 100;
  s = [0, []];
  s = createLock(s, vault, 200, 1000, 100, vault)[2];   \\ unlockTime=100
  viol = 0;
  for(t_idx = 1, 6,
    nows = [0, 1, 50, 99, 100, 101];
    n = nows[t_idx];
    r = claimLock(s, 0, n);
    if(n < 100 && r[1] != "revert",                              viol = viol + 1);
    if(n < 100 && r[1] == "revert" && r[2] != "NotUnlockedYet",  viol = viol + 1);
    if(n >= 100 && r[1] != "ok",                                  viol = viol + 1);
  );
  printf("  violations across now in {0,1,50,99,100,101}: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: default slot is unclaimable ----
print("--- INV-4: claim on default-zero slot reverts ---");
{
  s = [0, [emptyLock]];   \\ one slot, never written via createLock
  r = claimLock(s, 0, 99999);
  printf("  claim on default slot: %s (%s)\n", r[1], r[2]);
  if(r[1] != "revert" || r[2] != "NotUnlockedYet", print("  FAIL"), print("  OK"));
}
print("");

\\ Conservation summary helper. Defined at top level (PARI doesn't
\\ allow nested function defs inside `{ }` blocks — "closure not
\\ implemented").
activeSum(state) = {
  my(locks, total, j, l);
  locks = state[2];
  total = 0;
  for(j = 1, #locks,
    l = locks[j];
    if(l[4] == 0 && l[3] != 0, total = total + l[2]);
  );
  total;
}

\\ ---- INV-5: conservation. balance = sum of active lock amounts ----
print("--- INV-5: balance = sum(amount) over (claimedAt=0 AND unlockTime!=0) ---");
{
  vault = 100;
  user1 = 201; user2 = 202; user3 = 203;
  s = [0, []];
  s = createLock(s, vault, user1, 500, 100, vault)[2];   \\ lock 0
  s = createLock(s, vault, user2, 300, 200, vault)[2];   \\ lock 1
  s = createLock(s, vault, user3, 700, 150, vault)[2];   \\ lock 2
  balance_in = 500 + 300 + 700;
  printf("  after 3 creates: balance=%d  active_sum=%d\n", balance_in, activeSum(s));
  fail5 = 0;
  if(activeSum(s) != balance_in, fail5 = 1);

  \\ claim lock 0
  s = claimLock(s, 0, 100)[2];
  balance_in = balance_in - 500;
  printf("  after claim(0):  balance=%d  active_sum=%d\n", balance_in, activeSum(s));
  if(activeSum(s) != balance_in, fail5 = 1);

  \\ cancel lock 2
  s = cancelLock(s, 2, user3)[2];
  balance_in = balance_in - 700;
  printf("  after cancel(2): balance=%d  active_sum=%d\n", balance_in, activeSum(s));
  if(activeSum(s) != balance_in, fail5 = 1);

  if(fail5 == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: re-cancel after cancel reverts ----
print("--- INV-6: re-cancel after cancel reverts Unauthorized ---");
{
  vault = 100;
  user = 200;
  s = [0, []];
  s = createLock(s, vault, user, 1000, 50, vault)[2];
  r1 = cancelLock(s, 0, user);
  if(r1[1] != "ok", error("setup: first cancel should succeed"));
  s = r1[2];
  r2 = cancelLock(s, 0, user);   \\ slot is now default-zero, user=0 != caller
  printf("  re-cancel: %s (%s)\n", r2[1], r2[2]);
  if(r2[1] != "revert" || r2[2] != "Unauthorized", print("  FAIL"), print("  OK"));
}
print("");

print("=== UnstakingManager CAS — done ===");
