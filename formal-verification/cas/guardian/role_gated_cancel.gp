\\ role_gated_cancel.gp
\\
\\ CAS-side validation of Guardian (contracts/Guardian.sol) — a
\\ singleton AccessControlEnumerable contract that fans out to all
\\ optimistic governors as CANCELLER_ROLE and routes role-management
\\ to the timelocks they own.
\\
\\ Reference:
\\   contracts/Guardian.sol
\\
\\ Three roles, three distinct authorization rules:
\\
\\   DEFAULT_ADMIN_ROLE
\\     - admin of every role
\\     - can cancel ANY proposal (optimistic or pessimistic, defeated
\\       or not) via Guardian.cancel
\\     - can revokeOptimisticProposer on any managed governor's timelock
\\
\\   OPTIMISTIC_GUARDIAN_ROLE
\\     - can ONLY cancel a proposal that is:
\\         a) governor.isOptimistic(pid) = true
\\         b) governor.state(pid) != ProposalState.Defeated
\\     - has no role-management powers
\\
\\   OPTIMISTIC_GUARDIAN_MANAGER_ROLE
\\     - can grantOptimisticGuardian to a non-zero account
\\     - has no cancel powers, no revoke powers
\\
\\ Invariants probed (numbered to match the Rocq model):
\\
\\   INV-1  cancel(caller, pid) is authorized iff
\\            caller is admin
\\          OR
\\            caller has guardian role AND isOptimistic(pid) AND
\\            state(pid) != Defeated
\\          Probed via a truth-table sweep across role-flag combos and
\\          (isOptimistic, state) values.
\\
\\   INV-2  grantOptimisticGuardian succeeds iff
\\            caller has manager role AND account != 0.
\\          Probed against role-flag x account-value matrix.
\\
\\   INV-3  revokeOptimisticProposer succeeds iff caller has admin role
\\          AND the governor + timelock are both non-zero and have code.
\\          (Governor/timelock validity is a callee-side concern but the
\\          contract checks it explicitly in _governor / _timelock.)
\\
\\   INV-4  Role membership is monotonic under grant: after
\\            grantOptimisticGuardian(account), account is in the
\\            guardian set; no other addresses change membership.
\\
\\   INV-5  Zero-address rejection: every grant path that flows through
\\            _requireNonZero(account) reverts on account = 0. Probed
\\            for grantOptimisticGuardian.
\\
\\   INV-6  Two-tier cancel: an admin caller never sees the optimistic
\\            / defeated check, so even a Defeated pessimistic proposal
\\            is cancellable. A guardian-only caller hitting the same
\\            input reverts.

print("=== Guardian — CAS invariant validation ===");
print("");

\\ ---- Authorization decision function (model of cancel's gate) ----
\\
\\ caller_admin     : bool (caller has DEFAULT_ADMIN_ROLE)
\\ caller_guardian  : bool (caller has OPTIMISTIC_GUARDIAN_ROLE)
\\ is_optimistic    : bool (governor.isOptimistic(pid))
\\ is_defeated      : bool (governor.state(pid) == ProposalState.Defeated)
\\
\\ Returns 1 iff the contract proceeds to the inner cancel call; 0 iff
\\ it reverts at the gate (either UnauthorizedCaller or
\\ NotOptimisticProposal or DefeatedProposal).
cancel_authorized(caller_admin, caller_guardian, is_optimistic, is_defeated) = {
  if(caller_admin, return(1));
  if(!caller_guardian, return(0));
  if(!is_optimistic, return(0));
  if(is_defeated, return(0));
  1;
}

\\ ---- INV-1: full truth table for cancel authorization ----
print("--- INV-1: cancel authorization truth table ---");
viol_inv1 = 0;
{
  rows = 0;
  for(ca = 0, 1,
    for(cg = 0, 1,
      for(io = 0, 1,
        for(id = 0, 1,
          got = cancel_authorized(ca, cg, io, id);
          \\ Expected: admin always passes; guardian-only passes iff
          \\ optimistic AND not defeated; otherwise reverts.
          expected = if(ca, 1, if(cg && io && !id, 1, 0));
          if(got != expected, viol_inv1 = viol_inv1 + 1);
          rows = rows + 1;
        );
      );
    );
  );
  printf("  violations across %d (admin,guardian,optimistic,defeated) rows: %d\n", rows, viol_inv1);
}
if(viol_inv1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-2: grantOptimisticGuardian gate ----
\\
\\ caller_manager : bool (caller has OPTIMISTIC_GUARDIAN_MANAGER_ROLE)
\\ account        : address; modeled as a non-negative integer with 0
\\                  representing the zero address.
grant_authorized(caller_manager, account) = {
  if(!caller_manager, return(0));
  if(account == 0, return(0));
  1;
}

print("--- INV-2: grantOptimisticGuardian gate ---");
viol_inv2 = 0;
{
  addrs = [0, 1, 7, 100, 2^160 - 1];
  rows = 0;
  for(cm = 0, 1,
    for(ai = 1, length(addrs),
      acc = addrs[ai];
      got = grant_authorized(cm, acc);
      expected = if(cm && acc != 0, 1, 0);
      if(got != expected, viol_inv2 = viol_inv2 + 1);
      rows = rows + 1;
    );
  );
  printf("  violations across %d (manager, account) rows: %d\n", rows, viol_inv2);
}
if(viol_inv2 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-3: revokeOptimisticProposer gate ----
\\
\\ caller_admin     : bool
\\ governor_addr    : address (0 = invalid)
\\ governor_hasCode : bool (false = invalid)
\\ timelock_addr    : address
\\ timelock_hasCode : bool
revoke_authorized(caller_admin, gov_addr, gov_has_code, tl_addr, tl_has_code) = {
  if(!caller_admin, return(0));
  if(gov_addr == 0 || !gov_has_code, return(0));
  if(tl_addr == 0 || !tl_has_code, return(0));
  1;
}

print("--- INV-3: revokeOptimisticProposer gate ---");
viol_inv3 = 0;
{
  rows = 0;
  for(ca = 0, 1,
    for(ga = 0, 1,
      for(gc = 0, 1,
        for(ta = 0, 1,
          for(tc = 0, 1,
            gov = if(ga, 17, 0);
            tl  = if(ta, 23, 0);
            got = revoke_authorized(ca, gov, gc, tl, tc);
            expected = if(ca && gov != 0 && gc && tl != 0 && tc, 1, 0);
            if(got != expected, viol_inv3 = viol_inv3 + 1);
            rows = rows + 1;
          );
        );
      );
    );
  );
  printf("  violations across %d (admin,govA,govC,tlA,tlC) rows: %d\n", rows, viol_inv3);
}
if(viol_inv3 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-4: role membership is monotonic under grant ----
\\
\\ Model a guardian role set as a vector of (sorted) addresses; the
\\ grant operation inserts only if not already present, leaving every
\\ other entry untouched.
list_contains_addr(lst, x) = {
  my(n, i);
  n = length(lst);
  for(i = 1, n, if(lst[i] == x, return(1)));
  0;
}

grant_role(lst, account) = {
  if(account == 0, return(lst));
  if(list_contains_addr(lst, account), return(lst));
  concat(lst, [account]);
}

print("--- INV-4: grant_role monotone, idempotent, non-disturbing ---");
viol_inv4 = 0;
{
  starts = [[], [10], [10, 20, 30]];
  newcomers = [0, 5, 10, 99];
  rows = 0;
  for(si = 1, length(starts),
    s = starts[si];
    for(ai = 1, length(newcomers),
      acc = newcomers[ai];
      s2 = grant_role(s, acc);
      \\ Property (a): every old member stays.
      for(j = 1, length(s),
        if(!list_contains_addr(s2, s[j]), viol_inv4 = viol_inv4 + 1);
      );
      \\ Property (b): account is in s2 iff account != 0.
      if(acc == 0,
        if(s2 != s, viol_inv4 = viol_inv4 + 1)
        ,
        if(!list_contains_addr(s2, acc), viol_inv4 = viol_inv4 + 1)
      );
      \\ Property (c): no spurious additions (length grows by <= 1).
      if(length(s2) > length(s) + 1, viol_inv4 = viol_inv4 + 1);
      \\ Property (d): idempotent — a second grant is a no-op.
      s3 = grant_role(s2, acc);
      if(s3 != s2, viol_inv4 = viol_inv4 + 1);
      rows = rows + 1;
    );
  );
  printf("  violations across %d (set, account) rows: %d\n", rows, viol_inv4);
}
if(viol_inv4 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-5: zero-address rejection on grant ----
print("--- INV-5: grant rejects account=0 ---");
viol_inv5 = 0;
{
  for(cm = 0, 1,
    got = grant_authorized(cm, 0);
    if(got != 0, viol_inv5 = viol_inv5 + 1);
  );
  printf("  violations across both manager-flag values: %d\n", viol_inv5);
}
if(viol_inv5 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-6: two-tier cancel — admin bypasses optimistic check ----
print("--- INV-6: admin can cancel where guardian cannot ---");
viol_inv6 = 0;
{
  \\ Probe: a pessimistic proposal that has been Defeated.
  \\ Guardian-only must be rejected; admin must be admitted.
  cases = [
    \\ [is_optimistic, is_defeated, label]
    [0, 1, "pessimistic+defeated"],
    [0, 0, "pessimistic+live   "],
    [1, 1, "optimistic+defeated"]
  ];
  for(ci = 1, length(cases),
    io = cases[ci][1];
    id = cases[ci][2];
    lbl = cases[ci][3];
    admin_got    = cancel_authorized(1, 0, io, id);
    guardian_got = cancel_authorized(0, 1, io, id);
    if(admin_got != 1, viol_inv6 = viol_inv6 + 1);
    if(guardian_got != 0, viol_inv6 = viol_inv6 + 1);
    printf("  %s -> admin=%d guardian=%d\n", lbl, admin_got, guardian_got);
  );
}
if(viol_inv6 == 0, print("  OK"), print("  FAIL"));
print("");

print("=== Guardian CAS — done ===");
