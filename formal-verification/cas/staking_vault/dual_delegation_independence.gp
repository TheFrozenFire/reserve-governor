\\ dual_delegation_independence.gp
\\
\\ CAS-side validation of StakingVault's dual-delegation surface:
\\ the contract layers a per-account "optimistic" delegate set
\\ on top of OZ's standard ERC20Votes checkpoints. The two ledgers
\\ are independent — they both update on every transfer but neither
\\ perturbs the other.
\\
\\ Reference:
\\   contracts/staking/StakingVault.sol
\\     #L104-L105   optimisticDelegatees / optimisticDelegateCheckpoints
\\     #L499-L506   _update (transfer entry — both move)
\\     #L543-L549   _delegateOptimistic
\\     #L551-L571   _moveOptimisticDelegateVotes
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  Checkpoint independence:
\\          Changing the *optimistic* delegate ledger does not change
\\          the *standard* delegate ledger, and vice versa. Each
\\          transfer updates each ledger via its own checkpoint stack;
\\          the result of one is invariant under permuting the order
\\          of operations on the other.
\\
\\   INV-2  Conservation across transfers:
\\          _moveOptimisticDelegateVotes(from, to, amount) shifts
\\          exactly `amount` from the old delegate's optimistic votes
\\          to the new — sum of optimistic votes is preserved (modulo
\\          address(0), which absorbs/emits). Same for the standard
\\          ledger.
\\
\\   INV-3  Delegation re-pointing:
\\          When a user changes their optimistic delegatee, ALL of
\\          their current `balanceOf(account)` migrates: old.votes -=
\\          balance, new.votes += balance. (Source: _delegateOptimistic
\\          line 548 — the move uses balanceOf(account), not amount.)
\\
\\   INV-4  Self-delegation no-op:
\\          When from == to inside _moveOptimisticDelegateVotes, the
\\          function short-circuits without checkpoint writes (line
\\          552). Storage is bit-identical pre/post.
\\
\\   INV-5  address(0) sink/source:
\\          from == address(0) means votes are created (mint path);
\\          to == address(0) means votes are destroyed (burn path).
\\          No checkpoint write occurs on the zero side (lines 556 /
\\          564 guards).

print("=== StakingVault — dual-delegation independence CAS ===");
print("");

\\ ---- Address model ----
\\ Five candidate addresses. Index 1 is the zero address (address(0)).
\\ Holders use indices 2..5 by convention.
ZERO_ADDR = 1;
ADDR_A    = 2;
ADDR_B    = 3;
ADDR_C    = 4;
ADDR_D    = 5;
NADDR     = 5;

\\ ---- State model ----
\\ A "state" is a 4-vector:
\\   state[1] = balances           (NADDR-vector; balances[i] is balance of address i)
\\   state[2] = stdDelegatees      (NADDR-vector; stdDelegatees[i] = j means i delegates to j)
\\   state[3] = stdVotes           (NADDR-vector; stdVotes[i] = current standard votes of delegate i)
\\   state[4] = optDelegatees      (NADDR-vector; optDelegatees[i] = j)
\\   state[5] = optVotes           (NADDR-vector; optVotes[i] = current optimistic votes of delegate i)
\\
\\ Vote movement is the same for both ledgers; we share helper logic by
\\ accepting "which" -- 1 for standard, 2 for optimistic.

new_state() = {
  my(zeros);
  zeros = vector(NADDR, k, 0);
  \\ Default: every account self-delegates (matches IVotes default once
  \\ they call delegate(self)); equivalent for the optimistic path. We
  \\ model "undelegated" via 0/ZERO_ADDR, which absorbs votes.
  [zeros, vector(NADDR, k, ZERO_ADDR), vector(NADDR, k, 0),
          vector(NADDR, k, ZERO_ADDR), vector(NADDR, k, 0)];
}

\\ ---- Vote movement (shared by both ledgers) ----
\\ move_votes(votes, from, to, amount) returns the new votes vector
\\ after shifting `amount` from delegate `from` to delegate `to`.
\\ Mirrors _moveOptimisticDelegateVotes exactly:
\\   if from == to or amount == 0: return unchanged
\\   if from != 0: from.votes -= amount
\\   if to   != 0: to.votes   += amount
move_votes(votes, from, to, amount) = {
  my(v);
  if(from == to || amount == 0, return(votes));
  v = votes;
  if(from != ZERO_ADDR, v[from] = v[from] - amount);
  if(to   != ZERO_ADDR, v[to]   = v[to]   + amount);
  v;
}

\\ ---- Transfer (mints, burns, peer-to-peer) ----
\\ Mirrors the contract's _update: balances update, then BOTH ledgers
\\ get a move via their respective delegatee maps.
\\ from = ZERO_ADDR means mint (no balance debit on from).
\\ to   = ZERO_ADDR means burn (no balance credit on to).
transfer(st, from, to, amount) = {
  my(bals, sd, sv, od, ov, sFrom, sTo, oFrom, oTo);
  bals = st[1]; sd = st[2]; sv = st[3]; od = st[4]; ov = st[5];
  if(from != ZERO_ADDR, bals[from] = bals[from] - amount);
  if(to   != ZERO_ADDR, bals[to]   = bals[to]   + amount);
  sFrom = if(from == ZERO_ADDR, ZERO_ADDR, sd[from]);
  sTo   = if(to   == ZERO_ADDR, ZERO_ADDR, sd[to]);
  oFrom = if(from == ZERO_ADDR, ZERO_ADDR, od[from]);
  oTo   = if(to   == ZERO_ADDR, ZERO_ADDR, od[to]);
  sv = move_votes(sv, sFrom, sTo, amount);
  ov = move_votes(ov, oFrom, oTo, amount);
  [bals, sd, sv, od, ov];
}

\\ ---- Set standard delegatee for an account ----
\\ Mirrors OZ ERC20Votes._delegate: the account's full balance migrates.
set_std_delegate(st, account, new_delegate) = {
  my(bals, sd, sv, od, ov, old_d, bal);
  bals = st[1]; sd = st[2]; sv = st[3]; od = st[4]; ov = st[5];
  old_d = sd[account];
  sd[account] = new_delegate;
  bal = bals[account];
  sv = move_votes(sv, old_d, new_delegate, bal);
  [bals, sd, sv, od, ov];
}

\\ ---- Set optimistic delegatee for an account ----
\\ Mirrors _delegateOptimistic exactly.
set_opt_delegate(st, account, new_delegate) = {
  my(bals, sd, sv, od, ov, old_d, bal);
  bals = st[1]; sd = st[2]; sv = st[3]; od = st[4]; ov = st[5];
  old_d = od[account];
  od[account] = new_delegate;
  bal = bals[account];
  ov = move_votes(ov, old_d, new_delegate, bal);
  [bals, sd, sv, od, ov];
}

\\ ---- Helpers ----
sum_vec(v) = { my(s, k); s = 0; for(k = 1, length(v), s = s + v[k]); s; }
vec_eq(u, v) = { my(k); if(length(u) != length(v), return(0));
                 for(k = 1, length(u), if(u[k] != v[k], return(0))); 1; }

\\ ----------------------------------------------------------------------
\\ INV-1: Checkpoint independence
\\ ----------------------------------------------------------------------
\\ The two ledgers update independently. We probe by:
\\   (a) starting from a state where both delegate maps are non-trivial,
\\   (b) doing a transfer,
\\   (c) verifying: changing the optimistic delegate map between two
\\       different mappings yields the SAME standard ledger result.
\\       Conversely, changing the standard delegate map yields the
\\       SAME optimistic ledger result.

print("--- INV-1: checkpoint independence ---");
viol_inv1 = 0;
{
  \\ Set up base: A holds 100, B holds 50, C holds 10. Mints already done.
  \\ A delegates standard -> C, optimistic -> D.
  \\ B delegates standard -> D, optimistic -> A.
  st0 = new_state();
  st0 = transfer(st0, ZERO_ADDR, ADDR_A, 100);     \\ mint A
  st0 = transfer(st0, ZERO_ADDR, ADDR_B, 50);      \\ mint B
  st0 = transfer(st0, ZERO_ADDR, ADDR_C, 10);      \\ mint C
  st0 = set_std_delegate(st0, ADDR_A, ADDR_C);
  st0 = set_opt_delegate(st0, ADDR_A, ADDR_D);
  st0 = set_std_delegate(st0, ADDR_B, ADDR_D);
  st0 = set_opt_delegate(st0, ADDR_B, ADDR_A);

  \\ Variant: change ONLY the optimistic delegatees vs base.
  st_var_opt = st0;
  st_var_opt = set_opt_delegate(st_var_opt, ADDR_A, ADDR_B);
  st_var_opt = set_opt_delegate(st_var_opt, ADDR_B, ADDR_C);

  \\ After the optimistic-only mutation, the standard ledger MUST be
  \\ pointwise identical to st0's standard ledger.
  if(!vec_eq(st0[2], st_var_opt[2]), viol_inv1 = viol_inv1 + 1);
  if(!vec_eq(st0[3], st_var_opt[3]), viol_inv1 = viol_inv1 + 1);

  \\ Variant: change ONLY the standard delegatees vs base.
  st_var_std = st0;
  st_var_std = set_std_delegate(st_var_std, ADDR_A, ADDR_B);
  st_var_std = set_std_delegate(st_var_std, ADDR_B, ADDR_C);
  if(!vec_eq(st0[4], st_var_std[4]), viol_inv1 = viol_inv1 + 1);
  if(!vec_eq(st0[5], st_var_std[5]), viol_inv1 = viol_inv1 + 1);

  \\ Stronger probe: after a transfer A -> C of 30, each ledger's
  \\ post-state should be independent of the OTHER ledger's history.
  \\ Build a parallel state where the standard delegate map starts
  \\ differently but the optimistic map is the same as st0, then
  \\ transfer; the resulting optimistic vote-vector should match st0's.
  st_other_std = new_state();
  st_other_std = transfer(st_other_std, ZERO_ADDR, ADDR_A, 100);
  st_other_std = transfer(st_other_std, ZERO_ADDR, ADDR_B, 50);
  st_other_std = transfer(st_other_std, ZERO_ADDR, ADDR_C, 10);
  st_other_std = set_std_delegate(st_other_std, ADDR_A, ADDR_B);
  st_other_std = set_opt_delegate(st_other_std, ADDR_A, ADDR_D);
  st_other_std = set_std_delegate(st_other_std, ADDR_B, ADDR_A);
  st_other_std = set_opt_delegate(st_other_std, ADDR_B, ADDR_A);

  st0_post   = transfer(st0,         ADDR_A, ADDR_C, 30);
  st_op_post = transfer(st_other_std, ADDR_A, ADDR_C, 30);

  if(!vec_eq(st0_post[4], st_op_post[4]), viol_inv1 = viol_inv1 + 1);
  if(!vec_eq(st0_post[5], st_op_post[5]), viol_inv1 = viol_inv1 + 1);
}
printf("  violations: %d\n", viol_inv1);
if(viol_inv1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ----------------------------------------------------------------------
\\ INV-2: Conservation across transfers
\\ ----------------------------------------------------------------------
\\ Sum of votes over all *non-zero* delegates is preserved by a transfer
\\ that doesn't touch the zero address on either side. Holds for both
\\ ledgers.

print("--- INV-2: vote-sum conservation across transfers ---");
viol_inv2 = 0;
{
  \\ Seed: mint to A and B, set them to delegate to C and D.
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 70);
  st = transfer(st, ZERO_ADDR, ADDR_B, 30);
  st = set_std_delegate(st, ADDR_A, ADDR_C);
  st = set_opt_delegate(st, ADDR_A, ADDR_D);
  st = set_std_delegate(st, ADDR_B, ADDR_D);
  st = set_opt_delegate(st, ADDR_B, ADDR_C);

  sv_before = sum_vec(st[3]);
  ov_before = sum_vec(st[5]);

  \\ Transfer 20 from A to B (neither is zero, neither is delegate==zero).
  st_after = transfer(st, ADDR_A, ADDR_B, 20);

  sv_after = sum_vec(st_after[3]);
  ov_after = sum_vec(st_after[5]);

  if(sv_before != sv_after, viol_inv2 = viol_inv2 + 1);
  if(ov_before != ov_after, viol_inv2 = viol_inv2 + 1);
  printf("  standard sum:   before=%d  after=%d\n", sv_before, sv_after);
  printf("  optimistic sum: before=%d  after=%d\n", ov_before, ov_after);

  \\ Stronger: in the post-state, the specific delta is exactly +20 on the
  \\ to-delegate, -20 on the from-delegate (both ledgers).
  \\ Standard: A.delegate=C, B.delegate=D. Move = C -= 20, D += 20.
  if(st_after[3][ADDR_C] != st[3][ADDR_C] - 20, viol_inv2 = viol_inv2 + 1);
  if(st_after[3][ADDR_D] != st[3][ADDR_D] + 20, viol_inv2 = viol_inv2 + 1);
  \\ Optimistic: A.delegate=D, B.delegate=C. Move = D -= 20, C += 20.
  if(st_after[5][ADDR_D] != st[5][ADDR_D] - 20, viol_inv2 = viol_inv2 + 1);
  if(st_after[5][ADDR_C] != st[5][ADDR_C] + 20, viol_inv2 = viol_inv2 + 1);
}
printf("  violations: %d\n", viol_inv2);
if(viol_inv2 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ----------------------------------------------------------------------
\\ INV-3: Delegation re-pointing migrates ALL balance
\\ ----------------------------------------------------------------------
\\ When a user re-points their optimistic delegate, the FULL current
\\ balance moves from the old delegate's votes to the new — not just the
\\ delta. Same for the standard side.

print("--- INV-3: re-pointing migrates full balance ---");
viol_inv3 = 0;
{
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 137);    \\ mint A
  st = set_std_delegate(st, ADDR_A, ADDR_B);    \\ A.std -> B
  st = set_opt_delegate(st, ADDR_A, ADDR_C);    \\ A.opt -> C
  \\ Standard votes: B=137, all others 0.
  if(st[3][ADDR_B] != 137, viol_inv3 = viol_inv3 + 1);
  \\ Optimistic votes: C=137, all others 0.
  if(st[5][ADDR_C] != 137, viol_inv3 = viol_inv3 + 1);

  \\ Re-point A.opt from C to D.
  st = set_opt_delegate(st, ADDR_A, ADDR_D);
  \\ Optimistic post: C drops to 0, D becomes 137. Standard untouched.
  if(st[5][ADDR_C] != 0, viol_inv3 = viol_inv3 + 1);
  if(st[5][ADDR_D] != 137, viol_inv3 = viol_inv3 + 1);
  if(st[3][ADDR_B] != 137, viol_inv3 = viol_inv3 + 1);   \\ std untouched
  if(st[3][ADDR_C] != 0, viol_inv3 = viol_inv3 + 1);
  if(st[3][ADDR_D] != 0, viol_inv3 = viol_inv3 + 1);
  printf("  after A.opt: C->D:  std[B]=%d  opt[C]=%d  opt[D]=%d\n", st[3][ADDR_B], st[5][ADDR_C], st[5][ADDR_D]);

  \\ Re-point A.std from B to D, the opt side moves nothing.
  st = set_std_delegate(st, ADDR_A, ADDR_D);
  if(st[3][ADDR_B] != 0, viol_inv3 = viol_inv3 + 1);
  if(st[3][ADDR_D] != 137, viol_inv3 = viol_inv3 + 1);
  if(st[5][ADDR_D] != 137, viol_inv3 = viol_inv3 + 1);  \\ opt still D=137
  if(st[5][ADDR_C] != 0, viol_inv3 = viol_inv3 + 1);
}
printf("  violations: %d\n", viol_inv3);
if(viol_inv3 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ----------------------------------------------------------------------
\\ INV-4: Self-delegation no-op
\\ ----------------------------------------------------------------------
\\ If from == to inside _moveOptimisticDelegateVotes, no checkpoint
\\ write occurs. We probe via a transfer where both sender and receiver
\\ delegate to the SAME address — the votes vector must be bit-identical
\\ pre/post.

print("--- INV-4: self-delegation / same-target no-op ---");
viol_inv4 = 0;
{
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 40);
  st = transfer(st, ZERO_ADDR, ADDR_B, 60);
  \\ Both A and B delegate optimistic to C.
  st = set_opt_delegate(st, ADDR_A, ADDR_C);
  st = set_opt_delegate(st, ADDR_B, ADDR_C);
  \\ Both A and B delegate standard to D.
  st = set_std_delegate(st, ADDR_A, ADDR_D);
  st = set_std_delegate(st, ADDR_B, ADDR_D);

  votes_std_before = st[3];
  votes_opt_before = st[5];

  st_after = transfer(st, ADDR_A, ADDR_B, 25);

  \\ A.opt = B.opt = C, A.std = B.std = D — both ledgers should be unchanged.
  if(!vec_eq(votes_opt_before, st_after[5]), viol_inv4 = viol_inv4 + 1);
  if(!vec_eq(votes_std_before, st_after[3]), viol_inv4 = viol_inv4 + 1);
  printf("  after transfer with shared delegates: opt-vec identical? %s ; std-vec identical? %s\n",
    if(vec_eq(votes_opt_before, st_after[5]), "yes", "no"),
    if(vec_eq(votes_std_before, st_after[3]), "yes", "no"));

  \\ Sanity probe of move_votes directly:
  v = vector(NADDR, k, 0);
  v[ADDR_C] = 100;
  v_after = move_votes(v, ADDR_C, ADDR_C, 50);   \\ from == to, should be no-op
  if(!vec_eq(v, v_after), viol_inv4 = viol_inv4 + 1);
  v_after2 = move_votes(v, ADDR_C, ADDR_D, 0);   \\ amount = 0, should be no-op
  if(!vec_eq(v, v_after2), viol_inv4 = viol_inv4 + 1);
}
printf("  violations: %d\n", viol_inv4);
if(viol_inv4 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ----------------------------------------------------------------------
\\ INV-5: address(0) sink/source
\\ ----------------------------------------------------------------------
\\ from = 0x0 -> votes created (mint path): the to-delegate gains amount,
\\               but address(0) is NOT debited.
\\ to   = 0x0 -> votes destroyed (burn path): the from-delegate loses
\\               amount, but address(0) is NOT credited.

print("--- INV-5: address(0) sink/source ---");
viol_inv5 = 0;
{
  st = new_state();
  \\ Set A.opt -> C, A.std -> D so a future mint to A bumps both C and D.
  \\ But to set delegates with a balance you'd need a balance first; so
  \\ we set delegates first (with zero balance, no checkpoint moves), then
  \\ mint.
  st = set_opt_delegate(st, ADDR_A, ADDR_C);
  st = set_std_delegate(st, ADDR_A, ADDR_D);
  \\ Initial: all votes 0.
  if(sum_vec(st[3]) != 0, viol_inv5 = viol_inv5 + 1);
  if(sum_vec(st[5]) != 0, viol_inv5 = viol_inv5 + 1);

  \\ Mint 80 to A -> opt[C] = 80, std[D] = 80, sum increases by 80 on each.
  st = transfer(st, ZERO_ADDR, ADDR_A, 80);
  if(st[5][ADDR_C] != 80, viol_inv5 = viol_inv5 + 1);
  if(st[3][ADDR_D] != 80, viol_inv5 = viol_inv5 + 1);
  \\ Crucially, the zero address slot stays zero in both vectors.
  if(st[5][ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
  if(st[3][ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
  printf("  after mint(80, A):  opt[C]=%d  std[D]=%d  opt[0]=%d  std[0]=%d\n",
    st[5][ADDR_C], st[3][ADDR_D], st[5][ZERO_ADDR], st[3][ZERO_ADDR]);

  \\ Burn 30 from A -> opt[C] drops to 50, std[D] drops to 50,
  \\ zero address unaffected.
  st = transfer(st, ADDR_A, ZERO_ADDR, 30);
  if(st[5][ADDR_C] != 50, viol_inv5 = viol_inv5 + 1);
  if(st[3][ADDR_D] != 50, viol_inv5 = viol_inv5 + 1);
  if(st[5][ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
  if(st[3][ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
  printf("  after burn(30, A):  opt[C]=%d  std[D]=%d  opt[0]=%d  std[0]=%d\n",
    st[5][ADDR_C], st[3][ADDR_D], st[5][ZERO_ADDR], st[3][ZERO_ADDR]);

  \\ Direct probes on move_votes for the zero-address branches:
  v = vector(NADDR, k, 0);
  v[ADDR_C] = 10;
  \\ from=0: only credit to side; address(0) stays at 0.
  vplus = move_votes(v, ZERO_ADDR, ADDR_D, 7);
  if(vplus[ADDR_D] != 7, viol_inv5 = viol_inv5 + 1);
  if(vplus[ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
  \\ to=0: only debit from side; address(0) stays at 0.
  vminus = move_votes(v, ADDR_C, ZERO_ADDR, 4);
  if(vminus[ADDR_C] != 6, viol_inv5 = viol_inv5 + 1);
  if(vminus[ZERO_ADDR] != 0, viol_inv5 = viol_inv5 + 1);
}
printf("  violations: %d\n", viol_inv5);
if(viol_inv5 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ----------------------------------------------------------------------
\\ Calibration values exported to the Rocq xcheck
\\ ----------------------------------------------------------------------
\\ The xcheck file mirrors these specific numeric results via vm_compute.

print("--- Calibration values for Rocq xcheck ---");
{
  \\ Scenario A: mint 100 to ADDR_A, set A.opt->C, A.std->D. Then transfer
  \\ 30 from A to B (B has no delegate set so it stays self/zero).
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 100);
  st = set_opt_delegate(st, ADDR_A, ADDR_C);
  st = set_std_delegate(st, ADDR_A, ADDR_D);
  st_post = transfer(st, ADDR_A, ADDR_B, 30);
  printf("  scenarioA.balances[A]      = %d (expect 70)\n", st_post[1][ADDR_A]);
  printf("  scenarioA.balances[B]      = %d (expect 30)\n", st_post[1][ADDR_B]);
  printf("  scenarioA.optVotes[C]      = %d (expect 70)\n", st_post[5][ADDR_C]);
  printf("  scenarioA.stdVotes[D]      = %d (expect 70)\n", st_post[3][ADDR_D]);
  printf("  scenarioA.optVotes[B]      = %d (expect 0)\n", st_post[5][ADDR_B]);
  printf("  scenarioA.stdVotes[B]      = %d (expect 0)\n", st_post[3][ADDR_B]);

  \\ Scenario B: re-point optimistic. Start fresh.
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 137);
  st = set_opt_delegate(st, ADDR_A, ADDR_C);
  st = set_opt_delegate(st, ADDR_A, ADDR_D);
  printf("  scenarioB.optVotes[C]      = %d (expect 0)\n",   st[5][ADDR_C]);
  printf("  scenarioB.optVotes[D]      = %d (expect 137)\n", st[5][ADDR_D]);

  \\ Scenario C: shared-delegate transfer no-op (sum stays).
  st = new_state();
  st = transfer(st, ZERO_ADDR, ADDR_A, 40);
  st = transfer(st, ZERO_ADDR, ADDR_B, 60);
  st = set_opt_delegate(st, ADDR_A, ADDR_C);
  st = set_opt_delegate(st, ADDR_B, ADDR_C);
  before_sum = sum_vec(st[5]);
  st_after = transfer(st, ADDR_A, ADDR_B, 25);
  printf("  scenarioC.opt_sum_before   = %d (expect 100)\n", before_sum);
  printf("  scenarioC.opt_sum_after    = %d (expect 100)\n", sum_vec(st_after[5]));
  printf("  scenarioC.optVotes[C]_after= %d (expect 100)\n", st_after[5][ADDR_C]);
}
print("");

print("=== StakingVault dual delegation CAS — done ===");
