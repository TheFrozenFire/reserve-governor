\\ registration_lifecycle.gp
\\
\\ CAS-side validation of RewardTokenRegistry — a role-gated allowlist
\\ of ERC20 tokens that StakingVault is permitted to register as reward
\\ tokens.
\\
\\ Reference:
\\   contracts/staking/RewardTokenRegistry.sol
\\
\\ The contract wraps an OpenZeppelin EnumerableSet.AddressSet behind
\\ two role-gated mutators plus two view functions:
\\
\\   registerRewardToken(address)      onlyOwner
\\   unregisterRewardToken(address)    onlyOwnerOrEmergencyCouncil
\\   rewardTokens()  view  -> address[]
\\   isRegistered(addr) view  -> bool
\\
\\ Both mutators revert on the corresponding "no-op" path:
\\   register   reverts if the token is already a member
\\              (set.add returned false)
\\   unregister reverts if the token is not currently a member
\\              (set.remove returned false)
\\ This differs from SelectorRegistry (set.add idempotent) and is the
\\ critical asymmetry the simulation must capture.
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  register reverts on duplicate;
\\          unregister reverts on non-member.
\\          (No silent idempotence — distinct from SelectorRegistry.)
\\
\\   INV-2  isRegistered(t) <=> t in _rewardTokens.
\\          (Membership-observability across mixed sequences.)
\\
\\   INV-3  Successful register followed by successful unregister of
\\          the same token restores the prior set.
\\
\\   INV-4  Defense-in-depth boundary checks at register:
\\            rewardToken == address(0)   -> ZeroAddress revert
\\          (No forbidden-target list as in SelectorRegistry — the
\\          contract trusts owner-role callers with target choice.)
\\
\\   INV-5  Role-gated auth: register reverts when caller is not owner;
\\          unregister reverts when caller is neither owner nor
\\          emergency-council.
\\
\\   INV-6  Set semantics: registering N distinct tokens yields a
\\          size-N set; unregistering all of them brings the set back
\\          to empty.

print("=== RewardTokenRegistry — CAS invariant validation ===");
print("");

\\ Set state: state = list<address>  (no duplicates)

listContains(lst, x) = {
  my(k);
  for(k = 1, #lst, if(lst[k] == x, return(1)));
  0;
}

listRemove(lst, x) = {
  my(k, out);
  out = [];
  for(k = 1, #lst,
    if(lst[k] != x, out = concat(out, [lst[k]]));
  );
  out;
}

\\ Operations return ["ok", new_state] or ["revert", reason_string].
\\ Role checks are explicit booleans (modeling roleRegistry calls).

registerRewardToken(state, token, is_owner) = {
  if(!is_owner,        return(["revert", "InvalidCaller"]));
  if(token == 0,       return(["revert", "ZeroAddress"]));
  if(listContains(state, token),
                       return(["revert", "AlreadyRegistered"]));
  ["ok", concat(state, [token])];
}

unregisterRewardToken(state, token, is_owner_or_council) = {
  if(!is_owner_or_council,
                       return(["revert", "InvalidCaller"]));
  if(!listContains(state, token),
                       return(["revert", "NotRegistered"]));
  ["ok", listRemove(state, token)];
}

isRegistered(state, token) = listContains(state, token);

empty_state = [];

\\ ---- INV-1: register reverts on duplicate; unregister reverts on non-member ----
print("--- INV-1: revert on duplicate register / non-member unregister ---");
{
  s = empty_state;
  r1 = registerRewardToken(s, 100, 1); s = r1[2];
  r2 = registerRewardToken(s, 100, 1);
  r3 = unregisterRewardToken(s, 999, 1);
  printf("  register(100) twice -> [%s, %s] (%s)\n", r1[1], r2[1], r2[2]);
  printf("  unregister(999) on absent -> %s (%s)\n", r3[1], r3[2]);
  if(r1[1] == "ok" && r2[1] == "revert" && r2[2] == "AlreadyRegistered" &&
     r3[1] == "revert" && r3[2] == "NotRegistered",
     print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: isRegistered agrees with set membership ----
print("--- INV-2: isRegistered(t) <=> t in _rewardTokens ---");
{
  s = empty_state;
  s = registerRewardToken(s, 100, 1)[2];
  s = registerRewardToken(s, 200, 1)[2];
  s = registerRewardToken(s, 300, 1)[2];
  s = unregisterRewardToken(s, 200, 1)[2];
  cases = [[100, 1], [200, 0], [300, 1], [400, 0], [0, 0]];
  viol = 0;
  for(k = 1, #cases,
    actual = isRegistered(s, cases[k][1]);
    if(actual != cases[k][2], viol = viol + 1);
  );
  printf("  membership mismatches across %d probes: %d\n", #cases, viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-3: register then unregister restores prior state ----
print("--- INV-3: register then unregister restores prior set ---");
{
  s0 = empty_state;
  s0 = registerRewardToken(s0, 100, 1)[2];
  s1 = registerRewardToken(s0, 200, 1)[2];
  s2 = unregisterRewardToken(s1, 200, 1)[2];
  printf("  pre: %s  | mid: %s  | post: %s\n", Str(s0), Str(s1), Str(s2));
  if(s0 == s2, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: zero address rejected ----
print("--- INV-4: register reverts on address(0) ---");
{
  s = empty_state;
  r = registerRewardToken(s, 0, 1);
  printf("  register(0) -> %s (%s)\n", r[1], r[2]);
  if(r[1] == "revert" && r[2] == "ZeroAddress", print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-5: role-gated auth ----
print("--- INV-5: register/unregister role-gated ---");
{
  s = empty_state;
  s = registerRewardToken(s, 100, 1)[2];
  r1 = registerRewardToken(s, 200, 0);     \\ not owner
  r2 = unregisterRewardToken(s, 100, 0);   \\ not owner-or-council
  printf("  register(200, !owner) -> %s (%s)\n", r1[1], r1[2]);
  printf("  unregister(100, !auth) -> %s (%s)\n", r2[1], r2[2]);
  if(r1[1] == "revert" && r1[2] == "InvalidCaller" &&
     r2[1] == "revert" && r2[2] == "InvalidCaller",
     print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: set semantics across N register/unregister ----
print("--- INV-6: N register / N unregister returns to empty ---");
{
  s = empty_state;
  tokens = [101, 102, 103, 104, 105];
  for(k = 1, #tokens,
    r = registerRewardToken(s, tokens[k], 1);
    if(r[1] != "ok", error("expected ok register"));
    s = r[2];
  );
  size_mid = #s;
  for(k = 1, #tokens,
    r = unregisterRewardToken(s, tokens[k], 1);
    if(r[1] != "ok", error("expected ok unregister"));
    s = r[2];
  );
  size_end = #s;
  printf("  after %d registers: size=%d ; after matching unregisters: size=%d\n",
         #tokens, size_mid, size_end);
  if(size_mid == #tokens && size_end == 0, print("  OK"), print("  FAIL"));
}
print("");

print("=== RewardTokenRegistry CAS — done ===");
