\\ registry_history.gp
\\
\\ CAS-side validation of ReserveOptimisticGovernanceVersionRegistry —
\\ an append-only registry that records every released
\\ (StakingVault impl, Governor impl, Timelock impl) triple, keyed
\\ by keccak256(version_string), with a sticky deprecation flag.
\\
\\ Reference:
\\   contracts/VersionRegistry.sol
\\   contracts/staking/StakingVault.sol#_authorizeUpgrade
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  Append-only history. registerVersion only ever grows the
\\          history; no path removes an entry. Length is monotonically
\\          non-decreasing.
\\
\\   INV-2  Latest is monotone. After registerVersion(deployer_v),
\\          getLatestVersion returns (versionHash_v, deployer_v, ...).
\\
\\   INV-3  Deprecation is sticky. After deprecateVersion(h),
\\          isDeprecated[h] = true; a second deprecateVersion(h)
\\          reverts AlreadyDeprecated. The flag never flips back.
\\
\\   INV-4  Implementation triple integrity. After
\\          registerVersion(deployer with impls (svi, gi, ti)),
\\          getImplementationsForVersion(versionHash) = (svi, gi, ti),
\\          unchanged by any subsequent operation.
\\
\\   INV-5  Upgrade-gate correctness. The _authorizeUpgrade-style
\\          predicate
\\            ok(h, impl) == h == latestVersionHash
\\                       && !isDeprecated[latestVersionHash]
\\                       && impl == stakingVaultImpl_for(h)
\\          accepts exactly the latest non-deprecated entry's
\\          stakingVaultImpl.
\\
\\   INV-6  Role gates. registerVersion reverts when caller fails
\\          isOwner; deprecateVersion reverts when caller fails
\\          isOwnerOrEmergency. (Tested as preconditions.)

print("=== VersionRegistry — CAS invariant validation ===");
print("");

\\ ---- State model ----
\\
\\ state = [history, latest_idx, deprecated_set]
\\   history       : list of entries
\\                   entry = [versionHash, deployer, svi, gi, ti]
\\   latest_idx    : -1 if empty, else index of the last entry
\\   deprecated_set: list of versionHash values that have been deprecated
\\
\\ We model versionHash as a small distinct integer (the bytes of
\\ keccak256 are not load-bearing for the registry, only their
\\ uniqueness across registered versions).

listContains(lst, x) = {
  my(k);
  for(k = 1, #lst, if(lst[k] == x, return(1)));
  0;
}

historyContainsHash(history, h) = {
  my(k);
  for(k = 1, #history, if(history[k][1] == h, return(1)));
  0;
}

\\ Find entry by hash; returns the entry, or 0 if not present.
findEntry(history, h) = {
  my(k);
  for(k = 1, #history,
    if(history[k][1] == h, return(history[k]));
  );
  0;
}

\\ Returns ["ok", new_state] or ["revert", reason].
registerVersion(state, caller, isOwner_fn, h, deployer, svi, gi, ti) = {
  my(history, latest_idx, dep_set, e);
  if(!isOwner_fn(caller), return(["revert", "InvalidCaller"]));
  if(deployer == 0,          return(["revert", "ZeroAddress"]));
  history    = state[1];
  latest_idx = state[2];
  dep_set    = state[3];
  if(historyContainsHash(history, h), return(["revert", "InvalidRegistration"]));
  e = [h, deployer, svi, gi, ti];
  history    = concat(history, [e]);
  latest_idx = #history;   \\ 1-indexed
  ["ok", [history, latest_idx, dep_set]];
}

deprecateVersion(state, caller, isOwnerOrEmerg_fn, h) = {
  my(history, latest_idx, dep_set);
  if(!isOwnerOrEmerg_fn(caller), return(["revert", "InvalidCaller"]));
  history    = state[1];
  latest_idx = state[2];
  dep_set    = state[3];
  if(listContains(dep_set, h), return(["revert", "AlreadyDeprecated"]));
  dep_set = concat(dep_set, [h]);
  ["ok", [history, latest_idx, dep_set]];
}

getLatestVersion(state) = {
  my(history, latest_idx, dep_set, e);
  history    = state[1];
  latest_idx = state[2];
  dep_set    = state[3];
  if(latest_idx == 0 || #history == 0, return(["revert", "NotConfigured"]));
  e = history[latest_idx];
  ["ok", e[1], e[2], listContains(dep_set, e[1])];
}

getImplementationsForVersion(state, h) = {
  my(e);
  e = findEntry(state[1], h);
  if(e == 0, return(["none"]));
  ["ok", e[3], e[4], e[5]];
}

\\ _authorizeUpgrade predicate.
upgradeAuthorized(state, h, impl) = {
  my(latest);
  latest = getLatestVersion(state);
  if(latest[1] != "ok", return(0));
  if(latest[4] != 0, return(0));     \\ deprecated -> reject
  if(latest[2] != h, return(0));     \\ wrong hash -> reject
  if(getImplementationsForVersion(state, h)[2] != impl, return(0));
  1;
}

\\ Role-predicate fixtures.
owner_set = [1];                       \\ address 1 is owner
emerg_set = [1, 2];                    \\ addresses 1, 2 are owner-or-emergency
isOwner(c) = listContains(owner_set, c);
isOwnerOrEmerg(c) = listContains(emerg_set, c);

empty_state = [[], 0, []];

\\ ---- INV-1: history is append-only across a register sequence ----
print("--- INV-1: history is append-only ---");
viol_inv1 = 0;
{
  s = empty_state;
  pre_len = #s[1];
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  if(#s[1] != pre_len + 1, viol_inv1 = viol_inv1 + 1);
  pre_len = #s[1];
  s = registerVersion(s, 1, isOwner, 200, 1002, 2002, 3002, 4002)[2];
  if(#s[1] != pre_len + 1, viol_inv1 = viol_inv1 + 1);
  \\ Deprecation does NOT remove from history:
  s = deprecateVersion(s, 1, isOwnerOrEmerg, 100)[2];
  if(#s[1] != 2, viol_inv1 = viol_inv1 + 1);
  printf("  after 2 registers + 1 deprecate: history length = %d\n", #s[1]);
}
if(viol_inv1 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-2: getLatestVersion returns the most-recent register ----
print("--- INV-2: latest tracks the most-recent register ---");
viol_inv2 = 0;
{
  s = empty_state;
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  l1 = getLatestVersion(s);
  if(l1[2] != 100, viol_inv2 = viol_inv2 + 1);
  s = registerVersion(s, 1, isOwner, 200, 1002, 2002, 3002, 4002)[2];
  l2 = getLatestVersion(s);
  if(l2[2] != 200, viol_inv2 = viol_inv2 + 1);
  s = registerVersion(s, 1, isOwner, 300, 1003, 2003, 3003, 4003)[2];
  l3 = getLatestVersion(s);
  if(l3[2] != 300, viol_inv2 = viol_inv2 + 1);
  printf("  after 3 registers: latest hash = %d (expected 300)\n", l3[2]);
}
if(viol_inv2 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-3: deprecation is sticky ----
print("--- INV-3: deprecation is sticky ---");
viol_inv3 = 0;
{
  s = empty_state;
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  r1 = deprecateVersion(s, 1, isOwnerOrEmerg, 100);
  if(r1[1] != "ok", viol_inv3 = viol_inv3 + 1);
  s = r1[2];
  r2 = deprecateVersion(s, 1, isOwnerOrEmerg, 100);
  if(r2[1] != "revert" || r2[2] != "AlreadyDeprecated", viol_inv3 = viol_inv3 + 1);
  \\ Flag is observable via getLatestVersion:
  l = getLatestVersion(s);
  if(l[4] != 1, viol_inv3 = viol_inv3 + 1);
  printf("  re-deprecate -> revert? %s (%s)\n", r2[1], r2[2]);
  printf("  latest.deprecated flag after deprecate = %d\n", l[4]);
}
if(viol_inv3 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-4: implementation triple integrity ----
print("--- INV-4: getImplementationsForVersion returns recorded triple ---");
viol_inv4 = 0;
{
  s = empty_state;
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  s = registerVersion(s, 1, isOwner, 200, 1002, 2002, 3002, 4002)[2];
  t100 = getImplementationsForVersion(s, 100);
  t200 = getImplementationsForVersion(s, 200);
  if(t100[1] != "ok" || t100[2] != 2001 || t100[3] != 3001 || t100[4] != 4001,
    viol_inv4 = viol_inv4 + 1);
  if(t200[1] != "ok" || t200[2] != 2002 || t200[3] != 3002 || t200[4] != 4002,
    viol_inv4 = viol_inv4 + 1);
  \\ Deprecation does NOT touch the triple:
  s = deprecateVersion(s, 1, isOwnerOrEmerg, 100)[2];
  t100_after = getImplementationsForVersion(s, 100);
  if(t100_after[2] != 2001 || t100_after[3] != 3001 || t100_after[4] != 4001,
    viol_inv4 = viol_inv4 + 1);
  \\ Unregistered hash -> none:
  t_miss = getImplementationsForVersion(s, 999);
  if(t_miss[1] != "none", viol_inv4 = viol_inv4 + 1);
  printf("  v100 triple: (%d, %d, %d)\n", t100[2], t100[3], t100[4]);
  printf("  v100 triple post-deprecate: (%d, %d, %d)\n", t100_after[2], t100_after[3], t100_after[4]);
}
if(viol_inv4 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-5: upgrade-gate correctness ----
print("--- INV-5: upgrade_authorized accepts only latest non-deprecated svi ---");
viol_inv5 = 0;
{
  s = empty_state;
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  s = registerVersion(s, 1, isOwner, 200, 1002, 2002, 3002, 4002)[2];
  \\ Latest is v200 with svi 2002.
  if(upgradeAuthorized(s, 200, 2002) != 1, viol_inv5 = viol_inv5 + 1);
  \\ Stale hash:
  if(upgradeAuthorized(s, 100, 2001) != 0, viol_inv5 = viol_inv5 + 1);
  \\ Right hash, wrong impl:
  if(upgradeAuthorized(s, 200, 9999) != 0, viol_inv5 = viol_inv5 + 1);
  \\ Deprecate latest -> reject:
  s2 = deprecateVersion(s, 1, isOwnerOrEmerg, 200)[2];
  if(upgradeAuthorized(s2, 200, 2002) != 0, viol_inv5 = viol_inv5 + 1);
  \\ Empty registry:
  if(upgradeAuthorized(empty_state, 100, 2001) != 0, viol_inv5 = viol_inv5 + 1);
  printf("  acceptance: latest+impl=yes; stale=no; wrong-impl=no; deprecated=no; empty=no\n");
}
if(viol_inv5 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- INV-6: role gates on mutations ----
print("--- INV-6: register/deprecate require correct role ---");
viol_inv6 = 0;
{
  s = empty_state;
  \\ Non-owner cannot register:
  r1 = registerVersion(s, 99, isOwner, 100, 1001, 2001, 3001, 4001);
  if(r1[1] != "revert" || r1[2] != "InvalidCaller", viol_inv6 = viol_inv6 + 1);
  \\ Register as owner:
  s = registerVersion(s, 1, isOwner, 100, 1001, 2001, 3001, 4001)[2];
  \\ Non-emergency cannot deprecate:
  r2 = deprecateVersion(s, 99, isOwnerOrEmerg, 100);
  if(r2[1] != "revert" || r2[2] != "InvalidCaller", viol_inv6 = viol_inv6 + 1);
  \\ Emergency can deprecate (address 2):
  r3 = deprecateVersion(s, 2, isOwnerOrEmerg, 100);
  if(r3[1] != "ok", viol_inv6 = viol_inv6 + 1);
  \\ Zero-address deployer rejected:
  r4 = registerVersion(s, 1, isOwner, 200, 0, 2002, 3002, 4002);
  if(r4[1] != "revert" || r4[2] != "ZeroAddress", viol_inv6 = viol_inv6 + 1);
  \\ Re-register same hash rejected:
  r5 = registerVersion(s, 1, isOwner, 100, 1002, 2002, 3002, 4002);
  if(r5[1] != "revert" || r5[2] != "InvalidRegistration", viol_inv6 = viol_inv6 + 1);
  printf("  non-owner register: %s; non-emerg deprecate: %s; emerg deprecate: %s\n", r1[2], r2[2], r3[1]);
}
if(viol_inv6 == 0, print("  OK"), print("  FAIL"));
print("");

\\ ---- Edge: getLatestVersion on empty registry reverts ----
print("--- Edge: getLatestVersion on empty registry reverts NotConfigured ---");
viol_edge = 0;
{
  r = getLatestVersion(empty_state);
  if(r[1] != "revert" || r[2] != "NotConfigured", viol_edge = viol_edge + 1);
  printf("  empty getLatest: %s (%s)\n", r[1], r[2]);
}
if(viol_edge == 0, print("  OK"), print("  FAIL"));
print("");

print("=== VersionRegistry CAS — done ===");
