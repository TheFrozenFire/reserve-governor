\\ membership_consistency.gp
\\
\\ CAS-side validation of OptimisticSelectorRegistry — a
\\ `(target, selector)` allowlist with two coupled sets:
\\
\\   _targets : Set<address>
\\   _allowedSelectors : address -> Set<bytes32>
\\
\\ The contract maintains the cross-invariant: a target is in _targets
\\ iff its per-target selector set is non-empty.
\\
\\ Reference:
\\   contracts/governance/OptimisticSelectorRegistry.sol
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  add(t, []) is a no-op; add(t, [s, s]) is identical to
\\          add(t, [s]) (set semantics, no duplicate count).
\\
\\   INV-2  target_in_targets(t) <=> non_empty(allowed[t]).
\\          (Cross-set conservation across mixed sequences.)
\\
\\   INV-3  isAllowed(t, s) <=> s in allowed[t]. (Definitional but the
\\          contract route is via `_allowedSelectors[target].contains`.)
\\
\\   INV-4  add then remove of the same (t, s) restores prior state.
\\
\\   INV-5  remove on a non-member is a no-op; remove of the last
\\          selector for a target also removes the target.
\\
\\   INV-6  add reverts when:
\\            target in {self, governor, timelock, token}
\\            selector == bytes4(0)
\\          (Both modeled as algebraic preconditions on the add.)

print("=== OptimisticSelectorRegistry — CAS invariant validation ===");
print("");

\\ Set state: state = [targets_list, allowed_map]
\\   targets_list : list<address>           (no duplicates)
\\   allowed_map  : list of [target, list_of_selectors]
\\
\\ Both lists are ordered insert-time for determinism but the
\\ contract semantics are set-membership only.

\\ ---- Helpers ----
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

allowedFor(allowed_map, target) = {
  my(k);
  for(k = 1, #allowed_map,
    if(allowed_map[k][1] == target, return(allowed_map[k][2]));
  );
  [];
}

setAllowedFor(allowed_map, target, new_selectors) = {
  my(k, out, found);
  out = []; found = 0;
  for(k = 1, #allowed_map,
    if(allowed_map[k][1] == target,
      out = concat(out, [[target, new_selectors]]);
      found = 1;
    , out = concat(out, [allowed_map[k]]));
  );
  if(!found, out = concat(out, [[target, new_selectors]]));
  out;
}

\\ ---- Operations ----
\\ Returns ["ok", new_state] or ["revert", reason].
\\ forbidden_targets is a list of addresses that may not be added.

addSelector(state, target, selector, forbidden_targets) = {
  my(targets, allowed, sels, sels_new, added);
  if(listContains(forbidden_targets, target), return(["revert", "InvalidTarget"]));
  if(selector == 0,                            return(["revert", "InvalidSelector"]));
  targets = state[1];
  allowed = state[2];
  sels    = allowedFor(allowed, target);
  added   = !listContains(sels, selector);
  if(added,
    sels_new = concat(sels, [selector]);
    allowed  = setAllowedFor(allowed, target, sels_new);
    if(!listContains(targets, target), targets = concat(targets, [target]));
  );
  ["ok", [targets, allowed]];
}

\\ Strip per-target entries whose selector-list is empty. Models the
\\ Solidity mapping convention where unset keys return default-empty.
pruneAllowed(allowed) = {
  my(k, out);
  out = [];
  for(k = 1, #allowed,
    if(#allowed[k][2] > 0, out = concat(out, [allowed[k]]));
  );
  out;
}

removeSelector(state, target, selector) = {
  my(targets, allowed, sels, sels_new, removed);
  targets = state[1];
  allowed = state[2];
  sels    = allowedFor(allowed, target);
  removed = listContains(sels, selector);
  if(removed,
    sels_new = listRemove(sels, selector);
    allowed  = setAllowedFor(allowed, target, sels_new);
    allowed  = pruneAllowed(allowed);
    if(#sels_new == 0, targets = listRemove(targets, target));
  );
  ["ok", [targets, allowed]];
}

isAllowed(state, target, selector) = listContains(allowedFor(state[2], target), selector);

\\ Cross-invariant check: target in targets iff allowed[target] non-empty.
crossInvariant(state) = {
  my(targets, allowed, k, t, in_targets, in_map);
  targets = state[1];
  allowed = state[2];
  \\ Direction 1: every target in targets has a non-empty allowed set.
  for(k = 1, #targets,
    t = targets[k];
    if(#allowedFor(allowed, t) == 0, return(0));
  );
  \\ Direction 2: every target in allowed with non-empty selectors is in targets.
  for(k = 1, #allowed,
    t = allowed[k][1];
    in_map = #allowed[k][2];
    in_targets = listContains(targets, t);
    if(in_map > 0 && !in_targets, return(0));
  );
  1;
}

empty_state = [[], []];

\\ Calibration: pick small distinct integers as addresses, selectors.
self_addr     = 1;
gov_addr      = 2;
timelock_addr = 3;
token_addr    = 4;
forbidden     = [self_addr, gov_addr, timelock_addr, token_addr];

\\ ---- INV-1: add idempotence ----
print("--- INV-1: add idempotence and duplicate-call no-op ---");
{
  s = empty_state;
  r = addSelector(s, 10, 1000, forbidden); s = r[2];
  pre_sels = #allowedFor(s[2], 10);
  r = addSelector(s, 10, 1000, forbidden); s = r[2];
  post_sels = #allowedFor(s[2], 10);
  printf("  pre add count: %d ; post duplicate-add count: %d\n", pre_sels, post_sels);
  if(pre_sels == post_sels && pre_sels == 1, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: cross-invariant across mixed sequence ----
print("--- INV-2: target_in_targets <=> non_empty(allowed[target]) ---");
{
  s = empty_state;
  ops = [["add", 10, 1000], ["add", 10, 1001], ["add", 20, 2000],
         ["remove", 10, 1000], ["remove", 10, 1001],   \\ wipes target 10
         ["add", 30, 3000]];
  viol = 0;
  for(k = 1, #ops,
    op = ops[k];
    if(op[1] == "add",
      r = addSelector(s, op[2], op[3], forbidden),
      r = removeSelector(s, op[2], op[3]));
    if(r[1] != "ok", viol = viol + 1; next);
    s = r[2];
    if(crossInvariant(s) == 0, viol = viol + 1);
  );
  printf("  cross-invariant violations across %d ops: %d\n", #ops, viol);
  printf("  final targets: %s\n", Str(s[1]));
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-3: isAllowed agrees with set-membership ----
print("--- INV-3: isAllowed(t,s) == (s in allowed[t]) ---");
{
  s = empty_state;
  s = addSelector(s, 10, 1000, forbidden)[2];
  s = addSelector(s, 10, 1001, forbidden)[2];
  cases = [[10, 1000, 1], [10, 1001, 1], [10, 9999, 0], [20, 1000, 0]];
  viol = 0;
  for(k = 1, #cases,
    actual = isAllowed(s, cases[k][1], cases[k][2]);
    if(actual != cases[k][3], viol = viol + 1);
  );
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-4: add then remove restores prior state ----
print("--- INV-4: add then remove restores prior set ---");
{
  s0 = empty_state;
  s0 = addSelector(s0, 10, 1000, forbidden)[2];
  s1 = addSelector(s0, 20, 2000, forbidden)[2];
  s2 = removeSelector(s1, 20, 2000)[2];
  printf("  pre: %s  | mid: %s  | post: %s\n", Str(s0), Str(s1), Str(s2));
  if(s0 == s2, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-5: remove non-member is no-op; last removal also drops target ----
print("--- INV-5: remove-non-member no-op; last-removal drops target ---");
{
  s = empty_state;
  s = addSelector(s, 10, 1000, forbidden)[2];
  pre = s;
  r1 = removeSelector(s, 10, 9999);       \\ non-member selector
  if(r1[2] != pre, error("non-member remove should be a no-op"));
  s = r1[2];
  r2 = removeSelector(s, 10, 1000);       \\ last selector for target 10
  s = r2[2];
  printf("  after last-removal: targets=%s\n", Str(s[1]));
  if(#s[1] == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: revert paths ----
print("--- INV-6: add reverts on forbidden target / zero selector ---");
{
  s = empty_state;
  r1 = addSelector(s, gov_addr, 1000, forbidden);
  r2 = addSelector(s, 10, 0, forbidden);
  printf("  add(gov, 1000) -> %s (%s)\n", r1[1], r1[2]);
  printf("  add(10, 0)     -> %s (%s)\n", r2[1], r2[2]);
  if(r1[1] == "revert" && r1[2] == "InvalidTarget" &&
     r2[1] == "revert" && r2[2] == "InvalidSelector",
     print("  OK"), print("  FAIL"));
}
print("");

print("=== OptimisticSelectorRegistry CAS — done ===");
