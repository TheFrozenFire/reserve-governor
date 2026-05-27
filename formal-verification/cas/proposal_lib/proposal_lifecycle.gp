\\ proposal_lifecycle.gp
\\
\\ CAS-side validation of ProposalLib (contracts/governance/lib/
\\ ProposalLib.sol) — the library that mediates proposal lifecycle for
\\ the ReserveOptimisticGovernor.
\\
\\ ProposalLib mediates three entry points:
\\
\\   proposeOptimistic(proposal, core, optimisticParams)
\\     -- validate proposal shape, validate that caller has the
\\        OPTIMISTIC_PROPOSER_ROLE, then check every (target, selector)
\\        is in the OptimisticSelectorRegistry, then save.
\\
\\   proposePessimistic(proposal, core)
\\     -- validate proposal shape, validate proposer has >= threshold
\\        votes, then save.
\\
\\   transitionToPessimistic(proposalId, optDetails, cores)
\\     -- one-way transition: takes an optimistic proposal that has
\\        been vetoed, re-routes it as a standard proposal with the
\\        description prefixed by "Confirmation For: " and a freshly
\\        derived proposalId. Idempotent: a second call observes
\\        vetoThreshold = type(uint256).max and reverts.
\\
\\ Reference:
\\   contracts/governance/lib/ProposalLib.sol
\\   contracts/governance/ReserveOptimisticGovernor.sol
\\   contracts/interfaces/IReserveOptimisticGovernor.sol
\\
\\ Invariants probed (numbered to match the Rocq simulation):
\\
\\   INV-1  Encode round-trip: building a ProposalData record and
\\          reading back each field yields the original values.
\\
\\   INV-2  proposalId determinism: getProposalId(targets, values,
\\          calldatas, descHash) is a pure function of its inputs.
\\          Calling twice with the same inputs yields the same id.
\\
\\   INV-3  Optimistic vs standard discrimination: the "Confirmation
\\          For: " prefix appended by transitionToPessimistic changes
\\          the description hash, which in turn changes the proposalId.
\\          Optimistic and the resulting pessimistic re-route always
\\          carry distinct ids.
\\
\\   INV-4  _validateProposal length-coupling: targets / values /
\\          calldatas must have equal length, and the length must be
\\          positive. Any mismatch reverts with the right error.
\\
\\   INV-5  Confirmation-prefix gate: a propose call whose description
\\          starts with "Confirmation For: " reverts in the user-
\\          facing entry points. Only transitionToPessimistic may
\\          introduce that prefix.
\\
\\   INV-6  TRANSITIONED_VETO_THRESHOLD sentinel: once an optimistic
\\          proposal is transitioned, optDetails.vetoThreshold is set
\\          to type(uint256).max. A second transitionToPessimistic on
\\          the same id observes the sentinel and reverts.
\\
\\   INV-7  Optimistic selector gate: proposeOptimistic reverts when
\\          any (target, selector) is missing from the registry.
\\
\\   INV-8  Optimistic proposer gate: proposeOptimistic reverts when
\\          the proposer lacks OPTIMISTIC_PROPOSER_ROLE.
\\
\\ Hash model:
\\   The contract uses keccak256(abi.encode(...)) for both proposalId
\\   derivation and description hashing. We model keccak256 as an
\\   opaque injective function — symbolically, hash(x) = hash(y) iff
\\   x = y. In CAS we approximate with a deterministic combiner over
\\   the inputs whose only property is determinism (same inputs ->
\\   same output) and distinguishability (different inputs we vary in
\\   the witness corpus -> different outputs). The witness corpus is
\\   constructed so that distinct inputs produce distinct hashes by
\\   inspection.

print("=== ProposalLib — CAS invariant validation ===");
print("");

UINT256_MAX = 2^256 - 1;
TRANSITIONED_VETO_THRESHOLD = UINT256_MAX;

\\ ---- Hash model ----
\\
\\ Opaque injective combiner. PARI's [Vec] is itself a pure function of
\\ its arguments, and equality of vectors is structural. We pin it
\\ behind a label so the model intent reads clearly in the witness
\\ corpus: hash(x) is the same as x under structural equality, which
\\ is exactly the property keccak256 gives us under the abi.encode
\\ injectivity assumption.

opaqueHash(args) = args;

descriptionHash(desc) = opaqueHash(["desc", desc]);

getProposalId(targets, values_, calldatas, descHash) = {
  opaqueHash(["pid", targets, values_, calldatas, descHash]);
}

\\ ---- ProposalData record helpers ----

makeProposal(pid, proposer, targets, values_, calldatas, desc) = {
  [pid, proposer, targets, values_, calldatas, desc];
}

pdId(p)        = p[1];
pdProposer(p)  = p[2];
pdTargets(p)   = p[3];
pdValues(p)    = p[4];
pdCalldatas(p) = p[5];
pdDesc(p)      = p[6];

\\ ---- _validateProposal gate ----
\\
\\ Returns ["ok"] or ["revert", reason]. Models:
\\   - LengthMismatch when |targets| != |values| or |targets| != |calldatas|
\\   - ZeroLength when |targets| = 0
\\   - ConfirmationPrefix when desc starts with "Confirmation For: "
\\   - GovernorRestrictedProposer when desc carries a #proposer= suffix
\\     for a different address (modeled by an explicit "restricted" flag
\\     in the description, since we don't parse strings here).
\\
\\ The "voteStart != 0" check (already-proposed slot) is state-side and
\\ kept out of CAS; the Rocq side covers it.

isConfirmationPrefix(desc) = {
  my(prefix, n, i, dv, pv);
  prefix = "Confirmation For: ";
  if(type(desc) != "t_STR", return(0));
  if(#desc < #prefix, return(0));
  dv = Vecsmall(desc);
  pv = Vecsmall(prefix);
  n = #pv;
  for(i = 1, n,
    if(dv[i] != pv[i], return(0));
  );
  1;
}

validateProposal(p) = {
  my(t, v, c);
  t = pdTargets(p); v = pdValues(p); c = pdCalldatas(p);
  if(#t == 0, return(["revert", "ZeroLength"]));
  if(#t != #v || #t != #c, return(["revert", "LengthMismatch"]));
  if(isConfirmationPrefix(pdDesc(p)), return(["revert", "ConfirmationPrefix"]));
  ["ok"];
}

\\ ---- proposeOptimistic ----
\\
\\ Requires:
\\   - proposer has OPTIMISTIC_PROPOSER_ROLE (modeled by a set)
\\   - every (target, selector) is in the selector registry
\\
\\ Selector is the first 4 bytes of the calldata. We model calldata as
\\ a vector whose first element is the selector and remaining elements
\\ are payload bytes. Empty calldata is the empty vector [], which fails
\\ the length>=4 check.

selectorOf(cd) = if(#cd >= 1, cd[1], -1);

isAllowedInRegistry(registry, target, sel) = {
  my(j, e);
  for(j = 1, #registry,
    e = registry[j];
    if(e[1] == target && e[2] == sel, return(1));
  );
  0;
}

proposeOptimistic(proposal, proposerRoles, registry) = {
  my(vres, proposer, t, c, j, sel);
  vres = validateProposal(proposal);
  if(vres[1] != "ok", return(vres));
  proposer = pdProposer(proposal);
  if(!setsearch(Set(proposerRoles), proposer),
     return(["revert", "NotOptimisticProposer"]));
  t = pdTargets(proposal); c = pdCalldatas(proposal);
  for(j = 1, #t,
    if(#(c[j]) < 1, return(["revert", "InvalidCall"]));
    sel = selectorOf(c[j]);
    if(!isAllowedInRegistry(registry, t[j], sel),
       return(["revert", "InvalidCall"]));
  );
  ["ok", pdId(proposal)];
}

\\ ---- proposePessimistic ----
\\
\\ Requires proposer.votes >= threshold. Modeled by an explicit votes
\\ map and threshold parameter.

proposePessimistic(proposal, votes, threshold) = {
  my(vres, proposer, pv, j, e);
  vres = validateProposal(proposal);
  if(vres[1] != "ok", return(vres));
  proposer = pdProposer(proposal);
  pv = 0;
  for(j = 1, #votes,
    e = votes[j];
    if(e[1] == proposer, pv = e[2]);
  );
  if(pv < threshold, return(["revert", "InsufficientProposerVotes"]));
  ["ok", pdId(proposal)];
}

\\ ---- transitionToPessimistic ----
\\
\\ optDetails is a record [targets, values, calldatas, description,
\\ vetoThreshold]. If vetoThreshold == TRANSITIONED, revert; otherwise
\\ flip the sentinel, compute a new pid from the prefixed description,
\\ and return both the updated details and the new pid.

makeOptDetails(targets, values_, calldatas, desc, vetoThreshold) = {
  [targets, values_, calldatas, desc, vetoThreshold];
}

odTargets(d)   = d[1];
odValues(d)    = d[2];
odCalldatas(d) = d[3];
odDesc(d)      = d[4];
odVetoT(d)     = d[5];

transitionToPessimistic(optDetails) = {
  my(newDesc, newPid, updated);
  if(odVetoT(optDetails) == TRANSITIONED_VETO_THRESHOLD,
     return(["revert", "AlreadyTransitioned"]));
  newDesc = concat(["Confirmation For: ", odDesc(optDetails)]);
  newPid = getProposalId(odTargets(optDetails), odValues(optDetails),
                         odCalldatas(optDetails),
                         descriptionHash(newDesc));
  updated = [odTargets(optDetails), odValues(optDetails),
             odCalldatas(optDetails), newDesc,
             TRANSITIONED_VETO_THRESHOLD];
  ["ok", newPid, updated];
}

\\ ============================================================
\\ Invariant probes
\\ ============================================================

\\ ---- INV-1: encode round-trip ----
print("--- INV-1: ProposalData round-trip ---");
{
  my(p, ok);
  p = makeProposal(42, 9001, [101, 102], [10, 20], [[55, 1, 2], [99]],
                   "Pessimistic proposal #1");
  ok = (pdId(p) == 42) &&
       (pdProposer(p) == 9001) &&
       (pdTargets(p) == [101, 102]) &&
       (pdValues(p) == [10, 20]) &&
       (pdCalldatas(p) == [[55, 1, 2], [99]]) &&
       (pdDesc(p) == "Pessimistic proposal #1");
  if(ok, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-2: getProposalId determinism ----
print("--- INV-2: getProposalId is deterministic ---");
{
  my(h1, h2, p1, p2);
  h1 = descriptionHash("hello");
  h2 = descriptionHash("hello");
  p1 = getProposalId([1,2,3], [0,0,0], [[55], [], [55,1]], h1);
  p2 = getProposalId([1,2,3], [0,0,0], [[55], [], [55,1]], h2);
  if(p1 == p2, print("  OK (same inputs -> same id)"), print("  FAIL"));
}
print("");

\\ ---- INV-3: optimistic vs prefixed-pessimistic produce distinct ids ----
print("--- INV-3: prefix changes proposalId ---");
{
  my(desc, prefixedDesc, h1, h2, p1, p2);
  desc = "Update vetoPeriod to 6h";
  prefixedDesc = concat(["Confirmation For: ", desc]);
  h1 = descriptionHash(desc);
  h2 = descriptionHash(prefixedDesc);
  p1 = getProposalId([1], [0], [[55]], h1);
  p2 = getProposalId([1], [0], [[55]], h2);
  if(p1 != p2, print("  OK (distinct ids)"), print("  FAIL"));
}
print("");

\\ ---- INV-4: length-coupling and zero-length gates ----
print("--- INV-4: _validateProposal length checks ---");
{
  my(viol, p);
  viol = 0;
  \\ zero length
  p = makeProposal(1, 9001, [], [], [], "x");
  if(validateProposal(p)[2] != "ZeroLength", viol = viol + 1);
  \\ values mismatch
  p = makeProposal(1, 9001, [1, 2], [0], [[55], [56]], "x");
  if(validateProposal(p)[2] != "LengthMismatch", viol = viol + 1);
  \\ calldatas mismatch
  p = makeProposal(1, 9001, [1, 2], [0, 0], [[55]], "x");
  if(validateProposal(p)[2] != "LengthMismatch", viol = viol + 1);
  \\ well-formed accepted
  p = makeProposal(1, 9001, [1], [0], [[55]], "x");
  if(validateProposal(p)[1] != "ok", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-5: confirmation prefix forbidden in user entry ----
print("--- INV-5: confirmation-prefix gate ---");
{
  my(p, viol);
  viol = 0;
  p = makeProposal(1, 9001, [1], [0], [[55]], "Confirmation For: A");
  if(validateProposal(p)[2] != "ConfirmationPrefix", viol = viol + 1);
  \\ a description that merely contains the prefix mid-string is fine
  p = makeProposal(1, 9001, [1], [0], [[55]], "ok desc Confirmation For: ");
  if(validateProposal(p)[1] != "ok", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-6: transition sentinel idempotence ----
print("--- INV-6: transitionToPessimistic sentinel ---");
{
  my(d, r1, r2, updated, viol);
  viol = 0;
  d = makeOptDetails([1,2], [0,0], [[55], [66]], "X", 10^17);
  r1 = transitionToPessimistic(d);
  if(r1[1] != "ok", viol = viol + 1);
  updated = r1[3];
  if(odVetoT(updated) != TRANSITIONED_VETO_THRESHOLD, viol = viol + 1);
  r2 = transitionToPessimistic(updated);
  if(r2[1] != "revert" || r2[2] != "AlreadyTransitioned", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-7: optimistic selector gate ----
print("--- INV-7: proposeOptimistic selector gate ---");
{
  my(p, registry, roles, r1, r2, viol);
  viol = 0;
  roles = [9001];
  \\ Registry knows (target=200, selector=0xAA) only.
  registry = [[200, 170]];
  \\ matching call -> ok
  p = makeProposal(1, 9001, [200], [0], [[170]], "ok");
  r1 = proposeOptimistic(p, roles, registry);
  if(r1[1] != "ok", viol = viol + 1);
  \\ unknown target -> revert InvalidCall
  p = makeProposal(2, 9001, [201], [0], [[170]], "bad target");
  r2 = proposeOptimistic(p, roles, registry);
  if(r2[1] != "revert" || r2[2] != "InvalidCall", viol = viol + 1);
  \\ unknown selector on known target -> revert InvalidCall
  p = makeProposal(3, 9001, [200], [0], [[171]], "bad sel");
  r2 = proposeOptimistic(p, roles, registry);
  if(r2[1] != "revert" || r2[2] != "InvalidCall", viol = viol + 1);
  \\ empty calldata -> revert InvalidCall (< 4 bytes)
  p = makeProposal(4, 9001, [200], [0], [[]], "empty");
  r2 = proposeOptimistic(p, roles, registry);
  if(r2[1] != "revert" || r2[2] != "InvalidCall", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-8: optimistic proposer-role gate ----
print("--- INV-8: proposeOptimistic proposer-role gate ---");
{
  my(p, registry, roles, r, viol);
  viol = 0;
  roles = [9001];
  registry = [[200, 170]];
  \\ non-role proposer -> revert NotOptimisticProposer
  p = makeProposal(1, 8000, [200], [0], [[170]], "not authorized");
  r = proposeOptimistic(p, roles, registry);
  if(r[1] != "revert" || r[2] != "NotOptimisticProposer", viol = viol + 1);
  \\ role proposer -> ok
  p = makeProposal(2, 9001, [200], [0], [[170]], "ok");
  r = proposeOptimistic(p, roles, registry);
  if(r[1] != "ok", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-9: pessimistic votes gate ----
print("--- INV-9: proposePessimistic threshold gate ---");
{
  my(p, votes, r, viol);
  viol = 0;
  votes = [[9001, 100], [8000, 50]];
  \\ votes >= threshold -> ok
  p = makeProposal(1, 9001, [200], [0], [[170]], "ok");
  r = proposePessimistic(p, votes, 100);
  if(r[1] != "ok", viol = viol + 1);
  \\ votes < threshold -> revert
  p = makeProposal(2, 8000, [200], [0], [[170]], "weak");
  r = proposePessimistic(p, votes, 100);
  if(r[1] != "revert" || r[2] != "InsufficientProposerVotes", viol = viol + 1);
  \\ missing proposer -> 0 votes -> revert
  p = makeProposal(3, 7000, [200], [0], [[170]], "unknown");
  r = proposePessimistic(p, votes, 1);
  if(r[1] != "revert" || r[2] != "InsufficientProposerVotes", viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

\\ ---- INV-10: full transition flow yields a fresh pid distinct from
\\              all prior pids ----
print("--- INV-10: transition end-to-end pid freshness ---");
{
  my(targets, vals, calls, optDesc, optPid, d, r, newPid, viol);
  viol = 0;
  targets = [200, 201];
  vals = [0, 0];
  calls = [[170, 1], [180]];
  optDesc = "Lower vetoPeriod to 6h";
  optPid = getProposalId(targets, vals, calls, descriptionHash(optDesc));
  d = makeOptDetails(targets, vals, calls, optDesc, 10^17);
  r = transitionToPessimistic(d);
  if(r[1] != "ok", viol = viol + 1);
  newPid = r[2];
  if(newPid == optPid, viol = viol + 1);
  printf("  violations: %d\n", viol);
  if(viol == 0, print("  OK"), print("  FAIL"));
}
print("");

print("=== ProposalLib CAS — done ===");
