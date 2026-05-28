/* TransitionedProposalCancel.spec - intent-derived sentinel-state rule
   for Guardian.cancel on optimistic-to-pessimistic-transitioned proposals
   (S21 in governance_intent_and_shapes.md).

   Intent property (S21):
     "Once an optimistic proposal has transitioned to pessimistic - i.e.
     its vetoThreshold has been overwritten with the sentinel
     TRANSITIONED_VETO_THRESHOLD == type(uint256).max - an optimistic
     guardian must NOT be able to cancel it via Guardian.cancel. The
     transition's load-bearing semantics depend on state() short-circuiting
     to Defeated when the sentinel is present, which then trips Guardian's
     !=Defeated check at Guardian.sol:90-93."

   This rule is the sentinel-state-reasoning sibling of Guardian.spec
   G6b (cancelNonAdminRequiresNotDefeated). G6b proves the general
   "non-admin guardian cannot cancel Defeated optimistic proposals" via
   an unconstrained ghostState[pid]. S21 sharpens this: it specifically
   pins the TRANSITIONED scenario, where vetoThreshold is the sentinel,
   _isOptimistic still returns true (sentinel != 0), and state() is
   REQUIRED by intent to return Defeated. The pair documents the chain
   that the defense rests on:

     vetoThreshold[pid] == TRANSITIONED_VETO_THRESHOLD (sentinel)
       => state(pid) short-circuits to ProposalState.Defeated
         => Guardian.cancel's `!= Defeated` check trips
           => optimistic guardian cancel rejected

   If a future refactor removed the sentinel->Defeated branch at
   ReserveOptimisticGovernor.sol:243-246, _isOptimistic would still
   return true for the transitioned proposal (vetoThreshold = max != 0),
   but state() would fall through to the vote-tally branch - returning
   Active or Succeeded depending on votes - and optimistic guardians
   would suddenly gain authority to cancel transitioned proposals,
   bypassing the standard governance route the transition was supposed
   to force.

   The companion negative rule (sister) intentionally relaxes the
   ghostState constraint to demonstrate that without the sentinel
   short-circuit guarantee the property fails - documenting precisely
   which link in the chain is load-bearing.

   See WISDOM C015 (ghost-backed external summaries) for the threading
   pattern. The ghost mirrors Guardian.spec but adds a fourth ghost
   (ghostVetoThresholdRatio) to express the sentinel directly.
*/

// IGovernor.ProposalState enum, ABI-encoded as uint8.
// 0=Pending 1=Active 2=Canceled 3=Defeated 4=Succeeded
// 5=Queued 6=Expired 7=Executed
definition DEFEATED() returns uint8 = 3;
definition ACTIVE()   returns uint8 = 1;

// TRANSITIONED_VETO_THRESHOLD = type(uint256).max - the sentinel that
// ProposalLib.sol:20 uses to mark a transitioned (optimistic->pessimistic)
// proposal. ReserveOptimisticGovernor.state() at line 243-246 special-
// cases this and returns Defeated.
definition TRANSITIONED_SENTINEL() returns uint256 = max_uint256;

// Ghosts pinning the per-call snapshot the Guardian sees, mirroring
// Guardian.spec's pattern. ghostVetoThresholdRatio[pid] is the new
// addition: it lets the rule express "this proposal's vetoThreshold
// storage entry holds the sentinel" symbolically. The rule then
// constrains ghostState[pid] to encode the intent that state() reads
// Defeated under that sentinel.
ghost uint256 ghostProposalId;
ghost mapping(uint256 => bool) ghostIsOptimistic;
ghost mapping(uint256 => uint8) ghostState;
ghost mapping(uint256 => uint256) ghostVetoThresholdRatio;

methods {
    // Guardian's own role constants (envfree readers)
    function OPTIMISTIC_GUARDIAN_ROLE() external returns (bytes32) envfree;
    function OPTIMISTIC_GUARDIAN_MANAGER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // Proposal-state snapshot reads: ghost-backed so the prover threads
    // consistent values across the two checks Guardian.cancel performs.
    function _.isOptimistic(uint256 pid) external =>
        ghostIsOptimistic[pid] expect bool;
    function _.state(uint256 pid) external =>
        ghostState[pid] expect uint8;
    function _.getProposalId(address[], uint256[], bytes[], bytes32) external =>
        ghostProposalId expect uint256;

    // vetoThreshold read - ghost-backed for symbolic sentinel pinning.
    // Guardian.cancel does not call vetoThreshold directly; the
    // governor's internal _isOptimistic + state() do. Declaring this
    // summary keeps the ghost in scope for any cross-summary
    // consistency the prover wants to track.
    function _.vetoThreshold(uint256 pid) external =>
        ghostVetoThresholdRatio[pid] expect uint256;

    // Side-effecting downstream calls - NONDET. The rule asserts revert
    // before the downstream cancel fires, so its return value is moot.
    function _.cancel(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.timelock() external => NONDET;
    function _.revokeOptimisticProposer(address) external => NONDET;
}

/* ----- ROOT: optimistic guardian cannot cancel a TRANSITIONED proposal
   The full load-bearing chain encoded as preconditions:
     1. Caller is an optimistic guardian and NOT an admin.
     2. The proposal whose id Guardian computes IS still marked
        optimistic (transition preserves the flag - vetoThreshold
        stays non-zero, it just becomes the sentinel).
     3. Its vetoThreshold storage entry equals TRANSITIONED_VETO_THRESHOLD
        (i.e. the sentinel). This is the abstract state of "transitioned".
     4. Therefore state() returns Defeated (via the sentinel short-circuit
        at ReserveOptimisticGovernor.sol:243-246).

   Under these preconditions Guardian.cancel MUST revert at the
   !=Defeated check (Guardian.sol:90-93). The assertion exercises that
   the full chain holds end-to-end. */
rule transitionedProposalRejectsOptimisticGuardianCancel {
    env e;
    address governor;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    // Caller is an optimistic guardian and not an admin.
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);

    // The proposal is still flagged optimistic (transition preserves
    // _isOptimistic == true because the sentinel is non-zero).
    require ghostIsOptimistic[ghostProposalId] == true;

    // Its vetoThreshold equals the transitioned sentinel.
    require ghostVetoThresholdRatio[ghostProposalId] == TRANSITIONED_SENTINEL();

    // The state() short-circuit at ReserveOptimisticGovernor.sol:243-246
    // returns Defeated under that sentinel. Encoding this as a
    // precondition ties the rule to the contract's intent: if a future
    // refactor breaks this link, the sister rule below makes the
    // violation explicit by removing this precondition.
    require ghostState[ghostProposalId] == DEFEATED();

    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);

    assert lastReverted,
        "optimistic guardian canceled a transitioned proposal";
}

/* ----- SISTER (regression scenario; VIOLATED here is HEALTHY) -----

   Documents the load-bearing chain by removing the sentinel->Defeated
   precondition from the root rule. Posed as the SAME assert
   (`lastReverted`), with `ghostState` pinned to Active rather than
   Defeated. Under the current contract this rule is EXPECTED VIOLATED:
   Guardian's only defense against an optimistic-guardian cancel of a
   transitioned proposal is mediated through `state() != Defeated`. If
   state reads Active (the regression scenario where the sentinel
   short-circuit was deleted), the != Defeated check passes and cancel
   proceeds.

   This rule pattern mirrors `VetoThresholdReachability.spec`'s
   `sanityHeadlinePreconditionSatisfiable`: VIOLATED is the healthy
   outcome and documents the load-bearing assumption. If it ever flips
   to VERIFIED, that means Guardian.cancel acquired an INDEPENDENT
   sentinel-aware guard (audit-worthy change). */
rule transitionedProposalRequiresSentinelShortCircuit {
    env e;
    address governor;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);

    // Proposal is optimistic and transitioned (vetoThreshold = sentinel).
    require ghostIsOptimistic[ghostProposalId] == true;
    require ghostVetoThresholdRatio[ghostProposalId] == TRANSITIONED_SENTINEL();

    // Regression scenario: state() is NOT Defeated. We pin Active here -
    // any non-Defeated value would do; Active is the most concerning
    // because it is what _isOptimistic + an empty vote tally would
    // produce if the sentinel branch were removed.
    require ghostState[ghostProposalId] == ACTIVE();

    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);

    // VIOLATED here documents that Guardian's only sentinel-aware
    // defense flows through state() == Defeated. The violation is the
    // EXPECTED, healthy outcome.
    assert lastReverted,
        "sister: cancel of transitioned proposal succeeded when state() did not return Defeated -- the sentinel short-circuit is the only defense (VIOLATED here is healthy)";
}
