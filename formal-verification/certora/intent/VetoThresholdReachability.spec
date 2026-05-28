/* VetoThresholdReachability.spec — intent-derived Certora rule for the
   Cantina PR #36 wrong-spec finding.

   Intent property (the user-facing semantics this rule encodes):
     "The veto threshold must be reachable by the supply that can actually
      cast vetoes. A non-zero coalition of all eligible vetoers should be
      able to defeat the proposal."

   This rule is derived from the *intent* of the optimistic-veto design,
   not from inspection of ReserveOptimisticGovernor.sol. It distinguishes
   total token supply (pastTotalSupply) from the subset that can cast
   votes (pastOptimisticVotingSupply — only tokens whose holders set a
   non-zero optimistic delegate).

   On the pre-fix contract (the current state of this branch), the
   denominator of the veto threshold is `getPastTotalSupply(snapshot)`.
   So the threshold can be set so high (relative to the eligible
   electorate) that no coalition of all eligible vetoers can reach it.
   The rule poses exactly that adversarial state and asserts that the
   proposal is nevertheless settled (not Active, not Succeeded).

   On the post-fix contract (PR #36), the denominator switches to
   `getPastOptimisticVotingSupply(snapshot)`, the eligible coalition
   trivially reaches the threshold, and the rule verifies.

   Outcome on current pre-fix branch: VIOLATED — the rule is doing its job.

   See notes/cantina_pr36_postmortem.md for the postmortem and WISDOM
   C015 for the ghost-backed external-summary pattern. Mirror of the
   adversarial test from PR #36:
   `test_optimisticProposal_vetoThresholdUsesOptimisticDelegatedSupply`.
*/

/* IGovernor.ProposalState enum, ABI-encoded as uint8.
   0=Pending 1=Active 2=Canceled 3=Defeated 4=Succeeded 5=Queued 6=Expired 7=Executed */
definition PENDING()   returns uint8 = 0;
definition ACTIVE()    returns uint8 = 1;
definition CANCELED()  returns uint8 = 2;
definition DEFEATED()  returns uint8 = 3;
definition SUCCEEDED() returns uint8 = 4;
definition EXECUTED()  returns uint8 = 7;

/* WAD = 1e18. CVL has no `**`; `^` is XOR (WISDOM C001). Use base-10. */
definition WAD() returns uint256 = 1000000000000000000;

/* TRANSITIONED_VETO_THRESHOLD = type(uint256).max — the sentinel value
   ProposalLib.sol uses to mark a proposal that already transitioned
   optimistic -> pessimistic. state() short-circuits to Defeated when
   vetoThreshold[pid] equals this sentinel, so the rule must exclude it. */
definition MAX_U256() returns uint256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639935;

/* Ghost mappings distinguishing total supply from optimistic voting
   supply at a given snapshot. These back the external summaries below
   so the prover threads a single, consistent value per snapshot per
   rule invocation. The two ghosts are independent: the rule constrains
   their relative magnitudes to set up the bug scenario. */
ghost mapping(uint256 => uint256) ghostPastTotalSupply;
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;

methods {
    // Envfree readers we read directly from the rule.
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function proposalProposer(uint256) external returns (address) envfree;
    function proposalVotes(uint256) external returns (uint256, uint256, uint256) envfree;
    function proposalSnapshot(uint256) external returns (uint256) envfree;


    // === Ghost-backed external summaries (WISDOM C015) ===
    // The CURRENT contract calls getPastTotalSupply only. The summary on
    // getPastOptimisticVotingSupply is declared anyway: it's the read the
    // fixed contract would perform, and declaring it now makes the rule
    // forward-compatible across pre-fix and post-fix builds without spec
    // edits. On the pre-fix contract the second summary simply never
    // fires; the ghost is still defined and the rule reads it directly.
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;

    // Heavy NONDET on everything else we don't model. The rule's
    // assertion threads through `state()` which only reads the supply
    // (above), proposal storage (real), and proposalVotes (real OZ
    // storage that Certora explores freely).
    function _.getPastVotes(address, uint256) external => NONDET;
    function _.getPastOptimisticVotes(address, uint256) external => NONDET;
    function _.clock() external => NONDET;
    function _.CLOCK_MODE() external => NONDET;
    function _.hasRole(bytes32, address) external => NONDET;
    function _.scheduleBatch(address[], uint256[], bytes[], bytes32, bytes32, uint256) external => NONDET;
    function _.executeBatch(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;
    function _.executeBatchBypass(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;
    function _.cancel(bytes32) external => NONDET;
    function _.cancel(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.isOperationPending(bytes32) external => NONDET;
    function _.isOperationReady(bytes32) external => NONDET;
    function _.isOperationDone(bytes32) external => NONDET;
    function _.getMinDelay() external => NONDET;
    function _.getTimestamp(bytes32) external => NONDET;
    function _.hashOperationBatch(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;
    function _.isAllowed(address, bytes4) external => NONDET;

    // ThrottleLib / ProposalLib delegatecalls — irrelevant to state().
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;
}

/* ----- HEADLINE RULE: veto threshold reachable by eligible vetoers -----

   Pose a state where:
     - The proposal `pid` is optimistic and past its snapshot.
     - The eligible voting supply (optimistic-delegated tokens at
       snapshot) is strictly less than the total token supply at
       snapshot. I.e., passive (undelegated) holders exist.
     - The eligible coalition has fully voted Against (vetoVotes ==
       optimisticSupply > 0).
     - The veto threshold, applied to the eligible supply (the
       PR #36 semantics), would be met by the coalition.
     - The veto threshold, applied to the total supply (the current
       buggy semantics), is STRICTLY GREATER than the coalition's vote
       count — i.e., the bug renders Defeated unreachable.

   Conclusion: state(pid) must not still be Active or Succeeded —
   the legitimate coalition's veto must have settled the proposal.

   On the pre-fix contract: VIOLATED. The CEX will pin a scenario
   where vetoVotes == optimisticSupply but state == Active/Succeeded
   because vetoThresholdTok was computed against totalSupply.

   On the post-fix contract: VERIFIED. The eligible coalition meets
   the (now-correct) threshold and the contract returns Defeated. */
rule vetoThresholdReachableByEligibleVotersHeadline {
    env e;
    uint256 pid;

    // Proposal is optimistic (vetoThreshold storage entry is non-zero
    // and not the transitioned-marker sentinel).
    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();
    require vt <= WAD(); // construction invariant from _setOptimisticParams

    // Snapshot in the past relative to the block we're evaluating at.
    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;            // proposal exists
    require snapshot < e.block.timestamp; // past Pending

    uint256 optSupply = ghostPastOptimisticSupply[snapshot];
    uint256 totSupply = ghostPastTotalSupply[snapshot];

    // The "passive holders" scenario: eligible vetoers are a strict
    // subset of total supply. Both are non-zero.
    require optSupply > 0;
    require totSupply > 0;
    require optSupply < totSupply;

    // Coalition fully voted Against — this is the maximum legitimate
    // veto pressure the system can ever produce.
    uint256 againstVotes;
    uint256 forVotes;
    uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == optSupply;

    // Under the FIXED contract semantics, the coalition would meet
    // the threshold. (vt <= 1e18 implies vt*optSupply/1e18 <= optSupply,
    // and optSupply >= 1, so this holds automatically — but stating it
    // explicitly documents the intent and guards against pathological
    // `optSupply == 0` paths the prover might otherwise pick.)
    mathint thresholdTokFixed = (vt * optSupply) / WAD();
    require optSupply >= thresholdTokFixed;
    require optSupply >= 1;

    // Under the CURRENT (buggy) contract semantics, the coalition does
    // NOT meet the threshold. This is the bug-exposing precondition.
    mathint thresholdTokBuggy = (vt * totSupply) / WAD();
    require optSupply < thresholdTokBuggy;

    // Read the contract's current state for this proposal. The state()
    // override calls getPastTotalSupply(snapshot) — which our ghost
    // backs — and reads proposalVotes(pid) — which we've constrained.
    // Use the qualified enum type (CVL enum-handling pattern).
    IGovernor.ProposalState s = state(e, pid);

    // The settled-or-defeated outcomes are acceptable; Active and
    // Succeeded are the bug-signaling states. (Pending is excluded by
    // the snapshot precondition; Executed/Canceled imply the proposal
    // is already off the path — we accept those for soundness even
    // though they aren't reachable from this precondition without
    // prior calls.)
    assert s != IGovernor.ProposalState.Active
        && s != IGovernor.ProposalState.Succeeded,
        "eligible vetoer coalition could not settle proposal -- veto threshold unreachable against optimistic supply";
}

/* ----- SANITY CHECK: the rule's precondition is satisfiable -----
   A "vacuous-precondition" trap would silently pass the headline rule.
   This sanity check asserts FALSE under the same precondition: if the
   precondition is satisfiable the sanity check reports VIOLATED (which
   is the expected, healthy outcome per WISDOM C002). If the
   precondition were vacuous, this would VERIFY and we'd know the
   headline rule's pass is meaningless. */
rule sanityHeadlinePreconditionSatisfiable {
    env e;
    uint256 pid;

    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();
    require vt <= WAD();

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 optSupply = ghostPastOptimisticSupply[snapshot];
    uint256 totSupply = ghostPastTotalSupply[snapshot];
    require optSupply > 0;
    require totSupply > 0;
    require optSupply < totSupply;

    uint256 againstVotes;
    uint256 forVotes;
    uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == optSupply;

    mathint thresholdTokFixed = (vt * optSupply) / WAD();
    require optSupply >= thresholdTokFixed;
    require optSupply >= 1;

    mathint thresholdTokBuggy = (vt * totSupply) / WAD();
    require optSupply < thresholdTokBuggy;

    assert false, "sanity: precondition reachable (VIOLATED here is healthy)";
}
