/* WrongSnapshotTime.spec -- S2 wrong-snapshot-time intent rule.

   Catalog reference: notes/governance_intent_and_shapes.md, S2.

   Intent (S2 form):
     A function that reads time-keyed external state must read at the
     SEMANTICALLY CORRECT timepoint. The optimistic-veto state machine
     pins one timepoint per proposal -- the proposal's `voteStart`
     (a.k.a. `proposalSnapshot(pid)`). Every supply/votes read used to
     resolve `state(pid)` must be against THAT timepoint, never against
     `block.timestamp - 1` or any other "now"-ish moment.

   Concrete site under scrutiny:
     ReserveOptimisticGovernor.state() at
     contracts/governance/ReserveOptimisticGovernor.sol:249 reads
        token().getPastTotalSupply(snapshot)
     where `snapshot = proposalCore.voteStart`. Compare with
     ReserveOptimisticGovernor.proposalThreshold() at line 311 which
     reads
        token().getPastTotalSupply(block.timestamp - 1)
     -- a different timepoint. The two reads are correct for their
     respective intents (state() pins to the proposal's snapshot;
     proposalThreshold() pins to "now-1" at the moment of the
     propose() call), but a future refactor that swaps one for the
     other would break the state-machine semantics silently.

   Two-ghost C017 pattern:
     We back getPastTotalSupply with a SINGLE timepoint-keyed ghost
     mapping, then constrain TWO specific keys -- snapshot and
     (block.timestamp - 1) -- to disagree by a large margin. The
     assertion checks that state(pid)'s outcome depends only on the
     snapshot-keyed read, not the now-1-keyed read.

   Pose: the snapshot-keyed supply is small (threshold reachable);
   the now-1-keyed supply is huge (threshold unreachable). Coalition
   has cast all-against votes meeting the snapshot-supply threshold.

   Expected outcome on the current code:
     VERIFIED -- state() reads at snapshot, sees the small supply,
     and returns Defeated.

   If a regression switched the read to (block.timestamp - 1):
     VIOLATED -- the function would see the huge supply, the
     threshold would not be met, and state() would return Active or
     Succeeded.

   See:
     - WISDOM C001 ('^' is XOR, not exponent; use 1e18 = 10^18 literal)
     - WISDOM C002 (sanity check via assert false)
     - WISDOM C015 (ghost-backed external summaries)
     - WISDOM C017 (two-ghost summary divergence)
     - VetoThresholdReachability.spec (sibling rule, same external surface)
*/

/* IGovernor.ProposalState enum, ABI-encoded as uint8.
   0=Pending 1=Active 2=Canceled 3=Defeated 4=Succeeded 5=Queued 6=Expired 7=Executed */
definition PENDING()   returns uint8 = 0;
definition ACTIVE()    returns uint8 = 1;
definition CANCELED()  returns uint8 = 2;
definition DEFEATED()  returns uint8 = 3;
definition SUCCEEDED() returns uint8 = 4;
definition EXECUTED()  returns uint8 = 7;

/* WAD = 1e18. CVL has no '**'; '^' is XOR (WISDOM C001). Use base-10. */
definition WAD() returns uint256 = 1000000000000000000;

/* TRANSITIONED_VETO_THRESHOLD sentinel value. state() short-circuits
   to Defeated for transitioned proposals, bypassing the snapshot
   read -- we exclude this case so the rule pins the supply-driven
   branch. */
definition MAX_U256() returns uint256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639935;

/* Single timepoint-keyed ghost backing getPastTotalSupply. The rule
   constrains two specific keys to disagree, surfacing any read that
   uses the wrong timepoint (C017 generalization: distinct call sites
   of the same function are distinguished by argument value, not by
   summary identity). */
ghost mapping(uint256 => uint256) ghostPastTotalSupply;

/* Companion ghost for the optimistic-supply read. Declared so the
   spec is forward-compatible with the PR #36 fix that swaps the
   state() read to getPastOptimisticVotingSupply. */
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;

methods {
    // Envfree readers we read directly from the rule.
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function proposalProposer(uint256) external returns (address) envfree;
    function proposalVotes(uint256) external returns (uint256, uint256, uint256) envfree;
    function proposalSnapshot(uint256) external returns (uint256) envfree;

    // === Ghost-backed external summaries (WISDOM C015, C017) ===
    // The current state() calls getPastTotalSupply(snapshot). The
    // ghost keys distinguish snapshot-time reads from now-1 reads
    // when the rule probes both via require statements below.
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;

    // Heavy NONDET on every other external surface (mirrors the
    // VetoThresholdReachability.spec methods block).
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

    // ThrottleLib / ProposalLib delegatecalls -- irrelevant to state().
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;
}

/* ----- HEADLINE: state() reads supply at the proposal's snapshot -----

   Pose a state where:
     - The proposal `pid` is optimistic (vt != 0, vt != sentinel).
     - The snapshot is in the past (proposal is past Pending).
     - The supply AT THE SNAPSHOT is small but non-zero.
     - The supply at (block.timestamp - 1) is enormous -- big enough
       that, if the contract erroneously used IT, the threshold
       would be unreachable.
     - Against-votes equal the snapshot supply (full legitimate
       coalition vote).

   Under the SNAPSHOT-correct reading: threshold = max((vt*small)/1e18, 1)
     <= small <= againstVotes; the contract returns Defeated.
   Under the WRONG (now-1) reading: threshold = (vt*huge)/1e18 > small
     == againstVotes; the contract returns Active (or Succeeded after
     deadline).

   Assertion: state(pid) returns Defeated. The current code reads
   at snapshot, so the rule VERIFIES. A regression that swaps the
   read to (block.timestamp - 1) would VIOLATE the rule.

   Regression-guard value: pins the load-bearing semantic that
   state()'s denominator is the proposal's own snapshot, not the
   current block. */
rule stateReadsSupplyAtProposalSnapshot {
    env e;
    uint256 pid;

    // Proposal is optimistic (storage marks it so) and not the
    // transitioned-marker sentinel (which short-circuits state()
    // to Defeated regardless of supply -- vacuous for this rule).
    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();
    require vt <= WAD(); // construction invariant from _setOptimisticParams
    require vt >= 1;     // bug-witness needs a non-zero ratio

    // Snapshot in the past (proposal past Pending).
    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;             // proposal exists
    require snapshot < e.block.timestamp;

    // The two timepoints under test. (block.timestamp - 1) is the
    // "wrong" snapshot a regression might use; we constrain it to
    // be distinct from the proposal's snapshot so the prover can't
    // collapse the two reads into one ghost lookup.
    uint256 nowMinusOne = require_uint256(e.block.timestamp - 1);
    require snapshot != nowMinusOne;

    // The snapshot-time supply: small but non-zero, so the threshold
    // applied to it is reachable by a small coalition.
    uint256 supplyAtSnapshot = ghostPastTotalSupply[snapshot];
    require supplyAtSnapshot > 0;
    require supplyAtSnapshot <= 1000; // small enough that (vt*supply)/1e18 == 0
                                      // (then Math.max(_, 1) == 1)

    // The now-1 supply: huge, so the threshold applied to it would
    // be unreachable. Choose a value where (vt * supply) / 1e18 is
    // strictly larger than the snapshot supply -- the divergence
    // the bug-witness depends on.
    uint256 supplyAtNowMinusOne = ghostPastTotalSupply[nowMinusOne];
    // vt >= 1, so vt * supplyAtNowMinusOne >= supplyAtNowMinusOne. For
    // (vt * x) / 1e18 to exceed supplyAtSnapshot=1000, we need
    // vt * x > 1000 * 1e18. With vt minimal (1) we need x > 1000e18.
    require supplyAtNowMinusOne > 1000 * WAD();

    // Coalition has fully voted Against, matching the snapshot supply.
    // Under the snapshot reading: threshold = max((vt*1000)/1e18, 1).
    // For vt <= 1e18 and supplyAtSnapshot <= 1000, (vt*supplyAtSnapshot)
    // < 1e18 * 1000 / 1e18 = 1000 -- so threshold <= 1000 <= supply.
    // Specifically, threshold rounds down to 0 for small vt, then
    // Math.max bumps it to 1. Against votes of 1 (or more) defeats.
    uint256 againstVotes;
    uint256 forVotes;
    uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == supplyAtSnapshot;
    require againstVotes >= 1; // ensure the >= 1 threshold is met

    // Read the contract's current state for this proposal.
    IGovernor.ProposalState s = state(e, pid);

    // Under the snapshot-correct reading, state == Defeated.
    // A regression to now-1 would yield Active or Succeeded.
    // Executed/Canceled are unreachable from the preconditions but
    // are accepted as benign (the proposal is settled out of the
    // bug-window either way).
    assert s == IGovernor.ProposalState.Defeated
        || s == IGovernor.ProposalState.Executed
        || s == IGovernor.ProposalState.Canceled,
        "state() returned Active/Succeeded under the snapshot-correct supply -- read used a different timepoint than proposalSnapshot(pid)";
}

/* ----- SANITY CHECK: the precondition is satisfiable -----

   Per WISDOM C002, a vacuous precondition silently passes. This
   sanity check asserts false under the same precondition; VIOLATED
   here means the precondition is reachable (healthy). If this
   sanity check VERIFIES, the headline rule's pass would be
   meaningless. */
rule sanityHeadlinePreconditionSatisfiable {
    env e;
    uint256 pid;

    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();
    require vt <= WAD();
    require vt >= 1;

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 nowMinusOne = require_uint256(e.block.timestamp - 1);
    require snapshot != nowMinusOne;

    uint256 supplyAtSnapshot = ghostPastTotalSupply[snapshot];
    require supplyAtSnapshot > 0;
    require supplyAtSnapshot <= 1000;

    uint256 supplyAtNowMinusOne = ghostPastTotalSupply[nowMinusOne];
    require supplyAtNowMinusOne > 1000 * WAD();

    uint256 againstVotes;
    uint256 forVotes;
    uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == supplyAtSnapshot;
    require againstVotes >= 1;

    assert false, "sanity: precondition reachable (VIOLATED here is healthy)";
}
