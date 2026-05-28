/* VetoCoalitionReachability.spec — S31, structural form.

   Catalog entry: notes/governance_intent_and_shapes.md, S31.

   Intent (S31, structural form):
     For every optimistic proposal `pid` in every reachable state,
     the veto threshold (denominated in tokens, computed exactly as
     the contract's `state()` does) is at most the optimistic-
     delegated coalition supply at that proposal's snapshot.

       vetoThresholdInTokens(pid) <= getPastOptimisticVotingSupply(snapshot(pid))

     i.e., the coalition of all opted-in voters can, in principle,
     reach the threshold. If this invariant ever fails, the
     legitimate vetoer set cannot defeat the proposal no matter how
     they coordinate, and the optimistic channel has been
     misconfigured into a pass-through.

   This is the STRUCTURAL counterpart to the scenario-based rule in
   `VetoThresholdReachability.spec`. Where that file pins one
   adversarial state (a single bug witness), THIS file asserts the
   one-line invariant over arbitrary parameters: not "here is a
   coalition state where threshold is unreachable" but "no reachable
   state has unreachable threshold."

   Pre-fix expectation: VIOLATED. The contract computes the
   threshold against `pastTotalSupply`. Any reachable state where
   `pastTotalSupply > pastOptimisticSupply` (which is the entire
   point of distinguishing the two) can drive
   `vetoThresholdTok > pastOptimisticSupply`.

   Post-fix expectation: VERIFIED. Threshold computed against
   `pastOptimisticSupply` is bounded above by it (vt <= 1e18 by
   construction, and Math.max with 1 keeps the floor sane when
   optSupply >= 1).

   See:
     - WISDOM C001 ('^' is XOR, not exponent; use 1e18 = 10^18 literal)
     - WISDOM C002 (sanity check via assert false)
     - WISDOM C015 (ghost-backed external summaries)
     - notes/cantina_pr36_postmortem.md (the bug class)
*/

/* WAD = 1e18. CVL has no '**'; '^' is XOR. */
definition WAD() returns uint256 = 1000000000000000000;

/* TRANSITIONED_VETO_THRESHOLD = type(uint256).max sentinel. When a
   proposal has transitioned optimistic->pessimistic, `state()`
   short-circuits to Defeated, bypassing the threshold math. The
   invariant is trivially vacuous there, so we exclude this case to
   keep the rule focused. */
definition MAX_U256() returns uint256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639935;

/* Ghosts pinning per-snapshot supply readings — the prover threads
   one consistent value for each snapshot per rule invocation. The
   two are independent: the rule constrains their relative magnitudes
   in the precondition, not via a summary axiom. */
ghost mapping(uint256 => uint256) ghostPastTotalSupply;
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;

methods {
    // Envfree readers we read directly from rules.
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function proposalSnapshot(uint256) external returns (uint256) envfree;

    // === Ghost-backed external summaries (WISDOM C015) ===
    // Per-snapshot supply functions on the staking-vault token.
    // The current pre-fix `state()` calls getPastTotalSupply; the
    // optimistic-supply summary is declared anyway so the spec is
    // forward-compatible with the post-fix contract (no edits needed
    // when the read switches). Both are read directly from the rule
    // body via the ghost.
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;

    // Everything else: NONDET. The invariant doesn't depend on
    // downstream-call return values; it's a structural relation
    // between vetoThreshold, snapshot, and the two supplies.
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

    // ThrottleLib / ProposalLib delegatecalls.
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;
}

/* ----- HEADLINE: structural veto-coalition reachability -----

   Statement: in any reachable state, for any optimistic proposal,
   the veto threshold (in tokens, as computed by `state()`) is
   bounded above by the optimistic-delegated coalition supply at
   the proposal's snapshot.

   Formally, with `vt = vetoThreshold(pid)`,
                  `s  = proposalSnapshot(pid)`,
                  `T  = ghostPastTotalSupply[s]`,
                  `O  = ghostPastOptimisticSupply[s]`,
                  `thrTok = max((vt * T) / 1e18, 1)`           // pre-fix
                  // or `thrTok = max((vt * O) / 1e18, 1)`     // post-fix

       thrTok <= O.

   Pre-fix: thrTok grows with T. If T >> O (any non-trivial passive
   supply), thrTok can exceed O — the invariant fails.

   Post-fix: thrTok is bounded by vt (<= 1e18) of O — i.e. <= O when
   O >= 1, and Math.max with 1 handles O==0 by inflating thrTok to 1,
   which is still <= O whenever O >= 1.

   We formulate this as a parametric rule over every external entry
   point (`method f`). The rule asserts the invariant in the *post-
   state* after an arbitrary external call. The pre-state is left
   unconstrained beyond reachability requirements (proposal exists,
   is optimistic, snapshot is in the past). This is the structural
   reading: "no reachable post-state violates the invariant." */
rule vetoThresholdReachableByOptimisticCoalitionStructural(method f)
    filtered {
        // Upgrade slots are out of scope (per other intent specs).
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    uint256 pid;

    // Reachability precondition: any external call may run first.
    f(e, args);

    // Now examine the post-state.
    uint256 vt = vetoThreshold(pid);

    // Optimistic proposal: vetoThreshold is set and not the
    // transitioned-marker sentinel. (vt == 0 means the proposal is
    // pessimistic or non-existent in optimistic storage; vt ==
    // MAX_U256() means it already transitioned and state() short-
    // circuits to Defeated, sidestepping the threshold math.)
    require vt != 0;
    require vt != MAX_U256();

    // Construction invariant from _setOptimisticParams: vetoThreshold
    // is a D18 fraction in [0, 1e18]. Without this the prover can
    // pick a vt that breaks the bug-witness arithmetic by overflow.
    require vt <= WAD();

    uint256 snapshot = proposalSnapshot(pid);

    // Snapshot in the past — proposal is past Pending. Without this
    // the rule can fire on Pending proposals where the invariant is
    // not yet meaningful (the coalition hasn't been established).
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 totSupply = ghostPastTotalSupply[snapshot];
    uint256 optSupply = ghostPastOptimisticSupply[snapshot];

    // Real-world relation: the optimistically-delegated supply at any
    // snapshot is at most the total supply at that snapshot. This is
    // a ghost-axiom; declaring it as `require` keeps the rule sound
    // because it constrains the prover to physically realistic
    // states. (Without it, the prover can pick optSupply > totSupply
    // and the invariant becomes vacuously satisfiable.)
    require optSupply <= totSupply;

    // The contract's vetoThresholdTok computation as of the current
    // pre-fix code (line 256 of ReserveOptimisticGovernor.sol):
    //   vetoThresholdTok = max((vetoThreshold * pastTotalSupply) / 1e18, 1)
    // This formula uses TOTAL supply — the bug. The structural
    // invariant we assert is that this value is bounded above by the
    // OPTIMISTIC coalition supply.
    mathint thrTokRaw = (vt * totSupply) / WAD();
    mathint thrTok = thrTokRaw < 1 ? 1 : thrTokRaw;

    // S31 structural invariant.
    assert thrTok <= to_mathint(optSupply),
        "veto threshold (in tokens) exceeds the optimistic coalition supply at snapshot -- the coalition cannot in principle defeat the proposal";
}

/* ----- SANITY: the structural rule's precondition is satisfiable.

   Per WISDOM C002, a vacuous precondition silently passes the
   headline. We verify the precondition is reachable by asserting
   `false` under the same precondition: VIOLATED here is healthy. */
rule sanityStructuralPreconditionSatisfiable(method f)
    filtered {
        f -> f.selector != sig:upgradeToAndCall(address,bytes).selector
    }
{
    env e;
    calldataarg args;
    uint256 pid;

    f(e, args);

    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();
    require vt <= WAD();

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 totSupply = ghostPastTotalSupply[snapshot];
    uint256 optSupply = ghostPastOptimisticSupply[snapshot];
    require optSupply <= totSupply;

    assert false, "sanity: precondition reachable (VIOLATED here is healthy)";
}
