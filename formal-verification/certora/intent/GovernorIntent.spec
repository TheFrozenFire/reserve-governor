/* GovernorIntent.spec - intent-derived auth-discriminator rule for
   ReserveOptimisticGovernor.sol.

   See formal-verification/certora/intent/AuthDiscriminator.md for the
   methodology background.

   Property proved:
     ID4   setOptimisticParams(newParams) does NOT mutate the
           per-proposal vetoThreshold(pid) for any pid already present
           in optimisticProposalDetails. The global params are read at
           proposal-creation time and snapshotted into the per-proposal
           storage; future setOptimisticParams calls take effect on
           FUTURE proposals only.

   Why this is "intent-derived":
     The existing Governor.spec R3 proves "setOptimisticParams requires
     onlyGovernance" — a syntactic auth gate. The intent-derived form
     asks a different question: even when the governance-executor call
     succeeds, does the new threshold leak backward into already-
     created proposals?

     Threat: a proposer (or any actor with governance-execute power via
     the timelock) could otherwise game live vetoes by retroactively
     raising the threshold on an unfavourable optimistic proposal mid-
     voteperiod. The contract's defence is the snapshot inside
     proposeOptimistic (ReserveOptimisticGovernor.sol:161-167), which
     captures optimisticParams.vetoThreshold at creation. This rule
     pins that defence as a non-interference property: a global-params
     write does not perturb any per-proposal vetoThreshold slot.

     Coverage gap closed: a refactor that read `optimisticParams`
     directly from `state()` (instead of the snapshotted
     `vetoThreshold(pid)`) would still satisfy R3-R16 but would
     violate this rule.

   CVL shape:
     - Snapshot vetoThreshold(pid) before the setter.
     - Call setOptimisticParams with arbitrary new params (constrained
       to the valid range so the call itself does not revert).
     - Assert vetoThreshold(pid) is unchanged.

     We use the same self-timelock harness as Governor.spec R10-R12
     to satisfy onlyGovernance and skip the OZ deque-pop branch.
*/

methods {
    // Reserve overlay setter under test.
    function setOptimisticParams(IReserveOptimisticGovernor.OptimisticGovernanceParams) external;

    // Envfree readers.
    function timelock() external returns (address) envfree;
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function optimisticParams() external returns (uint48, uint32, uint256) envfree;

    // NONDET summaries mirroring Governor.spec.
    // Library external functions (delegatecalled).
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;

    // Token / votes.
    function _.getPastTotalSupply(uint256) external => NONDET;
    function _.getPastVotes(address, uint256) external => NONDET;
    function _.getPastOptimisticVotes(address, uint256) external => NONDET;
    function _.clock() external => NONDET;
    function _.CLOCK_MODE() external => NONDET;

    // Timelock interactions.
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
}

/* ----- ID4: setOptimisticParams does not perturb existing
   per-proposal vetoThreshold -----

   For any pid already in optimisticProposalDetails (vetoThreshold > 0
   pre-call), no successful setOptimisticParams call mutates that pid's
   vetoThreshold. The snapshot inside proposeOptimistic is the
   integrity boundary; this rule verifies the global-params setter
   stays on the correct side of it.

   Setter precondition wiring (mirrors Governor.spec R12):
     - msg.sender == this and timelock() == this so onlyGovernance
       passes and the OZ deque-pop branch is skipped.
     - newParams pinned inside the valid range so _setOptimisticParams
       does not revert on its own validation gates (those are R6-R11).
     - msg.value == 0 (no native value forwarded).
*/
rule setOptimisticParamsPreservesPerProposalThreshold {
    env e;
    uint256 pid;
    IReserveOptimisticGovernor.OptimisticGovernanceParams newParams;

    // Pin the governance-executor harness.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;

    // Constrain newParams to the valid range so the setter succeeds.
    require newParams.vetoDelay >= 1;
    require newParams.vetoDelay < 140737488355327; // < MAX_OPTIMISTIC_DELAY
    require newParams.vetoPeriod >= 300;           // MIN_OPTIMISTIC_VETO_PERIOD
    require newParams.vetoThreshold != 0;
    require newParams.vetoThreshold <= 1000000000000000000; // 1e18

    // The proposal under observation is an existing optimistic one.
    uint256 thresholdBefore = vetoThreshold(pid);
    require thresholdBefore != 0;

    setOptimisticParams(e, newParams);

    uint256 thresholdAfter = vetoThreshold(pid);

    assert thresholdAfter == thresholdBefore,
        "setOptimisticParams retroactively changed an existing proposal's vetoThreshold";
}
