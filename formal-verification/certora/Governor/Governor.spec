/* ReserveOptimisticGovernor.sol Certora spec — covers the auth-surface
   overlay this contract adds on top of OZ Governor.

   This is the largest contract in the codebase. We deliberately do NOT
   verify the full propose/queue/execute state machine — that lives in
   the Rocq proofs at formal-verification/rocq/proofs/Governor*.v. Here
   we isolate the optimistic-overlay invariants:

     R1   updateTimelock always reverts (locked timelock)
     R2   setProposalThrottle requires onlyGovernance
     R3   setOptimisticParams requires onlyGovernance
     R4   _setProposalThrottle rejects capacity == 0
     R5   _setProposalThrottle rejects capacity > MAX_PROPOSAL_THROTTLE_CAPACITY
     R6   _setOptimisticParams rejects vetoThreshold == 0
     R7   _setOptimisticParams rejects vetoThreshold > 1e18
     R8   _setOptimisticParams rejects vetoDelay == 0 (< MIN_OPTIMISTIC_VETO_DELAY)
     R9   _setOptimisticParams rejects vetoPeriod < MIN_OPTIMISTIC_VETO_PERIOD
     R10  setProposalThrottle persists the new capacity to storage
     R11  _setOptimisticParams rejects vetoDelay >= MAX_OPTIMISTIC_DELAY
          (upper-bound companion to R8; closes adversarial F2 in
          notes/adversarial_spec_correctness.md)
     R12  setOptimisticParams persists all three fields to storage
          (companion to R10; closes adversarial F4 in
          notes/adversarial_spec_correctness.md)

   Heavy NONDET summarisation is used for OZ Governor inherited internals
   and for the external ProposalLib / ThrottleLib delegatecalls. We're
   proving the optimistic-overlay logic, not OZ's internals.

   Exception: `hasRole` on the timelock is ghost-backed instead of NONDET
   so two reads of the same (role, account) pair agree. The fidelity
   concern is documented as F3 in notes/adversarial_summary_fidelity.md.
   None of the current R1-R12 rules dispatch through `hasRole`, but the
   ghost is a no-cost fidelity upgrade that lets future cancel-path or
   propose-path rules `require ghostHasRole[role][addr] == ...` to pin
   the auth outcome.

   Note on conf: `disable_internal_function_instrumentation: true` skips
   the auto-finder compilation pass (which has a path-resolution bug on
   this contract when the sources tree is deep). Internal call summaries
   in this spec are wildcard-external only, so we don't need autofinders.
*/

/* Ghost-backed hasRole. Replaces NONDET so that two AccessControl
   reads of the same (role, account) pair in a single transaction
   agree. Used by `_validateCancel` (CANCELLER_ROLE) and
   ProposalLib.proposeOptimistic (OPTIMISTIC_PROPOSER_ROLE), both of
   which are out-of-scope for the current rule set but in-scope for
   future extensions. Mirrors RewardTokenRegistry.spec / VersionRegistry.spec
   pattern (WISDOM C015). */
ghost mapping(bytes32 => mapping(address => bool)) ghostHasRole;

methods {
    // Reserve overlay setters
    function setProposalThrottle(uint256) external;
    function setOptimisticParams(IReserveOptimisticGovernor.OptimisticGovernanceParams) external;
    function updateTimelock(address) external;

    // Envfree readers
    function proposalThrottleCapacity() external returns (uint256) envfree;
    function timelock() external returns (address) envfree;
    // Auto-generated getter for the public `optimisticParams` field. The
    // struct unpacks to (uint48 vetoDelay, uint32 vetoPeriod, uint256 vetoThreshold).
    function optimisticParams() external returns (uint48, uint32, uint256) envfree;

    // === NONDET summaries for everything we don't want to model ===
    // Library external functions (delegatecalled)
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;

    // Token / votes
    function _.getPastTotalSupply(uint256) external => NONDET;
    function _.getPastVotes(address, uint256) external => NONDET;
    function _.getPastOptimisticVotes(address, uint256) external => NONDET;
    function _.clock() external => NONDET;
    function _.CLOCK_MODE() external => NONDET;

    // Timelock interactions
    // Ghost-backed (deterministic per (role, account)) — see header. This is
    // a fidelity-only upgrade; no current rule reads ghostHasRole, so the
    // ghost is fully unconstrained and behaves like NONDET for the existing
    // R1-R12 set.
    function _.hasRole(bytes32 role, address account) external =>
        ghostHasRole[role][account] expect bool;
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

    // Selector registry
    function _.isAllowed(address, bytes4) external => NONDET;

    // OZ Governor _checkGovernance — wholly delegate to its native behavior.
    // We DO NOT summarise it: the auth-gate rules need to observe the
    // executor-check semantics. But we DO summarise the deque pop loop
    // by way of optimistic_loop: true (see conf).
}

/* ----- R1: updateTimelock always reverts ----- */
rule updateTimelockAlwaysReverts {
    env e;
    address anyTimelock;

    updateTimelock@withrevert(e, anyTimelock);

    assert lastReverted, "updateTimelock did not revert";
}

/* ----- R2: setProposalThrottle requires onlyGovernance (executor == timelock) -----
   In GovernorTimelockControlUpgradeable, _executor() returns timelock(). The
   onlyGovernance gate reverts when msg.sender != _executor(). We assert any
   caller that is neither the timelock nor the governor itself reverts. */
rule setProposalThrottleOnlyGovernance {
    env e;
    uint256 newCapacity;

    require e.msg.sender != timelock();
    require e.msg.sender != currentContract;

    setProposalThrottle@withrevert(e, newCapacity);

    assert lastReverted, "non-governance caller succeeded in setProposalThrottle";
}

/* ----- R3: setOptimisticParams requires onlyGovernance ----- */
rule setOptimisticParamsOnlyGovernance {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    require e.msg.sender != timelock();
    require e.msg.sender != currentContract;

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "non-governance caller succeeded in setOptimisticParams";
}

/* ----- R4: _setProposalThrottle rejects capacity == 0 ----- */
rule setProposalThrottleRejectsZero {
    env e;

    // assume caller is governance (executor == self) so we test the inner check
    // We test the inner validation inside _setProposalThrottle / _setOptimisticParams.
    // To pass onlyGovernance we need msg.sender == _executor() == timelock(); we
    // additionally fix timelock() == this so the OZ deque-pop branch is skipped.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;

    setProposalThrottle@withrevert(e, 0);

    assert lastReverted, "setProposalThrottle accepted zero capacity";
}

/* ----- R5: _setProposalThrottle rejects capacity > MAX ----- */
rule setProposalThrottleRejectsTooLarge {
    env e;
    uint256 newCapacity;

    // We test the inner validation inside _setProposalThrottle / _setOptimisticParams.
    // To pass onlyGovernance we need msg.sender == _executor() == timelock(); we
    // additionally fix timelock() == this so the OZ deque-pop branch is skipped.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require newCapacity > 12; // MAX_PROPOSAL_THROTTLE_CAPACITY

    setProposalThrottle@withrevert(e, newCapacity);

    assert lastReverted, "setProposalThrottle accepted capacity > MAX";
}

/* ----- R6: setOptimisticParams rejects vetoThreshold == 0 ----- */
rule setOptimisticParamsRejectsZeroVetoThreshold {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    // We test the inner validation inside _setProposalThrottle / _setOptimisticParams.
    // To pass onlyGovernance we need msg.sender == _executor() == timelock(); we
    // additionally fix timelock() == this so the OZ deque-pop branch is skipped.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoThreshold == 0;

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "setOptimisticParams accepted vetoThreshold == 0";
}

/* ----- R7: setOptimisticParams rejects vetoThreshold > 1e18 ----- */
rule setOptimisticParamsRejectsTooLargeVetoThreshold {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    // We test the inner validation inside _setProposalThrottle / _setOptimisticParams.
    // To pass onlyGovernance we need msg.sender == _executor() == timelock(); we
    // additionally fix timelock() == this so the OZ deque-pop branch is skipped.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoThreshold > 1000000000000000000; // > 1e18

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "setOptimisticParams accepted vetoThreshold > 1e18";
}

/* ----- R8: setOptimisticParams rejects vetoDelay == 0 (< MIN_OPTIMISTIC_VETO_DELAY) ----- */
rule setOptimisticParamsRejectsZeroVetoDelay {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoDelay == 0;

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "setOptimisticParams accepted vetoDelay == 0";
}

/* ----- R9: setOptimisticParams rejects vetoPeriod < MIN_OPTIMISTIC_VETO_PERIOD (300s) ----- */
rule setOptimisticParamsRejectsShortVetoPeriod {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoPeriod < 300; // MIN_OPTIMISTIC_VETO_PERIOD = 5 minutes

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "setOptimisticParams accepted vetoPeriod < MIN";
}

/* ----- R10: setProposalThrottle persists newCapacity ----- */
rule setProposalThrottlePersistsCapacity {
    env e;
    uint256 newCapacity;

    // We test the inner validation inside _setProposalThrottle / _setOptimisticParams.
    // To pass onlyGovernance we need msg.sender == _executor() == timelock(); we
    // additionally fix timelock() == this so the OZ deque-pop branch is skipped.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require newCapacity != 0 && newCapacity <= 12;

    setProposalThrottle(e, newCapacity);

    assert proposalThrottleCapacity() == newCapacity,
        "setProposalThrottle did not persist capacity";
}

/* ----- R11: setOptimisticParams rejects vetoDelay >= MAX_OPTIMISTIC_DELAY -----
   Upper-bound companion to R8. MAX_OPTIMISTIC_DELAY = type(uint48).max / 2
   = (2^48 - 1) / 2 = 140737488355327 (see contracts/utils/Constants.sol:14).
   See adversarial_spec_correctness.md F2: without this rule a refactor that
   dropped the `< MAX_OPTIMISTIC_DELAY` clause would still satisfy R6-R10. */
rule setOptimisticParamsRejectsTooLargeVetoDelay {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoDelay >= 140737488355327; // MAX_OPTIMISTIC_DELAY = (2^48 - 1) / 2

    setOptimisticParams@withrevert(e, params);

    assert lastReverted, "setOptimisticParams accepted vetoDelay >= MAX_OPTIMISTIC_DELAY";
}

/* ----- R12: setOptimisticParams persists all three fields -----
   Companion to R10. The contract assigns the whole struct via
   `optimisticParams = params;` at ReserveOptimisticGovernor.sol:498.
   See adversarial_spec_correctness.md F4: a refactor that wrote only
   one struct field (e.g. shadow-local bug) would still satisfy R6-R9
   and R11 without this rule. */
rule setOptimisticParamsPersists {
    env e;
    IReserveOptimisticGovernor.OptimisticGovernanceParams params;

    // Same self-timelock harness as R4-R10 so the deque-pop branch is
    // skipped. Pin the inputs to the valid range so the call does not
    // revert in _setOptimisticParams.
    require e.msg.sender == currentContract;
    require timelock() == currentContract;
    require e.msg.value == 0;
    require params.vetoDelay >= 1; // MIN_OPTIMISTIC_VETO_DELAY = 1
    require params.vetoDelay < 140737488355327; // < MAX_OPTIMISTIC_DELAY
    require params.vetoPeriod >= 300; // MIN_OPTIMISTIC_VETO_PERIOD = 5 minutes
    require params.vetoThreshold != 0;
    require params.vetoThreshold <= 1000000000000000000; // 1e18

    setOptimisticParams(e, params);

    uint48 dAfter;
    uint32 pAfter;
    uint256 tAfter;
    dAfter, pAfter, tAfter = optimisticParams();

    assert dAfter == params.vetoDelay, "vetoDelay not persisted";
    assert pAfter == params.vetoPeriod, "vetoPeriod not persisted";
    assert tAfter == params.vetoThreshold, "vetoThreshold not persisted";
}
