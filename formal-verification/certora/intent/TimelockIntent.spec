/* TimelockIntent.spec - intent-derived auth-discriminator rule for
   TimelockControllerOptimistic.sol.

   See formal-verification/certora/intent/AuthDiscriminator.md for the
   methodology background.

   Property proved:
     ID2   executeBatch REVERTS even when the caller holds BOTH
           PROPOSER_ROLE and EXECUTOR_ROLE, as long as the operation's
           scheduled timestamp lies in the future
           (getTimestamp(id) > block.timestamp, i.e. OperationState.Waiting).

   Why this is "intent-derived":
     T6 in the existing Timelock.spec covers the *bypass* path
     (executeBatchBypass) which DOES allow PROPOSER+EXECUTOR to execute
     without delay. That's a documented escape hatch. The intent rule
     for the NORMAL path is that even the union of those two roles
     cannot collapse the delay invariant on a legitimately-scheduled
     operation: the delay is a wall-clock check, not a role check.

     Without this rule, a refactor that accidentally re-routed
     executeBatch through the bypass path (e.g. an "optimisation" that
     skipped _beforeCall) would not violate T1-T10. ID2 closes that
     coverage gap by asserting the time gate directly.
*/

methods {
    // OZ TimelockController role constants.
    function PROPOSER_ROLE() external returns (bytes32) envfree;
    function EXECUTOR_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // getTimestamp(id) is a pure storage read on _timestamps[id].
    function getTimestamp(bytes32) external returns (uint256) envfree;

    // Pure-function hash.
    function hashOperationBatch(address[], uint256[], bytes[], bytes32, bytes32)
        external returns (bytes32) envfree;
}

/* ----- ID2: PROPOSER + EXECUTOR cannot execute a Waiting operation -----
   Even with both auth gates satisfied, executeBatch reverts when the
   op's queued timestamp is still in the future. This is the time-gate
   intent: the delay invariant is wall-clock, not role-based.

   The op state we constrain is Waiting:
     timestamp != 0 (op is scheduled, not Unset)
     timestamp != 1 (op is not Done; _DONE_TIMESTAMP = 1)
     timestamp >  block.timestamp (still waiting; not yet Ready)

   We pin targets / values / payloads to empty arrays following the
   Timelock.spec T6/T7/T8 pattern, so the inner _execute dispatch loop
   inside executeBatch never runs - the conclusion (revert in
   _beforeCall) is upstream of the loop, so isolating the queue check
   from external-call side effects keeps the symbolic state space
   tractable.

   Note: executeBatch in OZ uses `onlyRoleOrOpenRole(EXECUTOR_ROLE)`,
   which is satisfied by msg.sender having EXECUTOR_ROLE directly.
   We additionally pin PROPOSER_ROLE to model the "strongest possible
   caller short of admin" — the rule still holds.
*/
rule proposerExecutorCannotBypassDelay {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;

    // Caller holds the maximum non-admin role bundle.
    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // Op is in Waiting state: scheduled, not done, not yet ripe.
    uint256 ts = getTimestamp(id);
    require ts != 0;                  // not Unset
    require ts != 1;                  // not Done (_DONE_TIMESTAMP)
    require ts > e.block.timestamp;   // not yet Ready

    executeBatch@withrevert(e, targets, values, payloads, predecessor, salt);

    assert lastReverted,
        "executeBatch accepted a Waiting operation under PROPOSER+EXECUTOR caller";
}
