/* TimelockPrecision.spec - S15: time-lock bypass via precision.

   Pins the inclusivity convention of the timelock's "ready to execute"
   gate. The OZ TimelockController readiness predicate is:

     getOperationState(id) == Ready
       iff   timestamp != 0
       and   timestamp != _DONE_TIMESTAMP   (= 1)
       and   timestamp <= block.timestamp

   The boundary case is `timestamp == block.timestamp`: the operation
   IS Ready at the exact second its scheduled time arrives. A
   neighbouring corner `timestamp == block.timestamp + 1` is Waiting -
   one second too early to execute. The two rules together pin the
   inclusive lower bound (`<=`).

   The bug shape S15 in
   `formal-verification/certora/notes/governance_intent_and_shapes.md`
   asks for a regression guard against any future change that breaks
   this boundary - e.g. flipping `<=` to `<` in getOperationState would
   make legitimate execute() at exactly the scheduled time revert.

   Rules:
     P1   executeBatch at the BOUNDARY (timestamp == block.timestamp)
            SUCCEEDS - the inclusive readiness gate passes at the
            exact scheduled moment.
     P2   executeBatch at BOUNDARY - 1 (timestamp == block.timestamp + 1,
            i.e. exactly one second too early) REVERTS - the gate is
            not satisfied off-by-one earlier.

   Both rules together pin the inclusivity to `<=`. If either side
   broke (gate too strict OR too loose), one of the two rules would
   VIOLATE.

   The Rocq side proves the same boundary in
   `formal-verification/rocq/proofs/Timelock.v` lines 193-195:
     get_ts s2 idA = nowS + delay
     /\ (nowB < nowS + delay -> op_status s2 idA nowB = OpWaiting)
     /\ op_status s2 idA (nowS + delay) = OpReady.
   The Certora rules are the bytecode-level witnesses of the same
   property, exercised through the live executeBatch entry point.

   The contract convention used here is INCLUSIVE LOWER BOUND
   (block.timestamp >= scheduledTime, equivalently
    scheduledTime <= block.timestamp). The OZ source at
   TimelockControllerUpgradeable.sol's `getOperationState`:
     } else if (timestamp > block.timestamp) {
         return OperationState.Waiting;
     } else {
         return OperationState.Ready;
   confirms the convention - strict `>` for Waiting means Ready
   includes equality. The Reserve TimelockControllerOptimistic does not
   override getOperationState; it inherits the OZ convention verbatim.

   Empty-arrays pattern (targets / values / payloads) follows
   Timelock.spec T6/T7/T8/ID2: isolates the queue-state transition
   from the inner `_execute` dispatch loop, which has no bearing on the
   readiness gate that is the actual property under test.

   rule_sanity: "none" matches Timelock.spec (T1-T10) and TimelockIntent
   (ID2). The OZ AccessControl + Timelock storage layout OOMs the
   sanity meta-check.
*/

methods {
    function PROPOSER_ROLE() external returns (bytes32) envfree;
    function EXECUTOR_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    function getTimestamp(bytes32) external returns (uint256) envfree;

    function hashOperationBatch(address[], uint256[], bytes[], bytes32, bytes32)
        external returns (bytes32) envfree;
}

/* ----- P1: executeBatch SUCCEEDS at the exact scheduled moment -----

   The operation's `timestamp` equals the current `block.timestamp`.
   Under the OZ inclusive-lower-bound convention this is Ready, and
   the executeBatch queue gate must accept it.

   Preconditions:
     - caller holds PROPOSER_ROLE + EXECUTOR_ROLE (auth gates pass)
     - empty arrays (no external dispatch in the loop body)
     - msg.value == 0 (no value to forward)
     - predecessor == 0 (no predecessor chain dependency)
     - timestamp == block.timestamp (boundary - the exact scheduled
       second has arrived)
     - block.timestamp > 1 (so timestamp != _DONE_TIMESTAMP = 1)

   Post: the call does NOT revert. The op transitions Ready -> Done.
*/
rule executeBatchSucceedsAtBoundary {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;
    require e.msg.value == 0;
    require predecessor == to_bytes32(0);

    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // Boundary case: scheduled time == current time.
    // We also require block.timestamp > 1 so that timestamp != _DONE_TIMESTAMP.
    require e.block.timestamp > 1;
    require getTimestamp(id) == e.block.timestamp;

    executeBatch@withrevert(e, targets, values, payloads, predecessor, salt);

    assert !lastReverted,
        "executeBatch reverted at the exact scheduled moment (inclusive lower bound broken)";
}

/* ----- P2: executeBatch REVERTS one second before the scheduled moment -----

   The operation's `timestamp` is `block.timestamp + 1` - i.e. the
   scheduled moment is one second in the future. Under the inclusive-
   lower-bound convention this is Waiting, and the executeBatch queue
   gate must reject it.

   This is the off-by-one corner the bug-shape S15 worries about: a
   future refactor that loosened the gate to `<` (or, equivalently,
   shifted the test to `timestamp <= block.timestamp + 1`) would let
   this rule VIOLATE.

   Preconditions mirror P1 with timestamp shifted by +1.
*/
rule executeBatchRevertsOneSecondEarly {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;

    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // One-second-early case: scheduled time == block.timestamp + 1.
    // No risk of colliding with the _DONE_TIMESTAMP = 1 sentinel since
    // block.timestamp + 1 > 1 iff block.timestamp >= 1, but we anchor
    // it explicitly for clarity.
    require e.block.timestamp >= 1;
    require getTimestamp(id) == require_uint256(e.block.timestamp + 1);

    executeBatch@withrevert(e, targets, values, payloads, predecessor, salt);

    assert lastReverted,
        "executeBatch accepted a Waiting op one second before the scheduled moment";
}
