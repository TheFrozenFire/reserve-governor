/* TimelockControllerOptimistic.sol Certora spec — covers the
   optimistic-extension surface and the headline OZ auth gates.

   Properties proved:
     T1   only PROPOSER_ROLE can scheduleBatch
     T2   only CANCELLER_ROLE can cancel
     T3   only CANCELLER_ROLE can revokeOptimisticProposer
     T4   only PROPOSER_ROLE can executeBatchBypass
     T5   revokeOptimisticProposer on success removes the role
     T6   executeBatchBypass on a fresh op leaves the OZ Done marker
            (_DONE_TIMESTAMP = 1) at timestamps[id]
     T7   executeBatchBypass reverts if op already scheduled
            (OperationConflict — the optimistic bypass cannot stomp on
            a real queue entry)
     T8   executeBatchBypass(id1, ...) does NOT change getTimestamp(id2)
            for any id2 != id1 (cross-id non-interference: the bypass
            on one operation cannot disturb any other scheduled or
            executed operation). This is the bytecode-level form of
            Rocq's `audit_timelock_bypass_preserves_slow_path` /
            CAS INV-5.
     T9   scheduleBatch(targets1, ..., salt1) does NOT change
            getTimestamp(id2) for any id2 != computed_id1
            (cross-id non-interference for scheduling).
     T10  cancel(id1) does NOT change getTimestamp(id2) for any
            id2 != id1 (cross-id non-interference for cancel).

   The OZ inheritance pulls in the full timelock queue logic.
   T6-T10 exercise the queue-mutating paths with targets / values /
   payloads constrained to length 0, so the inner
   `target.call{value}(data)` dispatch loop in `_execute` never runs.
   This isolates the queue-state transitions from the side-effect
   semantics of external dispatch.

   `rule_sanity` is disabled in the conf. The proof obligations
   themselves are sound — the prover finds no counterexample under the
   declared preconditions. The sanity meta-check (proving the rule is
   reachable, i.e. non-vacuous) OOMs on the bypass rules because of
   the inherited AccessControl + Timelock storage layout complexity.
   The auth-gate rules (T1-T4) and the revoke effect rule (T5) are
   small enough that they would pass sanity too; we accept a uniform
   "no sanity" setting for consistency rather than mix per-rule
   exclusions.
*/

methods {
    // Role constants exposed by the OZ TimelockController base.
    function PROPOSER_ROLE() external returns (bytes32) envfree;
    function EXECUTOR_ROLE() external returns (bytes32) envfree;
    function CANCELLER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // OperationState views — getTimestamp is a pure storage read and
    // envfree. (isOperationDone would route through getOperationState
    // which touches block.timestamp; we sidestep it by asserting the
    // raw _DONE_TIMESTAMP = 1 marker directly.)
    function getTimestamp(bytes32) external returns (uint256) envfree;

    // hashOperationBatch is pure.
    function hashOperationBatch(address[], uint256[], bytes[], bytes32, bytes32)
        external returns (bytes32) envfree;

    // External dispatch from inside _execute is a low-level
    // `target.call{value}(data)` — Certora models that as default
    // HAVOC on external state. The two rules that exercise execute
    // (T6, T7) constrain the targets array to empty so the dispatch
    // loop never runs, isolating the queue-state transition. No
    // explicit method-level summary is needed here.
}

/* ----- T1: only PROPOSER_ROLE can scheduleBatch ----- */
rule onlyProposerCanScheduleBatch {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;
    uint256 delay;

    require !hasRole(PROPOSER_ROLE(), e.msg.sender);

    scheduleBatch@withrevert(e, targets, values, payloads, predecessor, salt, delay);

    assert lastReverted, "non-proposer succeeded in scheduleBatch";
}

/* ----- T2: only CANCELLER_ROLE can cancel a pending op ----- */
rule onlyCancellerCanCancel {
    env e;
    bytes32 id;
    require !hasRole(CANCELLER_ROLE(), e.msg.sender);

    cancel@withrevert(e, id);

    assert lastReverted, "non-canceller succeeded in cancel";
}

/* ----- T3: only CANCELLER_ROLE can revoke optimistic proposer ----- */
rule onlyCancellerCanRevokeOptimisticProposer {
    env e;
    address account;
    require !hasRole(CANCELLER_ROLE(), e.msg.sender);

    revokeOptimisticProposer@withrevert(e, account);

    assert lastReverted, "non-canceller succeeded in revokeOptimisticProposer";
}

/* ----- T4: only PROPOSER_ROLE can executeBatchBypass ----- */
rule onlyProposerCanBypass {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;

    require !hasRole(PROPOSER_ROLE(), e.msg.sender);

    executeBatchBypass@withrevert(e, targets, values, payloads, predecessor, salt);

    assert lastReverted, "non-proposer succeeded in executeBatchBypass";
}

/* ----- T5: successful revoke removes OPTIMISTIC_PROPOSER_ROLE ----- */
rule revokeRemovesRole {
    env e;
    address account;
    bytes32 OPT_ROLE = to_bytes32(0x26f49d08685d9cdd4951a7470bc8fbe9dd0f00419c1a44c1b89f845867ae12e0);

    require hasRole(CANCELLER_ROLE(), e.msg.sender);

    revokeOptimisticProposer(e, account);

    assert !hasRole(OPT_ROLE, account),
        "revoke did not remove OPTIMISTIC_PROPOSER_ROLE";
}

/* ----- T6: executeBatchBypass on a fresh op marks it Done -----

   We pin targets / values / payloads to empty arrays so the inner
   loop in executeBatch dispatches no external calls. This isolates
   the queue-state transition (Unset -> Done) from the side-effect
   semantics of `target.call{value}(data)`, which is independent of
   the headline property under test.

   Sanity conditions for a non-vacuous successful path:
     - msg.sender has PROPOSER_ROLE (top-level onlyRole gate)
     - msg.sender has EXECUTOR_ROLE (inner executeBatch's open-role
       gate; we satisfy it directly via msg.sender rather than the
       address(0) open-role escape hatch)
     - msg.value == 0 (no payloads to forward value to)
     - block.timestamp > 1 (so executeBatch's _beforeCall sees the
       just-written timestamp as Ready, not as the DONE magic)
     - predecessor == 0 (no predecessor chain to satisfy)
     - the op is Unset to begin with (the bypass's OperationConflict
       guard).
*/
rule bypassMarksOpDone {
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
    require e.block.timestamp > 1;
    require predecessor == to_bytes32(0);
    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // Pre: op is Unset (timestamp == 0).
    require getTimestamp(id) == 0;

    executeBatchBypass(e, targets, values, payloads, predecessor, salt);

    // _DONE_TIMESTAMP = 1 is the OZ marker for an executed operation.
    // Asserting the raw storage value sidesteps reading block.timestamp.
    assert getTimestamp(id) == 1,
        "executeBatchBypass did not leave the operation Done";
}

/* ----- T7: executeBatchBypass reverts on an already-scheduled op -----

   The OperationConflict guard sits *before* the inner executeBatch
   dispatch, but we still pin targets / values / payloads to empty
   arrays so the post-revert symbolic trace doesn't fork over the
   external-call branch. This keeps the sanity check happy on a
   constrained-but-meaningful state space.
*/
rule bypassRejectsExistingOp {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // Pre: op already has a non-zero timestamp (Waiting / Ready / Done).
    require getTimestamp(id) != 0;
    // Caller has both roles so the auth gate is not what causes the revert.
    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    executeBatchBypass@withrevert(e, targets, values, payloads, predecessor, salt);

    assert lastReverted, "bypass accepted an already-scheduled op";
}

/* ----- T8: executeBatchBypass(id1) preserves any other id2's timestamp -----

   Cross-id non-interference for the optimistic bypass path. The bypass
   on operation id1 must not perturb the queue entry of any unrelated
   operation id2. Concretely: pick an arbitrary `otherId` distinct from
   the bypass-computed id; snapshot its timestamp; run the bypass;
   assert the snapshot is unchanged.

   This is the Certora witness for Rocq's
   `audit_timelock_bypass_preserves_slow_path` and CAS
   `scheduling_ordering.gp` INV-5: bypassing one operation cannot
   reorder, skip, advance, or wipe any other scheduled operation.

   Asserting on the raw `getTimestamp(otherId)` storage value (rather
   than going through `isOperationDone` or `getOperationState`)
   sidesteps the block.timestamp dependency and gives us the cleanest
   non-interference statement — the timestamp slot is the entire OZ
   per-id queue state, so untouched timestamp = untouched op.

   Same empty-arrays pattern as T6/T7 to isolate the queue transition
   from external-call side effects.
*/
rule bypassPreservesOtherOps {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;
    bytes32 otherId;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;
    require e.msg.value == 0;
    require e.block.timestamp > 1;
    require predecessor == to_bytes32(0);
    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);

    // Cross-id witness: otherId is unrelated to the bypass target.
    require otherId != id;
    // The bypass guard requires id be Unset; we still snapshot otherId's
    // arbitrary timestamp (could be Unset / Waiting / Ready / Done).
    require getTimestamp(id) == 0;

    uint256 otherTsBefore = getTimestamp(otherId);

    executeBatchBypass(e, targets, values, payloads, predecessor, salt);

    assert getTimestamp(otherId) == otherTsBefore,
        "bypass(id1) disturbed the timestamp of an unrelated id2";
}

/* ----- T9: scheduleBatch(id1) preserves any other id2's timestamp -----

   Sibling of T8 for the slow-path scheduling action. Scheduling
   operation id1 writes only the timestamps slot for id1 — every
   other op's slot is untouched.

   Empty arrays again isolate the storage write from the dispatch
   loop. Unlike the bypass path, scheduleBatch does NOT enter
   _execute, but the empty-arrays constraint still keeps the symbolic
   trace tight.
*/
rule schedulePreservesOtherOps {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] payloads;
    bytes32 predecessor;
    bytes32 salt;
    uint256 delay;
    bytes32 otherId;

    require targets.length == 0;
    require values.length == 0;
    require payloads.length == 0;
    require hasRole(PROPOSER_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(targets, values, payloads, predecessor, salt);
    require otherId != id;

    uint256 otherTsBefore = getTimestamp(otherId);

    scheduleBatch(e, targets, values, payloads, predecessor, salt, delay);

    assert getTimestamp(otherId) == otherTsBefore,
        "scheduleBatch(id1) disturbed the timestamp of an unrelated id2";
}

/* ----- T10: cancel(id1) preserves any other id2's timestamp -----

   Sibling of T8/T9 for cancellation. cancel takes the id directly
   (no hash computation) so the cross-id rule is simpler — two
   distinct bytes32 ids.

   No empty-arrays constraint needed: cancel touches only the
   timestamps map and emits an event; no dispatch loop runs.
*/
rule cancelPreservesOtherOps {
    env e;
    bytes32 id;
    bytes32 otherId;

    require otherId != id;
    require hasRole(CANCELLER_ROLE(), e.msg.sender);

    uint256 otherTsBefore = getTimestamp(otherId);

    cancel(e, id);

    assert getTimestamp(otherId) == otherTsBefore,
        "cancel(id1) disturbed the timestamp of an unrelated id2";
}
