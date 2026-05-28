# TimelockPrecision - S15: time-lock bypass via precision

Intent-derived regression guard for the OZ TimelockController readiness
boundary. Pairs with the existing `TimelockIntent.spec` ID2 (delay is
wall-clock, not role-based) by pinning the precision corner the ID2
rule does not address: the inclusive lower bound at
`block.timestamp >= scheduledTime`.

The shape backgrounded in
`formal-verification/certora/notes/governance_intent_and_shapes.md` S15
(lines 577-610): a future refactor that flipped the readiness gate
from `<=` to `<` (or to a stricter `>`) would silently shift the
boundary by one second. Either direction is a precision bug:

- Too strict (`>` instead of `>=`): a legitimate execute at exactly
  the scheduled time reverts. Operations stall for an extra second
  with no semantic justification.
- Too loose (e.g. `<=` shifted to `<= +1`): operations execute one
  second earlier than intended - a sub-second timelock bypass that
  scales (if compounded across upgrades) into a sliding-window
  privilege escalation.

T1-T10 in `Timelock/Timelock.spec` and ID2 in `intent/TimelockIntent.spec`
already cover the role gates and the gross-time-passing case. None of
them pin the exact `block.timestamp == scheduledTime` corner.

## Inclusivity convention used by the contract

The Reserve `TimelockControllerOptimistic` does NOT override
`getOperationState`. It inherits the OZ source verbatim, which uses
the strict `>` for the Waiting branch (OZ
`TimelockControllerUpgradeable.sol`):

```solidity
function getOperationState(bytes32 id) public view virtual returns (OperationState) {
    uint256 timestamp = getTimestamp(id);
    if (timestamp == 0) {
        return OperationState.Unset;
    } else if (timestamp == _DONE_TIMESTAMP) {
        return OperationState.Done;
    } else if (timestamp > block.timestamp) {
        return OperationState.Waiting;
    } else {
        return OperationState.Ready;
    }
}
```

`timestamp > block.timestamp` is Waiting; `timestamp <= block.timestamp`
(with the Unset / Done sentinels excluded) is Ready. The convention is
INCLUSIVE LOWER BOUND - the scheduled second is itself executable.

This matches the Rocq formalization in
`formal-verification/rocq/proofs/Timelock.v` lines 193-195, which
proves `op_status` is `OpReady` at exactly `nowS + delay` and
`OpWaiting` strictly before:

```
get_ts s2 idA = nowS + delay
/\ (nowB < nowS + delay -> op_status s2 idA nowB = OpWaiting)
/\ op_status s2 idA (nowS + delay) = OpReady.
```

## CVL form

Two paired rules. Together they pin inclusivity to `<=`:

```cvl
rule executeBatchSucceedsAtBoundary {
    env e;
    // empty arrays, msg.value == 0, predecessor == 0,
    // PROPOSER + EXECUTOR roles held, block.timestamp > 1
    bytes32 id = hashOperationBatch(...);
    require getTimestamp(id) == e.block.timestamp;  // boundary
    executeBatch@withrevert(e, ...);
    assert !lastReverted;
}

rule executeBatchRevertsOneSecondEarly {
    env e;
    // same harness preconditions
    bytes32 id = hashOperationBatch(...);
    require getTimestamp(id) == require_uint256(e.block.timestamp + 1);
    executeBatch@withrevert(e, ...);
    assert lastReverted;
}
```

Empty-arrays pattern follows the Timelock.spec T6/T7/T8/ID2 convention:
isolates the queue-state readiness gate from `_execute`'s dispatch
loop, which has no bearing on the property under test.

## Outcome

Both rules VERIFIED in under 1 second of solver time each.

```
Result for executeBatchRevertsOneSecondEarly: SUCCESS
Result for executeBatchSucceedsAtBoundary: SUCCESS
```

The contract uses the **inclusive lower bound** (`>=`) convention -
execute is permitted at `block.timestamp == scheduledTime`. This rule
file is a regression guard: any future change that flips the
inequality direction or shifts the boundary will cause exactly one of
the two rules to VIOLATE.

## Verification command

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/TimelockPrecision.conf
```

`rule_sanity` is `"none"` to match the rest of the Timelock corpus -
the OZ AccessControl + Timelock storage layout OOMs the sanity
meta-check (per Timelock.spec lines 36-42).
