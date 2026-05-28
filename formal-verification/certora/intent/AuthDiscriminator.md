# AuthDiscriminator - intent-derived auth-discriminator rules

Intent-derived Certora coverage for the auth-discriminator family of
properties. These rules go beyond the syntactic "this function reverts
when caller lacks role X" form (already covered across the per-contract
specs) and pin the SEMANTIC form: "even when this role is held, the
caller cannot achieve outcome Y unless precondition Z."

The methodology background is in
`formal-verification/certora/notes/cantina_pr36_postmortem.md` - the
"property-from-intent, not property-from-code" recommendation.

## Per-rule status

| ID  | Property                                                                   | Spec                                     | Status      |
|-----|----------------------------------------------------------------------------|------------------------------------------|-------------|
| ID1 | DEFAULT_ADMIN_ROLE alone cannot grant OPTIMISTIC_GUARDIAN_ROLE             | `GuardianIntent.spec`                    | VERIFIED    |
| ID2 | PROPOSER + EXECUTOR cannot execute a Waiting operation via executeBatch    | `TimelockIntent.spec`                    | VERIFIED    |
| ID3 | StakingVault admin cannot bypass existing UnstakingManager unlockTime     | (skipped - see structural reason below)  | SKIPPED     |
| ID4 | setOptimisticParams does not perturb per-proposal vetoThreshold snapshots  | `GovernorIntent.spec`                    | VERIFIED    |

## ID1 - admin alone cannot grant OPTIMISTIC_GUARDIAN_ROLE

### Intent
The Guardian threat model (Guardian.sol:21-25) assigns DEFAULT_ADMIN_ROLE
break-glass cancel-anything power, but explicitly carves OUT the role-
minting power. Only OPTIMISTIC_GUARDIAN_MANAGER_ROLE may mint new
OPTIMISTIC_GUARDIAN_ROLE holders. The existing G1 rule covers
"non-manager reverts" but does NOT enumerate the admin-without-manager
scenario - leaving a hypothetical refactor that grants admin a bypass
undetectable.

### CVL form
```cvl
rule adminAloneCannotGrantOptimisticGuardian {
    env e;
    address account;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require !hasRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE(), e.msg.sender);

    grantOptimisticGuardian@withrevert(e, account);

    assert lastReverted,
        "DEFAULT_ADMIN_ROLE bypassed OPTIMISTIC_GUARDIAN_MANAGER_ROLE on grantOptimisticGuardian";
}
```

### Outcome
VERIFIED. Sanity (non-vacuity) also passes: the prover finds a state
where the caller holds admin but not manager and the call reverts.

## ID2 - PROPOSER + EXECUTOR cannot execute a Waiting operation

### Intent
The timelock delay is wall-clock, not role-based. Even the strongest
non-admin caller (PROPOSER + EXECUTOR) cannot collapse a scheduled
operation's wait. The existing T6 rule covers the bypass path
(`executeBatchBypass`, which IS the documented escape hatch); the
intent rule for the NORMAL path is that `executeBatch` respects the
delay even under the strongest caller.

A refactor that accidentally re-routed `executeBatch` to skip
`_beforeCall` would not violate T1-T10; ID2 closes that gap.

### CVL form
```cvl
rule proposerExecutorCannotBypassDelay {
    env e;
    /* ... empty arrays to isolate the queue check from external dispatch ... */
    require hasRole(PROPOSER_ROLE(), e.msg.sender);
    require hasRole(EXECUTOR_ROLE(), e.msg.sender);

    bytes32 id = hashOperationBatch(...);
    uint256 ts = getTimestamp(id);
    require ts != 0 && ts != 1 && ts > e.block.timestamp;  // Waiting

    executeBatch@withrevert(e, ...);
    assert lastReverted, "...";
}
```

### Outcome
VERIFIED.

## ID3 - StakingVault admin cannot bypass UnstakingManager unlockTime

### Skipped - structural reason

The candidate threat ("admin sets `unstakingDelay` shorter and old
locks become claimable early") does not match the contract's actual
shape. Audit of UnstakingManager.sol shows:

1. `setUnstakingDelay` on StakingVault only mutates `unstakingDelay`,
   which is read at `createLock` time and BAKED into the lock's
   `unlockTime` (`block.timestamp + unstakingDelay`). The stored
   `unlockTime` is then immutable.
2. UnstakingManager has NO admin role. `claimLock` is permissionless
   and gated solely by `lock.unlockTime <= block.timestamp`. No code
   path mutates an existing lock's `unlockTime`.
3. The existing UnstakingManager.spec U3 already proves
   "claimLock reverts when block.timestamp < unlockTime."

The intent question "can admin shorten an existing lock's unlockTime"
therefore has the trivial answer NO - there's no method anywhere in
the system that can write to `locks[id].unlockTime` after createLock.
A non-interference rule on the UnstakingManager side ("no method
preserves unlockTime[lockId] of an existing lock") would add coverage,
but it is a per-contract NON-AUTH property (no role gate is at play),
which puts it outside the intent-derived auth-discriminator class. It
belongs alongside the U-series rules, not in this intent module.

We chose ID1, ID2, ID4 as the three with the cleanest auth-
discriminator framings.

## ID4 - setOptimisticParams preserves per-proposal vetoThreshold

### Intent
At `proposeOptimistic` (ReserveOptimisticGovernor.sol:161-167), the
contract snapshots `optimisticParams.vetoThreshold` into the per-
proposal slot `optimisticProposalDetails[pid].vetoThreshold`. The
governance executor's later calls to `setOptimisticParams(newParams)`
must NOT leak backward into already-created proposals - that would
enable retroactive threshold manipulation on live optimistic votes.

The existing R3 rule proves "setOptimisticParams requires
onlyGovernance" - syntactic auth. The intent question is different:
even when the auth gate passes (governance-execute-via-timelock does
go through), is the per-proposal snapshot still inviolate?

### CVL form
```cvl
rule setOptimisticParamsPreservesPerProposalThreshold {
    env e;
    uint256 pid;
    IReserveOptimisticGovernor.OptimisticGovernanceParams newParams;

    require e.msg.sender == currentContract;     // onlyGovernance
    require timelock() == currentContract;
    require e.msg.value == 0;
    require newParams in [valid range];          // setter does not revert

    uint256 thresholdBefore = vetoThreshold(pid);
    require thresholdBefore != 0;                // pid is an existing optimistic proposal

    setOptimisticParams(e, newParams);

    uint256 thresholdAfter = vetoThreshold(pid);
    assert thresholdAfter == thresholdBefore,
        "setOptimisticParams retroactively changed an existing proposal's vetoThreshold";
}
```

### Outcome
VERIFIED. Sanity witness shows `thresholdBefore == thresholdAfter ==
0x97e2000000002712` for an arbitrary pid - the slot truly is
untouched.

## Verification commands

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/GuardianIntent.conf
certoraRun.py formal-verification/certora/intent/TimelockIntent.conf
certoraRun.py formal-verification/certora/intent/GovernorIntent.conf
```

Each conf targets a distinct contract under verification; Certora
verifies one contract per run, so three confs is the cleanest layout.

All three runs completed with `SUCCESS` and exit code 0. Sanity checks
(non-vacuity) pass for the rules where they were enabled (ID1, ID4);
ID2 follows the Timelock.spec convention of `rule_sanity: "none"`
because the OZ AccessControl + Timelock storage layout OOMs the
sanity meta-check (documented in Timelock.spec lines 36-42).
