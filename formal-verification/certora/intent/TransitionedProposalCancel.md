# TransitionedProposalCancel - S21 sentinel-state cancel rejection

Intent-derived Certora coverage for `governance_intent_and_shapes.md`
shape **S21: Sentinel-value reasoning errors**, specifically the
transitioned-optimistic-proposal case. This rule pins the chain of
short-circuits that prevents an optimistic guardian from cancelling a
proposal that has already transitioned from optimistic to pessimistic.

## Intent (S21)

Once an optimistic proposal has transitioned to pessimistic, its
`vetoThreshold` storage slot is overwritten with the sentinel
`TRANSITIONED_VETO_THRESHOLD == type(uint256).max` (ProposalLib.sol:20).
The transition keeps `_isOptimistic` returning `true` (sentinel is
non-zero), but `state()` short-circuits to `Defeated` for that
proposal (ReserveOptimisticGovernor.sol:243-246). The whole point of
the transition is to force the proposal back through the standard
pessimistic governance route; optimistic guardians must lose their
cancel authority over it.

## Load-bearing chain documented by the rule

```
vetoThreshold[pid] == TRANSITIONED_VETO_THRESHOLD (sentinel = MAX_UINT256)
  -> state(pid) short-circuit at ReserveOptimisticGovernor.sol:243-246
    -> ProposalState.Defeated
      -> Guardian.cancel != Defeated check at Guardian.sol:90-93 trips
        -> optimistic-guardian cancel rejected
```

Each arrow is a single, removable link. If any link breaks, the
property fails. The pair of rules below records which link is
load-bearing.

## Per-rule status

| ID  | Rule                                                  | Status                  |
|-----|-------------------------------------------------------|-------------------------|
| S21 | `transitionedProposalRejectsOptimisticGuardianCancel` | VERIFIED                |
| -   | `transitionedProposalRequiresSentinelShortCircuit`    | VIOLATED (healthy)      |
| -   | `transitionedProposalRejectsOptimisticGuardianCancel-rule_not_vacuous` | VIOLATED (satisfiable)  |

The sister rule's VIOLATED status is the expected, healthy outcome -
it documents the load-bearing dependence on the sentinel-to-Defeated
short-circuit. The sanity check's VIOLATED status confirms the root
rule's precondition is satisfiable (per WISDOM C002, "Violated" on a
`_rule_not_vacuous` sanity meta-check means the original precondition
is reachable, which is what we want).

## Difference from Guardian G6b

`Guardian.spec` G6b (`cancelNonAdminRequiresNotDefeated`) is the
GENERAL "non-admin guardian cannot cancel any Defeated optimistic
proposal" rule. It does NOT pin WHY a particular proposal might be
Defeated - any value of `ghostState[pid] == DEFEATED()` is in scope.

S21 sharpens G6b in one specific axis: it pins the abstract STATE of
"transitioned" by constraining `ghostVetoThresholdRatio[pid]` to the
sentinel value. The new ghost makes the rule's intent explicit at the
storage level - it's the only rule in the suite that names the
sentinel directly. The sister rule then demonstrates the chain's
fragility: if the sentinel-to-Defeated short-circuit were removed,
`_isOptimistic` would still report the proposal as optimistic (the
sentinel is non-zero), `state()` would fall through to the vote-tally
branch, and the proposal would read Active or Succeeded. G6b would
NOT catch this regression because G6b's pre-state is "the proposal is
Defeated" - it presumes the chain already worked.

S21 = G6b's pre-state, sourced.

## Regression scenarios the rule guards against

1. A future edit removes the sentinel branch at
   `ReserveOptimisticGovernor.sol:243-246`. The S21 root rule would
   still verify ONLY because the precondition `ghostState ==
   Defeated()` is now unreachable from the sentinel scenario - the
   sanity check would flip to VERIFIED (vacuity), exposing the
   regression. The sister rule would flip to VERIFIED as well, since
   `state == Active` becomes the actual contract behavior.

2. A future edit changes `_isOptimistic` so that the sentinel value
   stops being treated as "optimistic" (e.g. an upper-bound check is
   added). This would silently change the semantics of every
   sentinel-aware path. The rule's precondition `ghostIsOptimistic ==
   true` paired with sentinel storage value pins this assumption.

3. A future edit adds a NEW Guardian-side guard that reads
   `vetoThreshold` directly (independent of `state()`). This would
   flip the sister rule from VIOLATED to VERIFIED, signalling an
   audit-worthy change to the documented threat model.

## Verification

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/TransitionedProposalCancel.conf
```

Tested on `feature/formal-verification` at the bootstrap commit; the
root rule verifies in ~5 seconds and the sister rule produces its
expected counterexample in ~8 seconds.
