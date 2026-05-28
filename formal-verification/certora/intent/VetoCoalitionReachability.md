# S31: Structural veto-coalition reachability invariant

Catalog reference: S31 in `notes/governance_intent_and_shapes.md`.

## Intent

For every optimistic proposal:

> `vetoThresholdInTokens(pid) <= getPastOptimisticVotingSupply(snapshot(pid))`

The veto threshold must be reachable by the coalition of all opted-in voters. This is the structural form of the Cantina catch — asserts the property as a one-line invariant over arbitrary parameters, making the PR #36 fix permanent rather than parameter-contingent.

## CVL form

Parametric rule over every external method, with ghost-backed summaries on both `_.getPastTotalSupply` and `_.getPastOptimisticVotingSupply` to surface the wrong-population denominator:

```cvl
ghost mapping(uint256 => uint256) ghostPastTotalSupply;
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;

methods {
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;
}

rule vetoThresholdReachableByOptimisticCoalitionStructural(method f)
    filtered { f -> f.selector != sig:upgradeToAndCall(address,bytes).selector }
{
    /* Setup ... */
    f(e, args);
    assert vetoThresholdInTokens(pid) <= ghostPastOptimisticSupply[snapshot];
}
```

## Outcome (run at `emv-1-certora-28-May--14-12` in worktree)

| Rule | Status |
|---|---|
| `envfreeFuncsStaticCheck` | VERIFIED |
| `vetoThresholdReachableByOptimisticCoalitionStructural` (ROOT) | **VIOLATED** |
| `sanityStructuralPreconditionSatisfiable` (ROOT) | VIOLATED (healthy — precondition satisfiable) |

Every method instantiation of the structural rule violated. The bug manifests at the storage level — `vetoThresholdInTokens` is computed against `getPastTotalSupply` which the ghost has no constraint forcing to equal `getPastOptimisticVotingSupply`. The prover constructs a witness where the two diverge, making the threshold exceed the optimistic supply.

This is the same Cantina catch the existing `VetoThresholdReachability.spec` demonstrated scenario-by-scenario, but expressed as the **structural invariant** form. The structural form is stronger:

- The scenario form: "for THIS specific configuration of supplies, the proposal stays Active despite full coalition veto."
- The structural form: "for ANY reachable storage state, the threshold exceeds the eligible coalition."

The structural form catches the bug independent of which method is called, what the snapshot value is, what the ratio is. It's the right shape for "this fix must remain valid under any future refactor."

## Comparison with `VetoThresholdReachability.spec`

| Aspect | `VetoThresholdReachability` (existing) | `VetoCoalitionReachability` (S31) |
|---|---|---|
| Form | Scenario rule with explicit precondition | Parametric invariant over all methods |
| Counterexample shape | Specific (pid, supply, ratio) tuple | Storage state with two-supply divergence |
| Refactor resistance | Tests one execution path | Tests invariant across reachable states |
| Solver cost | ~4 s | ~9 min (parametric expansion, near OOM) |
| Catches | The Cantina bug | The Cantina bug AND any future divergence between the two supply sources |

## Honest caveat: solver budget

The parametric expansion over every external method × 3 ROOT rules × method-instantiations × solver runs blew through 24 GB of available memory; multiple "extremely low available memory: 24MB" warnings during the run. The verification completed enough to surface the violations, but a production-grade run should narrow the method filter further (skip the 1-arg view functions that don't touch state) and possibly split the parametric rule by method category.

## Status

Verified that the rule's invariant fails on the current pre-fix contract. The PR #36 fix replaces `getPastTotalSupply` with `getPastOptimisticVotingSupply` at line 249, which would make the structural invariant hold (the two ghosts become read from the same source). Future regression test value: high.

## Relationship to the broader strategy

This is the second intent-derived rule that demonstrates the Cantina-shape catch (the first being `VetoThresholdReachability`). Having both is intentional:
- The scenario rule is fast and cheap, suitable for routine CI.
- The structural rule is comprehensive but heavy, suitable for pre-release verification or whenever the supply-handling code changes.

Together they capture the same property at two strengths.
