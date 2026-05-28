# S2: Wrong-snapshot-time intent rule

Catalog reference: S2 in `notes/governance_intent_and_shapes.md`.

## Intent

A function reading time-keyed external state must read at the
semantically correct timepoint. The optimistic-veto state machine
pins one timepoint per proposal -- `proposalSnapshot(pid)` (which
equals `proposalCore.voteStart`). Every supply read used to resolve
`state(pid)` must use THAT timepoint, never `block.timestamp - 1`
or any other "now"-ish moment.

The bug class: a refactor that swaps the snapshot-time read for a
current-time read would break the state-machine semantics silently.
The post-snapshot supply may differ from the snapshot supply because
mints, burns, or transfers between snapshot and execution change
both `getPastTotalSupply(snapshot)` and `getPastTotalSupply(now-1)`.
Snapshot is canonical; now-1 is not.

## Contract location pinned

`ReserveOptimisticGovernor.state()` at
`contracts/governance/ReserveOptimisticGovernor.sol:249`:

```solidity
uint256 pastSupply = token().getPastTotalSupply(snapshot);
```

Where `snapshot = proposalCore.voteStart`. Compare with the
sibling read at line 311 (in `proposalThreshold()`):

```solidity
uint256 supply = Math.max(1, token().getPastTotalSupply(block.timestamp - 1));
```

Both reads call the SAME external function with DIFFERENT timepoint
arguments. The two reads are correct for their respective intents
(state() pins to the proposal's snapshot; proposalThreshold() pins
to now-1 at the moment of the propose() call). The rule pins the
load-bearing semantic that `state()`'s denominator is the proposal's
own snapshot, not the current block.

## CVL form

Single timepoint-keyed ghost backing `getPastTotalSupply`, with the
rule body constraining two specific keys (`snapshot` and `now-1`)
to disagree. The C017 two-ghost pattern, generalized: distinct call
sites of the same function are distinguished by argument value.

```cvl
ghost mapping(uint256 => uint256) ghostPastTotalSupply;

methods {
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
}

rule stateReadsSupplyAtProposalSnapshot {
    env e;
    uint256 pid;

    uint256 vt = vetoThreshold(pid);
    require vt != 0 && vt != MAX_U256() && vt >= 1 && vt <= WAD();

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 nowMinusOne = require_uint256(e.block.timestamp - 1);
    require snapshot != nowMinusOne;

    // Snapshot supply: small, so threshold reachable.
    uint256 supplyAtSnapshot = ghostPastTotalSupply[snapshot];
    require supplyAtSnapshot > 0 && supplyAtSnapshot <= 1000;

    // Now-1 supply: huge, so if state() erroneously read at now-1
    // the threshold would NOT be reachable.
    uint256 supplyAtNowMinusOne = ghostPastTotalSupply[nowMinusOne];
    require supplyAtNowMinusOne > 1000 * WAD();

    // Coalition has cast all-against votes equal to snapshot supply.
    uint256 againstVotes; uint256 forVotes; uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == supplyAtSnapshot;
    require againstVotes >= 1;

    IGovernor.ProposalState s = state(e, pid);

    // Snapshot-correct reading: state() returns Defeated.
    // Regression to now-1 reading: state() returns Active/Succeeded.
    assert s == IGovernor.ProposalState.Defeated
        || s == IGovernor.ProposalState.Executed
        || s == IGovernor.ProposalState.Canceled,
        "state() returned Active/Succeeded under snapshot-correct supply -- read used a different timepoint than proposalSnapshot(pid)";
}
```

## Outcome on current code: VERIFIED

Run at `emv-1-certora-28-May--15-09` in worktree
`agent-a36ab7b50057006e5`.

| Rule                                          | Status                              |
|-----------------------------------------------|-------------------------------------|
| `envfreeFuncsStaticCheck`                     | VERIFIED                            |
| `stateReadsSupplyAtProposalSnapshot`          | **VERIFIED**                        |
| `sanityHeadlinePreconditionSatisfiable`       | VIOLATED (healthy)                  |
| `rule_not_vacuous` (auto vacuity)             | VIOLATED (healthy -- non-vacuous)   |

The headline rule VERIFIES because the current contract reads at
`proposalSnapshot(pid)`, exactly matching the intent. The sanity
check VIOLATED on `assert false` confirms the precondition is
satisfiable. The prover's automatic vacuity check independently
finds a non-vacuous witness (where `s = ProposalState.Executed`),
corroborating that the precondition is reachable.

Solver time: ~2 seconds (the rule's body threads through a single
state() call with ghost-backed supply reads).

## Regression-guard value

If a future refactor mistakenly changes line 249 to

```solidity
uint256 pastSupply = token().getPastTotalSupply(block.timestamp - 1);
```

the rule would VIOLATE. Witness: snapshot supply is `1`, now-1
supply is `1000 * 1e18`, vt is some small ratio, againstVotes is
`1`. Under the wrong read, threshold becomes
`max((vt * 1000e18) / 1e18, 1) = max(vt*1000, 1)` -- much greater
than `1`. The contract would return Active (or Succeeded after
deadline), violating the assertion.

This is the load-bearing structural guarantee: state() reads at
the proposal's pinned snapshot, period.

## Comparison with sibling rules

| Aspect                | `VetoThresholdReachability`        | `WrongSnapshotTime` (this)         |
|-----------------------|------------------------------------|-------------------------------------|
| Bug class             | S1 wrong-population denominator    | S2 wrong-snapshot-time              |
| Two-ghost pattern     | Two methods (totalSupply vs optSupply) | Two timepoint keys on same method |
| Expected outcome      | VIOLATED on pre-fix branch         | VERIFIED on current code            |
| Catches               | Cantina PR #36                     | Future refactor swapping snapshot   |
| Mode                  | Bug witness                        | Regression guard                    |
| Solver time           | ~4s                                 | ~2s                                 |

The two rules are sibling forms of the same C017 idiom -- one
distinguishes two methods (S1), the other distinguishes two
arguments to the same method (S2).

## Limitations

1. **Snapshot vs deadline branch.** The rule poses scenarios where
   the against-vote total equals the snapshot supply (full coalition
   veto). It does not separately test the `deadline >= block.timestamp`
   branch at line 269 -- that's a Pending/Active/Succeeded
   distinction independent of the snapshot read.

2. **Transitioned-marker excluded.** The `vt != MAX_U256()`
   precondition excludes proposals that already transitioned to
   pessimistic (where state() short-circuits to Defeated regardless
   of supply). Without this, the rule would catch a vacuous
   "all transitioned proposals are Defeated" pattern.

3. **Executed/Canceled accepted.** The rule's assertion permits
   Executed and Canceled outcomes alongside Defeated. These are
   not reachable from the rule's precondition without prior calls
   (the rule does not call any external function before `state()`),
   but accepting them keeps the rule sound for storage states
   reachable from outside the precondition.

4. **proposalThreshold() not separately tested.** The rule pins
   `state()` only. The sibling reads in `proposalThreshold()` at
   line 311 (using `block.timestamp - 1`) and in
   `ProposalLib._validateProposal` at line 83 (also `block.timestamp - 1`)
   are correct for their intent; a regression-guard for THOSE sites
   would require a different harness because the propose-time
   reads happen before `proposalSnapshot(pid)` is set.

## Re-running

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/WrongSnapshotTime.conf
```

## Cross-references

- `formal-verification/certora/notes/governance_intent_and_shapes.md` -- S2 entry
- `formal-verification/certora/WISDOM.md` -- C001 (XOR), C002 (sanity), C015 (ghost summaries), C017 (two-ghost divergence)
- `formal-verification/certora/intent/VetoThresholdReachability.spec` -- sibling rule (S1)
- `formal-verification/certora/intent/VetoCoalitionReachability.spec` -- structural form of S1
- `formal-verification/certora/Guardian/Guardian.spec` -- canonical ghost-backed snapshot pattern
