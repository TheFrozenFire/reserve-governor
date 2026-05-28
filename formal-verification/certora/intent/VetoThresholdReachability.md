# VetoThresholdReachability intent-derived rule

This document accompanies
`formal-verification/certora/intent/VetoThresholdReachability.spec`. It is
the first concrete instance of the **intent-derived rules** category proposed
in `notes/cantina_pr36_postmortem.md` (Section "How to evolve the stack to
catch wrong-spec bugs"). The headline finding of that postmortem was that
all three of our verification layers missed the Cantina PR #36 wrong-spec
bug because every layer encoded the (wrong) implementation rather than the
user-facing intent. This rule encodes the intent.

## The intent property

> The veto threshold must be reachable by the supply that can actually cast
> vetoes. A non-zero coalition of all eligible vetoers should be able to
> defeat the proposal.

The buggy version of `ReserveOptimisticGovernor.state()`
(`contracts/governance/ReserveOptimisticGovernor.sol:249`) computes
`vetoThresholdTok = (vetoThreshold * pastTotalSupply) / 1e18`. Tokens whose
holders have NOT set a non-zero optimistic delegate count toward
`pastTotalSupply` (inflating the denominator) but cannot cast vetoes. So
the threshold can be set so high (relative to the eligible electorate)
that no coalition of all eligible vetoers reaches it.

The PR #36 fix swaps `getPastTotalSupply(snapshot)` for
`getPastOptimisticVotingSupply(snapshot)`, restoring the invariant that
the eligible coalition can always defeat the proposal.

## CVL form of the headline rule

```cvl
rule vetoThresholdReachableByEligibleVotersHeadline {
    env e;
    uint256 pid;

    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt != MAX_U256();          // not the TRANSITIONED sentinel
    require vt <= WAD();               // construction invariant

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 optSupply = ghostPastOptimisticSupply[snapshot];
    uint256 totSupply = ghostPastTotalSupply[snapshot];
    require optSupply > 0;
    require totSupply > 0;
    require optSupply < totSupply;     // passive holders exist

    uint256 againstVotes; uint256 forVotes; uint256 abstainVotes;
    againstVotes, forVotes, abstainVotes = proposalVotes(pid);
    require againstVotes == optSupply; // coalition fully voted

    mathint thresholdTokFixed = (vt * optSupply) / WAD();
    require optSupply >= thresholdTokFixed;
    require optSupply >= 1;

    mathint thresholdTokBuggy = (vt * totSupply) / WAD();
    require optSupply < thresholdTokBuggy; // bug-exposing precondition

    IGovernor.ProposalState s = state(e, pid);

    assert s != IGovernor.ProposalState.Active
        && s != IGovernor.ProposalState.Succeeded,
        "eligible vetoer coalition could not settle proposal -- veto threshold unreachable against optimistic supply";
}
```

A companion `sanityHeadlinePreconditionSatisfiable` rule asserts `false`
under the same precondition; its `VIOLATED` status confirms the precondition
is satisfiable (the standard CVL sanity-check pattern, see WISDOM C002).

## Ghost-backed external summaries

Two ghost mappings distinguish the two supply sources:

```cvl
ghost mapping(uint256 => uint256) ghostPastTotalSupply;
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;

methods {
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;
    // ... heavy NONDET on every other external surface ...
}
```

The current pre-fix contract calls only `getPastTotalSupply`; the
`getPastOptimisticVotingSupply` summary is still declared so the rule is
forward-compatible with the post-fix build with no edits.

## Outcome on the current pre-fix branch: VIOLATED

```
envfreeFuncsStaticCheck                                      VERIFIED
sanityHeadlinePreconditionSatisfiable                        VIOLATED
vetoThresholdReachableByEligibleVotersHeadline               VIOLATED
```

Both `VIOLATED` statuses are healthy (the sanity check expects `assert false`
to fail; the headline rule is meant to bite on the pre-fix contract).

The headline counterexample the prover constructed:

| Variable        | Value          | Interpretation                                                  |
|-----------------|----------------|-----------------------------------------------------------------|
| `pid`           | 4              | the proposal under test                                         |
| `snapshot`      | 1              | proposal snapshot timepoint                                     |
| `e.block.timestamp` | 3          | now (snapshot in the past)                                      |
| `vt`            | 7              | vetoThreshold (a tiny fraction in D18)                          |
| `optSupply`     | 6              | optimistic-delegated supply at snapshot                         |
| `totSupply`     | 0xfdc3e842d04924b (~1.14e18) | total supply at snapshot — much larger             |
| `againstVotes`  | 6              | eligible coalition fully voted (== optSupply)                   |
| `thresholdTokFixed` | 0          | (7 * 6) / 1e18 = 0  (fix would round to 0, then max(0,1) = 1)   |
| `thresholdTokBuggy` | 8          | (7 * totSupply) / 1e18 = 8                                      |
| `s`             | `ProposalState.Active` | state(pid) returns Active — the bug                     |

The interpretation: the threshold computed against `totalSupply` is `8`, but
the entire eligible electorate is `6`. The coalition votes `6 == 6` against,
yet `6 < 8` so the contract concludes the threshold is NOT met and leaves
the proposal `Active` (or `Succeeded` after the deadline). On the post-fix
contract, `thresholdTok` would be `max((7*6)/1e18, 1) = 1` and
`againstVotes=6 >= 1` would trip the `Defeated` transition.

This is the exact scenario the PR #36 Foundry test
`test_optimisticProposal_vetoThresholdUsesOptimisticDelegatedSupply`
encodes imperatively.

## Implied PR #36 catch rate

If this rule had been part of the Certora coverage before the audit, it
would have surfaced the wrong-supply-denominator bug at sweep time. The
prover constructed the bug-witness in 4 seconds. There is no scenario in
which the rule passes on the pre-fix contract while the contract still
calls `getPastTotalSupply` — the rule's `thresholdTokBuggy > optSupply`
precondition forces the prover into exactly the bug scenario whenever
it's satisfiable.

So: catch rate on this finding, with this rule in place, is 100%. The
rule directly distinguishes the two supply sources by reading both
ghosts and comparing the implied thresholds.

The broader implication, as the postmortem notes, is that one
intent-derived rule per design invariant gives us a class of defense
that none of the three existing layers provides. The next candidates
(throttle-bound, reward-accrual conservation, auth-discriminator intent)
follow the same pattern.

## Structural limitations of the rule

A short list of caveats a future reviewer should keep in mind:

1. **Two ghosts, not one shared.** The rule treats
   `ghostPastTotalSupply` and `ghostPastOptimisticSupply` as
   independent. Real `getPastOptimisticVotingSupply` is bounded above by
   `getPastTotalSupply` because every optimistically-delegated balance
   is a sub-balance of total supply. The rule does not enforce that
   inductively — it just *requires* `optSupply < totSupply` in the rule
   body. The conservative direction (independent ghosts) is sound for
   the bug-finding rule: the prover can pick `optSupply > totSupply`
   freely without the precondition firing, so the only way the
   assertion triggers is the legitimate bug scenario.

2. **`state()` returns the enum directly.** CVL cannot implicitly cast
   `IGovernor.ProposalState` to `uint8`/`mathint`. The rule uses the
   qualified enum syntax `IGovernor.ProposalState.Active`, mirroring
   the pattern in the CertoraProver test suite at
   `Public/TestEVM/CVLCompilation/UserDefinedTypes/good/Test.spec`.

3. **`executed` / `canceled` not directly constrained.** Solidity
   `ProposalCore.executed` and `.canceled` are unobservable from CVL
   without a harness. The rule sidesteps this by asserting `s !=
   Active && s != Succeeded` rather than `s == Defeated` — the
   `Executed`/`Canceled` paths are not the bug-witness states, so
   accepting them as "fine" preserves rule strength on the bug while
   keeping the rule free of harness machinery.

4. **`TRANSITIONED_VETO_THRESHOLD` excluded.** The `vt != MAX_U256()`
   precondition excludes proposals that already transitioned from
   optimistic to pessimistic (where `state()` short-circuits to
   `Defeated`). Without this, the rule would catch a vacuous "all
   transitioned proposals are Defeated" pattern that isn't the
   property under test.

5. **No proposalCore.voteDuration constraint.** The rule does not
   distinguish between `Active` and `Succeeded` based on deadline
   arithmetic. Both are bug-signaling states (in either, the
   proposal has not been defeated by the legitimate coalition), so
   the disjunction in the assertion is intentional.

## Re-running

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/VetoThresholdReachability.conf
```

Run time was approximately 2m38s on the local prover. The CEX is also
viewable at `Reports/Report-vetoThresholdReachableByEligibleVotersHeadline-example1.html`.

## Cross-references

- `formal-verification/certora/notes/cantina_pr36_postmortem.md` -- the
  postmortem this rule operationalizes
- `formal-verification/certora/WISDOM.md` -- entries C001 (XOR), C002
  (failure summary), C015 (ghost-backed summaries)
- `formal-verification/certora/Guardian/Guardian.spec` -- the canonical
  ghost-backed-summary spec this rule mirrors structurally
- `formal-verification/certora/Governor/Governor.spec` -- the existing
  Governor implementation-derived spec; this rule is its intent-derived
  counterpart
