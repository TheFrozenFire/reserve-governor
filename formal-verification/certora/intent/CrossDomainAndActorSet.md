# CrossDomainAndActorSet -- S26 + S27 intent rules

Same-class siblings of the Cantina PR #36 catch, distinguished by
which axis they probe:

- **S26 (cross-domain validation)** -- input validated in one
  domain (units, types, populations) but used in another. The catch
  here is the dimensional-scaling test on `proposalThreshold()`:
  the {tok} return value MUST scale linearly with `getPastTotalSupply`.
  A refactor that dropped the supply multiply (e.g. compared the
  D18 fraction directly against votes) would still typecheck but
  would break the scaling invariant.

- **S27 (wrong-actor-set check, per-account variant)** -- auth or
  weight check reads one population when another is semantically
  correct. The Cantina catch was per-supply (`getPastTotalSupply` vs
  `getPastOptimisticVotingSupply`); S27 is the per-account analogue
  (`getPastVotes(account, t)` vs `getPastOptimisticVotes(account, t)`).
  Both reads exist on the staking-vault token; the contract picks
  one in `_castVote` depending on whether the proposal is optimistic.

Both use the **two-ghost-divergence pattern** (WISDOM C017): each
related external read is summarized to its own ghost mapping, and
rules constrain the two ghosts to disagree. The wildcard-NONDET form
is BLIND to which method was called (both reads collapse to a single
fresh nondeterministic choice); two ghosts make the choice
observable, which is exactly what catches the Cantina-class bug.

## Catalog references

- `notes/governance_intent_and_shapes.md` -- S26 and S27 entries.
- `notes/cantina_pr36_postmortem.md` -- the original
  wrong-population catch.
- `notes/same_shape_hunt.md` -- F5 (the original S27 hit on
  `UnstakingManager.claimLock`).
- `WISDOM.md` -- C017 (two-ghost-divergence pattern).

## Rules

### S26.1 -- `proposalThresholdScalesLinearlyWithSupply`

**Intent.** `proposalThreshold()` returns a {tok} value computed as
`ceil(proposalThresholdRatio * supply / 1e18)`. As supply scales
from S1 to S2 (at distinct timepoints), the returned values must
scale by the same ratio. The exact bound:

```
| thr(S1) * S2 - thr(S2) * S1 | <= S1 + S2
```

where the additive slack of `S1 + S2` accounts for the CEIL rounding
(<= 1 tok error each side, cross-multiplied by the other supply).

**Two-ghost connection.** The ghost mapping `ghostPastTotalSupply`
captures the {tok} supply read at distinct snapshots. The cross-
domain catch: if the contract dropped the supply multiply, the
returned value would be CONSTANT in supply, breaking the linearity
bound for any S1 != S2.

**CVL shape.**
```cvl
uint256 s1 = ghostPastTotalSupply[ts1];
uint256 s2 = ghostPastTotalSupply[ts2];
uint256 thr1 = proposalThreshold(e1);
uint256 thr2 = proposalThreshold(e2);
assert | thr1 * s2 - thr2 * s1 | <= s1 + s2;
```

**Expected outcome.** VERIFIED on the current contract -- the
supply multiplication is present at
`ReserveOptimisticGovernor.sol:314`.

A refactor that compared `proposalThresholdRatio` directly against
`getVotes(proposer, t)` (e.g. someone "simplified" the function by
removing the supply mul, thinking the D18 ratio was a direct vote
threshold) would VIOLATE this rule.

### S26.2 -- `sanityS26PreconditionSatisfiable`

Vacuity check (WISDOM C002). VIOLATED here is healthy: documents
that the S26 precondition is reachable.

### S27.1 -- `castVoteOptimisticReadsOptimisticVotes`

**Intent.** `castVote(pid, AGAINST)` on an optimistic proposal
credits exactly `getPastOptimisticVotes(account, snapshot)` to
`againstVotes` -- NOT `getPastVotes(account, snapshot)`.

**Two-ghost connection.** Two ghost mappings:
- `ghostPastVotes[account][snapshot]` -- standard delegated weight
- `ghostPastOptimisticVotes[account][snapshot]` -- opted-in weight

Pin them to disagree (`X != Y`), call `castVote`, assert the
recorded delta equals `Y` (the optimistic value). If the contract
read the WRONG ghost on the optimistic branch, the delta would
equal `X` and the rule VIOLATES.

**CVL shape.**
```cvl
require ghostPastVotes[acct][snap] != ghostPastOptimisticVotes[acct][snap];
castVote(e, pid, AGAINST);
assert againstAfter - againstBefore == ghostPastOptimisticVotes[acct][snap];
```

**Expected outcome.** VERIFIED on the current contract --
`_castVote` at `ReserveOptimisticGovernor.sol:413` correctly
selects `_getOptimisticVotes(account, snapshot)` when the proposal
is optimistic.

If a refactor swapped the two reads on the optimistic branch (e.g.
"simplified" by always using `_getVotes`), the rule would VIOLATE.
This is the per-account form of the Cantina bug: the contract
would aggregate vetoes from the WRONG actor set against the
threshold.

### S27.2 -- `sanityS27PreconditionSatisfiable`

Vacuity check. VIOLATED here is healthy.

### S27.3 -- `castVotePessimisticReadsPastVotes`

**Intent (dual).** `castVote(pid, AGAINST)` on a pessimistic
proposal credits exactly `getPastVotes(account, snapshot)` -- the
standard delegated weight, NOT the optimistic-delegated weight.

This is the mirror of S27.1: the auth-discriminator
`_isOptimistic` must steer the {ghost} read to the *correct*
ghost on both branches. Verifying S27.1 alone leaves open the
question of whether the pessimistic branch is also wired
correctly; S27.3 closes that gap.

**Expected outcome.** VERIFIED -- the same `_castVote` branches to
`_getVotes(account, snapshot, params)` on the non-optimistic side.

## Two-ghost-divergence summary

| Rule  | Ghost A                       | Ghost B                            | Constrained to disagree | Asserts contract reads |
|-------|-------------------------------|------------------------------------|-------------------------|------------------------|
| S26.1 | ghostPastTotalSupply[ts1]     | ghostPastTotalSupply[ts2]          | ts1 != ts2 (same ghost) | Linear in supply ratio |
| S27.1 | ghostPastVotes[a][s]          | ghostPastOptimisticVotes[a][s]     | X != Y                  | Optimistic ghost       |
| S27.3 | ghostPastVotes[a][s]          | ghostPastOptimisticVotes[a][s]     | X != Y                  | Past-votes ghost       |

S26.1 is a degenerate two-ghost case (single ghost, two keys); the
divergence is in the *input* to the ghost, not across two ghost
families. S27.1 and S27.3 are the textbook C017 form, mirroring
the Cantina catch on per-account semantics.

## Catches that would VIOLATE these rules

- A refactor of `proposalThreshold()` that removed the
  `supply` multiplication, returning the D18 fraction directly --
  VIOLATES S26.1.
- A refactor of `_castVote` that branched the wrong way (used
  `_getOptimisticVotes` for pessimistic proposals or vice versa) --
  VIOLATES S27.1 or S27.3.
- A refactor of `_castVote` that always used `_getVotes` regardless
  of `_isOptimistic` -- VIOLATES S27.1 specifically. This is the
  exact per-account analogue of the Cantina headline (per-supply
  variant).
- A refactor that summed both reads (`_getVotes + _getOptimisticVotes`)
  for double-counted weight -- VIOLATES S27.1 (delta would be X+Y
  not Y).

## Soundness notes

The rules rely on the two-ghost summary form (WISDOM C015 / C017).
NONDET-on-everything would be insensitive to the read choice; the
ghost form is precisely strong enough to distinguish them. The
rules do NOT assume any axiom relating the two ghosts (no
`getPastVotes <= getPastOptimisticVotes` or similar) -- both are
free uint256 values, and the assertion is purely a behavioral
discriminator.

## Status

See the run log in `emv-*-certora-CrossDomainAndActorSet-*`. Each
rule status is reported via `treeView/treeViewStatus_*.json`. The
sanity rules (S26.2, S27.2) are EXPECTED VIOLATED (healthy per
WISDOM C002); the headline rules (S26.1, S27.1, S27.3) are
EXPECTED VERIFIED on the current contract.
