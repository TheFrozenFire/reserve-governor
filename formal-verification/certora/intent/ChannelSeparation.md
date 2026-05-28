# ChannelSeparation - S33 optimistic vs standard channel separation

Intent-derived Certora coverage for `governance_intent_and_shapes.md`
shape **S33: Optimistic vs standard channel cross-pollination**. The
two governance channels (optimistic and standard / pessimistic) share
`ProposalCore` storage. Each function that branches on
`_isOptimistic(pid)` is a divergence point - and each divergence is
a place where the intent for one channel could leak into the other.
This spec pins the channel separation at the four most plausible
cross-pollination paths.

## Intent (S33)

The on-chain discriminator is the per-proposal `vetoThreshold`
sentinel: `vetoThreshold(pid) != 0` means "optimistic" (covering both
a live optimistic proposal in `[1, 1e18]` AND a transitioned proposal
stamped with `TRANSITIONED_VETO_THRESHOLD == type(uint256).max`).
`vetoThreshold(pid) == 0` means "standard / pessimistic / nonexistent."

The asymmetric branch points are:

| Function              | Optimistic branch                          | Standard branch                              |
|-----------------------|--------------------------------------------|----------------------------------------------|
| `_queueOperations`    | reverts                                    | OZ default (schedule into timelock)          |
| `_executeOperations`  | bypass via `executeBatchBypass`            | OZ default (execute through timelock)        |
| `_validateCancel`     | `s != Defeated`                            | `s == Pending`                               |
| `_countVote`          | require `support == Against`               | OZ default (For / Against / Abstain)         |
| `_castVote`           | weight via `_getOptimisticVotes`           | weight via `_getVotes`                       |
| `proposalNeedsQueuing`| returns `false` (bypass)                   | returns `true` (commit to timelock)          |
| `state()`             | sentinel `MAX_UINT256` short-circuits to Defeated; else custom optimistic state machine | OZ default |

The four rules below pin the channel-separation invariants at the
queue, vote, and proposal-needs-queuing surfaces, plus the encoding
boundary itself.

## Rules

### CS1: `optimisticProposalCannotEnterStandardQueue`

`queue(...)` reverts when `vetoThreshold(pid) != 0`, covering BOTH a
live optimistic proposal AND a transitioned proposal stamped with the
sentinel. The override at `ReserveOptimisticGovernor.sol:340`
unconditionally reverts via
`OptimisticGovernor__OptimisticProposalCannotBeQueued`. Channel-
separation framing of Governor.spec R13 - the rule survives the
transitioned-proposal case (`vetoThreshold == max_uint256`), which is
the load-bearing extension over R13's pid-range coverage.

### CS2: `standardProposalNeedsTimelockQueuing`

For any pid with `vetoThreshold == 0` (standard / pessimistic), the
view `proposalNeedsQueuing(pid)` returns `true`. The override at line
294 early-returns `false` if `_isOptimistic`; otherwise it falls
through to `super.proposalNeedsQueuing(...)` which OZ implements as a
constant `return true` (`GovernorTimelockControlUpgradeable.sol:90`).

DUAL of Governor.spec R15. Together R15 + CS2 give a complete
partition: optimistic bypasses the queue, standard commits to it.

### CS3: `channelDeterminedByVetoThresholdSentinel`

For any existing proposal (`proposalSnapshot(pid) != 0`), the public
view `isOptimistic(pid)` returns exactly `vetoThreshold(pid) != 0`.
This pins the encoding boundary directly: there is exactly ONE bit of
channel-discrimination state per proposal, and it lives in the
`vetoThreshold` storage slot.

A future refactor that changed `_isOptimistic` to e.g.
`vetoThreshold > 0 && vetoThreshold <= 1e18` (adding an upper bound)
would silently make transitioned proposals look pessimistic, breaking
the sentinel-to-Defeated short-circuit in `state()` and the guard in
`_queueOperations`. CS3 would VIOLATE under that refactor, surfacing
the regression before downstream rules silently weaken.

### CS4: `optimisticProposalRejectsNonAgainstVotes`

`castVote(pid, support)` reverts when `vetoThreshold(pid) != 0` AND
`support != Against`. The override at lines 395-398 requires
`(!_isOptimistic || support == VoteType.Against)`. Channel-separation
framing of Governor.spec R14 - same sentinel coverage as CS1, so the
constraint also holds for transitioned proposals.

## Per-rule status

| ID  | Rule                                               | Status                  |
|-----|----------------------------------------------------|-------------------------|
| CS1 | `optimisticProposalCannotEnterStandardQueue`       | VERIFIED                |
| CS2 | `standardProposalNeedsTimelockQueuing`             | VERIFIED                |
| CS3 | `channelDeterminedByVetoThresholdSentinel`         | VERIFIED                |
| CS4 | `optimisticProposalRejectsNonAgainstVotes`         | VERIFIED                |
| -   | `optimisticProposalCannotEnterStandardQueue-rule_not_vacuous` | VIOLATED (satisfiable)  |
| -   | `standardProposalNeedsTimelockQueuing-rule_not_vacuous`       | VIOLATED (satisfiable)  |
| -   | `channelDeterminedByVetoThresholdSentinel-rule_not_vacuous`   | VIOLATED (satisfiable)  |
| -   | `optimisticProposalRejectsNonAgainstVotes-rule_not_vacuous`   | VIOLATED (satisfiable)  |

Each `_rule_not_vacuous` sanity meta-check is expected to report
VIOLATED - per WISDOM C002 that means the precondition is reachable,
which is the healthy outcome. If any sanity check flipped to VERIFIED,
the corresponding root rule would be vacuously passing.

## Channel-separation guarantees pinned

The four rules together encode the following guarantee:

```
vetoThreshold(pid) != 0  <==>  proposal is on the optimistic channel
                          ==>  queue() reverts                  [CS1]
                          ==>  castVote(pid, non-Against) reverts [CS4]
                          ==>  isOptimistic(pid) == true        [CS3]

vetoThreshold(pid) == 0  <==>  proposal is on the standard channel
                          ==>  proposalNeedsQueuing(pid) == true [CS2]
                          ==>  isOptimistic(pid) == false        [CS3]
```

The biconditional encoded by CS3 is the load-bearing link: it pins the
sentinel storage slot as the sole channel discriminator, so CS1, CS2,
and CS4 can each be stated in terms of `vetoThreshold` directly.

## How these add new content over existing coverage

- **Governor.spec R13** (`optimisticProposalCannotBeQueued`) is
  almost identical to CS1 in CVL form. CS1 explicitly frames the
  channel-separation perspective and surfaces that the rule covers
  the transitioned-proposal case (`vetoThreshold == MAX_UINT256`).
- **Governor.spec R15** (`optimisticProposalNeedsNoQueuing`) gives
  the optimistic side; CS2 is its DUAL, pinning the standard
  channel's commitment to the timelock. A future refactor that
  changed the fallthrough to `return false` would still satisfy R15
  but violate CS2.
- **Governor.spec R14** (`optimisticProposalAcceptsOnlyAgainst`)
  carries CS4's constraint. CS4's channel-separation framing surfaces
  the same property as the dual of "standard channel accepts
  For / Against / Abstain."
- **CS3 is wholly new.** No other rule pins the encoding boundary
  itself - the alignment of the public `isOptimistic` view with the
  `vetoThreshold != 0` storage predicate. CS3 fences this link
  directly, making any encoding-level refactor immediately visible.

## Regression scenarios the rules guard against

1. A refactor to `_isOptimistic` that adds an upper-bound check (e.g.
   `vetoThreshold > 0 && vetoThreshold <= 1e18`) would silently treat
   transitioned proposals (sentinel = `MAX_UINT256`) as standard.
   CS3 VIOLATES immediately; CS1 / CS4 weaken silently.
2. A refactor to `proposalNeedsQueuing` that changes the fallthrough
   from `return true` to a tally-aware computation would still
   satisfy R15 (which only constrains the optimistic side) but
   violate CS2.
3. A refactor that removes the `OptimisticProposalCannotBeQueued`
   guard at `_queueOperations` (e.g. as a misguided "let optimistic
   proposals optionally queue") would violate CS1. R13 catches this
   on the same scope but CS1 frames the channel-separation impact.
4. A refactor to `_countVote` that drops the
   `OptimisticProposalCanOnlyBeVetoed` check would violate CS4. R14
   catches this directly; CS4 frames the channel-separation impact.

## Verification

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/ChannelSeparation.conf
```

Run on `feature/formal-verification` at the bootstrap commit; total
run-time approximately 5 minutes. CS3 verifies in ~2 seconds; CS1
in ~20 seconds; CS2 in ~2 seconds; CS4 in ~2 minutes (the OZ
`_validateStateBitmap` symbolic explosion under the castVote chain).
