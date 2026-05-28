# ThrottleBound — intent-derived proposer-throttle 2*capacity bound

Intent-derived Certora coverage for the proposer-throttle headline
claim: "an adversary cannot bypass the proposer throttle." This is the
Certora counterpart to the Rocq theorem
`Integration_no_throttle_bypass.no_throttle_bypass` and the CAS
witness `cas/proposer_throttle/charge_evolution.gp`.

## Intent statement (verbatim)

> Under any sequence of `consumeProposalCharge` calls by any proposer,
> the total D18 charge drained within a `PROPOSAL_THROTTLE_PERIOD`
> (12-hour) window is bounded above by `2 * FIX_ONE`. Equivalently,
> when `FIX_ONE mod capacity = 0` (production calibrates
> `capacity = 5`, which divides `1e18` cleanly), the number of
> successful consumes in such a window is bounded above by
> `2 * capacity`.

The factor of two comes from the throttle potentially carrying a full
`FIX_ONE` of pre-existing charge into the window AND receiving a full
period's worth of refill across the window.

## CVL form actually shipped

Certora rules reason about single-step transitions. To capture a bound
over arbitrary-length sequences we factor the property into two CVL
rules plus a base-case rule, which together discharge the inductive
argument:

| Rule  | Status   | Maps to                                  |
|-------|----------|------------------------------------------|
| TB1 `telescopedInvariantPreserved`               | VERIFIED | Rocq `reachable_drain_le_refill` (inductive step) |
| TB2 `invariantImpliesTwoCapacityDrainBound`      | VERIFIED | Rocq `successful_consumes_drain_bounded` (closed form) |
| TB3 `consumeIncrementsAccumulatedDrainByExactlySlot` | VERIFIED | Rocq `consume_drain_identity` (per-step drain) |
| TB4 `consumeRevertsWhenCapacityZero`             | VERIFIED | Library precondition (no div-by-zero) |
| TB5 `setAnchorEstablishesInvariantBase`          | VERIFIED | Rocq `Reachable_init` (base case) |

The telescoped invariant the Rocq proof maintains is

```
accumulatedDrain[a] + currentCharge[a]
  <= anchorCharge[a]
     + (lastUpdated[a] - anchorTime[a]) * FIX_ONE / PERIOD
```

The harness (`ThrottleBoundHarness.sol`) exposes ghost state
(`anchorCharge`, `anchorTime`, `accumulatedDrain` per account) and a
`consumeAndTrack` wrapper that calls `consumeProposalCharge` and
increments `accumulatedDrain` by the per-consume slot. TB1 proves the
invariant is preserved across one `consumeAndTrack` call; TB5 proves
`setAnchor` establishes the base case. The inductive composition
(any number of consumes preserves the invariant) is then a pure
mathematical induction — which Certora discharges automatically by
parametricity: every external call must preserve the property, and the
only external paths that mutate the relevant state are the ones TB1
covers.

TB2 separately proves the closed-form bound: given the invariant AND
`lastUpdated - anchorTime <= PERIOD` AND validity bounds, the
accumulated drain in the window is at most `2 * FIX_ONE`. This is the
headline numeric bound.

## How the full bound shipped

The full `2 * FIX_ONE` drain bound (equivalent to `2 * capacity` count
bound under the divisibility assumption) is captured by the
conjunction TB1 AND TB2 AND TB5:

- TB5 establishes the invariant at the start of any window
  (`setAnchor`).
- TB1 preserves the invariant across every consume
  (`consumeAndTrack`).
- TB2 derives `accumulatedDrain <= 2 * FIX_ONE` from the invariant
  plus the PERIOD window constraint.

The count form `n <= 2 * capacity` is one division away: since each
`consumeAndTrack` adds exactly `FIX_ONE / capacity` to
`accumulatedDrain` (TB3), `n * (FIX_ONE / capacity) <= 2 * FIX_ONE`,
so `n <= 2 * capacity` whenever `capacity` divides `FIX_ONE` exactly.

## Honest scoping notes

1. **Window framing is harness-driven.** The `setAnchor` call is a
   harness primitive, not a contract method. The intent of "a window"
   in the on-chain semantics is implicit (any 12-hour interval), but
   Certora needs an explicit anchor to compare against. The harness
   makes the anchor a first-class object the prover can reason about,
   then we prove the bound for an arbitrary anchor placement. This is
   the same modeling choice the Rocq proof makes (`t_init` is an
   arbitrary valid starting throttle).

2. **The `e.block.timestamp - anchorLU <= 4 * PERIOD` precondition on
   TB1** keeps SMT arithmetic in linear range. The closed-form bound
   TB2 operates over a tighter `<= PERIOD` window, which is the
   semantically relevant one. The four-period slack on TB1 only
   bounds the symbolic-arithmetic state space; it does not weaken
   the bound itself, since TB1 only proves preservation
   (an inductive step) and the closed form derives from TB2 which
   uses the tight window.

3. **The count form `n <= 2 * capacity`** is captured indirectly:
   TB3 pins the per-consume increment to `FIX_ONE / capacity`, and
   TB2 bounds the cumulative drain at `2 * FIX_ONE`. Combining them
   in CVL would require either nonlinear-multiplication reasoning the
   SMT does not handle cleanly OR a per-`capacity` instantiation
   (write TB2bis for each capacity in [1..12]). We rely on the
   downstream Rocq theorem (`successful_consumes_count_bounded`) for
   the algebraic step from drain bound to count bound.

4. **Multi-account adversaries are out of scope.** The Rocq theorem
   bounds consumes by a *single* proposer. An adversary using N
   accounts to each consume the throttle is a separate intent
   property (`N * 2 * capacity` total consumes are possible across
   N proposers, but no single account exceeds `2 * capacity`). The
   `ProposalThrottleStorage` is per-account by construction, so the
   per-account bound is the relevant one.

## Verification command

```sh
source ~/git/reserve/_tools/certora/env.sh
certoraRun.py formal-verification/certora/intent/ThrottleBound.conf
```

All 5 rules + sanity checks verified in run `emv-23-certora-28-May--12-30`.
