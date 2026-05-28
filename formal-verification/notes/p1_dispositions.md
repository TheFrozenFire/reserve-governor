# P1 dispositions (decisions, no contract changes)

Four P1 backlog items are decision-shaped rather than work-shaped:
either "tighten the simulation" or "tighten the contract" or
"document and accept." For each, this memo records the decision and
the reasoning.

The proof-writing P1 items (#103, #119, #120) and the deeper
external-validation items (#105, #124) are tracked separately.

---

## #101 — Governor sentinel: simulation vs contract encoding

**Question.** The contract stores transition-to-pessimistic by
writing `vetoThreshold = type(uint256).max` (see
[`lib/ProposalLib.sol:122`](../../contracts/governance/lib/ProposalLib.sol)),
and `state()` short-circuits to Defeated when it reads that sentinel
(see [`ReserveOptimisticGovernor.sol:243`](../../contracts/governance/ReserveOptimisticGovernor.sol)).
The simulation in `Governor.v` instead sets `phase := PhaseDefeated`
directly. Decide: tighten the simulation to use the sentinel, or
accept the divergence.

**Decision: accept and document.**

The two encodings are observationally equivalent on every theorem
already proved (state queries return Defeated, no further
transitions, no double-execution). The audit-narrative claims are
all about observable behavior, not storage layout.

The non-de-escalation proof (`commit a288c7c`) introduced a parallel
`transition_to_pessimistic_sentinel` operation that *does* use the
sentinel encoding, so when a downstream proof needs the explicit
sentinel storage value, it can call that operation. Other proofs
keep using the simpler phase-direct form.

Tightening the simulation would require re-proving roughly six
lemmas in `Governor.v` and its dependents (`Governor_validity`,
`Governor_xcheck`, `Governor_no_de_escalation`,
`Governor_no_double_execution`, two integration files). Zero
audit-narrative gain.

**Action:** none. Documented here.

---

## #102 — ProposerThrottle: per-consume rounding leak

**Question.** [`ThrottleLib.sol:25`](../../contracts/governance/lib/ThrottleLib.sol)
subtracts `1e18 / capacity` (integer division) from `currentCharge`
per consume. When `capacity` doesn't divide 1e18 evenly, the discard
is `1e18 mod capacity` D18 per consume. Concretely, for `capacity =
7`: leak per consume = 1 D18 wei. For `capacity = 3`: 1 D18 wei.

Bounded by `(capacity - 1)` D18 per consume in the worst case.
Decide: accept and document, change subtraction formula, or use
ceil-division.

**Decision: accept and document.**

The leak is `(capacity - 1) / 1e18` of one proposal slot per consume.
At `capacity = 7` (a contrived worst-case for residual), that's 6
wei of D18 per consume against 1e18 wei per slot — six millionths of
a femto-slot, per consume. Over 10^9 consumes, total accumulated
leak is ~6e-9 slots. The throttle is not a precise-accounting
instrument; it's a per-12h rate limiter.

Switching to `(currentCharge * capacity - 1e18) / capacity` would
introduce a different rounding bias (toward over-subtraction), and
ceil-division would let the contract refuse a valid proposal under
some inputs. Neither alternative is clearly better.

The CAS witness `cas/proposer_throttle/charge_evolution.gp` INV-6
already documents the leak's existence and bounds it.

**Action:** none. Leak is bounded and documented in the CAS witness.

---

## #104 — Native rewards: 2.78 ppm overshoot from discrete exponential

**Question.** [`StakingVault.sol:490`](../../contracts/staking/StakingVault.sol)
computes the per-payout handout fraction as:

```
1e18 - UD60x18.wrap(1e18 - rewardRatio).powu(elapsed).unwrap() - 1
```

The continuous-time target is `1 - e^(-rate * elapsed)`. With
`rewardRatio = ln(2) / halfLife`, the discrete `powu` overshoots the
continuous form by approximately 2.78 ppm over one half-life.
Documented in the CAS witness `cas/staking_vault/exchange_rate.gp`
INV-6. Decide: tighten the calibration, or accept.

**Decision: accept and document.**

The overshoot is one-directional (always in the user's favor — they
get marginally more reward than the continuous-target). The
magnitude (~3 ppm per halfLife) is below any reasonable token's unit
of account. The contract uses integer exponent `powu` to avoid the
gas cost of `exp`, and the calibration `LN_2 / halfLife` already
encodes the "ln 2" factor for continuous halving — the residual
2.78 ppm is a numerical artifact of `(1 - r)^n` versus `e^(-rn)` for
small `r`.

Tightening would require either (a) replacing `powu` with a more
expensive operation, or (b) pre-distorting `rewardRatio` to absorb
the overshoot — but the distortion would itself drift if `halfLife`
changes, since the overshoot depends on `rewardRatio`.

This is a known calibration artifact. Document the ~3 ppm tolerance
as a property of the reward stream.

**Action:** none beyond the existing CAS-side documentation.

---

## #121 — No-throttle-bypass: 2× capacity worst case

**Question.** The headline theorem `audit_no_throttle_bypass` bounds
successful consumes at `2 * capacity` per `PROPOSAL_THROTTLE_PERIOD`
window (tight at `capacity` only for drained-start). This is a real
arithmetic property: a window can span from `currentCharge = 1e18`
through a `1e18` refill to a second `1e18` charge level, allowing
`2 * capacity` consumes total. Decide: document in product
rate-limit messaging, tighten the contract to enforce drained-start,
or shorten the throttle period.

**Decision: document.**

The 2× behavior is the well-known token-bucket window-edge effect.
Any per-window rate limiter exhibits it: bursting at the end of one
window plus the start of the next can deliver up to 2× the
nominal rate. Tightening the contract to drained-start at submission
time would change the API surface (proposals would silently fail
when the throttle hasn't actually been bypassed by anyone) and
introduce its own corner cases.

Shortening the throttle period to halve the effective cap would
change the configured policy, which is governance's decision and
out of scope here.

The audit-narrative theorem is correct as stated. Product messaging
around the rate limit should describe the per-account cap as "up to
2× capacity per `PROPOSAL_THROTTLE_PERIOD`" rather than "capacity
per `PROPOSAL_THROTTLE_PERIOD`", to set accurate user expectations.

**Action:** none on the contract side. The recommendation for
product-messaging is recorded here so it surfaces if/when rate-limit
docs are written.

---

# What stays open

These four items are now decisions of record. The remaining P1 work
is proof-writing and external-validation:

- **#103** Integration_withdraw_immediate.v — new proof file
- **#119** Guardian revoke/cancel validity backfill — new proofs
- **#120** StakingVault Delegation validity / conservation — new proofs
- **#105** UD60x18 powu axioms — validate against deployed PRBMath
- **#124** Yul-equivalence for upgrade_authorized — bridge to bytecode
