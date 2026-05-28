# Rewards conservation — attempted, did NOT close

This rule was the third of four intent-derived candidates from
`notes/cantina_pr36_postmortem.md`. Intended property:

> For each reward token `t`:
> `RewardInfo[t].totalClaimed + sum_{users} UserRewardInfo[t][user].accruedRewards <= balanceAccounted[t]`

## What was attempted

Four rules using CVL's storage-hook ghost-sum pattern:

- `rewardConservationInductive(method f)` — parametric over every
  external method, asserting the invariant pre- and post-call.
- `claimPreservesLedgerGap` — single-step, on the claim path
  specifically.
- `singleUserConservation(method f)` — collapses sum to one user.
- `twoUserConservation(method f)` — collapses sum to two users.

See `RewardConservation.spec`.

## Outcome: every rule VIOLATED on `feature/formal-verification`

The Certora run at `emv-24-certora-28-May--12-30` reports counter-
examples for:

- `claimPreservesLedgerGap` (single-step)
- `rewardConservationInductive` on `claimRewards`, `transfer`,
  `transferFrom`, `initialize`, plus sanity (vacuity) failures on
  pure view methods like `approve`, `checkpoints`,
  `optimisticCheckpoints`
- `singleUserConservation` on `claimRewards`, `transfer`,
  `transferFrom`, `setRewardRatio`, `depositAndDelegate`,
  `initialize`, `poke`
- `twoUserConservation` on the same method set

The breadth of the violation pattern — including on methods that
shouldn't touch reward accounting at all — points strongly at
**modeling fidelity**, not a real conservation bug.

## Root cause: NONDET balance reads

`StakingVault` tracks the high-water mark of rewards via internal
state (`nativeBalanceLastKnown`, `balanceAccounted`) that's updated
by reading `balanceOf(this)` on the underlying asset and reward
tokens. Our spec NONDET-summarizes these IERC20 reads:

```cvl
function _.balanceOf(address) external => NONDET;
```

The prover therefore picks an arbitrary `balanceOf` per call. It
can pick a value that's smaller than the tracked accounting, which
makes `balanceAccounted` an over-statement relative to what's
actually in the vault — and that breaks conservation by
construction. Every method that touches `accrueRewards` or reads
`balanceOf` ends up exposed.

This is the same NONDET-too-loose pattern the summary-fidelity
adversarial review surfaced in `notes/adversarial_summary_fidelity.md`,
applied at a deeper layer: not a TOCTOU across two reads, but a
fundamental discrepancy between the model's accounting and the
ERC20's actual balance.

## What would need to change to make this rule close

Three options, ordered by feasibility:

### Option A: model the underlying ERC20

Use Certora's `DISPATCHER(true)` summary or a harness ERC20 mock
that tracks `balanceOf` consistently. Then `balanceAccounted`
tracking has a real anchor.

```cvl
function _.balanceOf(address) external => DISPATCHER(true);
```

This requires deploying a mock ERC20 alongside the StakingVault and
configuring the conf with `files: ["StakingVault.sol", "MockERC20.sol"]`.

### Option B: bound the assumption

Add a `requireInvariant` chain or explicit precondition:
`balanceOf(this) >= balanceAccounted`. This says "we assume the
vault's actual balance is at least what we've accounted for" — true
in any non-malicious deployment but unsound if a reward token is
adversarial (deflationary, fee-on-transfer, etc.).

### Option C: weaken the property

State conservation *as a delta*: any single call increases
`balanceAccounted` by at most the change in `balanceOf(this)`.
That's weaker but doesn't require modeling the underlying ERC20.

## Decision: ship as *attempted, did not close*

This is the honest result. The intent-derived rules-without-vapor-
proofs discipline (per the postmortem memo) means we don't ship a
verified-looking rule that actually doesn't constrain the
conservation property. The spec is in the repo for future work to
build on; the violation report documents exactly what would need to
change.

## Comparable Rocq result

The Rocq-side conservation theorem
(`rocq/proofs/StakingVaultRewards_conservation.v`,
`audit_rewards_conservation`) DOES close — because the Rocq sim
explicitly models the contract's balance accounting as a single
ground-truth quantity, not as an external NONDET read. The Rocq
sim's purity (everything is a pure function) makes this provable
in a way that bytecode-level Certora cannot without a harness.

That's not a defect in either tool — it's a structural property of
where each operates. This file documents the gap.
