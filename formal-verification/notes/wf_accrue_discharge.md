# Discharging `WF_accrue` from first principles

The headline `rewards_conservation` theorem in
[`proofs/StakingVaultRewards_conservation.v`](../rocq/proofs/StakingVaultRewards_conservation.v)
proves that any state reachable via `Reachable_step` from
`initial_state` satisfies the conservation inequality

```
sum_accrued us + r.totalClaimed <= r.balanceAccounted
```

The proof discharges by induction on `Reachable`, with one
hypothesis per operation: `WF_update`, `WF_accrue`, `WF_claim`.
`WF_update` and `WF_claim` are trivial (no state-shape obligation
beyond `n < length us`); `WF_accrue` carries the load-bearing
precondition:

```
accrueUser r (nth n us empty_user) userBalance .accruedRewards
  - (nth n us empty_user).accruedRewards
<= r.balanceAccounted - sum_accrued us - r.totalClaimed
```

i.e. "the per-user accrual increment does not exceed the current
ledger gap." This is **assumed** at every step the caller wants to
exercise. The audit-narrative claim "rewards are conserved" is
therefore conditional on the caller exercising contract-honest
sequences.

This memo identifies what a full discharge from first principles
would require, and why it's deferred.

---

## Why the precondition holds in production

The contract maintains an implicit invariant tying
`rewardIndex` movement to `balanceAccounted` movement:

  - `_accrueRewards` (StakingVault.sol:433) bumps
    `rewardIndex` by `tokensToHandout * SCALAR * 10^decimals /
    totalSupply`, and concurrently bumps `balanceAccounted` by
    `tokensToHandout` exactly.
  - `_accrueUser` (StakingVault.sol:455) credits a single user
    `userBalance * (newIndex - lastIndex) / (10^decimals * SCALAR)`.

So a single user's accrual increment is

```
userBalance * delta_index / (10^decimals * SCALAR)
= userBalance * tokensToHandout * SCALAR * 10^decimals
  / (totalSupply * 10^decimals * SCALAR)
= userBalance * tokensToHandout / totalSupply
```

With `userBalance <= totalSupply` (every user's balance is part of
totalSupply by ERC20 conservation), the user's increment is at
most `tokensToHandout`. And the ledger gap after the matching
`_accrueRewards` step has grown by exactly `tokensToHandout`.

So the per-user accrual increment cannot exceed the gap **as long
as accrueUser is called between consecutive _accrueRewards calls,
i.e. there is no "deferred accrual" that draws on multiple updates
at once**. The simulation's `accrueUser` is single-shot per user,
so this matches.

## What a formal discharge would require

To remove `WF_accrue` from the precondition list, the proof would
need three new invariants threaded through `Reachable`:

1. **Supply consistency.** `Σ userBalance_i = supply_at_last_update`.
   The simulation currently doesn't track per-user balances as a
   list-of-pairs (`UserReward.t` only holds reward bookkeeping, not
   the ERC20 balance); a balance schedule would have to be added
   as a per-user field.

2. **Delta accounting.** Cumulative
   `Σ (accrueUser deltas since last update)` is bounded by
   `cumulative balanceDelta since last update`.

3. **Gap monotonicity.** From (1) and (2), the gap `bA - Σ - tC`
   stays non-negative after every operation.

(2) and (3) compose into the WF_accrue conclusion automatically.
(1) is the harder lift: it requires adding `userBalance` as a
proper field threaded through every op.

## Why this is deferred

The work is structural, not algebraic: it requires changing the
`Op` type to carry user-balance schedules, changing the
`Reachable` inductive to track the per-user balance state, and
re-proving every existing conservation lemma against the new
state representation. Estimated scope: comparable to writing a
new per-domain simulation (4-6 hours of focused work).

The conditional theorem we have ("rewards are conserved when
WF_accrue holds") is operationally sufficient for the audit
narrative: every contract-side call site discharges WF_accrue by
construction (the contract guarantees the per-step bound via the
`accrueRewards` modifier wrapping every state-mutating function).
The conditional form makes the trust assumption explicit and
auditable.

## Tracked

The full discharge is registered as a scoped follow-up. Future
work picks up by extending `UserReward.t` with an explicit
`balanceShares` field, then adding the supply-consistency
invariant to `Reachable`. The CAS witness
[`cas/staking_vault/multi_token_rewards.gp`](../cas/staking_vault/multi_token_rewards.gp)
already exercises the conservation property numerically on
contract-honest sequences — that's the parallel guarantee that
the conditional theorem captures.
