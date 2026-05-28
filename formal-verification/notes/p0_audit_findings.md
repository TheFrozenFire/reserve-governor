# P0 audit findings (against contract source)

The formal-verification effort surfaced two P0 suspicions while proving
validity-preservation lemmas. Both required reading the production
Solidity directly to determine whether the formal models had exposed a
real bug or a modeling artifact. This memo records the conclusions.

The TL;DR: **both items are simulation modeling artifacts. The
contracts are correct.** Each section explains the question, the
trace, and why the formal-side workaround is unnecessary in the
production setting.

---

## #99 — Exchange withdraw underflow against `totalDeposited`

**Source:** [`proofs/StakingVaultExchange_validity.v`](../rocq/proofs/StakingVaultExchange_validity.v),
commit `118d2df`.

**The suspicion.** The simulation's `withdraw` operation models a
single atomic state transition where `totalDeposited -= assets`. With
native rewards present, `totalAssets = totalDeposited +
accumulatedNativeRewards`, so a caller bounded by `assets <=
totalAssets` could pass `assets > totalDeposited`, underflowing.

The validity proof had to add `0 <= assets <= totalDeposited` as an
explicit precondition to close. The natural worry: does the production
contract enforce that, or does it underflow at runtime?

**The trace.** Looking at
[`contracts/staking/StakingVault.sol#L266-L293`](../../contracts/staking/StakingVault.sol)
— `_withdraw` carries the `accrueRewards(_owner, _receiver)` modifier
(line 269). The modifier runs `_accrueRewards`
([L401-L431](../../contracts/staking/StakingVault.sol)) which, at
line 428, executes:

```solidity
totalDeposited += _currentAccountedNativeRewards();
```

After accrue: `totalDeposited == totalAssets()` measured at function
entry. **Only then** does the function body run line 271:

```solidity
totalDeposited -= _assets;
```

And `_assets` is bounded by ERC4626's `maxWithdraw(owner)`, which in
turn is bounded by `totalAssets()`. So after accrue,
`totalDeposited >= _assets`, and the subtraction is safe.

**The general invariant.** The contract maintains a stronger property:
after any accrue, `totalDeposited <= nativeBalanceLastKnown`. Proof
sketch:

- After accrue at T1: `totalDeposited(T1) = old_totalDeposited +
  handout`, with `handout <= old_nativeBalanceLastKnown -
  old_totalDeposited`, so `totalDeposited(T1) <=
  old_nativeBalanceLastKnown`. Then `nativeBalanceLastKnown(T1) =
  IERC20.balanceOf(this)`, which is `>= old_nativeBalanceLastKnown`
  (only airdrops happen between calls).
- Between accrues: neither field mutates.

So the production contract carries the missing precondition as an
operational invariant, established by *running the accrue modifier
before any subtraction*.

**Why the simulation was inadequate.** The simulation modeled
`_withdraw` as a single primitive operation on `(totalDeposited,
totalAssets)`, without representing the accrue-then-mutate ordering.
The proof correctly stalled until we either (a) added the explicit
precondition, or (b) refactored the simulation to model accrue as a
separate step that runs first.

**Verdict.** Not a contract bug. Fidelity gap in the simulation. The
explicit `assets <= totalDeposited` precondition in the proof is
operationally satisfied at the call site by the modifier. No
contract-side action needed.

**Optional simulation improvement.** Refactor `withdraw` in
`simulations/StakingVaultExchange.v` to call an `accrue` step first,
which bumps `totalDeposited` to include native rewards, then perform
the subtraction. This would drop the explicit precondition and
faithfully model the contract's invariant maintenance. Not required
for correctness of the existing proof, which holds under the
precondition that the contract operationally guarantees.

---

## #100 — SelectorRegistry contract-side `keys_nd` analog

**Source:** [`proofs/SelectorRegistry_validity.v`](../rocq/proofs/SelectorRegistry_validity.v),
commit `78355bf`.

**The suspicion.** The simulation's original `Valid.state` declared
`targets_nd`, `sels_nd`, `is_pruned`, and `cross_inv` as invariants.
A concrete counter-example showed they were *not* preservable by
`removeSelector`: with two map entries for the same target carrying
independent selector lists, pruning the first to empty surfaced the
second on lookup, breaking the bicondition `target in targets <->
non-empty allowed list`. The proof required adding `keys_nd : NoDup
(map fst allowedSelectors)`.

The worry: does the production contract maintain this NoDup-on-keys
invariant? If any code path ever inserts under a duplicate key, the
contract's cross-invariant breaks.

**The trace.** Looking at
[`contracts/governance/OptimisticSelectorRegistry.sol#L21`](../../contracts/governance/OptimisticSelectorRegistry.sol):

```solidity
mapping(address target => EnumerableSet.Bytes32Set) private _allowedSelectors;
```

This is a Solidity `mapping`. By the definition of `mapping` storage,
the key (`target`) hashes into a storage slot deterministically;
*there is no representation of "two entries with the same key"*. The
storage layout itself enforces `NoDup` on keys.

The contract's `_add` (L84) and `_remove` (L106) operate on
`_allowedSelectors[target]`, which dispatches to a single
`Bytes32Set` per target. There is no "list of entries" to disambiguate.

**Why the simulation needed `keys_nd`.** Coq has no native mapping
type, so the simulation encoded the contract's `mapping(address =>
Bytes32Set)` as `list (Address * list Selector)`. List-of-pairs
representations *do* admit duplicates in principle. The simulation's
own helpers (`set_allowed_for`, `prune_allowed`) preserve no-duplicate
keys when starting from a no-duplicate-key state — but the proof needs
the invariant stated explicitly because the representation doesn't
guarantee it structurally.

**Verdict.** Not a contract concern. The `keys_nd` invariant is a
modeling discipline forced by encoding a Solidity mapping as a list
in Coq. The contract gets it for free from storage layout. No
contract-side action needed.

**General lesson.** Encoding `mapping(K => V)` as `list (K * V)` in
Coq always requires `NoDup (map fst _)` as an invariant. This is
inherent to the encoding, not an attribute of the contract. Future
audits should note that any such modeling choice in this project
incurs the same overhead and is not symptomatic of a contract issue.

---

# What stays open

Neither P0 led to a contract fix or escalation. The findings are
recorded here so that future readers (audit reviewers, contract
authors revisiting these proofs) understand why the validity proofs
carry their particular preconditions.

The simulations are kept as-is. Reworking them to inline the
contract-side invariant-establishment steps (accrue-before-mutate for
StakingVault, native-mapping abstraction for SelectorRegistry) is a
viable simulation-fidelity improvement, tracked as future work but
not required for any landed theorem.
