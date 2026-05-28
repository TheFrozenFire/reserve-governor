# Rocq + CAS informed Certora priorities

Read-only exploration aligning the three verification layers
(Rocq simulation proofs in `formal-verification/rocq/`, PARI/GP CAS
witnesses in `formal-verification/cas/`, Certora CVL specs in
`formal-verification/certora/`) to identify the highest-leverage
next Certora work.

## Summary

Rocq carries ~150 audit-narrative theorems across 12 contract
domains (`rocq/Audit.v`), heavily weighted toward state-machine
safety, conservation, and per-domain validity preservation against
a hand-written Gallina simulation. CAS provides numerical witnesses
that cross-check the simulation against the production arithmetic
(twelve `.gp` scripts, INV-numbered to match Rocq invariants).
Certora today covers 58 rules across 8 contracts, weighted toward
role gates, zero-value rejects, and single-step post-conditions
where the prover can close cleanly without summarizing whole
sub-machines. Certora's biggest leverage is in three places:
(1) re-proving the simple state-mutation rules already Rocq-proved
so they also hold on the **emitted bytecode** (source-to-bytecode
equivalence), (2) covering arithmetic edges Rocq punts on (rounding
direction, overflow boundaries, OZ mulDiv corners), and (3) hardening
TOCTOU/oracle-purity gaps the Rocq simulation cannot reach by its
shape (Audit.v Caveat-4, Caveat-11).

## Layer comparison

### What Rocq proves that Certora doesn't (yet)

A property is a candidate for Certora porting when its CVL form is
expressible without modeling an unbounded sub-machine, and the
property's value comes from re-confirming it at the bytecode layer
(catching solc/Yul lowering bugs, ABI-encoding edges, modifier
expansion subtleties).

| Rocq theorem | Certora port worth it? | Reason |
|---|---|---|
| `audit_throttle_consume_storage_delta` (charge -= FIX_ONE/capacity, lastUpdated := now) | **Yes — high.** Direct port: single state delta on a single function. Confirms solc didn't lower the integer divide differently than the simulation. | CAS already witnesses INV-2 numerically; CVL closes the bytecode side. |
| `audit_throttle_preserves_validity` (0 <= currentCharge <= FIX_ONE) | **Yes — high.** Invariant over a small storage struct. Trivial CVL `invariant` block. | |
| `audit_unstaking_no_double_spend` (lock cannot be both claimed and cancelled) | **Partially in Certora (U5, U6).** Rocq's reachable-state form is stronger; CVL form is per-state. Acceptable gap — the per-state form is the inductive base. | |
| `audit_unstaking_createLock_conservation` (total_active += amount) | **Yes — medium.** CVL ghost variable summing active amounts; assert delta after createLock. Catches accounting drift at bytecode. | |
| `audit_vault_round_trip_floor_bound` (convertToAssets(convertToShares(a)) <= a) | **Yes — high, but scope.** Already-deferred in Certora README per OZ `mulDiv` overflow. The general case explodes; a **bounded-scope** rule (assets < 1e30, supply < 1e30) is provable and high-value. | |
| `audit_vault_share_rate_monotone_under_accrue` (share price never falls on accrue) | **Yes — medium.** Express as: after `_accrueRewards`, `convertToAssets(1e18) >= old_convertToAssets(1e18)`. May need `_calculateHandout` CONSTANT summary (same trick StakingVault.spec already uses). | |
| `audit_rewards_index_monotone` (rewardIndex non-decreasing) | **Yes — high.** Direct CVL invariant; bytecode-level confirmation is cheap. | CAS INV-1 witnesses this; triple confirmation candidate. |
| `audit_rewards_totalClaimed_monotone` | **Yes — high.** Same pattern. | |
| `audit_rewards_claim_zeroes_accrued` | **Yes — medium.** Post-condition on claim: accruedRewards[user] == 0. | |
| `audit_rewards_conservation` (balanceAccounted = Σ accrued + totalClaimed) | **No.** Sum over a mapping doesn't have a clean CVL idiom; needs heavy ghost arithmetic. Rocq is the right tool here. (And Caveat-1 already documents this is conservation-as-hypothesis even in Rocq.) | |
| `audit_governor_execute_twice_reverts` (execute_optimistic single-shot) | **Yes — high.** Rule shape: call execute, store result, call execute again, assert revert. Models OZ proposal state machine via NONDET, only execution-path matters. | |
| `audit_governor_propose_requires_throttle` | **Yes — medium.** CVL can express: if `consumeProposalCharge` reverts (NONDET-controlled), `proposeOptimistic` reverts. | |
| `audit_governor_cannot_de_escalate_after_transition` | **No.** Full reachable-state induction over the eight-phase machine; CVL's parametric rules can't carry the induction. Rocq is correct tool. | |
| `audit_governor_terminal_phase_exclusivity` (PhaseExecuted xor PhaseStdExecuted) | **Partial.** A per-state form ("never both flags set at once") is a CVL invariant; the over-traces form is Rocq. | |
| `audit_timelock_no_double_execute` / `audit_timelock_done_absorbing` | **Yes — high.** Already half-covered (T6 marks Done; T7 rejects rescheduled). A **doubleExecuteReverts** rule and a **doneAbsorbing** invariant are natural CVL. | |
| `audit_timelock_bypass_preserves_slow_path` (bypass(B) doesn't touch A's timestamp) | **Yes — high.** Direct two-id parametric rule: pick A, B with A != B, bypass(B), assert timestamps[A] unchanged. | |
| `audit_guardian_only_cancel_reverts_on_defeated` (guardian-only cannot cancel Defeated) | **Yes — high.** Already half-covered (G5 = unauthorized). The guardian-vs-admin tier split needs a ghost-backed `state(id)` summary; pattern matches the existing `ghostIsOwner` idiom. | |
| `audit_version_register_extends_history` / `audit_version_deprecate_sticky` | **Mostly covered (V4, V5, V6).** Sticky deprecation = V4; cross-key isolation = V6. Append-only history is the only piece deferred (V7 — needs ghost-tied invariant on private `latestVersion`). | |
| `audit_integration_propose_optimistic_implies_throttle_and_allowlist` | **No.** This is the meat of the cross-contract composition — Rocq's right surface. CVL would need NONDET summaries that defeat the purpose. | |
| `audit_integration_no_throttle_bypass` (2*capacity bound per 12h window) | **No.** Telescoping sum over n consumes — Rocq's natural strength. CAS witnesses INV-1; not Certora's tool. | |
| `audit_integration_register_then_authorize_self` (latest && !deprecated) | **Yes — high.** This is exactly `_authorizeUpgrade` at the bytecode, currently deferred in StakingVault.spec. Yul-equivalence memo (`notes/yul_equivalence_upgrade_authorized.md`) already identifies the function structure. Direct Certora rule pinning the auth check IS the bridge to bytecode. | |

### What CAS validates that Certora could verify against bytecode

CAS scripts produce numerical witnesses against the same arithmetic
the contract uses (PARI big-int evaluator mimics the Yul semantics).
A property that holds across the CAS sweep is a property the CVL
prover should be able to close on the bytecode — and any discrepancy
between the CAS witness and the Certora result is a smell worth
investigating.

- **`charge_evolution.gp` INV-2** (per-consume delta exactly
  `FIX_ONE/capacity`). CAS proves this on integer-arithmetic
  witnesses; Certora can close it against the actual Yul integer
  div emitted for `ThrottleLib.consumeProposalCharge`. Triple
  candidate. (Discrepancy here would mean solc/Yul changed the
  rounding direction.)
- **`charge_evolution.gp` INV-6** (per-consume rounding leak
  bounded by `capacity` wei). The exact wei-level leak is what
  makes the `2 * capacity` headline bound require divisibility;
  a CVL rule asserting `floor(1e18/capacity) * capacity <= 1e18
  < (floor(1e18/capacity)+1) * capacity` makes the implicit
  precondition explicit. Medium.
- **`exchange_rate.gp` INV-1** (`handout(0, _) == 0` and
  `handout(_, 0) == 0`). Trivial CVL; matches Certora's existing
  SV1/SV2 (`convertToShares(0) == 0`). Already triple-covered for
  the conversion edge; not yet covered for the handout primitive
  itself.
- **`exchange_rate.gp` INV-2** (`handout(b, t) <= b`). Bytecode-
  level proof would catch any Yul lowering bug that overflows
  the handout multiplication. CVL form requires summarizing
  `UD60x18.powu` as nondeterministic-in-[0,1e18] (current
  StakingVault.spec already does this with `_calculateHandout =>
  CONSTANT`). High.
- **`lock_lifecycle.gp` INV-5** (conservation: `targetToken.balanceOf(this)
  == Σ amount over active locks`). The cross-contract invariant.
  Certora can express it via a ghost mirror of the active-locks
  sum + a ghost mirror of token balanceOf, asserting equality.
  Medium — has the EnumerableSet/ghost pattern complexity.
- **`scheduling_ordering.gp` INV-5** (bypass(B) doesn't disturb
  scheduled A). Same as `audit_timelock_bypass_preserves_slow_path`.
  Triple candidate.
- **`multi_token_rewards.gp` INV-3** (per-user accrue delta sums
  to total payout with bounded floor drift). The per-user side
  is provable in CVL with a small ghost; the aggregate is Rocq's
  territory.

### What Certora could uniquely catch (bytecode-only, ABI-edge, reentrancy)

Properties that **only** the Certora layer can express, because
they depend on EVM-level behavior the Rocq simulation abstracts
away.

- **`_executor()` deque-pop coverage** in OZ Governor. The Rocq
  `Governor` simulation does not model the deque used to decide
  whether a call originated from the timelock execution. Certora
  reads it through `optimistic_loop`/`loop_iter`. Any
  `onlyGovernance` rule (already in Governor.spec R2, R3) catches
  bytecode-level confusion the Rocq sim can't reach.
- **Storage-slot collision invariants** for upgrades. The Rocq
  simulation has no storage layout. Certora rules asserting
  "storage[N] is only mutated by function F" catch upgrade-related
  storage corruption that Rocq can't see.
- **ABI-encoding edge cases** in `cancel(address[], uint256[],
  bytes[], bytes32)` and `executeBatch(...)`. Calldata length
  underflow, dynamic array boundary tricks. Rocq sees only the
  high-level inputs. **High value for the Guardian cancel surface
  given the documented TOCTOU concern (Audit.v Caveat-4).**
- **Modifier expansion / inheritance order.** The
  `onlyRole(DEFAULT_ADMIN_ROLE)` check on
  `StakingVault._authorizeUpgrade` is documented in Audit.v
  Caveat-3 as "NOT covered by Integration_upgrade_authorization."
  Certora is the right tool — a direct rule that a non-admin
  caller cannot reach the version-registry check.
- **`onlyRole` race conditions** during constructor / initializer.
  The Rocq simulation starts from a `valid_initial_state`. The
  bytecode has an initializer path; Certora can express
  "post-initialize, role X is granted to exactly the deployer
  argument."
- **Reentrancy through hookable tokens** (Audit.v Caveat-11
  partial). The Rocq ERC20 mock is a pure oracle; the Yul has
  actual external calls. Certora can model an arbitrary reentrant
  re-entry via the wildcard external summaries flipping internal
  storage between calls. (Limited but possible — pick a known
  reentry-sensitive function like `claimRewards` and assert that
  re-entering it from inside `transfer` doesn't double-pay.)

## Triple-confirmation candidates (highest priority)

Properties where Rocq has a clean machine-checked proof, CAS has
a numerical witness, AND Certora can express the property without
modeling an unbounded sub-machine.

### TC1: ProposerThrottle `consume` storage delta is exact

**Rocq evidence:** `proofs/ProposerThrottle.v` —
`consume_success_storage_delta` (re-exported as
`audit_throttle_consume_storage_delta`). States that after a
successful consume, `lastUpdated := now` and `currentCharge :=
readCharge_pre - FIX_ONE/capacity`.

**CAS evidence:** `cas/proposer_throttle/charge_evolution.gp`,
INV-2 ("After consumeProposalCharge succeeds at time [now]: ...").
Sweeps capacities `{1, 2, 3, 5, 7, 10, 100}` and validates the
two-field delta exactly.

**Certora approach:** Single rule on `ThrottleLib.consumeProposalCharge`
(library — needs a thin caller harness, or invoke via Governor's
`proposeOptimistic` with NONDET summaries on everything else).
Capture `currentCharge` and `lastUpdated` before/after. Assert the
delta. No summaries needed beyond what Governor.spec already does.

**Why high-priority:** Confirms that the solc compilation of the
integer division `FIX_ONE / capacity` matches the Gallina
specification. The rounding direction here is what makes the
`2 * capacity` headline bound work; a silent rounding flip at the
Yul level would break the entire `Integration_no_throttle_bypass`
result. This is the single cheapest "triple confirmation" win in
the codebase.

### TC2: StakingVault rewardIndex is monotone non-decreasing

**Rocq evidence:** `proofs/StakingVaultRewards.v` —
`updateRewardIndex_monotone` (re-exported as
`audit_rewards_index_monotone`).

**CAS evidence:** `cas/staking_vault/multi_token_rewards.gp`,
INV-1 ("rewardIndex is monotonically non-decreasing across
accruals"). Sweeps 8 successive accruals against a deterministic
supply.

**Certora approach:** CVL `invariant` (parametric over reward
token address): `forall token: rewardInfo[token].rewardIndex
>= old(rewardInfo[token].rewardIndex)` across every state
transition. Needs the existing NONDET summaries on IERC20
balanceOf / transfer. The `_calculateHandout => CONSTANT` summary
in StakingVault.spec is too coarse — would need to refine to
`>= old_constant` instead. Tractable.

**Why high-priority:** The rewardIndex monotonicity is the
linchpin of the entire reward accounting model. If a Yul-level
underflow or signedness bug could move the index backwards once,
every accrued-balance computation downstream is wrong. CVL on
bytecode is the strongest signal we can get short of running
production.

### TC3: Timelock `executeBatchBypass(B)` does not disturb a separately scheduled `A`

**Rocq evidence:** `proofs/Timelock.v` —
`bypass_preserves_slow_path` (re-exported as
`audit_timelock_bypass_preserves_slow_path`).

**CAS evidence:** `cas/timelock/scheduling_ordering.gp`, INV-5
("Bypass preserves slow-path queue ordering: after
scheduleBatch(A, delay); bypass(B); the queued A's executableAt
is unchanged"). Concrete event-replay scenario.

**Certora approach:** Two-id parametric rule. Pre-state: `timestamps[idA]
== tsA != 0` (Waiting). Action: `executeBatchBypass(..., salt_B)`
where the computed `idB != idA`. Post-state assertion:
`timestamps[idA] == tsA` (unchanged). The current Timelock.spec
T6 covers the Done marker on `id`; this rule covers cross-id
non-interference. The empty-arrays pattern in T6/T7 carries over
directly.

**Why high-priority:** The bypass path is the optimistic
fast-track that auditors will scrutinize most heavily because
it sidesteps the normal delay gate. Re-proving the
"doesn't-disturb-the-queue" property at bytecode level (in
addition to Rocq) closes the most plausible audit objection
to the bypass feature.

### TC4: Reward accruedRewards monotone non-decreasing for a user

**Rocq evidence:** `proofs/StakingVaultRewards.v` —
`accrueUser_accrued_monotone` (re-exported as
`audit_rewards_user_accrued_monotone`).

**CAS evidence:** `cas/staking_vault/multi_token_rewards.gp`,
INV-2 ("userRewardTracker.accruedRewards is non-decreasing
across accruals, assuming positive balance and non-negative
deltaIndex").

**Certora approach:** Parametric over `(user, token)`: assert
`userRewardTracker[user][token].accruedRewards >= old(...)`
across any transition that does NOT include `claim`. (Claim is
the only operation that zeroes it; everything else must be
monotone.) Same `_calculateHandout` summary refinement as TC2.

**Why high-priority:** Pairs naturally with TC2 — together
they cover the read-side and write-side of the reward index
accounting. Catching a single skipped accrual or a sign-flipped
delta requires both rules.

### TC5: VersionRegistry `_authorizeUpgrade` accepts iff (latest && !deprecated)

**Rocq evidence:** `proofs/Integration_upgrade_authorization.v` —
three theorems (`register_then_authorize_self`,
`register_two_then_authorize_rejects_old`,
`register_deprecate_then_authorize_rejects`), re-exported as
`audit_integration_register_then_authorize_self` (plus two
siblings).

**CAS evidence:** `cas/version_registry/registry_history.gp`,
INV-5 ("Upgrade-gate correctness. The _authorizeUpgrade-style
predicate ...").

**Certora approach:** This is currently a documented gap
(certora/README.md: `_authorizeUpgrade` (StakingVault) deferred).
The Yul-equivalence memo `notes/yul_equivalence_upgrade_authorized.md`
identifies the exact Yul function (`fun_authorizeUpgrade_inner`)
and its three checks (`isDeprecated`, `latestVersionHash ==
queryHash`, `stakingVaultImpl == registered_impl`). A CVL rule
on `StakingVault._authorizeUpgrade` (calling out to a
ghost-backed VersionRegistry) closes this.

**Why high-priority:** Audit.v Caveat-3 explicitly says the
Integration theorem does NOT cover the `onlyRole` admin gate.
Certora can — it sees the modifier expansion. **This single
rule replaces both the deferred Certora item AND the deferred
Yul-equivalence mechanization sketch.**

## Recommended next Certora work (prioritized)

1. **[high]** `executeOptimisticOneShot` (Governor) — port
   `audit_governor_execute_twice_reverts`. Single rule; calls
   `execute_optimistic` once, captures the result via a status
   ghost, calls again, asserts revert. Closes the no-double-execute
   property at bytecode. Pairs with the existing G7-style
   single-shot timelock coverage.
2. **[high]** `rewardIndexMonotone` (StakingVault) — TC2 above.
   CVL invariant on `rewardInfo[*].rewardIndex` across every
   state-mutating method. Refine the existing
   `_calculateHandout => CONSTANT` summary to
   `_calculateHandout => MONOTONE` (CVL has this primitive).
3. **[high]** `bypassDoesNotDisturbOtherIds` (Timelock) — TC3
   above. Two-id parametric rule. Fits naturally into Timelock.spec.
4. **[high]** `authorizeUpgradeRequiresLatestAndActive`
   (StakingVault) — TC5 above. Removes one of the explicitly-deferred
   items in certora/README.md and closes Audit.v Caveat-3.
5. **[high]** `consumeStorageDeltaExact` (Governor or a Throttle
   harness) — TC1 above. Confirms the integer divide rounding
   direction on `FIX_ONE / capacity`.
6. **[med]** `userAccruedMonotoneExceptClaim` (StakingVault) — TC4.
   Pairs with #2.
7. **[med]** `guardianCannotCancelDefeatedOptimistic` (Guardian) —
   port the tier-split from `audit_guardian_only_cancel_reverts_on_defeated`.
   Needs the ghost-backed `state(id)` summary pattern already
   used in RewardTokenRegistry/VersionRegistry specs. Existing
   G5 covers unauthorized; this adds guardian-vs-admin
   discrimination.
8. **[med]** `terminalPhasesAreExclusive` (Governor) — per-state
   form of `audit_governor_terminal_phase_exclusivity`. CVL
   invariant: `!(PhaseExecuted && PhaseStdExecuted)` for any
   stored proposal. Trivial if the storage layout exposes both
   flags; needs a ghost otherwise.
9. **[med]** `createLockConservation` (UnstakingManager) — port
   `audit_unstaking_createLock_conservation`. Ghost `total_active`,
   assert delta == `amount` after createLock when `unlockTime > 0`.
10. **[low]** `vaultRoundTripFloorBound`, bounded scope
    (StakingVault) — `convertToAssets(convertToShares(a)) <= a`
    for `a < 1e30`. Already-deferred in README; bounded scope
    sidesteps the OZ `mulDiv` overflow that blew up the solver.
    Worth attempting with a tightened `require a < 2^100`.

## Anti-recommendations (where NOT to put Certora effort)

- **`audit_rewards_conservation`** (balanceAccounted = Σ accrued
  + totalClaimed). The sum over a mapping doesn't have a clean
  CVL idiom, and Audit.v Caveat-1 already documents the proof
  as conservation-as-hypothesis. CVL would add no information
  the Rocq layer already has, and would burn solver time on
  ghost-arithmetic plumbing. Leave with Rocq.
- **`audit_integration_no_throttle_bypass`** (2*capacity in
  12h window). Telescoping induction over a sequence of consume
  calls — naturally Rocq's strength. CVL can't carry the
  sequence; you'd need to model an arbitrary-length proposal
  sequence with NONDET timestamps, and the prover would either
  time out or fail vacuously.
- **`audit_governor_cannot_de_escalate_after_transition`**.
  Full reachable-state induction over the eight-phase machine.
  Beyond CVL's parametric-rule shape.
- **`audit_proposal_id_injective`** (proposalId hash injective).
  Already an OZ-Governor concern at the keccak level. Certora
  uses `optimistic_hashing: true` which assumes collision
  freedom — re-asserting injectivity inside that frame is
  vacuous. Rocq handles it as a `Parameter + Axiom-injective`,
  which is honest about the assumption.
- **End-to-end existence theorems**
  (`optimistic_lifecycle_exists`, `standard_lifecycle_exists`).
  Audit.v Caveat-10 already flags these as decorative. CVL
  re-proving them would amplify the same problem. Better to
  invest in Foundry-level lifecycle fuzz tests if reachability
  validation is the goal.

---

**Estimated effort for the top 5 items above:** ~2-4 hours each
based on the patterns already established in
`Governor.spec`, `Timelock.spec`, and `StakingVault.spec`. The
hardest piece is #4 (`authorizeUpgradeRequiresLatestAndActive`)
because it spans two contracts and needs the ghost-backed
RoleRegistry + VersionRegistry summaries threaded through; budget
6-8 hours for that one. Total: ~16-24 hours of focused CVL work
to close all five high-priority items.
