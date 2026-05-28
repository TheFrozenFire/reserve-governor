# Governance intent + bug-shape catalog

Read-only synthesis. Reads governor README, contract NatSpec, audit
notes, Rocq Audit.v caveats, and the Cantina postmortem; derives a
catalog of common bug shapes, each evaluated against the Reserve
Governor codebase with concrete `file:line` citations and CVL rule
sketches where applicable.

The goal is to surface intent-vs-code mismatches of the same class as
the Cantina PR #36 finding, without re-doing the same-shape hunt
already in `same_shape_hunt.md`. References to that hunt's F1..F8 are
made explicit where they intersect.

---

## Part 1: Reserve Governor — what is it for?

### Two governance paths

The system unifies two proposal flows through a single timelock.

**Optimistic (fast)** is the routine-governance channel
(`proposeOptimistic` at
`contracts/governance/ReserveOptimisticGovernor.sol:149-174`). A small
set of trusted EOAs holding `OPTIMISTIC_PROPOSER_ROLE` can submit
proposals that auto-execute after a short veto window unless a
veto-coalition rises to defeat them. Optimistic proposals are
constrained to whitelisted `(target, selector)` pairs registered in
`OptimisticSelectorRegistry` (`isAllowed` at
`contracts/governance/OptimisticSelectorRegistry.sol:68-70`), with
self/governor/timelock/token excluded as targets at registration time
(`contracts/governance/OptimisticSelectorRegistry.sol:84-91`).
Optimistic execution **bypasses** the timelock delay
(`_timelock().executeBatchBypass(...)` at
`contracts/governance/ReserveOptimisticGovernor.sol:355-357`). The
optimistic surface is gated by a per-proposer throttle of N proposals
per 12 hours (`ThrottleLib.consumeProposalCharge` at
`contracts/governance/lib/ThrottleLib.sol:18-27`).

**Standard (slow)** is the channel for everything that touches the
system itself: parameter changes, role grants/revokes, upgrades.
`propose` is permissionless modulo a proposal-threshold gate
(`contracts/governance/lib/ProposalLib.sol:82-89`). Voting follows OZ
`GovernorCountingSimple` with `GovernorPreventLateQuorum`. Successful
slow proposals must be queued through the timelock
(`_queueOperations` at
`contracts/governance/ReserveOptimisticGovernor.sol:333-343` rejects
queuing of optimistic proposals).

The **fast-to-slow transition** is the unique escalation hinge:
when veto votes reach threshold, `_tallyUpdated` calls
`ProposalLib.transitionToPessimistic`
(`contracts/governance/lib/ProposalLib.sol:109-143`), which marks the
optimistic proposal with the `TRANSITIONED_VETO_THRESHOLD` sentinel
(`uint256.max`) and spawns a fresh standard "Confirmation For: ..."
proposal under a new id. The original is now permanently `Defeated`
via the sentinel short-circuit in `state()` at
`contracts/governance/ReserveOptimisticGovernor.sol:243-246`.

### Role architecture and threat model

| Role | Held by | Power | Defends against |
|---|---|---|---|
| `OPTIMISTIC_PROPOSER_ROLE` | Trusted EOAs (granted by timelock) | Submit optimistic proposals (`proposeOptimistic`) | Spam / unauthorized fast-path use |
| `OPTIMISTIC_GUARDIAN_ROLE` | Bot keys on shared `Guardian` | Cancel non-Defeated optimistic proposals only (`Guardian.cancel` at `contracts/Guardian.sol:88-94`) | Malicious-but-not-yet-vetoed proposals; key-rotation grief |
| `OPTIMISTIC_GUARDIAN_MANAGER_ROLE` | Manager on shared `Guardian` | Grant new optimistic guardians; cannot cancel | Operational hygiene for guardian roster |
| `DEFAULT_ADMIN_ROLE` on `Guardian` | Break-glass council | Cancel anything that the timelock guardian can cancel; revoke optimistic proposer (`Guardian.revokeOptimisticProposer` at `contracts/Guardian.sol:66-68`) | Compromised proposer / large-scale incident |
| `PROPOSER_ROLE`, `EXECUTOR_ROLE` (timelock) | Governor only | Schedule + execute through timelock | Privilege escalation — README at `README.md:189` declares these must NEVER be granted elsewhere |
| `CANCELLER_ROLE` (timelock) | Governor + shared `Guardian` | Cancel proposals; revoke optimistic proposer | Lock-in of malicious proposals |
| `DEFAULT_ADMIN_ROLE` on StakingVault | Eventually timelock (intended) | UUPS upgrades; reward token mgmt; unstaking-delay | Vault upgrade safety / parameter governance |

The implicit separation of powers: **the optimistic guardian can stop
fast proposals; only the admin can stop slow proposals.** A single
role that could do both would collapse the safety guarantee that
slow proposals get full voting deliberation.

### Economic model

`StakingVault` is an ERC4626 over an underlying asset (the "voting
token"). Depositors mint shares; shares carry separate **standard**
and **optimistic** voting weight, each independently delegable.
Deposits do not auto-self-delegate (the `deposit` path mints shares
but doesn't touch either delegation ledger); only
`depositAndDelegate` does. Withdrawals go through the
`UnstakingManager` with a configurable delay (max 4 weeks per
`contracts/utils/Constants.sol:26`).

**No slashing.** Stakers earn multi-token rewards on a half-life
decay (the kernel is `1 - (1 - rewardRatio)^elapsed` at
`contracts/staking/StakingVault.sol:480-494`), driven by external
deposits of reward tokens. The vault accrues rewards via an index
update on every `_update` (transfer/mint/burn). A **native rewards**
branch lets the underlying asset itself serve as a reward stream —
when the vault holds asset balance above `totalDeposited`, the
delta streams pro-rata to share-holders via
`_currentAccountedNativeRewards`
(`contracts/staking/StakingVault.sol:245-250`). This makes the
classical ERC4626 first-depositor donation attack inverted — the
donor distributes the donation to other share-holders rather than
capturing it (see `test/ShareInflationAttack.t.sol:25-61`).

Reward tokens must be registered in `RewardTokenRegistry`. Once
removed, a token is permanently blocked from being re-added via the
`disallowedRewardTokens` sticky-flag at
`contracts/staking/StakingVault.sol:101,314,330`.

### Trust assumptions (read from `notes/external_dependencies.md`)

**Trusted by design:**
- OZ proxy infrastructure (UUPS, ERC1967, Clones).
- OZ `AccessControl` role-store consistency.
- OZ `Math.mulDiv` exact integer arithmetic.
- OZ `Checkpoints.Trace208` for past-vote lookups.
- `Strings.tryParseAddress` for proposer-suffix matching.
- ECDSA recovery (used only on the optimistic delegate-by-sig path).
- `@prb/math` `UD60x18.powu` reward decay (CAS-axiomatized).
- `IRoleRegistry` external singleton (out-of-scope governance).
- Reward token honest-ERC20 behavior (rejects blacklist tokens,
  fee-on-transfer tokens, rebasing tokens, callbacks — see Audit.v
  Caveat-9).

**Explicitly distrusted:**
- Optimistic proposers can be malicious / compromised — hence the
  veto window, the throttle, the selector allowlist, and the
  `revokeOptimisticProposer` ability for the admin council
  (`README.md:228`).
- Arbitrary proposal targets — out-of-scope behavior; safety relies
  on the selector allowlist (optimistic) or quorum + delay (slow).
- Voters who do not delegate — they count toward total supply but
  cannot vote. *This is the population the Cantina denominator was
  wrong about.*

### Emergent / system-level intent

These properties aren't per-function but are intended at the system
level. Each is a candidate for an intent-derived rule.

- **No role can both propose and veto a single proposal.** The
  `OPTIMISTIC_PROPOSER_ROLE` and `OPTIMISTIC_GUARDIAN_ROLE` are
  disjoint by intent. Code does not enforce disjointness; if a
  single address holds both, they can submit then cancel to grief
  vetoers. (Bug shape S6, S31, S34.)
- **Optimistic execution is bounded in scope to the selector
  allowlist.** No optimistic path may modify the governance system
  itself (`OptimisticSelectorRegistry._add` blocks
  self/governor/timelock/token at
  `contracts/governance/OptimisticSelectorRegistry.sol:86-91`).
  Slow proposals are the only channel for self-modification.
- **No proposal can execute through both channels.** Defeated +
  transitioned optimistic proposals are not re-executable; the
  spawned confirmation proposal has a different id. (S35.)
- **Throughput is bounded by the throttle + recharge.** A single
  proposer is bounded at `2 * capacity` per 12h (Rocq
  `audit_neg_no_throttle_bypass`); the system bound is
  `N * 2 * capacity` for N proposers — `Audit.v` Caveat-2.
- **The veto threshold must be reachable by the population of
  legitimate vetoers.** The Cantina bug violated this; the fix in
  PR #36 restores it.
- **Vault rewards are conserved.** `sum(claimed) +
  sum(accrued) <= sum(deposited rewards)` over any sequence. (Rocq
  `audit_rewards_conservation`, conditional on `WF_accrue` —
  Caveat-1.)
- **Lock-IDs are unique and one-shot.** Each `UnstakingManager`
  lock can transition to at most one of {claimed, cancelled}.
- **A `Versioned` upgrade target must be both registered and not
  deprecated.** `StakingVault._authorizeUpgrade` is the
  load-bearing gate.

---

## Part 2: Bug-shape applicability catalog

For each shape: applies / where / rule sketch / priority /
confidence. Skipped shapes get a one-line dismissal.

### S1: Wrong-population denominator (the Cantina shape)

**Applies:** Yes. Already documented at length in
`same_shape_hunt.md` F1 (proposalThreshold) and F2 (state auto-cancel).
The headline bug is at
`contracts/governance/ReserveOptimisticGovernor.sol:249,256`.

**Intent-derived rule sketch:** see
`certora/intent/VetoThresholdReachability.spec` — already authored
and demonstrated VIOLATED on the pre-fix branch.

**Priority:** P0 (done).
**Confidence:** High — both empirically demonstrated and post-mortem
documented.

### S2: Wrong-snapshot time — function reads at one moment when intent dictates another

**Applies:** Partially.

**Where:** Two places worth examining:
- `ReserveOptimisticGovernor.proposalThreshold()` at
  `contracts/governance/ReserveOptimisticGovernor.sol:308-315` reads
  `getPastTotalSupply(block.timestamp - 1)` — the snapshot is "the
  block before the read", not "the snapshot of the proposal under
  consideration". A proposer who acquires `getVotes` at T1 by
  delegating then immediately calls `propose` will be measured
  against the supply at T1-1, which can be different if a large
  mint/burn happened in the same block. The two reads
  (`getVotes(proposer, block.timestamp-1)` in
  `ProposalLib.sol:83` and `getPastTotalSupply(block.timestamp-1)`
  in line 311) share the snapshot — that's the design — but the
  pessimistic checks measure the proposer's votes against a
  threshold that itself depends on `totalSupply` at the same moment.
  This is internally consistent; the concern is whether
  `block.timestamp - 1` is the right snapshot or whether the
  proposal's own `voteStart` would be more semantically correct.
- `Guardian.cancel` at `contracts/Guardian.sol:88-94` reads
  `state(proposalId)` and `isOptimistic(proposalId)` at the moment
  of the cancel call; the proposal can transition between this
  read and the `cancel` call's eventual state-mutation inside the
  governor (Audit.v Caveat-4). The intent is "guardian can cancel
  a non-Defeated optimistic proposal at the time of the call" —
  the implementation honors that, but TOCTOU between the two reads
  matters.

**Rule sketch (Certora, single-step):**

```cvl
rule guardianStateReadIsAuthoritative {
    env e; uint256 pid;
    require !hasRole(DEFAULT_ADMIN_ROLE, e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE, e.msg.sender);

    // The state at the moment of authorization must match the state
    // at the moment of cancel. No transition between.
    IGovernor.ProposalState s1 = state(e, pid);
    require s1 != IGovernor.ProposalState.Defeated;
    require isOptimistic(e, pid);

    cancel@withrevert(e, ...);
    // assert: did not revert, AND post-cancel state is Canceled.
    assert !lastReverted;
}
```

**Priority:** P1.
**Confidence:** Medium — Caveat-4 already calls out TOCTOU as
unsound under the pure-oracle model. The bytecode-level rule would
be Certora's natural lane.

### S3: Off-by-one boundary

**Applies:** Yes — multiple sites worth checking.

**Where:**
- `_validateCancel` at
  `contracts/governance/ReserveOptimisticGovernor.sol:387`:
  `s != ProposalState.Defeated` (exclusive) for optimistic vs
  `s == ProposalState.Pending` (inclusive) for pessimistic. See
  `same_shape_hunt.md` F3 — strong asymmetry, plausibly a copy-paste
  error.
- `state()` deadline check at
  `contracts/governance/ReserveOptimisticGovernor.sol:269`:
  `deadline >= block.timestamp` (inclusive). At `block.timestamp ==
  deadline`, the proposal is still `Active`. That's the OZ
  convention; consistent.
- `Math.max(vetoThresholdTok, 1)` at
  `contracts/governance/ReserveOptimisticGovernor.sol:257`: ensures
  threshold is at least 1 token. This means a single token holder
  voting against can defeat a proposal where `vetoThreshold *
  supply < 1e18`. Probably intentional but worth flagging.
- `Math.max(1, super.proposalThreshold())` at
  `contracts/governance/ReserveOptimisticGovernor.sol:208,311`:
  ensures quorum and proposal threshold are at least 1.
- `proposalThrottle` rounding: `1e18 / capacity` at
  `contracts/governance/lib/ThrottleLib.sol:25` — if `capacity`
  doesn't divide `1e18` evenly, the burn is slightly less than
  `1/capacity` of charge, meaning the throttle is **slightly
  permissive** (you get marginally more proposals than the nominal
  capacity). Rocq's `audit_neg_no_throttle_bypass` bounds this at
  `2*capacity` not `capacity` — Caveat-2.

**Rule sketch:**

```cvl
rule throttleNeverGrantsMoreThanTwoCapacity {
    env e1; env e2;
    require e2.block.timestamp - e1.block.timestamp == 12 hours;
    address proposer;

    // Bound: between e1 and e2, the number of successful
    // consumeProposalCharge calls is at most 2 * capacity.
    // (Sketched; needs storage-delta accounting.)
}
```

**Priority:** P1 for the `_validateCancel` asymmetry (already in
F3); P2 for the throttle rounding.
**Confidence:** Medium for F3, low for the others.

### S4: TOCTOU / read-then-act

**Applies:** Yes — same site as S2.

**Where:**
- `Guardian.cancel`: reads `state` and `isOptimistic`, then forwards
  `cancel`. Between the two, `_tallyUpdated` could trigger
  `transitionToPessimistic` if a veto vote arrived simultaneously.
- `_castVote -> _tallyUpdated -> transitionToPessimistic`: the
  `_castVote` path reads `proposalSnapshot(proposalId)` and
  `_isOptimistic(proposalId)` at the top
  (`contracts/governance/ReserveOptimisticGovernor.sol:411,413`),
  then writes votes, then potentially mutates `vetoThreshold` to
  the sentinel. A second `_castVote` arriving in the same block
  after transition reads the *new* `vetoThreshold` and sees
  `_isOptimistic == false` (since sentinel != 0 still passes
  `_isOptimistic`, but transitions trigger off `state ==
  Defeated`). The race is more subtle than it looks.

**Rule sketch:** this is naturally a Rocq theorem because it
requires reasoning about sequenced operations and serializability;
Certora's parametric rules don't model inter-call concurrency
well. Could be expressed as a CVL parametric rule "for any sequence
of `castVote` calls, the final state is independent of order" —
but the proof discharges much more cleanly in Rocq.

**Priority:** P2 — Audit.v Caveat-4 is the right place to document
this; rule is structurally Rocq-natural.
**Confidence:** Medium.

### S5: Privilege escalation through composition — function A gates on X, function B calls A and gates on Y

**Applies:** Yes — one concrete site.

**Where:** `Guardian.revokeOptimisticProposer` at
`contracts/Guardian.sol:66-68` gates on `DEFAULT_ADMIN_ROLE` on the
Guardian. It forwards to `TimelockControllerOptimistic.revokeOptimisticProposer`
at `contracts/governance/TimelockControllerOptimistic.sol:69-71`,
which gates on `CANCELLER_ROLE` on the timelock. The Guardian holds
`CANCELLER_ROLE` on each timelock (per
`README.md:298-300`), so the composition works:
admin-on-Guardian → caller has CANCELLER on timelock (via
Guardian) → can revoke proposer. The intent is that a non-admin
on Guardian cannot revoke, which is true *as long as* the only
external holder of `CANCELLER_ROLE` is the Guardian. If governance
ever grants `CANCELLER_ROLE` to another address, that address can
directly call `revokeOptimisticProposer` without Guardian's admin
gate.

**Rule sketch:**

```cvl
rule onlyGuardianAdminEffectivelyRevokesProposer {
    env e; address proposer;
    require !hasRole(DEFAULT_ADMIN_ROLE_GUARDIAN, e.msg.sender);
    // If we revoke through Guardian, expect revert.
    guardian.revokeOptimisticProposer@withrevert(e, governor, proposer);
    assert lastReverted;
}
```
But this is incomplete — the **system-level** property is "the only
path to revocation is through Guardian admin." Bytecode-level
Certora can't prove this without enumerating all CANCELLER_ROLE
holders.

**Priority:** P2 (system invariant; needs Rocq + role-store
discipline).
**Confidence:** Medium — depends on production wiring.

### S6: Cross-function reentrancy

**Applies:** Partially — the StakingVault reward-claim path was
explicitly designed safe.

**Where:**
- `claimRewards` at
  `contracts/staking/StakingVault.sol:341-366`: zeros
  `accruedRewards` *before* `safeTransfer`, so reentrancy can't
  double-claim. (Per `external_dependencies.md` lines 188-191.)
- `_withdraw` at `contracts/staking/StakingVault.sol:266-293` —
  burns shares first, then calls `unstakingManager.createLock`
  which itself calls `safeTransferFrom` of the asset token. A
  malicious asset token could reenter `_withdraw` from inside its
  own `transferFrom`. Effect: re-entering `_withdraw` operates on
  the now-decremented `totalDeposited`, so an attacker can't
  double-withdraw (the burn already happened), but state observation
  during the call is non-atomic. Conclusion: defensive but not a
  visible bug.
- `_executeOperations` for optimistic proposals at
  `contracts/governance/ReserveOptimisticGovernor.sol:352-357`:
  the executed target can call back into the governor. The
  `executed` flag on `ProposalCore` is set by the OZ Governor
  internals *before* the external call (OZ-standard CEI pattern).

**Rule sketch:** Rocq is better suited to reentrancy proofs; CVL
can express "no two executions of the same proposalId can both
succeed" but lacks first-class reentrancy modeling.

**Priority:** P2.
**Confidence:** Low — the contracts appear defensive.

### S7: First-depositor share manipulation

**Skip.** Empirically refuted by `test/ShareInflationAttack.t.sol`;
the native-rewards branch inverts the attack. The variant 1
test demonstrates the donation flows TO the victim, not to the
attacker. Documented.

### S8: Donation attacks (direct token transfer bypasses internal accounting)

**Applies:** Partially.

**Where:** `StakingVault` reads its own asset balance via
`IERC20(asset()).balanceOf(address(this))` at
`contracts/staking/StakingVault.sol:292,429,437` to compute
`nativeBalanceLastKnown`. A direct transfer to the vault bypasses
the `_deposit` accounting path. The accrue logic at line 428-430
treats the gap as native rewards and streams it. This is the
designed behavior, not a bug — but it does mean **anyone can
inject "rewards" into the vault by sending the asset directly**,
without any admin role. For low-value griefing this is moot; for
strategic timing (e.g., immediately before a snapshot that depends
on share price), this could matter.

**Rule sketch:**

```cvl
rule donationIsNonExtractableByDonor {
    env e; uint256 amount;
    require amount > 0;
    // Pre: donor has no shares.
    require balanceOf(e.msg.sender) == 0;
    // Direct asset transfer (modeled as a balance bump).
    havoc nativeBalance assuming nativeBalance@new == nativeBalance@old + amount;
    // ...
    assert balanceOf(e.msg.sender) == 0 && asset_balanceOf(e.msg.sender) <= initial_asset_balanceOf(e.msg.sender);
}
```
Better expressed as a Rocq theorem (it requires reasoning across
multiple `accrue` + `withdraw` operations).

**Priority:** P2.
**Confidence:** Medium — already exists at the integration-test
layer (`ShareInflationAttack.t.sol`).

### S9: Snapshot griefing (manipulate state in the same block as a snapshot)

**Applies:** Partially.

**Where:** `proposalThreshold()` at
`contracts/governance/ReserveOptimisticGovernor.sol:308-315` reads
supply at `block.timestamp - 1`. A proposer can mint a large share
position in block N, wait one block (N+1), call `propose()` — the
threshold is measured at N which captured the new mint. Symmetric:
a proposer can flash-loan asset, deposit, propose, withdraw — but
ERC4626 share lock-in via the `_update` hook means transfers
update both delegations, so the dust between mint and withdraw is
short-lived. Combined with `unstakingDelay` (max 4 weeks per
`Constants.sol:26`), and the requirement that the proposer holds
delegated votes (not just shares) when `propose` is called, this
attack requires forethought.

The optimistic path is unaffected because optimistic propose is
role-gated, not vote-weight gated.

**Rule sketch:** "If the same address mints + proposes in the same
block, the proposal threshold check uses the pre-mint supply." But
the contract intentionally uses `block.timestamp - 1`, so the
check IS pre-mint. Possibly designed-correct.

**Priority:** P2.
**Confidence:** Low (likely designed).

### S10: Delegation cycles or self-delegation manipulation

**Applies:** Partially.

**Where:** `StakingVault._delegateOptimistic` at
`contracts/staking/StakingVault.sol:543-549` accepts arbitrary
delegatee including `address(0)` (no-op for the to-side) and
`account` itself (self-delegate). No cycle protection — but
ERC20Votes' delegation model is by-pointer, not by-graph, so
cycles cannot form (each account has at most one delegatee). The
real concern is **delegate-then-transfer race**: A self-delegates
at T1, transfers all shares to B at T2 in the same block. The
checkpoint at T2 records A's drop to zero and B's increase by
the same amount. Snapshot at T1 still records A's stake. This is
the standard ERC20Votes behavior.

**Skip — modeled correctly by OZ.**

### S11: Initialize / upgrade boundary

**Applies:** Yes.

**Where:**
- `StakingVault.initialize` at
  `contracts/staking/StakingVault.sol:144-179`: `msg.sender` is
  assumed to be the deployer (`IReserveOptimisticGovernorDeployer`).
  If anyone front-runs the deployer's initialize, they can set
  arbitrary `rewardTokenRegistry`, `versionRegistry`, and (via
  `unstakingManager = new UnstakingManager(_underlying)`) create
  a sibling unstaking manager. The proxy + atomic-init pattern in
  `Deployer.sol` should prevent this in practice, but the
  `_disableInitializers()` in the constructor relies on the proxy
  being initialized in the same transaction. Audit.v Caveat-11
  explicitly flags this as an out-of-scope risk.
- `TimelockControllerOptimistic._authorizeUpgrade` at
  `contracts/governance/TimelockControllerOptimistic.sol:96-98`:
  `require(msg.sender == address(this))` — self-call only. This
  is correct only if the timelock can only call itself through a
  scheduled-execute. If a malicious timelock op schedules an
  `upgradeToAndCall(badImpl)` from itself, the gate passes — but
  that's the entire point of upgrades through governance.

**Rule sketch:**

```cvl
rule timelockSelfUpgradeOnly {
    env e; address impl;
    require e.msg.sender != currentContract;
    upgradeToAndCall@withrevert(e, impl, "");
    assert lastReverted;
}
```

**Priority:** P1 (the self-call check is exactly the kind of
single-step parametric rule Certora is best at).
**Confidence:** High.

### S12: Storage collision in proxy + implementation

**Skip.** UUPS via OZ; the implementation contracts inherit
upgradeable bases in a fixed order. New `StakingVault`
implementations must remain layout-compatible (README at
`README.md:518`). Out-of-scope for Certora — would need a separate
storage-layout differ tool. Worth noting that the comment ordering
matters: `StakingVault` declares storage in a delicate order
mixed with inherited `__gap`-less upgradeable bases.

### S13: Wrong rounding direction in favor of vault vs user

**Applies:** Partially — same as F7 in `same_shape_hunt.md`.

**Where:**
- `proposalThreshold` rounds CEIL
  (`ReserveOptimisticGovernor.sol:314`).
- `vetoThreshold` rounds FLOOR + max(1)
  (`ReserveOptimisticGovernor.sol:256-257`).
- ERC4626 conversions in OZ default round in favor of the vault
  (i.e., against the user). `convertToShares` and `convertToAssets`
  inherit the OZ defaults. Reward index multiplications at
  `StakingVault.sol:445,469` use `Math.mulDiv` which rounds floor;
  this means a sliver of reward dust stays in the vault per
  accrual.

**Rule sketch:** Already in F7. Worth adding a "user can't drain
via repeated deposit/withdraw" rule that integrates over many
operations — Rocq-natural.

**Priority:** P2.
**Confidence:** Medium — likely designed but undocumented.

### S14: Quorum vs threshold confusion (N% participation AND M% approval)

**Applies:** Partially.

**Where:** Slow proposals use OZ `GovernorVotesQuorumFraction` for
quorum, where `quorum(timepoint) = quorumNumerator * pastTotalSupply
/ 1e18` (after override at
`ReserveOptimisticGovernor.sol:202-209`). The pessimistic path
inherits OZ's "vote is succeeded iff `forVotes > againstVotes` AND
`forVotes + abstainVotes >= quorum`". A proposal with 51%
abstaining + 0% for could technically meet quorum without
approval — but OZ correctly rejects this: `forVotes > againstVotes`
requires `forVotes >= 1`. The single edge case is: zero supply +
zero votes — `quorum = max(1, 0)` = 1, so the proposal cannot meet
quorum without at least one for vote. Fine.

**Skip — OZ-standard, audited.**

### S15: Time-lock bypass via precision

**Applies:** Partially.

**Where:** `TimelockControllerOptimistic.executeBatchBypass` at
`contracts/governance/TimelockControllerOptimistic.sol:76-93`
**explicitly bypasses the delay** — the marker `$._timestamps[id]
= block.timestamp` makes the operation immediately Ready. The
intent is "optimistic proposals don't wait for the timelock
delay" (README at `README.md:296`). The precision check is:
`$._timestamps[id] == 0` at line 88 — if an operation with the
same id was scheduled normally (i.e., on the slow path) but not
yet executed, `executeBatchBypass` would revert. Conversely, if
an optimistic op was bypass-executed, its `_timestamps[id]` is
now `block.timestamp` (non-zero); a follow-up bypass with the
same id would revert. Reasonable. But the `id` derivation includes
`salt = bytes20(address(this)) ^ descriptionHash` from
`ReserveOptimisticGovernor.sol:356` — same shape as S37.

**Rule sketch:**

```cvl
rule bypassConflictsWithExistingSchedule {
    env e;
    bytes32 id;
    require _timestamps[id] != 0;  // op already exists
    executeBatchBypass@withrevert(e, ..., id-equivalent-args);
    assert lastReverted;
}
```

**Priority:** P1 (closely related to F-CG1's "lifecycle state
machine uncovered" finding in the synthesis).
**Confidence:** High.

### S16: Emergency power scope creep

**Applies:** Partially.

**Where:** `Guardian` has three roles, and the README
(`README.md:193`) is careful to separate "DEFAULT_ADMIN can cancel
any proposal type the timelock guardian can cancel" from
"OPTIMISTIC_GUARDIAN can only cancel non-Defeated optimistic
proposals". This is the intended scope — but the implementation
gate at `contracts/Guardian.sol:79-94` only restricts the
non-admin branch. The admin branch (`isAdmin == true`) calls
`managedGovernor.cancel(...)` without any state check — meaning
the admin can cancel a proposal in *any* state, including
Executed (where `cancel` would revert downstream), Defeated, or
already Canceled. That's defensive — the inner cancel will revert
or no-op — but the surface implies a broader scope than the
README documents.

**Also:** `Guardian.revokeOptimisticProposer` only requires admin
on Guardian. The README states this is the break-glass authority.
But the lack of a cooldown / threshold / time-delay means a
compromised admin key can instantly nuke all proposers.

**Rule sketch:**

```cvl
rule guardianAdminCannotExecuteOrUpgrade {
    env e;
    require hasRole(DEFAULT_ADMIN_ROLE, e.msg.sender);
    // Admin can cancel and revoke. Cannot do anything else
    // that would mutate the governor system.
    // (Enumeration of methods would close this rule.)
}
```

**Priority:** P2.
**Confidence:** Low — the Guardian's surface is small.

### S17: Proposal griefing (drain attention/gas)

**Applies:** Yes — explicitly anticipated in the README at
`README.md:228`.

**Where:** A malicious optimistic proposer could submit a proposal
with very-long calldata to inflate the gas cost of every veto
vote (since `castVote` may call into accrue + checkpoint paths).
The README's explicit defense: `revokeOptimisticProposer`. There's
no inline gas cap; the defense is operational.

**Rule sketch:** Not naturally a Certora rule. The intent property
would be "no single proposer can prevent timely vetoes" — a
liveness property, which CVL doesn't express.

**Priority:** Skip (operational mitigation, not formal-verifiable).
**Confidence:** N/A.

### S18: State-machine asymmetry (propose path doesn't mirror cancel path)

**Applies:** Yes — F3 in `same_shape_hunt.md` documents the
`_validateCancel` optimistic-vs-pessimistic asymmetry.

**Where:** `contracts/governance/ReserveOptimisticGovernor.sol:387`
— optimistic uses `!= Defeated`, pessimistic uses `== Pending`.

**Priority:** P1 (per F3).
**Confidence:** Medium-high.

### S19: Auto-execution race (execute + cancel both win)

**Applies:** Partially.

**Where:** Optimistic `state()` at
`contracts/governance/ReserveOptimisticGovernor.sol:216-277`
deterministically resolves to one state per `(block.timestamp,
storage)` snapshot. The OZ Governor `execute()` requires
`state() == Succeeded`. `cancel()` calls `_validateCancel` which
also reads `state()`. Within a single block, both calls would
read the same `state()`, but a `cancel` followed by `execute` in
the same block sets `proposalCore.canceled = true` mid-block; the
`execute` would then see `state() == Canceled` and revert. Safe.

**Skip — deterministic state machine.**

### S20: Sandwich / front-run on price-based decisions

**Skip.** The governor's `state()` reads `block.timestamp` and
checkpoint values; no AMM-price-style sensitivity.

### S21: Sentinel-value reasoning errors

**Applies:** Yes — this is structurally important.

**Where:**
- `vetoThreshold = type(uint256).max` is the
  `TRANSITIONED_VETO_THRESHOLD` sentinel
  (`ProposalLib.sol:20`). It marks "this proposal already
  transitioned to pessimistic; treat as Defeated permanently".
  But `_isOptimistic` at
  `ReserveOptimisticGovernor.sol:504-506` returns
  `vetoThreshold(proposalId) != 0` — so a TRANSITIONED proposal
  still passes the `_isOptimistic` check (the sentinel is
  non-zero). This means `Guardian.cancel` at
  `contracts/Guardian.sol:88-94` calls `isOptimistic` which
  returns `true` for transitioned proposals; then the
  `!= Defeated` check at line 90-93 blocks the cancel. So the
  defense holds — but two short-circuits chained: sentinel makes
  `state() == Defeated`, which then blocks guardian cancel. If a
  refactor removes the sentinel→Defeated short-circuit, guardians
  would suddenly gain authority to cancel transitioned proposals.
  Fragile.
- `disallowedRewardTokens[token]` at
  `contracts/staking/StakingVault.sol:101,314,330` is a sticky
  flag — once removed via `removeRewardToken`, never re-addable.
  Sentinel is `true` for disallowed, `false` for normal. The
  default (uninitialized) state is `false` — i.e., not disallowed
  — which is correct because the registry registration is the gate.
- `Lock.unlockTime != 0` at
  `contracts/staking/UnstakingManager.sol:75` distinguishes a real
  lock from a deleted/never-existed slot. After `cancelLock` at
  line 64 (`delete locks[lockId]`), the slot's `unlockTime == 0`,
  so `claimLock` reverts with `NotUnlockedYet`. Reasonable.

**Rule sketch:** Already implicit in the existing Guardian.spec
G6 family. Worth a dedicated rule.

```cvl
rule transitionedProposalCannotBeCanceledByOptimisticGuardian {
    env e; uint256 pid;
    require !hasRole(DEFAULT_ADMIN_ROLE, e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE, e.msg.sender);
    require vetoThreshold(pid) == MAX_U256(); // sentinel = transitioned
    cancel@withrevert(e, ...);
    assert lastReverted;
}
```

**Priority:** P1.
**Confidence:** High.

### S22: Inheritance override silent change

**Applies:** Yes.

**Where:**
- `ReserveOptimisticGovernor.state()` overrides
  `GovernorUpgradeable.state` and
  `GovernorTimelockControlUpgradeable.state` at
  `contracts/governance/ReserveOptimisticGovernor.sol:216-277`.
  For optimistic proposals, the override branches into a custom
  implementation; for pessimistic, it falls back to `super.state()`.
  A future OZ upgrade that changes `super.state()` semantics would
  silently change pessimistic behavior. Less concerning because OZ
  version is pinned.
- `_validateCancel` override at line 374-388 — F3.
- `_executeOperations` override at line 345-363 — replaces the
  timelock-queue path with `executeBatchBypass` for optimistic
  proposals.
- `cancel` re-exported as `override` at line 191-198 with no body
  change. Pointless from a semantics view; needed for interface
  compliance. Worth confirming the OZ `cancel` semantics match
  the intent.

**Rule sketch:** "For every override, the documented semantics
match the inherited contract." Not naturally CVL — needs source
diff against pinned OZ version.

**Priority:** P2.
**Confidence:** Low.

### S23: Modifier interaction

**Applies:** Yes.

**Where:**
- `addRewardToken` at
  `contracts/staking/StakingVault.sol:312` has `onlyRole(DEFAULT_ADMIN_ROLE)`
  and reads `rewardTokenRegistry.isRegistered(...)`. Two-modifier
  composition is fine.
- `claimRewards` has `accrueRewards(msg.sender, msg.sender)`. The
  modifier writes to `userRewardTrackers`, then the function body
  reads `accruedRewards` and transfers. Order is correct.
- `_withdraw` has `accrueRewards(_owner, _receiver)` —
  the modifier runs first, then the body subtracts
  `totalDeposited`. P0 audit finding #99 already documents that
  the modifier ensures `totalDeposited >= _assets` post-accrue.
  Important inheritance: if a future override skips the
  `accrueRewards` modifier on `_withdraw`, the subtraction
  underflows.

**Rule sketch:**

```cvl
rule withdrawAlwaysAccruesFirst {
    env e;
    uint256 totalDeposited_pre = totalDeposited(e);
    uint256 nativeBalance_pre = nativeBalanceLastKnown(e);
    require nativeBalance_pre > totalDeposited_pre; // accruable

    withdraw(e, ...);

    // After withdraw, totalDeposited must reflect that accrue
    // ran (and then subtracted).
}
```

**Priority:** P1.
**Confidence:** Medium-high — directly mitigates the regression
that the P0 finding #99 identified as latent.

### S24: Dead code / unreachable state

**Skip.** Brief scan didn't reveal obvious dead code. The
`_validateProposal._isValidDescriptionForProposer` at
`ProposalLib.sol:200-221` is exercised only when description ends
in `#proposer=<address>` — that's a real, used path.

### S25: Default-value bugs (uninitialized state field used as if initialized)

**Applies:** Yes.

**Where:**
- `Lock.unlockTime == 0` is treated as "lock does not exist"
  (`UnstakingManager.sol:75`). The default value of
  `unlockTime` for a never-written slot is `0`. Safe.
- `ProposalCore.voteStart == 0` is treated as "proposal does not
  exist" (`ProposalLib.sol:151-155`). Defaults match.
- `optimisticDelegatees[account] == address(0)` means "no
  delegate". The `_moveOptimisticDelegateVotes` at
  `contracts/staking/StakingVault.sol:551-571` early-returns when
  from/to are zero. This is also the **Cantina-bug-relevant
  state** — undelegated accounts hold shares but contribute zero
  to optimistic voting supply.
- `vetoThreshold(proposalId) == 0` means "not optimistic". A
  fresh proposalId returns 0, so `_isOptimistic` correctly returns
  false for nonexistent proposals.

**Rule sketch:** Many implicit; one explicit candidate:

```cvl
rule defaultVetoThresholdImpliesNotOptimistic {
    uint256 pid;
    require vetoThreshold(pid) == 0;
    assert !_isOptimistic_pure(pid);
}
```

**Priority:** P2.
**Confidence:** High (low risk).

### S26: Cross-domain validation

**Applies:** Yes.

**Where:**
- `OptimisticSelectorRegistry._add` at
  `contracts/governance/OptimisticSelectorRegistry.sol:84-104`
  validates `target` against `governor`, `timelock`, and `token`
  addresses. The `token` reference is **read live** via
  `governor.token()` — if a future governor adds a setter that
  changes the token, the registry's exclusion silently shifts to
  the new token (see `same_shape_hunt.md` cross-contract obs).
- `StakingVault._accrueRewards` at
  `contracts/staking/StakingVault.sol:401-431` iterates
  `rewardTokens.values()` and reads
  `rewardTokenRegistry.isRegistered(...)`. The two sets can drift:
  a token can be in `rewardTokens` but not in
  `rewardTokenRegistry` (if registry-side unregister happened
  after vault-side add). The skip at line 408-411 handles this —
  accruals freeze for the token, but already-accrued claims
  remain claimable.

**Rule sketch:**

```cvl
rule rewardTokenAccrualFreezesWhenUnregistered {
    env e; address token;
    require !rewardTokenRegistry.isRegistered(e, token);
    require isRewardToken(e, token);

    // payoutLastPaid for token should be advanced but no new accrual happens.
    uint256 totalAccountedBefore = rewardTrackers[token].balanceAccounted;
    poke(e);
    assert rewardTrackers[token].balanceAccounted == totalAccountedBefore;
}
```

**Priority:** P1 — this is the same-class concern as the Cantina
shape (two populations can drift apart and the code reads from
the wrong one).
**Confidence:** Medium-high.

### S27: Wrong-actor-set check

**Applies:** Yes — F5 in `same_shape_hunt.md` (UnstakingManager
`claimLock` permissionless vs `cancelLock` owner-only).

**Where:** `contracts/staking/UnstakingManager.sol:72-82` —
`claimLock` has no actor check.

**Priority:** P1 (per F5).
**Confidence:** Medium.

### S28: Phase-confusion errors

**Applies:** Partially.

**Where:** `_castVote` at
`contracts/governance/ReserveOptimisticGovernor.sol:404-425`
calls `_validateStateBitmap(proposalId, _encodeStateBitmap(Active))`
— vote only allowed in Active. Within Active, the optimistic vs
pessimistic distinction is then made by `_isOptimistic`. The
`_countVote` override at line 390-401 rejects non-Against support
on optimistic proposals. Fine.

A nontrivial case: between Defeated (optimistic) and
transitioned (sentinel-set), there's a window where
`_castVote` could be called on a transitioned proposal. The
sentinel makes `state()` return Defeated, so
`_validateStateBitmap(Active)` reverts. Safe.

**Skip — covered by OZ's state-bitmap discipline.**

### S29: Carry-forward identity errors

**Applies:** Yes — F4 in `same_shape_hunt.md`
(`transitionToPessimistic` carries the proposer without
re-validating threshold or role).

**Where:** `contracts/governance/lib/ProposalLib.sol:133-140`.

**Priority:** P1 (per F4).
**Confidence:** Medium.

### S30: Off-token rebalancing / unintended fee paths

**Skip.** No fees in this protocol. Reward distribution flows
follow the indexed-accrual pattern with no fee tier.

### S31: Veto-blocking griefing — strategic non-participation

**Applies:** Yes — and this is the **same risk as the Cantina
bug, from a different angle.**

**Where:** The bug shape is "the population of effective vetoers
is smaller than the contract assumes." The Cantina bug treated
total supply as the denominator; the fix treats opted-in supply.
But even with the fix, **opted-in voters who decline to vote**
still contribute to the threshold's effective-reachability.
The fix says "100 tokens delegated, threshold 50% means 50 tokens
suffice"; but if 90 of those 100 delegated tokens belong to a
single inactive whale, the active 10 can never reach 50.

This is the **structural** version of the Cantina bug:
denominator is right, but participation rate (which the contract
doesn't measure) is the actual bottleneck.

**Rule sketch:** "For any optimistic proposal, there exists a
coalition of delegated voters who can defeat it" — provable.
"Such a coalition is plausibly assemblable in the veto window" —
not formally provable (depends on off-chain coordination).

The closest formal property:

```cvl
rule vetoCoalitionCanAlwaysReachThreshold {
    env e; uint256 pid;
    require isOptimistic(e, pid);
    uint256 thresholdTok = vetoThresholdInTokens(e, pid);
    uint256 optSupply = getPastOptimisticVotingSupply(snapshot(pid));
    assert thresholdTok <= optSupply;
}
```

This is the strong version of the Cantina fix. It guarantees
**reachability in principle**, not in practice.

**Priority:** P0 — this is the right reframing of the Cantina
property.
**Confidence:** High — the rule the postmortem actually
recommended.

### S32: Quorum capture (small coalition can pass anything)

**Applies:** Partially.

**Where:** Slow proposals require `forVotes >= quorum`. If quorum
is set very low (the parameter `quorumNumerator` is governance-
controlled, with the only constraint `>= 0`), a small delegated
coalition can pass anything. The constraint
`Math.max(1, super.quorum(timepoint))` at
`ReserveOptimisticGovernor.sol:208` only ensures quorum is at
least 1 wei — meaningless protection. There is no minimum quorum
floor.

**Rule sketch:**

```cvl
rule quorumNumeratorBoundedBelow {
    require quorumNumerator() >= MIN_QUORUM_NUMERATOR();
}
```
But there's no such constant — quorum is intentionally
governance-tunable.

**Priority:** Skip — this is policy, not a code bug.
**Confidence:** N/A.

### S33: Optimistic vs standard channel cross-pollination

**Applies:** Yes — explored in F3, F4 above.

The two channels share `ProposalCore` storage. Asymmetries in
`_validateCancel`, `_executeOperations`, `_queueOperations`,
`_countVote`, `_castVote`, `_tallyUpdated`, and `state()` are all
the places they diverge. **Each divergence is a place where the
intent for one channel could leak into the other.**

A specific concern: `proposalVotes(pid)` returns
`(againstVotes, forVotes, abstainVotes)`. For an optimistic
proposal, only `againstVotes` is ever non-zero (per the
`_countVote` revert at line 396). But the *storage* still has
slots for `forVotes` and `abstainVotes`. If a state transition
somehow allowed votes to be recounted under pessimistic rules
(e.g., a transitioned proposal reusing the same `proposalId`
storage — which doesn't happen, but the design is sensitive to
it), the legacy vote counts would matter.

**Rule sketch:**

```cvl
rule optimisticProposalHasNoForOrAbstain {
    env e; uint256 pid;
    require isOptimistic(e, pid);
    uint256 against; uint256 forV; uint256 abstain;
    against, forV, abstain = proposalVotes(e, pid);
    assert forV == 0 && abstain == 0;
}
```

**Priority:** P1.
**Confidence:** High.

### S34: Cancel-after-execute / execute-after-cancel

**Skip.** `proposalCore.executed` and `proposalCore.canceled` are
both checked in OZ's `_cancel` / `_execute` paths. The state
machine is well-formed. (Rocq has
`audit_governor_no_double_execution`.)

### S35: Proposal id collision

**Applies:** Yes — structurally important.

**Where:** `getProposalId(targets, values, calldatas,
descriptionHash)` is the OZ hash. The transition path at
`ProposalLib.sol:124-131` derives a **new** id by prepending
`"Confirmation For: "` to the description. If a future proposer
crafts a fresh proposal whose description equals
`"Confirmation For: <original-description>"`, with the same
targets/values/calldatas, they would collide with the
transitioned proposal. The contract defends against this at
`ProposalLib.sol:162-165`:

```solidity
require(
    bytes18(bytes(proposal.description)) != CONFIRMATION_PREFIX_BYTES,
    OptimisticGovernor__ConfirmationPrefixNotAllowed()
);
```

So both `proposeOptimistic` and `proposePessimistic` reject
descriptions starting with the confirmation prefix. **Good
defense.**

**Rule sketch:**

```cvl
rule confirmationPrefixReservedForTransition {
    env e; address[] tgts; uint256[] vals; bytes[] cds; string desc;
    require bytes18OfStr(desc) == CONFIRMATION_PREFIX_BYTES;
    propose@withrevert(e, tgts, vals, cds, desc);
    assert lastReverted;
}
```

**Priority:** P1.
**Confidence:** High.

### S36: Sentinel-state ambiguity (`Defeated` reachable by either threshold OR explicit cancel)

**Applies:** Yes.

**Where:** `state()` returns `Defeated` in two cases for an
optimistic proposal:
- The `TRANSITIONED_VETO_THRESHOLD` sentinel
  (`ReserveOptimisticGovernor.sol:243-246`).
- `againstVotes >= vetoThresholdTok` short-circuit
  (line 262-264).

These look identical from the outside — both return
`ProposalState.Defeated`. A consumer that branches on "is this
defeated for transition reasons or for veto reasons?" can't
distinguish. `Guardian.cancel` reads `state() != Defeated` —
both cases block the cancel, which is the right behavior. So
the ambiguity is benign.

But a downstream caller (e.g., an off-chain indexer or a future
governance feature) that needs to distinguish "really defeated"
from "transitioned" would need to read `vetoThreshold(pid)`
directly to disambiguate. Worth surfacing as an interface
clarification.

**Rule sketch:** Not a code-level bug; documentation hardening.

**Priority:** P2.
**Confidence:** Low.

### S37: Confirmation-prefix manipulation / executeBatchBypass salt prefix

**Applies:** Yes.

**Where:** `_executeOperations` for optimistic proposals at
`contracts/governance/ReserveOptimisticGovernor.sol:355-357`:

```solidity
_timelock().executeBatchBypass{ value: msg.value }(
    targets, values, calldatas, 0, bytes20(address(this)) ^ descriptionHash
);
```

The salt is `bytes20(address(this)) XOR descriptionHash`. This
gives a 256-bit salt where the high 96 bits come from
descriptionHash. Two different optimistic proposals with the same
calldata but different descriptions will have different salts,
hence different timelock operation ids. Good.

But: a slow proposal can also call `scheduleBatch` (through the
governor's pessimistic path) with arbitrary salt. If a slow
proposal crafts calldata + values + targets matching an
about-to-be-executed optimistic proposal, with a salt that
collides under the XOR pattern, **the slow proposal could pre-occupy
the timelock op slot**. Then the optimistic bypass would fail
at the `$._timestamps[id] == 0` check. Result: a DoS where a slow
proposer pre-empts an optimistic proposer's expected execution
slot.

But the slow proposal must first pass quorum + voting, which is
expensive. And the optimistic bypass requires
`bytes20(address(this)) XOR descriptionHash` — the attacker needs
to predict the descriptionHash, then mint a colliding scheduled
op. Feasible if the optimistic proposal's description is
public-known at submission time (it is — `proposeOptimistic` emits
`ProposalCreated`). The attacker has the veto window to schedule
their colliding op via a slow proposal — but slow proposals
have voting + delay, so the timing is tight. Audit.v Caveat-11
explicitly flags this:

> executeBatchBypass salt-collision DoS if PROPOSER_ROLE
> expands beyond governor.

**Rule sketch:**

```cvl
rule bypassSaltUniqueAcrossOptimisticProposals {
    env e; uint256 pid1; uint256 pid2;
    require pid1 != pid2;
    require isOptimistic(e, pid1);
    require isOptimistic(e, pid2);

    bytes32 salt1 = bytes20(currentContract) ^ descriptionHashOf(pid1);
    bytes32 salt2 = bytes20(currentContract) ^ descriptionHashOf(pid2);
    // Plus targets/values/calldatas — id hashing.
    assert hashOperationBatch(...salt1...) != hashOperationBatch(...salt2...);
}
```

But this doesn't cover the slow-vs-optimistic collision — that's
the real risk and it's structurally cross-channel.

**Priority:** P1 — Audit.v already calls it out.
**Confidence:** Medium.

---

## Part 3: Synthesis

### Top 5 candidate intent-derived rules to write next

1. **S31 (Cantina-prime): veto coalition reachability post-fix.**
   The Cantina fix corrects the denominator, but the right
   long-run intent rule is "for any veto threshold setting +
   delegate state, a coalition that includes every opted-in
   voter must be able to defeat the proposal."

   ```cvl
   rule vetoCoalitionCanAlwaysReachThreshold {
       env e; uint256 pid;
       require isOptimistic(e, pid);
       uint256 thresholdTok = vetoThresholdInTokens(e, pid);
       uint256 optSupply = getPastOptimisticVotingSupply(snapshot(pid));
       assert thresholdTok <= optSupply;
   }
   ```
   This is the stronger, structurally-symmetric version of the
   existing `VetoThresholdReachability.spec`. It enforces the
   intent even when the contract is fixed.

2. **S21: transitioned proposals are not cancelable by optimistic
   guardians.** A regression guard against future sentinel-handling
   refactors. The chain {sentinel → state==Defeated → guardian
   cancel rejected} is fragile.

   ```cvl
   rule transitionedProposalRejectsOptimisticGuardianCancel {
       env e; uint256 pid;
       require !hasRole(DEFAULT_ADMIN_ROLE_GUARDIAN, e.msg.sender);
       require hasRole(OPTIMISTIC_GUARDIAN_ROLE, e.msg.sender);
       require vetoThreshold(e, pid) == MAX_U256();
       guardian.cancel@withrevert(e, governor, ...);
       assert lastReverted;
   }
   ```

3. **S35: confirmation prefix is reserved.** The defense at
   `ProposalLib.sol:162-165` is load-bearing for transitioned-
   proposal-id uniqueness. A rule that asserts the defense
   directly catches any future weakening.

   ```cvl
   rule confirmationPrefixReservedForTransition {
       env e; address[] t; uint256[] v; bytes[] c; string d;
       require startsWithConfirmationPrefix(d);
       propose@withrevert(e, t, v, c, d);
       assert lastReverted;
   }
   ```

   Justification: this is the single defense that prevents
   proposalId collision between the transition spawn and a
   user-submitted "Confirmation For:" pessimistic proposal.

### Shape classes that are STRUCTURALLY hard for Certora here

- **Reachability over long traces.** S1/S31's "coalition reaches
  threshold" + S6/S4's TOCTOU + S34's no-double-execution are
  all about *sequences* of operations, not single steps. Rocq's
  `Reachable` inductive is the natural home (see Audit.v's nine
  `Reachable` cases for Governor). Certora can ratify these as
  parametric rules but can't induct.
- **Conservation under arbitrary token sequences.** Rewards
  conservation, lock-balance conservation, total-deposited
  conservation — Audit.v Caveat-1 already notes this lives in
  Rocq via `WF_accrue`-style induction. Certora rule attempts
  hit NONDET-too-loose (see `notes/rewards_conservation_attempt`
  per session history).
- **Liveness.** S17, S31. CVL doesn't express "the system
  eventually does X." Property-based testing or game-theoretic
  modeling is the right tool.
- **Inter-contract role compositions.** S5 (privilege escalation
  through composition) is naturally Rocq because it requires
  modeling the full role-store across multiple contracts. The
  `access_control_threading.md` plan is the right direction.

### Shape classes that are STRUCTURALLY easy and underexploited

- **Modifier-resolution invariants.** S23 (modifier interaction)
  is easy in CVL because each method's modifier chain is
  statically resolved by the prover. The
  `withdrawAlwaysAccruesFirst` sketch is one rule away.
- **Sentinel-value reachability checks.** S21, S25, S35 are all
  one-rule parametric assertions: "if storage X equals sentinel
  value Y, then method Z reverts". Trivial in CVL.
- **State-machine asymmetry detection.** S18 (F3) is exactly the
  kind of thing Certora can prove with two paired rules
  (`optimisticProposerCannotCancelActive` +
  `pessimisticProposerCanOnlyCancelPending`). The lack of these
  rules is a coverage gap, not a structural limit.
- **External-summary fidelity.** The Cantina bug's specific
  manifestation — NONDET summaries on `getPastTotalSupply` and
  `getPastOptimisticVotingSupply` — is one of two patterns now
  well-understood: replace NONDET with ghost-backed summaries
  (WISDOM C015). The same pattern applies to every external
  read in every spec.

### Implications for the broader verification strategy

The Cantina catch demonstrated that **intent-first rules surface
classes of bugs that code-first rules miss**. The catalog above
makes three takeaways concrete:

First, **the highest-leverage intent rules are about
denominators, populations, and reachability.** The Cantina shape
is the headline; S26 (cross-domain registry drift), S31 (coalition
reachability), and S32 (quorum capture) are all variants. Each
asks "what population should this quantity be computed against?"
and answers it from the design-doc, not from the code. The same
question applied to non-token quantities (reward index, lock
total, version hash) yields more rules in the same family.

Second, **the right division of labor is sharper than "Certora
for parametric, Rocq for inductive."** It's "Certora for
single-step state-machine assertions that involve external
reads (with ghost-backed summaries), Rocq for compositional
properties over sequences of operations." The shapes that survive
both lenses are the ones audit value comes from — S21, S23, S35
all sit there. Shapes that need only one lens (S31 → Certora; S5,
S31's liveness twin → Rocq) should be assigned to that lens and
not redundantly attempted in the other.

Third, **the Audit.v caveats are a roadmap, not an apology.**
Caveat-2 (system-level throttle), Caveat-3 (admin-role gate on
`_authorizeUpgrade`), Caveat-7 (open-executor mode unmodeled),
Caveat-11 (six attack vectors structurally outside the model)
are all places where a new intent rule could displace the
caveat. The intent-first lens should be expanded specifically to
attack those caveats, in priority order: Caveat-3 first (single
parametric rule against `_authorizeUpgrade`'s role gate),
Caveat-11's `executeBatchBypass` salt collision second (S37
rule), Caveat-2's system-level throttle bound third (a parametric
rule over all proposers — needs harness for the proposer-set
enumeration but is tractable).

The deprioritization counterpoint: **shapes that are designed-by-
intent rather than coding errors should be removed from the
backlog.** S7 (refuted empirically), S14 (OZ-audited),
S20 (no relevant prices), S32 (policy, not a bug), S34 (covered
by OZ + Rocq) are five candidate skips that previous audits had
listed but that are not productive targets.
