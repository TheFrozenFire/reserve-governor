# Walker-completeness audit

**Date:** 2026-05-31
**HEAD:** `dbf4844`
**Auditor vantage:** walker-completeness — for each composite walker
axiom, can the underlying Yul walker actually be Qed'd, or is the
axiom hand-waving?

## Methodology

For each `Axiom run_fun_<fn>_at_proj_sim` (and `_at_storage_base`
variant), I:

1. Read the axiom statement (preconditions + Skolemized post-storage).
2. Read the docstring describing the Yul body's structural steps
   (S1..Sn).
3. Opened the corresponding shallow form
   (`formal-verification/rocq/generated/*_shallow.v`) and inspected
   the actual body — counted top-level statements, branches, external
   calls, sstore sites, intra-contract sub-calls.
4. Classified by walker-proof tractability.

The classification axis is "could a Coq engineer following the R040 /
R047 / R051 / R067 recipe write the walker proof?":

| Class | Meaning |
|-------|---------|
| **MECHANICAL** | Walker body is a straight assembly of already-Qed leaves; the proof is 100-300 LOC of tactic glue; no missing primitives. |
| **EFFORT** | 1-2 hour focused session — a sub-walker is implicit but tractable. May need 1-2 new leaves or a per-target observational bridge. |
| **DOUBTFUL** | Heavy body (300+ Yul statements), nontrivial branches, intra-contract calls into bodies with their OWN composite axioms. Proof would need to dispatch through a chain of 3-5 composite axioms. The walker shape is documented, but writing it would be a multi-day workstream and may surface unknown blockers. |
| **HAND-WAVING** | Post-state Skolem is so abstract that the axiom is unfalsifiable in practice (e.g. "exists memory' such that ⇓ succeeds, with `proj_post` left as a Parameter on the same data the walker computes"). Or, the function dispatches into external `delegatecall` / `staticcall` whose callee-spec is itself axiomatised. |

## Inventory of composite walker axioms

Found **45 composite walker axioms** across 11 equivalence files
(`grep -rn '^  Axiom run_fun_'`):

| # | File | Axiom | Yul body | Branches | Ext calls | sstores | Class |
|---|------|-------|----------|----------|-----------|---------|-------|
| 1 | ProposalLib.v | `run_fun__saveProposal_580_at_storage_base` | ~95 LOC | 0 | 0 | 3 (offsets 0/20/26) | **EFFORT** |
| 2 | ProposalLib.v | `run_fun__validateProposal_507_at_storage_base` | ~50 LOC | 1 (success branch only) | 1 staticcall (governor.state) | 0 | **EFFORT** |
| 3 | ProposalLib.v | `run_fun_proposeOptimistic_179_at_storage_base` | ~180 LOC | 1 + loop | 3 staticcalls + sub-call into _saveProposal_580 | 3 (via sub) | **DOUBTFUL** |
| 4 | ProposalLib.v | `run_fun_proposePessimistic_288_at_storage_base` | ~190 LOC | 1 + loop | 4 staticcalls + sub-call | 3 (via sub) | **DOUBTFUL** |
| 5 | ProposalLib.v | `run_fun_transitionToPessimistic_400_at_storage_base` | ~150 LOC | 0 | 4 staticcalls + sub-call into _saveProposal_580 | 4 (1 inline + 3 via sub) | **DOUBTFUL** |
| 6 | VersionRegistry.v | `run_fun_deprecateVersion_187_at_proj_sim` | ~60 LOC | 2 (call result + isDeprecated) | 1 staticcall (roleRegistry.isOwnerOrEmergency) | 1 (bool at slot 1) | **EFFORT** |
| 7 | VersionRegistry.v | `run_fun_registerVersion_152_at_proj_sim` | ~150 LOC | 3 (2 call results + zero-check) | 2 staticcalls (roleRegistry, Versioned.version) + keccak | 2 (slot 0 deployments + slot 2 latestVersion) | **DOUBTFUL** |
| 8 | StakingVaultExchange.v | `run_fun_deposit_4312_at_storage_base` | ~280 LOC | 2+ (maxDeposit revert, unstakingDelay branch via sub) | 2+ staticcalls + ERC20 transferFrom CALL | 8+ (totalDeposited, nativeBalance, supply, balances, Votes ckpts, OptimisticDelegate ckpts) | **HAND-WAVING** |
| 9 | StakingVaultExchange.v | `run_fun_mint_4356_at_storage_base` | ~260 LOC | same as deposit + ceiling preview | same as deposit | same as deposit | **HAND-WAVING** |
| 10 | StakingVaultExchange.v | `run_fun_withdraw_4403_at_storage_base` | ~320 LOC | 2 paths (delay==0 vs delay>0), spendAllowance branch | 2-3 staticcalls + ERC20 transfer/forceApprove + unstakingManager.createLock CALL | 10+ (supply, balances, Votes, optimistic delegate, totalDeposited, nativeBalance, allowance via spend) | **HAND-WAVING** |
| 11 | StakingVaultExchange.v | `run_fun_redeem_4450_at_storage_base` | ~310 LOC | same as withdraw | same as withdraw | same as withdraw | **HAND-WAVING** |
| 12 | RewardTokenRegistry.v | `run_fun__add_240_at_proj_sim_not_in` | ~50 LOC of EnumerableSet body | 1 (switch on _contains) | 0 (intra) | 2 (array_push + positions map) | **MECHANICAL** |
| 13 | RewardTokenRegistry.v | `run_fun__add_240_at_proj_sim_in` | ~10 LOC (no-op branch) | 1 | 0 | 0 | **MECHANICAL** |
| 14 | RewardTokenRegistry.v | `run_fun__remove_324_at_proj_sim_in` | ~110 LOC (swap-and-pop) | 2 (positions==0 + valueIndex!=lastIndex) | 0 | 4-5 (position write, body write, array_pop, positions=0) | **EFFORT** |
| 15 | RewardTokenRegistry.v | `run_fun__remove_324_at_proj_sim_not_in` | ~10 LOC (no-op branch) | 1 | 0 | 0 | **MECHANICAL** |
| 16 | RewardTokenRegistry.v | `run_fun_registerRewardToken_101_at_proj_sim` | ~70 LOC | 2 (call result + zero check) | 1 staticcall (roleRegistry.isOwner) + intra `fun_add_711 → fun__add_240` | 2 (via sub) | **EFFORT** |
| 17 | RewardTokenRegistry.v | `run_fun_unregisterRewardToken_131_at_proj_sim` | ~60 LOC | 2 (call result + remove returns 1) | 1 staticcall (roleRegistry.isOwnerOrEmergency) + intra `fun_remove_738 → fun__remove_324` | 4-5 (via sub) | **EFFORT** |
| 18 | ReserveOptimisticGovernor.v | `run_fun_propose_389_at_proj_sim` | ~400 LOC | many | delegatecall into ProposalLib | many (via delegatecall) | **HAND-WAVING** |
| 19 | ReserveOptimisticGovernor.v | `run_fun_castVote_4378_at_proj_sim` | ~250 LOC | 3+ (optimistic/pessimistic branch, defeated→transition path) | 2-3 staticcalls + ProposalLib delegatecall | many | **HAND-WAVING** |
| 20 | ReserveOptimisticGovernor.v | `run_fun_execute_4145_at_proj_sim` | ~350 LOC | 2 (optimistic vs pessimistic) | TimelockController CALL or super._executeOperations chain | many | **HAND-WAVING** |
| 21 | SelectorRegistry.v | `run_fun_registerSelectors_145_at_proj_sim` | ~140 LOC + for-loop | unbounded loop + sub-branches | 1 staticcall (governor.timelock modifier) + intra `fun__add_369` × N | 2N+ (per-target & per-selector OZ EnumerableSet writes + log2 per iter) | **DOUBTFUL** |
| 22 | SelectorRegistry.v | `run_fun_unregisterSelectors_180_at_proj_sim` | ~150 LOC + for-loop | unbounded loop + conditional `_targets` removal | 1 staticcall + intra `fun_remove_2599`/`fun_remove_2411` (swap-and-pop) | many | **DOUBTFUL** |
| 23 | SelectorRegistry.v | `run_fun_isAllowed_211_at_proj_sim` | view fn | 2-3 (nested EnumerableSet lookups) | 0 | 0 (pure read) | **EFFORT** |
| 24 | SelectorRegistry.v | `run_fun_targets_191_at_proj_sim` | view fn (memory copy) | bounded loop (length) | 0 | 0 | **EFFORT** |
| 25 | SelectorRegistry.v | `run_fun_selectorsAllowed_264_at_proj_sim` | view fn (memory copy per target) | bounded loop | 0 | 0 | **EFFORT** |
| 26 | TimelockControllerOptimistic.v | `run_fun_revokeOptimisticProposer_136_at_proj_sim` | ~50 LOC | gated by onlyRole | intra `fun__revokeRole_121` (R059 swap-and-pop) | many via sub | **EFFORT** (the sub-walker is the same Guardian R059 axiom — see #43) |
| 27 | TimelockControllerOptimistic.v | `run_fun_executeBatchBypass_201_at_proj_sim` | ~85 LOC | 1 (require timestamps[id]==0) | onlyRole checkRole + opaque per-target dispatch + intra `fun_executeBatch_1552` | 2 (timestamps[id]:=now then :=DONE) | **DOUBTFUL** |
| 28 | TimelockControllerOptimistic.v | `run_fun_scheduleBatch_1295_at_proj_sim` | ~230 LOC + for-loop | per-iteration require + branch | onlyRole + keccak | N (timestamps[id_i] for each batch member) | **DOUBTFUL** |
| 29 | TimelockControllerOptimistic.v | `run_fun_executeBatch_1552_at_proj_sim` | ~220 LOC | 1 (predecessor != 0 branch — pinned to 0 by precondition) + per-target loop | onlyRole + per-target external CALL | 1 (timestamps[id]:=DONE) | **DOUBTFUL** |
| 30 | TimelockControllerOptimistic.v | `run_fun_cancel_1394_at_proj_sim` | ~90 LOC | 1 (require isOperationPending) | onlyRole | 1 (timestamps[id]:=0) | **EFFORT** |
| 31 | StakingVaultRewards.v | `run_fun_setRewardRatio_1036_at_proj_sim` | ~40 LOC + accrueRewards modifier | accrueRewards loop over rewardTokens (N), each with per-token reads/writes | onlyRole staticcall + per-token isRegistered staticcall + ERC20.balanceOf staticcall | 1 inline (rewardRatio) + ~5N from accrue | **DOUBTFUL** |
| 32 | StakingVaultRewards.v | `run_fun_poke_1082_at_proj_sim` | ~5 LOC (empty body) + accrueRewards modifier | accrueRewards loop | per-token staticcalls (N) | ~5N from accrue | **DOUBTFUL** |
| 33 | StakingVaultRewards.v | `run_fun_claimRewards_1010_at_proj_sim` | ~190 LOC + for-loop + accrueRewards modifier | per-token branch (if accrued > 0) | per-token safeTransfer CALL + accrueRewards staticcalls | ~3N writes (totalClaimed, accruedRewards:=0, plus accrue effects) | **HAND-WAVING** |
| 34 | StakingVaultAdmin.v | `run_fun_setUnstakingDelay_750_at_proj_sim` | ~25 LOC | 1 (require delay <= MAX) | onlyRole checkRole staticcall | 1 (slot 5) | **MECHANICAL** |
| 35 | StakingVaultAdmin.v | `run_fun_setRewardRatio_1036_at_proj_sim` | (same as #31 — duplicated axiom for the admin file's projection) | same | same | same | **DOUBTFUL** |
| 36 | StakingVaultAdmin.v | `run_fun_grantRole_13574_at_proj_sim` | ~80 LOC | hasRole switch + add-if-not-already | onlyRole | 2 (hasRole := 1 + EnumerableSet add) | **EFFORT** (R055/R068 sub-recipe) |
| 37 | StakingVaultAdmin.v | `run_fun_revokeRole_13593_at_proj_sim` | ~90 LOC + swap-and-pop | hasRole + remove-if-present | onlyRole | 2-5 (hasRole := 0 + swap-and-pop on EnumerableSet) | **EFFORT** (matches R059 — Guardian's open work; see #43) |
| 38 | StakingVaultAdmin.v | `run_fun_renounceRole_13616_at_proj_sim` | ~60 LOC | callerConfirmation check + hasRole + remove | 0 | same as revoke | **EFFORT** |
| 39 | StakingVaultAdmin.v | `run_fun__authorizeUpgrade_1574_at_proj_sim` | ~130 LOC | 2 (deprecated check + hash mismatch) | 3 staticcalls (Versioned.version, registry.getLatestVersion, registry.getImplementationsForVersion) | 0 (read-only) | **DOUBTFUL** |
| 40 | StakingVaultAdmin.v | `run_fun_upgradeToAndCall_2829_at_proj_sim` | ~150 LOC | 1 (data.length > 0 branch) | _authorizeUpgrade chain + IERC1822 staticcall + DELEGATECALL into new impl | 1 inline (IMPLEMENTATION_SLOT) + opaque delegatecall side-effects | **HAND-WAVING** |
| 41 | AccessControlEnumerable.v | `run_fun__at_1791_at_proj_sim` | ~30 LOC | 1 (bounds panic) | 0 | 0 (read-only) | **MECHANICAL** |
| 42 | AccessControlEnumerable.v | `run_fun_getRoleMembers_672_at_proj_sim` | ~50 LOC + memory-copy loop | bounded by role length | 0 | 0 (read-only, memory only) | **EFFORT** (the file's own docstring estimates ~300 LOC; no structural blocker) |
| 43 | Guardian.v | `run_fun__revokeRole_736_at_proj_sim_member` | OZ EnumerableSet remove (swap-and-pop) | 2 nontrivial (last-element fast path / non-last) | 0 | 5 (hasRole, position, length, body, position cleanup) | **EFFORT** (Guardian's own docstring estimates ~800-1200 LOC; the file describes the walker shape exhaustively) |
| 44 | Guardian.v | `run_fun_cancel_238_at_proj_sim_admin` | ~345 LOC | 2 (isAdmin gate, call result branches) | 4 staticcalls (hasRole, _governor, governor.getProposalId) + 1 external CALL (managedGovernor.cancel) | 0 (storage UNCHANGED — view+call) | **DOUBTFUL** |
| 45 | Guardian.v | `run_fun_cancel_238_at_proj_sim_guardian` | same body, more branches taken | 5+ (admin=false, guardian=true, isOptimistic, state!=Defeated, etc.) | 6 staticcalls + 1 CALL | 0 (storage UNCHANGED) | **DOUBTFUL** |

### Tally

| Class | Count |
|-------|-------|
| MECHANICAL | 6 |
| EFFORT | 14 |
| DOUBTFUL | 15 |
| HAND-WAVING | 10 |
| **Total** | **45** |

The DOUBTFUL + HAND-WAVING combined (25/45 = 56%) are the bulk of the
audit's load-bearing surface. The framework's R067 / R070 recipe is
well-designed for the MECHANICAL/EFFORT bottom half; the top half is
where the soundness argument is straining.

## CLOSES MECHANICALLY (most simple cases — sanity check)

These axioms describe Yul bodies that are short (≤ 50 statements), have
1-2 obvious branches, no external calls, and write to 0-2 storage slots
via existing R040 sstore wrappers. The walker tactics (`lu/cu/p` glue
loop, case-split before `eexists`, sstore-wrapper apply) from R040 /
R047 / R051 / R067 should close them in 100-300 LOC.

| Axiom | Why mechanical |
|-------|----------------|
| `run_fun_setUnstakingDelay_750_at_proj_sim` | 25 LOC, 1 require + 1 sstore at literal slot 5 + log. No external calls (the onlyRole modifier uses an internal hasRole sub-call already-Qed via R055-style chain). Drop-in for the R067 milestone recipe. |
| `run_fun__add_240_at_proj_sim_in` | The IN-SET no-op branch of EnumerableSet add: switch takes if-arm, returns 0, no storage write. ~10 statements. |
| `run_fun__remove_324_at_proj_sim_not_in` | Mirror no-op; same shape. |
| `run_fun__add_240_at_proj_sim_not_in` | NOT-IN-SET add path: array_push + positions[v] := length. ~50 statements, no branching after the switch, two known sstore wrappers. The post-storage is precisely what the framework's MapToArray + Map primitives produce. |
| `run_fun__at_1791_at_proj_sim` | OZ EnumerableSet `_at(index)`: sload length, bounds check, dataslot derivation, sload at offset. ~30 statements. The post-state contains a keccak in scratch memory (already a known dataslot derivation primitive). |
| `run_fun_getRoleMembers_672_at_proj_sim` (memory copy) | The file's own docstring estimates ~300 LOC; "no structural blockers". Bounded loop, all reads, only writes scratch memory at fixed offsets. Could plausibly be moved to EFFORT depending on the memory-allocator framework state. |

**Reading:** these axioms exist mostly as a productivity shortcut. Their
soundness is not the worry — closing them is purely tactic-engineering
labor. If you wanted to retire 6 axioms in a single 2-3 day push, this
is the set.

## CLOSES WITH EFFORT

These are the medium-complexity cases. The walker shape is documented;
the leaves exist; but they involve at least one of: a swap-and-pop
EnumerableSet-remove (R059's shape), an unbounded but well-structured
loop, a non-trivial branch that needs `eexists` ordering. Typical
estimate per axiom: 1-2 days of focused work.

Representative axioms in this bucket:

- `run_fun__remove_324_at_proj_sim_in` (RewardTokenRegistry)
- `run_fun__validateProposal_507_at_storage_base` (ProposalLib)
- `run_fun__saveProposal_580_at_storage_base` (ProposalLib)
- `run_fun_deprecateVersion_187_at_proj_sim` (VersionRegistry)
- `run_fun_registerRewardToken_101_at_proj_sim` / `run_fun_unregisterRewardToken_131_at_proj_sim`
- `run_fun_cancel_1394_at_proj_sim` (TimelockControllerOptimistic)
- `run_fun_revokeOptimisticProposer_136_at_proj_sim` (TimelockControllerOptimistic)
- View axioms in SelectorRegistry (`isAllowed`, `targets`, `selectorsAllowed`)
- Three StakingVaultAdmin role-mutation axioms (`grantRole`, `revokeRole`, `renounceRole`)
- `run_fun__revokeRole_736_at_proj_sim_member` — Guardian's R059 walker

The most leveraged item here is the Guardian R059 walker:
`run_fun__revokeRole_736_at_proj_sim_member` is one Yul function but it
unblocks 4 dependent axioms in two other files (StakingVaultAdmin's
`revokeRole_13593`, `renounceRole_13616`, and indirectly
TimelockControllerOptimistic's `revokeOptimisticProposer_136` which
calls `_revokeRole` internally). Guardian.v's own docstring (lines
9137-9203) lays out the walker shape in unusual detail and explicitly
estimates ~800-1200 LOC of work. The justification is honest — the
shape is known, the leaves exist, no novel framework piece is required.

## DOUBTFUL

These are the axioms most worth scrutinizing. The Yul body is large,
has nontrivial branching that the walker has to dispatch on, and
typically involves a chain of intra-contract sub-calls (each of which
has its own composite axiom) PLUS one or more external staticcalls. A
"walker proof" here would be a multi-hundred-LOC Coq file dispatching
through 3-5 axiom hooks while threading memory state, returndata, and
storage projections.

### `run_fun_propose_389_at_proj_sim` (ReserveOptimisticGovernor) — ~400 LOC body

The Governor's `propose()` is a thin wrapper that **delegatecalls into
ProposalLib**. The composite walker axiom asserts that after the
delegatecall, the storage post-state matches
`proj_post_propose_389 storage_base pid ... votingDelay votingPeriod
now`. The walker would have to:

1. Dispatch the delegatecall via a bridge analogous to R063's static-
   call bridge — but delegatecall is **state-modifying** and so the
   bridge has to thread storage through the callee's body.
2. The callee body is ProposalLib's `proposePessimistic_288` — itself a
   DOUBTFUL composite axiom (chain of 4 staticcalls into governor for
   votingDelay/votingPeriod, plus `_saveProposal_580`).
3. The post-state Skolem `proj_post_propose_389` takes
   `votingDelay/votingPeriod` as arguments but the WALKER reads them
   from staticcalls — the precondition doesn't tie those staticcall
   returns to the Skolem's arguments. A walker proof would have to
   either tighten the precondition (e.g.
   `governor_votingDelay_returns = votingDelay`) or admit that the
   Skolem absorbs the staticcall return values opaquely. The latter is
   what the current axiom does, which is part of why this is doubtful
   rather than mechanical-with-effort.

**Gap:** the proj_post_propose_389 axiom is stated with `pid`,
`votingDelay`, `votingPeriod` as free parameters that the existential
"chooses". A buggy walker could chose any value for these. The bridge
axiom `proj_post_propose_389_observes` is reflexivity-only — it offers
no constraint. The Guardian R067 / R069 audit-time bridge axioms
contain real content; this one does not.

### `run_fun_castVote_4378_at_proj_sim` (ReserveOptimisticGovernor) — ~250 LOC body

Branches on `_isOptimistic(pid)` at runtime, which itself is a sload
through the GovernorBase lens (Wave 2 binding obligation, per the
docstring). The walker has to:

- Dispatch on optimistic vs pessimistic (the precondition has the
  optimistic gate but the WALKER decision is a sload from
  `optimisticProposalDetails[pid].vetoThreshold`).
- In the optimistic case, do a staticcall to `_getOptimisticVotes`
  (cross-contract into the IOptimisticVotes-bearing token).
- In the just-crossed-threshold case, dispatch into ProposalLib's
  `transitionToPessimistic_400` (which is itself DOUBTFUL — has 4
  staticcalls + a sub-call into `_saveProposal_580`).
- Bookkeep _proposalVotes[pid] write with checked_add.

The docstring acknowledges this is "Wave 2 binding work". The current
axiom is the unconstrained shape; the binding work would tighten the
gate disjunction into a case-split and the walker proof would dispatch
each case. **The gap is real — there is no constraint that ties the
walker's optimistic-vs-pessimistic choice to the precondition.**

### `run_fun_execute_4145_at_proj_sim` (ReserveOptimisticGovernor) — ~350 LOC body

Dispatches on `_isOptimistic`:
- Optimistic: `TimelockControllerOptimistic.executeBatchBypass` — a
  cross-contract CALL.
- Pessimistic: `super._executeOperations` from GovernorTimelockControl.

Same shape concern as castVote. The Skolem
`proj_post_execute_4145 storage_base pid isOpt now` takes `isOpt` as
argument, but the walker reads it from storage — there's nothing in
the axiom tying the walker's storage read to the Skolem's `isOpt`
argument.

### `run_fun_proposeOptimistic_179_at_storage_base` (ProposalLib) — ~180 LOC body, 5 staticcalls

The walker has to: (1) close the validateProposal sub-call (own
DOUBTFUL axiom), (2) dispatch 3+ staticcalls each with their own
callee-spec axiom (governor.timelock, timelock.hasRole(role,
proposer), governor.selectorRegistry), (3) drive a for-loop over
targets each doing extcodesize+staticcall+require, (4) finally close
`_saveProposal_580`. Estimated proof effort: 800-1200 LOC of glue
across 5+ leaves.

### `run_fun_proposePessimistic_288_at_storage_base` (ProposalLib) — mirror of propose Optimistic

Same shape, different gating (votes-threshold via two staticcalls
instead of a role staticcall). Same concern: the
`votingDelay`/`votingPeriod` returns from the staticcalls are absorbed
opaquely by the Skolem.

### `run_fun_transitionToPessimistic_400_at_storage_base` (ProposalLib) — ~150 LOC, 4 staticcalls

Calls `_saveProposal_580` at the end with `votingDelay`/`votingPeriod`
returned from staticcalls. Same Skolem-absorbs-staticcall concern.

### `run_fun_registerSelectors_145_at_proj_sim` / `run_fun_unregisterSelectors_180_at_proj_sim` (SelectorRegistry) — ~140 LOC body + unbounded for-loop

Per-iteration: read target/selector, optionally check the forbidden
list (register only), call OZ EnumerableSet add/remove on
`_allowedSelectors[target]`, conditionally call EnumerableSet
add/remove on `_targets`. The composite walker would need induction
over the batch list — and the corpus has no inductive walker pattern
yet (every other walker is straight-line). The cross-invariant
preservation (target in _targets iff _allowedSelectors[target] is
nonempty) is asserted by `set_eq_in_targets ∧ set_eq_at_target` on the
post-state.

**Gap:** the post-state Skolem `proj_sim_post_register_selectors sim
forbidden batch` is loose — it claims set-equality at every
target/selector, but does not pin per-iteration position values or
slot-3 body ordering. A buggy walker that skipped a batch element or
double-added would still satisfy the set-equality if (by coincidence)
the duplicate compresses to the same membership predicate. The bridge
axioms (`proj_sim_register_selectors_observes`) are stated as
existence, not uniqueness.

### `run_fun_registerVersion_152_at_proj_sim` (VersionRegistry) — ~150 LOC, 2 staticcalls + keccak

Has a keccak step (S25: keccak256 of the abi-encoded version string
returned from a staticcall). The trust axiom
`versioned_version_hashes_to_versionHash` is stated as `True` — a
genuine "trust me" axiom that asserts NO content. The walker would
need that axiom to be a real bridge tying the staticcall return + the
keccak result to `version_hash v`. Today it's a placeholder.

### `run_fun_executeBatchBypass_201` / `scheduleBatch_1295` / `executeBatch_1552` (TimelockControllerOptimistic)

`executeBatch_1552` has a per-target `_execute` opaque external call
that "the sim model doesn't track". This is reasonable for the audit
narrative (Timelock state machine is about the queue ordering, not the
side-effects) but the composite walker has to formally dispatch every
target's external call via a R063-style bridge AND admit that the
side-effects don't disturb the Timelock storage. That's a non-trivial
trust.

`scheduleBatch_1295` has a for-loop over targets, each writing
`timestamps[id_i]`. Same per-iteration induction concern as
register/unregisterSelectors.

### `run_fun_setRewardRatio_1036_at_proj_sim` / `run_fun_poke_1082_at_proj_sim` (StakingVaultRewards)

The `accrueRewards` modifier wraps the body and walks the rewardTokens
list (per-token reads/writes, including a `isRegistered` staticcall to
the reward-token-registry per iteration, plus an ERC20 balanceOf
staticcall). The post-storage Skolem absorbs all the per-token
accruals opaquely.

### `run_fun__authorizeUpgrade_1574_at_proj_sim` (StakingVaultAdmin) — ~130 LOC, 3 staticcalls

Three sequential staticcalls into the version registry, each with a
keccak-based callee-spec axiom. Storage is UNCHANGED (this is just a
sanity-check view), but each staticcall's return value is consumed by
a require_helper. **The walker has to:** (a) thread call_result=1
through three bridges, (b) decode the dynamic-length return for
`getLatestVersion()` (an `(bytes32, string, address, bool)` tuple —
the audit-time obligation is bigger than what
`StaticCallBridge.run_staticcall_to_word` covers).

### `run_fun_cancel_238_at_proj_sim_admin` / `_guardian` (Guardian) — 345-LOC body, 4-6 staticcalls + 1 CALL

These have multiple branches and 4+ external calls; the storage is
UNCHANGED (cancel doesn't write Guardian storage) but the walker still
has to dispatch each call. The two axioms cover the two role-branches
of the same function — there's actually a third (non-admin AND
non-guardian) reachable case that's unauthorized and reverts; the
walker proof must show the two success-axioms exhaust the success
disjunction in the milestone theorem.

## HAND-WAVING

These axioms are where the walker-completeness assertion is weakest.
Each has at least one of:

- A delegatecall into a contract whose body is itself axiomatised.
- A staticcall whose return value is absorbed by the Skolem rather
  than constrained by the precondition.
- A post-storage that touches 8+ slots whose effects are absorbed
  opaquely.
- A reentry-sensitive ordering (the ZERO-FIRST pattern in
  claimRewards) whose mechanization requires modelling all the
  intermediate states.

### `run_fun_deposit_4312_at_storage_base` / `mint_4356` / `withdraw_4403` / `redeem_4450` (StakingVaultExchange)

Each of these has a body of 280-320 Yul statements. They touch
**8+ distinct storage slots** in different namespaces:
- ERC20 balances + totalSupply
- ERC4626 totalAssets cache
- ReentrancyGuard status
- Votes delegateCkpt + total_ckpt (chain of checkpoints)
- StakingVault optimisticDelegateCkpt
- Per-reward-token trackers (5 slots each — totalRewards,
  lastUpdated, accruedRewards, totalClaimed, totalDeposited)
- StakingVault native bookkeeping (totalDeposited,
  nativeBalanceLastKnown, nativeRewardsLastPaid)
- ERC20 allowance (withdraw/redeem only — via _spendAllowance)

Plus external CALLs to:
- The underlying asset.transferFrom (deposit/mint) or asset.transfer
  (withdraw/redeem)
- SafeERC20.forceApprove + unstakingManager.createLock (withdraw/redeem
  delay>0 branch)
- ERC20.balanceOf staticcall (totalAssets)

The post-state Skolem `proj_post_deposit_4312 storage_base caller
assets receiver now` is an OPAQUE function of these arguments —
nothing in the corpus today tells me the Skolem agrees with the sim's
`deposit` definition. The observational bridges are stated as
`storage_equiv` reflexivity-style placeholders.

**The honest assessment:** these axioms could be satisfied by ANY
function that "exists memory' such that the body executes successfully
and produces some post-storage". The walker proof would not just need
the existing R040 / R047 / R067 toolkit — it would need the entire
ERC4626 + Votes + ReentrancyGuard equivalence layers ALSO Qed (which
they are not — they're framed as slot-agnostic helpers, per R072).
Writing the walker is a multi-week workstream.

### `run_fun_claimRewards_1010_at_proj_sim` (StakingVaultRewards)

ZERO-FIRST reentrancy: the inner loop writes
`accruedRewards := 0` BEFORE calling `safeTransfer` to the reward
token. The composite axiom doesn't capture the intermediate state —
it only asserts the start-and-end. But the audit-narrative claim is
about REENTRANCY safety, which is precisely about intermediate states.
The walker proof would have to expose the intermediate state for the
reentrancy lemma to chain — the current axiom shape doesn't allow
that.

The reentrancy proof is already mechanized at the SIM level in
`proofs/StakingVaultRewardsReentrancy.v` — but the lifting from
sim-level reentrancy to walker-level reentrancy is not closed by the
composite axiom as stated.

### `run_fun_propose_389` / `castVote_4378` / `execute_4145` (ReserveOptimisticGovernor)

Already discussed above (delegatecall to ProposalLib, branching on
`_isOptimistic` storage with no precondition tie). The "HAND-WAVING"
classification (vs DOUBTFUL) is because the gating storage read is
NOT in the precondition — the axiom unconditionally asserts existence
of a walker post-state agreeing with the Skolem regardless of
runtime branch choice.

### `run_fun_upgradeToAndCall_2829` (StakingVaultAdmin)

DELEGATECALLs into the new implementation's `initialize_v<N>`
reinitializer with `data`. The walker's post-state absorbs the
delegatecall's storage side-effects via the Skolem
`proj_post_upgradeToAndCall_2829 storage_base newImpl data_mpos`. The
delegatecall's effect is whatever the new impl writes — there is NO
constraint on what that is. A malicious upgrade could write anywhere
and the axiom would still hold.

The audit-narrative defense is that the version-registry
authorization (via `_authorizeUpgrade`) is the trust gate. That's a
valid OPERATIONAL defense but it doesn't make the walker axiom
meaningful — the axiom asserts a post-state that the framework cannot
distinguish from a buggy impl.

## Recommendations

### Highest-priority axioms to retire by writing the actual walker proof

These three would have the highest leverage per LOC. Picking them
because:
- The work is bounded and known-shape (no novel framework piece
  required).
- They unblock dependent axioms (closing one removes 2-3 others
  via composition).
- They're in the most-trusted contracts of the corpus (governance
  flow, role-management).

**1. `run_fun__revokeRole_736_at_proj_sim_member` (Guardian.v)**

Effort estimate: ~800-1200 LOC, 2-3 day workstream. The Guardian.v
docstring (lines 9137-9203) lays out the walker shape exhaustively —
swap-and-pop EnumerableSet remove, 5 storage writes, no external
calls. Closing this unblocks four downstream axioms:
- `run_fun_revokeRole_13593_at_proj_sim` (StakingVaultAdmin)
- `run_fun_renounceRole_13616_at_proj_sim` (StakingVaultAdmin)
- `run_fun_revokeOptimisticProposer_136_at_proj_sim`
  (TimelockControllerOptimistic)
- Future ERC20Votes / StakingVault delegation axioms that will need
  the same OZ EnumerableSet remove walker.

The R059 bridge lemmas are already Qed; only the walker glue remains.
This is the most-leverage / lowest-risk retirement target in the corpus.

**2. `run_fun_setUnstakingDelay_750_at_proj_sim` (StakingVaultAdmin.v)**

Effort estimate: ~200-300 LOC, single-day workstream. Pure
MECHANICAL — onlyRole + one require + one sstore at literal slot 5 +
one log. Closing this establishes the **template** for every other
"admin-gated simple-sstore" axiom (which there are many of, including
several non-listed StakingVaultAdmin getters that will need walkers
when their writeable counterparts arrive). Closing this is a
forcing-function for the corpus to validate "the R067 recipe + admin
gate" without any other complications.

**3. `run_fun_deprecateVersion_187_at_proj_sim` (VersionRegistry.v)**

Effort estimate: ~400-600 LOC. The VersionRegistry docstring (lines
1332-1481) lists every step (S1-S18) and explicitly enumerates the
remaining residuals (memory prelude, post-bridge — bool sstore is
already DONE). The leaves are catalogued. Closing this validates the
end-to-end **staticcall bridge through R063** in a real walker
proof — which the corpus hasn't done yet. Every other staticcall-bearing
axiom would benefit from the methodology this closure would crystallize.

### Other tractable retirements

Beyond the top three, the following are tractable as one-day
exercises:
- `run_fun__add_240_at_proj_sim_in` (RewardTokenRegistry — no-op
  branch, 10 statements)
- `run_fun__remove_324_at_proj_sim_not_in` (mirror no-op)
- `run_fun_cancel_1394_at_proj_sim` (TimelockController — one sstore,
  one require, no external)
- `run_fun_isAllowed_211_at_proj_sim` (SelectorRegistry view — once
  the OZ EnumerableSet `_contains` body is bridged)
- `run_fun__at_1791_at_proj_sim` (AccessControlEnumerable — sload at
  derived offset)

A 3-week focused push could plausibly close all of MECHANICAL + half
of EFFORT (12-14 axioms), reducing the trust budget by ~30% and —
critically — establishing the walker-proof methodology in code rather
than docstring.

### Axioms that should NOT be retired before architectural work

The HAND-WAVING set (10 axioms) is not tractable as walker-proof work
in isolation. They would require:

- A real ERC20 / ERC4626 / Votes / ReentrancyGuard equivalence layer
  (currently scoped as R072 slot-agnostic helpers — these don't bridge
  the walker).
- A delegatecall bridge (currently only `StaticCallBridge` exists).
- A reentrancy-aware Hoare-triple format (the current
  `{{? ... ⇓ ... | ... ?}}` shape is sequential-state; reentrancy
  needs interleaving).
- A precondition-to-runtime-branch tightening pattern (e.g. the
  `_isOptimistic` storage read tying to the precondition disjunction).

These should be flagged in the audit deliverable as **trust boundaries
the framework cannot currently discharge**. The audit can describe
them honestly — "the framework's current expressivity cannot
mechanize these — they are accepted as parametric trust at the
specification level, paired with sim-level model proofs in
`proofs/StakingVaultRewardsReentrancy.v` etc."

### Documentation-vs-content honesty check

The docstrings for the DOUBTFUL/HAND-WAVING axioms are generally
**accurate** — they describe the walker shape, list the staticcalls,
flag the Wave 2 binding obligations. They do not over-claim mechanical
closure. The honesty is in the docstring; the gap is in the
specification's looseness (Skolem absorbs runtime branch decisions /
staticcall returns). A reader of the docstring will not be fooled.

However, three specific patterns deserve calling out:

1. **`versioned_version_hashes_to_versionHash` (VersionRegistry) is
   stated as `True`.** It's a placeholder where a real bridge needs to
   live. Any walker proof for `registerVersion_152` would fail because
   the True-axiom cannot be applied to tie the keccak output to the
   version-hash invariant.

2. **`targets_view_matches_sim` and
   `selectors_allowed_view_matches_sim` (SelectorRegistry)** are also
   `True`. They are placeholder bridges for the abi-encoded memory
   array output. Same issue.

3. **`igovernor_state_returns_not_defeated` /
   `igovernor_cancel_returns_pid` (Guardian)** are similar `True`
   placeholders. The audit-time obligation is that the Governor's
   `state()` and `cancel()` honor the precondition; today the bridge
   asserts nothing.

These should be retired by writing real bridges, or moved to the audit
deliverable as **known incomplete callee specifications**.

## Summary

- **45 composite walker axioms** total. The classification skews
  toward DOUBTFUL/HAND-WAVING (25/45 = 56%) — load-bearing for the
  audit narrative.
- The R067 / R070 recipe is well-designed for the MECHANICAL/EFFORT
  bottom half. The recipe does NOT scale to the HAND-WAVING top of
  the corpus where delegatecall, runtime-branch storage reads, and
  multi-namespace storage mutation co-occur.
- **Three immediate retirements** (Guardian R059 revoke walker,
  StakingVault setUnstakingDelay, VersionRegistry deprecateVersion)
  would reduce the trust budget by ~3 axioms direct + ~4 dependent
  (via the R059 propagation) and establish the walker-proof
  methodology in code.
- **Six `True` placeholder axioms** (versioned_version_hashes,
  targets_view_matches_sim, selectors_allowed_view_matches_sim,
  igovernor_state_returns_not_defeated, igovernor_cancel_returns_pid,
  proj_post_*_observes-as-reflexivity) should be either retired by
  writing real bridges or surfaced in the audit deliverable as known
  incomplete specifications.
- The HAND-WAVING tier (10 axioms — Governor delegatecall, StakingVault
  ERC4626 mutators, claimRewards reentrancy) is honestly NOT amenable
  to walker-proof retirement without architectural work on the
  framework's expressivity (delegatecall bridge, ERC4626 equivalence
  layer, reentrancy-aware Hoare-triple format). These should be
  documented as parametric-trust boundaries with sim-level
  counterproofs (which several of them already have — e.g.
  `StakingVaultRewardsReentrancy.v`).
