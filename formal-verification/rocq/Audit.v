(** ============================================================
    Reserve Governor — formal verification Audit index.

    Audit-facing re-export surface. The goal is to give an auditor a
    single file to read top-to-bottom that surfaces every
    decision-relevant theorem with the calibration / context needed to
    interpret it.

    The audit is organized into three parts:

      Part I  — Per-domain headlines (validity / conservation / safety /
                negative theorems for each of the 12 components).
      Part II — Integration theorems (cross-domain composition).
      Part III — Adversarial / negative theorems ("X cannot happen"),
                cross-referenced from their domain section so an auditor
                can find every reachable-state denial in one place.

    The component order mirrors the protocol stack:

      1. ProposerThrottle             — per-account proposal frequency
                                         cap.
      2. UnstakingManager             — time-locked withdrawal queue,
                                         with conservation deltas and
                                         no-double-spend.
      3. OptimisticSelectorRegistry   — (target, selector) whitelist
                                         with NoDup + pruned-keys
                                         invariant.
      4. StakingVault — Exchange       — ERC4626 exchange-rate floor,
                                         deposit/accrue bookkeeping, and
                                         the never-underwater invariant.
      5. StakingVault — Rewards        — multi-token index-based reward
                                         accrual with full conservation
                                         (balanceAccounted = Σ accrued +
                                         totalClaimed).
      6. StakingVault — Delegation     — dual-track (standard /
                                         optimistic) delegation
                                         conservation and independence.
      7. ProposalLib                   — proposal validation and the
                                         optimistic → pessimistic
                                         transition primitive.
      8. ReserveOptimisticGovernor    — hybrid optimistic/standard
                                         governance escalation state
                                         machine, with non-de-escalation
                                         after transition and
                                         no-double-execution.
      9. TimelockControllerOptimistic — execution queue with
                                         bypass-for-optimistic path and
                                         the single-shot theorem on the
                                         reachable-state level.
     10. Guardian                      — admin/guardian role layer over
                                         cancel/grant/revoke (NEW).
     11. RewardTokenRegistry          — owner-gated list of accepted
                                         reward tokens (NEW).
     12. VersionRegistry              — append-only version history
                                         with sticky deprecation (NEW).

    Each section [Require]s its proof modules and re-exports the
    load-bearing safety lemmas via [Notation] under [audit_<feature>]
    names. The closing section gives a one-screen table-of-contents of
    every [audit_*] name and the property it captures, intended as the
    auditor's entry point.

    See [../README.md] for the dual-track Rocq + CAS verification
    rationale and [../notes/simulation_fidelity_audit.md] for the
    catalog of known divergences between this simulation and the
    production contracts.
*)

(* All proof modules are pulled in by [Require] only, so symbols stay
   namespaced and there is no scope collision between modules that
   each export their own [Valid] submodule. The [Notation]s below
   reference everything by fully-qualified name. *)

(* Round-2 baseline modules. *)
Require ReserveGovernor.proofs.ProposerThrottle.
Require ReserveGovernor.proofs.ProposerThrottle_validity.
Require ReserveGovernor.proofs.UnstakingManager.
Require ReserveGovernor.proofs.UnstakingManager_validity.
Require ReserveGovernor.proofs.SelectorRegistry.
Require ReserveGovernor.proofs.StakingVaultExchange.
Require ReserveGovernor.proofs.StakingVaultRewards.
Require ReserveGovernor.proofs.StakingVaultDelegation.
Require ReserveGovernor.proofs.StakingVaultDelegation_validity.
Require ReserveGovernor.proofs.ProposalLib.
Require ReserveGovernor.proofs.ProposalLib_validity.
Require ReserveGovernor.proofs.Governor.
Require ReserveGovernor.proofs.Governor_validity.
Require ReserveGovernor.proofs.Timelock.
Require ReserveGovernor.proofs.Timelock_validity.

(* Round-3 backfill: validity, conservation, no-de-escalation. *)
Require ReserveGovernor.proofs.UnstakingManager_conservation.
Require ReserveGovernor.proofs.SelectorRegistry_validity.
Require ReserveGovernor.proofs.StakingVaultExchange_validity.
Require ReserveGovernor.proofs.StakingVaultRewards_conservation.
Require ReserveGovernor.proofs.Governor_no_de_escalation.

(* Round-4 additions: new components, single-shot/no-double-spend
   negative theorems, and a new integration. *)
Require ReserveGovernor.proofs.Guardian.
Require ReserveGovernor.proofs.Guardian_validity.
Require ReserveGovernor.proofs.RewardTokenRegistry.
Require ReserveGovernor.proofs.RewardTokenRegistry_validity.
Require ReserveGovernor.proofs.VersionRegistry.
Require ReserveGovernor.proofs.VersionRegistry_validity.
Require ReserveGovernor.proofs.UnstakingManager_no_double_spend.
Require ReserveGovernor.proofs.Governor_no_double_execution.
Require ReserveGovernor.proofs.Timelock_single_shot.

(* Integration modules — cross-domain composition theorems. *)
Require ReserveGovernor.proofs.Integration_withdraw_lockup.
Require ReserveGovernor.proofs.Integration_withdraw_immediate.
Require ReserveGovernor.proofs.Integration_optimistic_propose.
Require ReserveGovernor.proofs.Integration_governor_timelock.
Require ReserveGovernor.proofs.Integration_no_throttle_bypass.
Require ReserveGovernor.proofs.Integration_upgrade_authorization.


(** ============================================================
    ============================================================
    ===                                                      ===
    ===              Coverage caveats (READ FIRST)           ===
    ===                                                      ===
    ============================================================
    ============================================================

    The audit-narrative theorems below are stated as cleanly as
    possible, but several headline names sound stronger than what
    the theorem actually constrains. This section is the honest
    caveat surface — an external auditor reading Audit.v should
    treat it as the asterisk on every Part I/II/III claim that
    follows.

    Source: multi-vantage adversarial review documented at
    [../../notes/adversarial_review_synthesis.md] (banked from the
    six-agent review of 2026-05-27).

    Caveat-1 (rewards conservation is conditional on WF_accrue).
    ---------------------------------------------------------------
    [audit_rewards_conservation] in Section 5 is proved by
    induction over [Reachable], which is built from
    [step_well_formed]. The [WF_accrue] constructor of
    [step_well_formed] requires
      accrueUser delta <= balanceAccounted - sum_accrued - totalClaimed
    at every step — i.e. the per-step bound that IS the conservation
    inequality. So the theorem is "if every reachable accrue step
    already preserved conservation, then conservation holds." A
    real first-principles discharge requires three new invariants
    threaded through Reachable (supply consistency, delta
    accounting, gap monotonicity); see
    [../../notes/wf_accrue_discharge.md]. Treat the theorem as a
    refactoring of the obligation onto callers, not a reduction of
    the trust surface.

    Caveat-2 (no-throttle-bypass is per-account, not system-level).
    ---------------------------------------------------------------
    [audit_neg_no_throttle_bypass] in Section 9 bounds successful
    consumes at [2 * capacity] per window per proposer. With N
    proposer-role holders, total system throughput is N * 2 *
    capacity. No theorem bounds the proposer-set size or sybil
    cost. Read this claim as "a single proposer can't exceed 2x";
    NOT "the protocol can't exceed 2x" globally.

    Caveat-3 (upgrade_authorized excludes the admin-role gate).
    ---------------------------------------------------------------
    The Section 11 integration theorems
    ([audit_integration_register_then_authorize_self] et al.) prove
    the version-registry-side check (latest && !deprecated) for
    [StakingVault._authorizeUpgrade], explicitly NOT the
    [onlyRole(DEFAULT_ADMIN_ROLE)] modifier on that function. A
    caller who somehow reaches [_authorizeUpgrade] without
    DEFAULT_ADMIN_ROLE is NOT excluded by any landed theorem.
    Source: [../../notes/yul_equivalence_upgrade_authorized.md].

    Caveat-4 (Guardian oracle purity is unsound across TOCTOU).
    ---------------------------------------------------------------
    [audit_guardian_only_cancel_reverts_on_defeated],
    [audit_guardian_cancel_guardian_path] et al. take
    [is_optimistic_oracle] and [proposal_state_oracle] as pure
    [ProposalId -> ...] functions. On chain these are external
    SLOADs against mutable Governor storage, racing with
    [transitionToPessimistic] and [_tallyUpdated]. A guardian
    cancel that the proofs say succeeds may revert on chain when
    the proposal transitions between reads. The model assumes
    serialization the EVM does not provide.

    Caveat-5 (Yul equivalence is sketched, not mechanized).
    ---------------------------------------------------------------
    Every audit_* claim about Solidity-source behavior is stated
    against the hand-written Gallina simulation, not the emitted
    Yul bytecode. The bridge sketch in
    [../../notes/yul_equivalence_upgrade_authorized.md] identifies
    the work needed for one example. Until the bridge is
    mechanized, divergence between simulation and bytecode is not
    audited.

    Caveat-6 (Sim/contract precondition gap on several operations).
    ---------------------------------------------------------------
    Adversarial review found that the simulation under-constrains
    several operations relative to the contract — accepting inputs
    the production code refuses. Concrete known gaps (sim-fidelity
    review):
      - Governor.add_veto admits votes from any phase; contract
        rejects via _validateStateBitmap(Active) and
        _countVote(Against only).
      - Governor.cancel skips _validateCancel role + state rules.
      - Governor.observe misses the pastSupply==0 -> Canceled branch.
      - StakingVaultExchange.withdraw collapses both unstakingDelay
        branches into one; revert condition uses totalAssets rather
        than maxWithdraw(owner).
      - StakingVaultDelegation.set_opt_delegate never reverts;
        contract reverts via SafeCast.toUint208 on overflow.
    Per-domain "preserves_validity" claims hold for the sim's looser
    operation, not the contract's tighter one.

    Caveat-7 (Inherited OZ functions silently unmodeled).
    ---------------------------------------------------------------
    Several state-mutating functions inherited from OZ are not
    modeled in their owning domain's simulation:
      - Guardian: admin-driven [grantRole(GUARDIAN, account)] can
        bypass the zero-address check that [grantOptimisticGuardian]
        enforces.
      - Timelock: [revokeOptimisticProposer] (CANCELLER_ROLE-gated,
        state-mutating) is entirely absent.
      - Timelock: open-executor mode ([executor = address(0)] in
        initializer) is structurally absent.
    Negative theorems for these domains say nothing about sequences
    containing the unmodeled operations.

    Caveat-8 (External-library trust assumptions are load-bearing).
    ---------------------------------------------------------------
    Three external dependencies are axiomatized rather than fully
    mechanized:
      - PRBMath UD60x18.powu via 5 axioms ([mocks/PRBMath.v]).
        Differential-tested in
        [../../test/PRBMathPowuAxioms.t.sol] but the fuzz coverage
        caps exponents far below production-realistic values
        (block.timestamp deltas routinely exceed 86400; tests cap
        at 256 or 1000).
      - OZ Checkpoints.Trace208 via a relaxed mock that silently
        overwrites on out-of-order keys ([mocks/Trace208.v]). The
        OZ-faithful [push_checked] variant exists but is unused.
        L2-deployments with sub-second timestamps can diverge.
      - OZ AccessControlEnumerable via the new [mocks/AccessControl.v]
        — but the three Tier-4 domains (Guardian, VersionRegistry,
        RewardTokenRegistry) DO NOT use it. They still model role
        state locally with ad-hoc lists or boolean Parameters.
        Cross-contract "only X can call Y" claims cannot be stated
        until the per-domain rewiring lands ([../../notes/access_control_threading.md]).

    Caveat-9 (Reward-token trust assumption excludes common tokens).
    ---------------------------------------------------------------
    The ERC20 mock ([mocks/ERC20.v]) models exact-debit/exact-credit
    transfers. The following deployed token classes violate the
    model:
      - Blacklist tokens (USDT, USDC) — safeTransfer can revert on
        a blacklisted recipient, breaking [claimRewards] mid-batch.
      - Rebasing tokens (stETH, etc.) — balanceOf can decrease
        between blocks without a transfer; the reward-index delta
        computes phantom outflows.
      - Fee-on-transfer tokens (PAXG, some BNB tokens) — recipient
        receives less than amount; balanceLastKnown accounting
        drifts upward forever.
      - Callback tokens (ERC777, ERC1363) — transfer-time callbacks
        enable reentrancy into [_accrueRewards] mid-claim.
    The "rewards-conservation" theorem holds for the honest-ERC20
    model only.

    Caveat-10 (End-to-end existence theorems are decorative).
    ---------------------------------------------------------------
    [optimistic_lifecycle_exists] and [standard_lifecycle_exists]
    in [proofs/EndToEnd_*.v] are not surfaced by any audit_*
    notation in Part II. They are existence-only claims (`exists
    sequence, conclusion`) with cherry-picked numeric constants
    (vetoThreshold=10, supply=100, no votes cast). The standard
    flow uses an oracle step [advance_to_std_active] outside the
    per-domain Reachable inductive. Time monotonicity is [<=] with
    an unused [t2], permitting timestamp collapse. Treat these as
    "the system can be wired up coherently", NOT "the system works
    under contention".

    Caveat-11 (Protocol-level attacks not covered by formal model).
    ---------------------------------------------------------------
    Several real attack vectors are structurally outside the formal
    model. Documented in adversarial review:
      - Reentrancy via hookable underlying tokens (no transaction
        model; tokens are pure oracles).
      - ERC4626 first-depositor + asset-donation reward capture
        (the half-life rewards stream over a donated balance gap).
      - Proposer can cancel a Succeeded optimistic proposal,
        burning the throttle slot (DoS / censorship by the original
        proposer).
      - executeBatchBypass salt-collision DoS if PROPOSER_ROLE
        expands beyond governor.
      - StakingVault.initialize trusts arbitrary msg.sender as
        deployer (off-canonical-deployment risk).
      - Guardian.cancel TOCTOU with _tallyUpdated transition
        (proposer races a vetoer to nudge path toward easy
        cancel-and-retry).
    These would need Foundry-level fuzz/invariant tests or
    Yul-equivalence proofs to surface; the existing Gallina
    simulations cannot reach them.
*)


(** ============================================================
    ============================================================
    ===                                                      ===
    ===                  Part I — Per-domain headlines       ===
    ===                                                      ===
    ============================================================
    ============================================================ *)


(** ============================================================
    === Section 1: ProposerThrottle ===
    ============================================================

    [ProposerThrottle] caps the frequency of optimistic proposals per
    account using a fixed-point "charge" that linearly refills over a
    12-hour window. Each proposal burns [FIX_ONE / capacity] of charge.

    Headlines:
      - [audit_proposalsAvailable_le_capacity] : the per-12h proposal
        budget visible to any caller is bounded by [capacity], no
        matter the clock or stored charge.
      - [audit_throttle_consume_success_iff_available] : a [consume]
        call succeeds iff the caller has at least one slot's worth
        of charge.
      - [audit_throttle_consume_revert_iff_no_proposals] : the
        complementary revert side of the same gate.
      - [audit_throttle_consume_storage_delta] : a successful consume
        bumps [lastUpdated := now] and decrements [currentCharge] by
        exactly [FIX_ONE / capacity] — no other writes.
      - [audit_throttle_preserves_validity] : [consume] preserves the
        [0 <= currentCharge <= FIX_ONE] storage invariant.
*)

Notation audit_proposalsAvailable_le_capacity :=
  ReserveGovernor.proofs.ProposerThrottle.ProposerThrottleProofs.proposalsAvailable_le_capacity.

Notation audit_throttle_consume_success_iff_available :=
  ReserveGovernor.proofs.ProposerThrottle.ProposerThrottleProofs.consume_success_iff_proposal_available.

Notation audit_throttle_consume_revert_iff_no_proposals :=
  ReserveGovernor.proofs.ProposerThrottle.ProposerThrottleProofs.consume_revert_iff_no_proposals_available.

Notation audit_throttle_consume_storage_delta :=
  ReserveGovernor.proofs.ProposerThrottle.ProposerThrottleProofs.consume_success_storage_delta.

Notation audit_throttle_preserves_validity :=
  ReserveGovernor.proofs.ProposerThrottle_validity.ProposerThrottleValidity.consume_preserves_validity.


(** ============================================================
    === Section 2: UnstakingManager ===
    ============================================================

    [UnstakingManager] holds the time-locked queue between unstake
    request and asset release. Each user-owned lock has an
    [unlockTime] (the earliest moment it can be claimed) and a
    [claimedAt] timestamp set on successful release.

    Headlines (round-2 originals):
      - [audit_unstaking_claim_then_claim_reverts] : every lock is
        claimable at most once — a second claim on the same lockId
        reverts.
      - [audit_unstaking_cancel_then_claim_reverts] : a cancelled lock
        cannot be claimed.
      - [audit_unstaking_claim_before_maturity_reverts] : the time-lock
        is honored — claim before [unlockTime] always reverts.
      - [audit_unstaking_claim_on_default_reverts] : a lockId pointing
        at the default-zero slot is unclaimable.
      - [audit_unstaking_createLock_preserves_validity] : creating a
        lock preserves the structural state invariant.

    Round-3 conservation backfill:
      - [audit_unstaking_createLock_conservation] : [createLock]
        increases [total_active] by exactly [amount] when
        [unlockTime > 0].
      - [audit_unstaking_createLock_zero_unlock_no_delta] : the
        degenerate [unlockTime = 0] branch leaves [total_active]
        unchanged (a fresh slot indistinguishable from default).
      - [audit_unstaking_cancelLock_conservation] : a successful
        [cancelLock] decreases [total_active] by exactly the cancelled
        lock's pre-cancel [active_amount].
      - [audit_unstaking_claimLock_conservation] : a successful
        [claimLock] decreases [total_active] by exactly the claimed
        lock's [amount].
      - [audit_unstaking_total_active_bounded] : if every per-lock
        [amount] fits in U256 and their sum fits in U256, so does
        [total_active] (overflow-safety of the running sum).

    Round-4 negative theorem (cross-referenced in Part III):
      - [audit_unstaking_no_double_spend] : on any reachable state,
        no [lockId] can be both claimed and cancelled (the two
        resolution states are exclusive at the storage level).
*)

Notation audit_unstaking_claim_then_claim_reverts :=
  ReserveGovernor.proofs.UnstakingManager.UnstakingManagerProofs.claim_then_claim_reverts.

Notation audit_unstaking_cancel_then_claim_reverts :=
  ReserveGovernor.proofs.UnstakingManager.UnstakingManagerProofs.cancel_then_claim_reverts.

Notation audit_unstaking_claim_before_maturity_reverts :=
  ReserveGovernor.proofs.UnstakingManager.UnstakingManagerProofs.claim_before_maturity_reverts.

Notation audit_unstaking_claim_on_default_reverts :=
  ReserveGovernor.proofs.UnstakingManager.UnstakingManagerProofs.claim_on_default_reverts.

Notation audit_unstaking_createLock_preserves_validity :=
  ReserveGovernor.proofs.UnstakingManager_validity.UnstakingManagerValidity.createLock_preserves_validity.

(* Round-3 conservation. *)
Notation audit_unstaking_createLock_conservation :=
  ReserveGovernor.proofs.UnstakingManager_conservation.UnstakingManagerConservation.createLock_conservation.

Notation audit_unstaking_createLock_zero_unlock_no_delta :=
  ReserveGovernor.proofs.UnstakingManager_conservation.UnstakingManagerConservation.createLock_with_zero_unlock_no_delta.

Notation audit_unstaking_cancelLock_conservation :=
  ReserveGovernor.proofs.UnstakingManager_conservation.UnstakingManagerConservation.cancelLock_conservation.

Notation audit_unstaking_claimLock_conservation :=
  ReserveGovernor.proofs.UnstakingManager_conservation.UnstakingManagerConservation.claimLock_conservation.

Notation audit_unstaking_total_active_bounded :=
  ReserveGovernor.proofs.UnstakingManager_conservation.UnstakingManagerConservation.total_active_bounded_by_max_locks.

(* Round-4 negative theorem. *)
Notation audit_unstaking_no_double_spend :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_double_spend.

Notation audit_unstaking_no_double_spend_sequence :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_double_spend_sequence.

Notation audit_unstaking_no_cancel_then_claim_sequence :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_cancel_then_claim_sequence.


(** ============================================================
    === Section 3: OptimisticSelectorRegistry ===
    ============================================================

    [OptimisticSelectorRegistry] is the (target, function-selector)
    whitelist that gates optimistic proposals. A call survives the
    optimistic call-validation gate only if the (target, selector)
    pair is registered.

    Headlines (round-2 originals):
      - [audit_selector_isAllowed_iff_member] : the public [isAllowed]
        query is exactly set membership against the stored allowlist.
      - [audit_selector_addSelector_idempotent] : registering the same
        (target, selector) twice has no further effect.
      - [audit_selector_remove_nonmember_noop] : removing an entry that
        isn't registered is a no-op (no state change, no revert).
      - [audit_selector_addSelector_forbidden_reverts] : adding a
        forbidden target (governor / timelock self-addresses) reverts.
      - [audit_selector_addSelector_zero_reverts] : adding the
        zero-selector reverts.

    Round-3 backfill (validity):
      - [audit_selector_addSelector_preserves_validity] :
        [addSelector] preserves the keys-NoDup / sels-NoDup /
        pruned-keys invariant.
      - [audit_selector_removeSelector_preserves_validity] :
        symmetric for [removeSelector].
*)

Notation audit_selector_isAllowed_iff_member :=
  ReserveGovernor.proofs.SelectorRegistry.SelectorRegistryProofs.isAllowed_iff_member.

Notation audit_selector_addSelector_idempotent :=
  ReserveGovernor.proofs.SelectorRegistry.SelectorRegistryProofs.addSelector_idempotent.

Notation audit_selector_remove_nonmember_noop :=
  ReserveGovernor.proofs.SelectorRegistry.SelectorRegistryProofs.removeSelector_nonmember_noop.

Notation audit_selector_addSelector_forbidden_reverts :=
  ReserveGovernor.proofs.SelectorRegistry.SelectorRegistryProofs.addSelector_forbidden_reverts.

Notation audit_selector_addSelector_zero_reverts :=
  ReserveGovernor.proofs.SelectorRegistry.SelectorRegistryProofs.addSelector_zero_selector_reverts.

(* Round-3 validity. *)
Notation audit_selector_addSelector_preserves_validity :=
  ReserveGovernor.proofs.SelectorRegistry_validity.SelectorRegistryValidity.addSelector_preserves_validity.

Notation audit_selector_removeSelector_preserves_validity :=
  ReserveGovernor.proofs.SelectorRegistry_validity.SelectorRegistryValidity.removeSelector_preserves_validity.


(** ============================================================
    === Section 4: StakingVault — Exchange surface ===
    ============================================================

    [StakingVault] is an ERC4626 vault over the stake asset. The
    exchange surface mediates between assets and shares; native
    rewards are reflected via [accrue], which raises [totalAssets]
    while leaving [totalSupply] alone (so the share rate is
    non-decreasing).

    Headlines (round-2 originals):
      - [audit_vault_round_trip_floor_bound] : converting assets to
        shares and back never returns more than the original input —
        the round-trip is monotonically lossy (in the user's favor
        from the vault's solvency perspective).
      - [audit_vault_share_rate_monotone_under_accrue] : the share
        price never falls when rewards accrue.
      - [audit_vault_deposit_storage_delta] : the assets/shares
        bookkeeping after a deposit is exactly [totalDeposited +=
        assets, totalSupply += shares].
      - [audit_vault_accrue_preserves_share_book] : [accrue] only
        touches the reward bucket; [totalSupply] and [totalDeposited]
        are invariant.

    Round-3 backfill (validity + never-underwater):
      - [audit_vault_deposit_preserves_validity] : [deposit] preserves
        the [totalSupply <= totalDeposited * SHARES_DECIMAL_OFFSET]
        solvency invariant.
      - [audit_vault_withdraw_preserves_validity] : symmetric for
        [withdraw].
      - [audit_vault_accrue_preserves_validity] : [accrue] preserves
        the solvency invariant (accrual only raises totalDeposited).
      - [audit_vault_never_underwater] : on any [Valid.state], the
        share/asset bookkeeping never crosses into a state where
        totalSupply outruns the asset-side accounting.
*)

Notation audit_vault_round_trip_floor_bound :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.round_trip_floor_bound.

Notation audit_vault_share_rate_monotone_under_accrue :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.accrue_share_rate_monotone.

Notation audit_vault_deposit_storage_delta :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.deposit_storage_delta.

Notation audit_vault_accrue_preserves_share_book :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.accrue_preserves_share_book.

(* Round-3 validity / never-underwater. *)
Notation audit_vault_deposit_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultExchange_validity.StakingVaultExchangeValidity.deposit_preserves_validity.

Notation audit_vault_withdraw_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultExchange_validity.StakingVaultExchangeValidity.withdraw_preserves_validity.

Notation audit_vault_accrue_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultExchange_validity.StakingVaultExchangeValidity.accrue_preserves_validity.

Notation audit_vault_never_underwater :=
  ReserveGovernor.proofs.StakingVaultExchange_validity.StakingVaultExchangeValidity.never_underwater.


(** ============================================================
    === Section 5: StakingVault — Multi-token Rewards ===
    ============================================================

    Reward distribution uses the standard "global index" pattern:
    each token has a per-share [rewardIndex] that strictly grows over
    time, and each user caches the index value at their last accrual
    so their pending rewards are computed as
    [balance * (index - lastIndex)].

    Headlines (round-2 originals):
      - [audit_rewards_index_monotone] : the global [rewardIndex] is
        non-decreasing across [updateRewardIndex].
      - [audit_rewards_user_accrued_monotone] : a user's accrued
        balance only grows under [accrueUser]; rewards are never
        silently lost.
      - [audit_rewards_claim_zeroes_accrued] : a successful [claim]
        zeroes the user's accrued bucket atomically.
      - [audit_rewards_claim_returns_accrued] : the claim disburses
        exactly the user's prior accrued balance.
      - [audit_rewards_totalClaimed_monotone] : the global
        [totalClaimed] counter is non-decreasing across claims.
      - [audit_rewards_no_op_when_index_stable] : if the global index
        hasn't moved since the user's last touch, [accrueUser] is a
        no-op.

    Round-3 conservation:
      - [audit_rewards_conservation] : the full bookkeeping invariant
        [balanceAccounted = Σ user.accruedRewards + totalClaimed]
        holds at every state reachable by [updateRewardIndex],
        [accrueUser], and [claimUser]. Tokens are neither created
        nor destroyed by reward operations.
*)

Notation audit_rewards_index_monotone :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.updateRewardIndex_monotone.

Notation audit_rewards_user_accrued_monotone :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.accrueUser_accrued_monotone.

Notation audit_rewards_claim_zeroes_accrued :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.claimUser_zeroes_accrued.

Notation audit_rewards_claim_returns_accrued :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.claimUser_returns_accrued.

Notation audit_rewards_totalClaimed_monotone :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.claimUser_totalClaimed_monotone.

Notation audit_rewards_no_op_when_index_stable :=
  ReserveGovernor.proofs.StakingVaultRewards.StakingVaultRewardsProofs.accrueUser_no_op_when_index_stable.

(* Round-3 conservation. *)
Notation audit_rewards_conservation :=
  ReserveGovernor.proofs.StakingVaultRewards_conservation.StakingVaultRewardsConservation.rewards_conservation.


(** ============================================================
    === Section 6: StakingVault — Dual Delegation ===
    ============================================================

    [StakingVault] maintains two independent vote ledgers
    (standard / optimistic) keyed by delegatee. A transfer between
    two accounts updates both ledgers in parallel, debiting the
    sender's delegate and crediting the recipient's delegate on each
    ledger separately.

    Headlines:
      - [audit_delegation_transfer_preserves_total_votes] : a transfer
        between accounts with distinct non-zero delegates conserves
        the sum of votes [delegate(from) + delegate(to)] on both
        ledgers.
      - [audit_delegation_opt_independent_of_std] : the optimistic
        ledger's evolution under [transfer] depends only on the
        optimistic ledger and the balances.
      - [audit_delegation_std_independent_of_opt] : symmetric
        independence in the other direction.
      - [audit_delegation_self_transfer_noop] : a transfer between
        accounts sharing the same delegate on both ledgers leaves
        both vote vectors unchanged.
      - [audit_delegation_change_moves_all_balance] : re-pointing an
        account's optimistic delegate moves the account's full
        balance from the old delegate to the new one, leaving every
        other delegate's vote count untouched.
      - [audit_delegation_mint_no_zero_credit] : minting never
        credits the zero delegate.
      - [audit_delegation_burn_no_zero_credit] : burning never
        credits the zero delegate.
      - [audit_delegation_transfer_preserves_validity] : the storage
        shape invariant (non-negative balances and votes) survives
        any transfer that respects the natural debit preconditions.
      - [audit_delegation_set_opt_delegate_preserves_validity] :
        same for optimistic-delegate re-pointing.
      - [audit_delegation_set_std_delegate_preserves_validity] :
        same for standard-delegate re-pointing.
*)

Notation audit_delegation_transfer_preserves_total_votes :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.transfer_preserves_total_votes.

Notation audit_delegation_opt_independent_of_std :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.transfer_opt_independent_of_std.

Notation audit_delegation_std_independent_of_opt :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.transfer_std_independent_of_opt.

Notation audit_delegation_self_transfer_noop :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.self_transfer_noop.

Notation audit_delegation_change_moves_all_balance :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.delegate_change_moves_all_balance.

Notation audit_delegation_mint_no_zero_credit :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.transfer_mint_no_zero_credit.

Notation audit_delegation_burn_no_zero_credit :=
  ReserveGovernor.proofs.StakingVaultDelegation.StakingVaultDelegationProofs.transfer_burn_no_zero_credit.

Notation audit_delegation_transfer_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultDelegation_validity.StakingVaultDelegationValidity.transfer_preserves_validity.

Notation audit_delegation_set_opt_delegate_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultDelegation_validity.StakingVaultDelegationValidity.set_opt_delegate_preserves_validity.

Notation audit_delegation_set_std_delegate_preserves_validity :=
  ReserveGovernor.proofs.StakingVaultDelegation_validity.StakingVaultDelegationValidity.set_std_delegate_preserves_validity.


(** ============================================================
    === Section 7: ProposalLib ===
    ============================================================

    [ProposalLib] is the shared validation entry-point used by both
    [proposeOptimistic] and [proposePessimistic]. It enforces
    well-formedness of the proposal payload (matching lengths, no
    confirmation-prefixed descriptions, suffix-restricted proposer
    if present) and owns the optimistic → pessimistic transition
    primitive.

    Headlines:
      - [audit_proposal_id_injective] : the proposalId hash is
        injective on (targets, values, calldatas, description).
      - [audit_proposal_transition_changes_pid] : prepending
        "Confirmation For: " always changes the proposalId.
      - [audit_proposal_rejects_confirmation_prefix],
        [audit_proposal_rejects_length_mismatch_*],
        [audit_proposal_rejects_zero_length],
        [audit_proposal_rejects_already_proposed],
        [audit_proposal_rejects_restricted_proposer] : the suite of
        well-formedness guards.
      - [audit_proposal_optimistic_role_gate] : optimistic propose
        requires the role.
      - [audit_proposal_optimistic_call_gate] : optimistic propose
        requires every (target, selector) to be allowlisted.
      - [audit_proposal_pessimistic_votes_gate] : pessimistic
        propose requires votes >= proposalThreshold.
      - [audit_proposal_transition_idempotent] /
        [audit_proposal_transition_terminal] : the optimistic →
        pessimistic transition is one-way.
*)

Notation audit_proposal_id_injective :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.proposalIdOf_inj.

Notation audit_proposal_transition_changes_pid :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.transition_changes_pid.

Notation audit_proposal_rejects_confirmation_prefix :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_confirmation_prefix.

Notation audit_proposal_rejects_length_mismatch_tv :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_length_mismatch_tv.

Notation audit_proposal_rejects_length_mismatch_tc :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_length_mismatch_tc.

Notation audit_proposal_rejects_zero_length :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_zero_length.

Notation audit_proposal_rejects_already_proposed :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_already_proposed.

Notation audit_proposal_rejects_restricted_proposer :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.validateProposal_rejects_restricted_proposer.

Notation audit_proposal_optimistic_role_gate :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.proposeOptimistic_rejects_non_role.

Notation audit_proposal_optimistic_call_gate :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.proposeOptimistic_rejects_invalid_call.

Notation audit_proposal_pessimistic_votes_gate :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.proposePessimistic_rejects_insufficient_votes.

Notation audit_proposal_transition_idempotent :=
  ReserveGovernor.proofs.ProposalLib.ProposalLibProofs.transition_then_transition_reverts.

Notation audit_proposal_transition_terminal :=
  ReserveGovernor.proofs.ProposalLib_validity.ProposalLibValidity.transition_produces_terminal_details.


(** ============================================================
    === Section 8: ReserveOptimisticGovernor ===
    ============================================================

    [ReserveOptimisticGovernor] is the hybrid governance contract.
    Each proposal is either optimistic (auto-passes unless vetoed)
    or standard (requires votes ≥ proposalThreshold and a positive
    tally). The escalation state machine has eight named phases;
    successful execution is captured by reaching [PhaseExecuted] or
    [PhaseStdExecuted].

    Headlines (round-2 originals):
      - [audit_governor_optimistic_execution_iff_succeeded] :
        [execute_optimistic] succeeds iff the proposal's observable
        phase at [now] is [PhaseSucceeded].
      - [audit_governor_veto_threshold_correctness] : within the
        active veto window, the proposal observes [PhaseDefeated]
        iff [againstVotes >= vetoThresholdTok].
      - [audit_governor_optimistic_cannot_be_queued] : optimistic
        proposals cannot enter the slow-path execute queue.
      - [audit_governor_execute_standard_requires_queued] : standard
        execution requires the proposal to already be in
        [PhaseStdQueued].
      - [audit_governor_execute_twice_reverts] : a successful
        [execute_optimistic] makes any subsequent
        [execute_optimistic] revert — execution is one-shot.
      - [audit_governor_propose_requires_throttle] :
        [propose_optimistic] reverts when the throttle has no
        charges remaining.
      - [audit_governor_propose_requires_allowlist] : a successful
        [propose_optimistic] proves every (target, selector) in the
        proposal is registered in the allowlist.
      - [audit_governor_transition_parent_phase] : after a
        successful [transition_to_pessimistic], the parent proposal
        is in [PhaseDefeated] and the child starts in
        [PhaseStdPending].
      - [audit_governor_vetoThresholdTok_floor] : the on-chain
        [vetoThresholdTok] is always >= 1.
      - [audit_governor_propose_preserves_validity] : a successful
        [propose_optimistic] produces a [Valid.proposal].

    Round-3 (non-de-escalation):
      - [audit_governor_cannot_de_escalate_after_transition] : after
        [transition_to_pessimistic], no sequence of [add_veto]
        increments can drive the parent's observable phase back to
        [PhaseActive] / [PhaseSucceeded] / [PhaseSubmitted].
      - [audit_governor_cannot_observe_active_or_succeeded] : the
        corollary form, explicitly disallowing the three
        non-defeated phases.
      - [audit_governor_transition_sentinel_writes] : the explicit
        [vetoThresholdTok := 2^256 - 1] sentinel encoding produces a
        parent with the sentinel stamp.
      - [audit_governor_transition_sentinel_unreachable] : under the
        sentinel encoding, the optimistic [PhaseDefeated] arm of
        [observe] is unreachable through votes alone — the phase
        pin is the only path.

    Round-4 (no-double-execution):
      - [audit_governor_terminal_phase_exclusivity] : a stored
        proposal cannot simultaneously observe [PhaseExecuted] and
        [PhaseStdExecuted] — the two terminal phases are exclusive.
      - [audit_governor_no_double_execution] : along any reachable
        execution chain, [execute_optimistic] and [execute_standard]
        cannot both succeed on the same proposal.
*)

Notation audit_governor_optimistic_execution_iff_succeeded :=
  ReserveGovernor.proofs.Governor.GovernorProofs.execute_optimistic_success_iff_succeeded.

Notation audit_governor_veto_threshold_correctness :=
  ReserveGovernor.proofs.Governor.GovernorProofs.observe_defeated_iff_threshold_in_window.

Notation audit_governor_optimistic_cannot_be_queued :=
  ReserveGovernor.proofs.Governor.GovernorProofs.optimistic_cannot_be_queued.

Notation audit_governor_execute_standard_requires_queued :=
  ReserveGovernor.proofs.Governor.GovernorProofs.execute_standard_requires_queued.

Notation audit_governor_queue_requires_succeeded :=
  ReserveGovernor.proofs.Governor.GovernorProofs.queue_operations_requires_succeeded.

Notation audit_governor_execute_twice_reverts :=
  ReserveGovernor.proofs.Governor.GovernorProofs.execute_optimistic_then_execute_optimistic_reverts.

Notation audit_governor_propose_requires_throttle :=
  ReserveGovernor.proofs.Governor.GovernorProofs.propose_optimistic_requires_charge.

Notation audit_governor_propose_requires_allowlist :=
  ReserveGovernor.proofs.Governor.GovernorProofs.propose_optimistic_requires_allowlist.

Notation audit_governor_propose_denies_disallowed_call :=
  ReserveGovernor.proofs.Governor.GovernorProofs.propose_optimistic_denies_disallowed_call.

Notation audit_governor_propose_success_witness :=
  ReserveGovernor.proofs.Governor.GovernorProofs.propose_optimistic_success_witness.

Notation audit_governor_transition_parent_defeated :=
  ReserveGovernor.proofs.Governor.GovernorProofs.transition_parent_phase_defeated.

Notation audit_governor_transition_child_pending :=
  ReserveGovernor.proofs.Governor.GovernorProofs.transition_child_phase_pending.

Notation audit_governor_vetoThresholdTok_floor :=
  ReserveGovernor.proofs.Governor.GovernorProofs.vetoThresholdTok_ge_1.

Notation audit_governor_propose_preserves_validity :=
  ReserveGovernor.proofs.Governor_validity.GovernorValidity.propose_optimistic_preserves_validity.

(* Round-3 no-de-escalation. *)
Notation audit_governor_cannot_de_escalate_after_transition :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.cannot_de_escalate_after_transition.

Notation audit_governor_cannot_observe_active_or_succeeded :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.cannot_observe_active_or_succeeded.

Notation audit_governor_transition_sentinel_writes :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.transition_writes_sentinel_lemma.

Notation audit_governor_transition_sentinel_unreachable :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.sentinel_makes_defeated_unreachable.

(* Round-4 no-double-execution. *)
Notation audit_governor_terminal_phase_exclusivity :=
  ReserveGovernor.proofs.Governor_no_double_execution.GovernorNoDoubleExecution.terminal_phase_exclusivity.

Notation audit_governor_terminal_phase_exclusivity_sym :=
  ReserveGovernor.proofs.Governor_no_double_execution.GovernorNoDoubleExecution.terminal_phase_exclusivity_sym.

Notation audit_governor_no_double_execution :=
  ReserveGovernor.proofs.Governor_no_double_execution.GovernorNoDoubleExecution.no_double_execution.


(** ============================================================
    === Section 9: TimelockControllerOptimistic ===
    ============================================================

    [TimelockControllerOptimistic] is the execution queue. Operations
    are scheduled with a [minDelay], wait through [OpWaiting], become
    [OpReady] once their timestamp matures, and are marked [OpDone]
    (with sentinel timestamp 1) after execution. A bypass path
    (gated by PROPOSER_ROLE) lets optimistic-passed proposals skip
    the delay, but must not affect any independently scheduled
    op on the standard path.

    Headlines (round-2 originals):
      - [audit_timelock_execute_before_maturity_reverts] : the time
        lock is honored — [executeBatch] on a still-Waiting op
        reverts NotReady.
      - [audit_timelock_no_double_execute] : a successful
        [executeBatch] makes any subsequent [executeBatch] on the
        same id revert — execution is one-shot at the
        single-operation level.
      - [audit_timelock_cancel_blocks_execute] : after [cancel], the
        op is reset to Unset and any subsequent [executeBatch]
        reverts.
      - [audit_timelock_bypass_requires_proposer] : the bypass path
        reverts Unauthorized when the caller lacks PROPOSER_ROLE.
      - [audit_timelock_bypass_preserves_slow_path] : after a bypass
        execution of op B, an independently scheduled op A still has
        its original timestamp and is still Waiting at any [now]
        before its maturity.
      - [audit_timelock_bypass_on_scheduled_reverts] : bypass on an
        already-scheduled op reverts OperationConflict.
      - [audit_timelock_*_preserves_validity] : the state-shape
        invariant (every stored timestamp is Unset (0), Done (1), or
        strictly above the Done sentinel) is preserved by
        [scheduleBatch], [executeBatch], [cancel],
        [executeBatchBypass].

    Round-4 single-shot:
      - [audit_timelock_single_shot_no_double_execute] : along any
        reachable trace, no two [executeBatch] calls on the same op
        can both succeed (the no-double-execute claim lifted from
        a single transition to the full transition system).
      - [audit_timelock_execute_count_le_one] : the count of
        successful executes on any single op in any reachable trace
        is at most one.
      - [audit_timelock_no_two_successful_executes_on_same_id] :
        symmetric phrasing — pairs of reachable execute traces
        cannot both end with a different post-state for the same
        op.
      - [audit_timelock_done_absorbing] : once an op reaches the
        Done state, no further [scheduleBatch] / [executeBatch] /
        [cancel] / [executeBatchBypass] can change its timestamp.
      - [audit_timelock_op_done_persists] : [OpDone] is reachable
        only via [executeBatch] or [executeBatchBypass], and persists
        across the full transition graph from that point on.
*)

Notation audit_timelock_execute_before_maturity_reverts :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.execute_before_maturity_reverts.

Notation audit_timelock_no_double_execute :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.execute_then_execute_reverts.

Notation audit_timelock_cancel_blocks_execute :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.cancel_then_execute_reverts.

Notation audit_timelock_bypass_requires_proposer :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.bypass_without_proposer_reverts.

Notation audit_timelock_bypass_preserves_slow_path :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.bypass_preserves_slow_path.

Notation audit_timelock_bypass_on_scheduled_reverts :=
  ReserveGovernor.proofs.Timelock.TimelockProofs.bypass_after_schedule_conflicts.

Notation audit_timelock_schedule_preserves_validity :=
  ReserveGovernor.proofs.Timelock_validity.TimelockValidity.scheduleBatch_preserves_validity.

Notation audit_timelock_execute_preserves_validity :=
  ReserveGovernor.proofs.Timelock_validity.TimelockValidity.executeBatch_preserves_validity.

Notation audit_timelock_cancel_preserves_validity :=
  ReserveGovernor.proofs.Timelock_validity.TimelockValidity.cancel_preserves_validity.

Notation audit_timelock_bypass_preserves_validity :=
  ReserveGovernor.proofs.Timelock_validity.TimelockValidity.executeBatchBypass_preserves_validity.

(* Round-4 single-shot. *)
Notation audit_timelock_single_shot_no_double_execute :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.no_double_execute.

Notation audit_timelock_execute_count_le_one :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.execute_count_reachable_le_one.

Notation audit_timelock_no_two_successful_executes_on_same_id :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.no_two_successful_executes_on_same_id.

Notation audit_timelock_op_done_persists :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.op_done_persists.

Notation audit_timelock_done_absorbing :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.done_is_absorbing.


(** ============================================================
    === Section 10: Guardian (NEW round 4) ===
    ============================================================

    [Guardian] is the role layer that gates [cancel],
    [grantOptimisticGuardian], and [revokeOptimisticProposer] on the
    governor. It distinguishes two tiers:

      - Admins can cancel any proposal regardless of phase.
      - Guardians (without admin) can only cancel optimistic
        proposals that are NOT in [PSDefeated].

    Plus a manager role gates [grantOptimisticGuardian]; an admin
    role gates [revokeOptimisticProposer]; and both grant/revoke
    paths reject the zero address.

    Headlines:
      - [audit_guardian_cancel_requires_authorization] : every
        successful [cancel] proves the caller has admin or guardian.
      - [audit_guardian_admin_cancel_unrestricted] : an admin caller's
        [cancel] succeeds regardless of proposal phase or optimistic-
        ness (only the governor-validity gates apply).
      - [audit_guardian_only_cancel_reverts_on_defeated] : a
        guardian-only caller (not admin) cannot cancel a Defeated
        proposal — the two-tier role design is enforced.
      - [audit_guardian_admin_cancel_succeeds_on_defeated] : the
        admin counterpart — admins CAN cancel Defeated proposals.
      - [audit_guardian_cancel_unauthorized] : an unauthorized caller
        (neither admin nor guardian) reverts before any other check.
      - [audit_guardian_grant_requires_manager] : grant requires the
        manager role.
      - [audit_guardian_grant_rejects_zero] : zero-address grants
        revert.
      - [audit_guardian_revoke_requires_admin] : revoke requires the
        admin role.
      - [audit_guardian_revoke_validates_addresses] : revoke checks
        governor and timelock are non-zero contracts.
      - [audit_guardian_grant_inserts_account] : a successful grant
        actually inserts the account into the guardian set and
        leaves admins / managers untouched.
      - [audit_guardian_grant_preserves_validity] : grant preserves
        the role-list invariant (NoDup, no zeros).
      - [audit_guardian_revoke_role_preserves_validity] : OZ's
        inherited [revokeRole] preserves the role-list invariant
        across every role kind (admin / manager / guardian).
      - [audit_guardian_renounce_role_preserves_validity] : OZ's
        inherited [renounceRole] preserves the invariant.
      - [audit_guardian_cancel_preserves_validity] : [cancel] is a
        pure dispatch and trivially preserves storage validity.
      - [audit_guardian_revoke_proposer_preserves_validity] :
        [revokeOptimisticProposer] dispatches to the timelock and
        does not touch Guardian's own role sets.
*)

Notation audit_guardian_cancel_requires_authorization :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.cancel_requires_authorization.

Notation audit_guardian_admin_cancel_unrestricted :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.cancel_admin_unrestricted.

Notation audit_guardian_only_cancel_reverts_on_defeated :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.guardian_only_cancel_reverts_on_defeated.

Notation audit_guardian_admin_cancel_succeeds_on_defeated :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.admin_cancel_succeeds_on_defeated.

Notation audit_guardian_cancel_unauthorized :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.cancel_unauthorized.

Notation audit_guardian_grant_requires_manager :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.grant_requires_manager.

Notation audit_guardian_grant_rejects_zero :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.grant_rejects_zero.

Notation audit_guardian_revoke_requires_admin :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.revoke_proposer_requires_admin.

Notation audit_guardian_revoke_validates_addresses :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.revoke_proposer_validates_addresses.

Notation audit_guardian_grant_inserts_account :=
  ReserveGovernor.proofs.Guardian.GuardianProofs.grant_inserts_account.

Notation audit_guardian_grant_preserves_validity :=
  ReserveGovernor.proofs.Guardian_validity.GuardianValidity.grant_preserves_validity.

Notation audit_guardian_revoke_role_preserves_validity :=
  ReserveGovernor.proofs.Guardian_validity.GuardianValidity.revoke_preserves_validity.

Notation audit_guardian_renounce_role_preserves_validity :=
  ReserveGovernor.proofs.Guardian_validity.GuardianValidity.renounce_preserves_validity.

Notation audit_guardian_cancel_preserves_validity :=
  ReserveGovernor.proofs.Guardian_validity.GuardianValidity.cancel_preserves_validity.

Notation audit_guardian_revoke_proposer_preserves_validity :=
  ReserveGovernor.proofs.Guardian_validity.GuardianValidity.revoke_optimistic_proposer_preserves_validity.


(** ============================================================
    === Section 11: RewardTokenRegistry (NEW round 4) ===
    ============================================================

    [RewardTokenRegistry] is the owner-gated list of accepted reward
    tokens. Tokens can be registered (added) and unregistered
    (removed), with isRegistered as the public membership query.

    Headlines:
      - [audit_reward_token_isRegistered_iff_member] :
        [isRegistered] is exactly set membership.
      - [audit_reward_token_register_success_adds] : a successful
        [registerRewardToken] makes the token observable as
        registered.
      - [audit_reward_token_unregister_success_removes] : a
        successful [unregisterRewardToken] removes the token from
        the observable list.
      - [audit_reward_token_register_duplicate_reverts] : registering
        an already-registered token reverts.
      - [audit_reward_token_unregister_nonmember_reverts] :
        unregistering a non-member reverts.
      - [audit_reward_token_register_zero_reverts] : the zero
        address is rejected at registration.
      - [audit_reward_token_register_not_owner_reverts] : non-owner
        register reverts.
      - [audit_reward_token_unregister_not_authorized_reverts] :
        unauthorized unregister reverts.
      - [audit_reward_token_register_preserves_validity] : register
        preserves the NoDup invariant on the token list.
      - [audit_reward_token_unregister_preserves_validity] : same
        for unregister.
*)

Notation audit_reward_token_isRegistered_iff_member :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.isRegistered_iff_member.

Notation audit_reward_token_register_success_adds :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.registerRewardToken_success_adds.

Notation audit_reward_token_unregister_success_removes :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.unregisterRewardToken_success_removes.

Notation audit_reward_token_register_duplicate_reverts :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.registerRewardToken_duplicate_reverts.

Notation audit_reward_token_unregister_nonmember_reverts :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.unregisterRewardToken_nonmember_reverts.

Notation audit_reward_token_register_zero_reverts :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.registerRewardToken_zero_reverts.

Notation audit_reward_token_register_not_owner_reverts :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.registerRewardToken_not_owner_reverts.

Notation audit_reward_token_unregister_not_authorized_reverts :=
  ReserveGovernor.proofs.RewardTokenRegistry.RewardTokenRegistryProofs.unregisterRewardToken_not_authorized_reverts.

Notation audit_reward_token_register_preserves_validity :=
  ReserveGovernor.proofs.RewardTokenRegistry_validity.RewardTokenRegistryValidity.registerRewardToken_preserves_validity.

Notation audit_reward_token_unregister_preserves_validity :=
  ReserveGovernor.proofs.RewardTokenRegistry_validity.RewardTokenRegistryValidity.unregisterRewardToken_preserves_validity.


(** ============================================================
    === Section 12: VersionRegistry (NEW round 4) ===
    ============================================================

    [VersionRegistry] is the append-only history of deployed
    implementation triples (stakingVault / governor / timelock). It
    is owner-gated for registration, owner-or-emergency-gated for
    deprecation, and acts as the upgrade-authorization oracle for
    [StakingVault].

    Headlines:
      - [audit_version_register_extends_history] : a successful
        [registerVersion] appends exactly one entry to the history,
        with all fields fixed by the caller's input.
      - [audit_version_register_reregister_reverts] : a second
        register of the same version (by hash) reverts.
      - [audit_version_getLatest_returns_appended] : after a
        successful register, [getLatestVersion] returns the
        just-appended entry.
      - [audit_version_register_impl_triple] : after register, the
        impl-triple lookup for that hash returns exactly the
        registered triple.
      - [audit_version_deprecate_sticky] : once a version is
        deprecated, any future deprecate on the same version hash
        reverts AlreadyDeprecated — deprecation is one-way.
      - [audit_version_register_requires_owner] : non-owner register
        reverts.
      - [audit_version_deprecate_requires_role] : non-owner /
        non-emergency deprecate reverts.
      - [audit_version_getLatest_empty_reverts] : empty registry's
        getLatestVersion reverts NotConfigured.
      - [audit_version_register_preserves_validity] : register
        preserves the "all history hashes match their entry's
        version_hash" + NoDup invariant.
      - [audit_version_deprecate_preserves_validity] : deprecate
        preserves the same invariant.
*)

Notation audit_version_register_extends_history :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.registerVersion_extends_history.

Notation audit_version_register_reregister_reverts :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.registerVersion_reregister_reverts.

Notation audit_version_getLatest_returns_appended :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.registerVersion_getLatestVersion.

Notation audit_version_register_impl_triple :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.registerVersion_impl_triple.

Notation audit_version_deprecate_sticky :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.deprecateVersion_sticky.

Notation audit_version_register_requires_owner :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.registerVersion_requires_owner.

Notation audit_version_deprecate_requires_role :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.deprecateVersion_requires_role.

Notation audit_version_getLatest_empty_reverts :=
  ReserveGovernor.proofs.VersionRegistry.VersionRegistryProofs.getLatestVersion_empty_reverts.

Notation audit_version_register_preserves_validity :=
  ReserveGovernor.proofs.VersionRegistry_validity.VersionRegistryValidity.registerVersion_preserves_state.

Notation audit_version_deprecate_preserves_validity :=
  ReserveGovernor.proofs.VersionRegistry_validity.VersionRegistryValidity.deprecateVersion_preserves_state.


(** ============================================================
    ============================================================
    ===                                                      ===
    ===                Part II — Integration theorems        ===
    ===                                                      ===
    ============================================================
    ============================================================

    Cross-domain composition theorems. Each name below is a single
    proven property whose statement references at least two domain
    surfaces.
*)


(** ----- Integration: StakingVault + UnstakingManager -----

    [audit_integration_withdraw_with_lockup_conserves_value] : the
    full withdraw cycle conserves value end-to-end —
    [vault.totalDeposited] dropping by exactly the cycled amount is
    matched by [manager.total_active] going up by the same.

    [audit_integration_cancel_drops_total_active] : cancelling an
    unstake lock that came from a previous [withdraw_with_lockup]
    drops the manager's [total_active] by the lock's full amount.
*)

Notation audit_integration_withdraw_with_lockup_conserves_value :=
  ReserveGovernor.proofs.Integration_withdraw_lockup.IntegrationWithdrawLockup.withdraw_with_lockup_conserves_value.

Notation audit_integration_cancel_drops_total_active :=
  ReserveGovernor.proofs.Integration_withdraw_lockup.IntegrationWithdrawLockup.cancel_drops_total_active.

(** ----- Integration: immediate-transfer branch (unstakingDelay = 0) -----

    [audit_integration_withdraw_immediate_conserves_value] : the
    vault's [totalDeposited] decrement equals the receiver's ERC20
    balance increase, with no lockup in between.

    [audit_integration_withdraw_immediate_debits_vault] : the vault's
    own ERC20 balance loses [assets], closing the transfer pair.
*)

Notation audit_integration_withdraw_immediate_conserves_value :=
  ReserveGovernor.proofs.Integration_withdraw_immediate.IntegrationWithdrawImmediate.withdraw_immediate_conserves_value.

Notation audit_integration_withdraw_immediate_debits_vault :=
  ReserveGovernor.proofs.Integration_withdraw_immediate.IntegrationWithdrawImmediate.withdraw_immediate_debits_vault.


(** ----- Integration: Governor + ProposerThrottle + SelectorRegistry -----

    [audit_integration_propose_optimistic_implies_throttle_and_allowlist]
    : a successful [propose_optimistic] proves both that the throttle
    was consumed AND that every (target, selector) in the proposal is
    a member of the selector registry's allowlist — the two gates
    are not just promised on paper, they hold at the simulation
    surface.
*)

Notation audit_integration_propose_optimistic_implies_throttle_and_allowlist :=
  ReserveGovernor.proofs.Integration_optimistic_propose.IntegrationOptimisticPropose.propose_optimistic_implies_throttle_consumed_and_selectors_whitelisted.


(** ----- Integration: Governor + Timelock -----

    [audit_integration_escalate_then_queue_then_execute_chain] : the
    end-to-end pessimistic execution chain — transition, queue,
    timelock-schedule, wait, timelock-execute, governor-execute —
    composes correctly with no observable gap.

    [audit_integration_execute_standard_blocked_before_maturity] :
    the chain is blocked at the timelock-maturity gate. Calling
    governor.execute_standard before the timelock op matures reverts.
*)

Notation audit_integration_escalate_then_queue_then_execute_chain :=
  ReserveGovernor.proofs.Integration_governor_timelock.IntegrationGovernorTimelock.escalate_then_queue_then_execute_chain.

Notation audit_integration_execute_standard_blocked_before_maturity :=
  ReserveGovernor.proofs.Integration_governor_timelock.IntegrationGovernorTimelock.execute_standard_blocked_before_maturity.


(** ----- Integration: No throttle bypass (Governor + ProposerThrottle) -----

    [audit_integration_no_throttle_bypass] : on any reachable
    sequence of [propose_optimistic] calls by a single proposer
    within a 12h window, the count of successes is bounded by
    [2 * capacity] (initial bucket + one window's refill).

    [audit_integration_no_throttle_bypass_drain] : the unconditional
    D18-drain variant — total drain is bounded by [2 * FIX_ONE]
    regardless of capacity divisibility.

    [audit_integration_no_throttle_bypass_tight_start] : the
    tight-start corollary — if the proposer's throttle started at
    [currentCharge = 0], the count in one window is bounded by
    [capacity] (not [2 * capacity]).
*)

Notation audit_integration_no_throttle_bypass :=
  ReserveGovernor.proofs.Integration_no_throttle_bypass.IntegrationNoThrottleBypass.no_throttle_bypass.

Notation audit_integration_no_throttle_bypass_drain :=
  ReserveGovernor.proofs.Integration_no_throttle_bypass.IntegrationNoThrottleBypass.no_throttle_bypass_drain.

Notation audit_integration_no_throttle_bypass_tight_start :=
  ReserveGovernor.proofs.Integration_no_throttle_bypass.IntegrationNoThrottleBypass.no_throttle_bypass_tight_start.


(** ----- Integration: Upgrade authorization (VersionRegistry + StakingVault) -----

    [audit_integration_register_then_authorize_self] : after
    [registerVersion v], the upgrade-authorization oracle accepts
    upgrades to the just-registered implementation.

    [audit_integration_register_two_then_authorize_rejects_old] :
    after registering [v1] then [v2] (with [v1 <> v2]), upgrades to
    [v1]'s implementation are rejected — only the latest registered
    version authorizes.

    [audit_integration_register_deprecate_then_authorize_rejects] :
    once a version is deprecated, the upgrade oracle rejects
    upgrades to its implementation, regardless of supplied impl.
*)

Notation audit_integration_register_then_authorize_self :=
  ReserveGovernor.proofs.Integration_upgrade_authorization.IntegrationUpgradeAuthorization.register_then_authorize_self.

Notation audit_integration_register_two_then_authorize_rejects_old :=
  ReserveGovernor.proofs.Integration_upgrade_authorization.IntegrationUpgradeAuthorization.register_two_then_authorize_rejects_old.

Notation audit_integration_register_deprecate_then_authorize_rejects :=
  ReserveGovernor.proofs.Integration_upgrade_authorization.IntegrationUpgradeAuthorization.register_deprecate_then_authorize_rejects.


(** ============================================================
    ============================================================
    ===                                                      ===
    ===          Part III — Adversarial / negative theorems  ===
    ===                                                      ===
    ============================================================
    ============================================================

    Explicit "X cannot happen" claims, with the names introduced
    above re-exposed here as a single index. Each notation in this
    part is an alias for a notation in Part I or Part II — the
    underlying theorem is referenced exactly once in this file. The
    aliasing is intentional: an auditor scanning the negative-safety
    surface should be able to read this section top to bottom
    without leaving it.

    Coverage map:
      - UnstakingManager: lock cannot be both claimed and cancelled.
      - Governor: terminal phases are exclusive (no double execute,
        no de-escalation after transition).
      - Timelock: single op cannot be executed twice along any
        reachable trace.
      - ProposerThrottle: a proposer cannot exceed
        [2 * capacity] successful proposals per 12h window.
*)

(** ----- UnstakingManager negative theorems ----- *)

Notation audit_neg_unstaking_no_double_spend :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_double_spend.

Notation audit_neg_unstaking_reachable_no_double_resolved :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.reachable_no_double_resolved.

Notation audit_neg_unstaking_no_double_spend_after_claim :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_double_spend_after_claim.

Notation audit_neg_unstaking_no_double_spend_after_cancel :=
  ReserveGovernor.proofs.UnstakingManager_no_double_spend.UnstakingManagerNoDoubleSpend.no_double_spend_after_cancel.


(** ----- Governor negative theorems ----- *)

Notation audit_neg_governor_terminal_phase_exclusivity :=
  ReserveGovernor.proofs.Governor_no_double_execution.GovernorNoDoubleExecution.terminal_phase_exclusivity.

Notation audit_neg_governor_no_double_execution :=
  ReserveGovernor.proofs.Governor_no_double_execution.GovernorNoDoubleExecution.no_double_execution.

Notation audit_neg_governor_cannot_de_escalate :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.cannot_de_escalate_after_transition.

Notation audit_neg_governor_cannot_observe_active_or_succeeded :=
  ReserveGovernor.proofs.Governor_no_de_escalation.GovernorNoDeEscalation.cannot_observe_active_or_succeeded.


(** ----- Timelock negative theorems ----- *)

Notation audit_neg_timelock_no_double_execute :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.no_double_execute.

Notation audit_neg_timelock_no_two_successful_executes_on_same_id :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.no_two_successful_executes_on_same_id.

Notation audit_neg_timelock_done_absorbing :=
  ReserveGovernor.proofs.Timelock_single_shot.TimelockSingleShot.done_is_absorbing.


(** ----- ProposerThrottle / Governor composition negative theorem ----- *)

Notation audit_neg_no_throttle_bypass :=
  ReserveGovernor.proofs.Integration_no_throttle_bypass.IntegrationNoThrottleBypass.no_throttle_bypass.


(** ============================================================
    === Headlines, at a glance ===
    ============================================================

    Table of contents — every safety theorem exported above, in one
    block, with a one-line natural-language summary. This is the
    auditor's index: pick a property, cross-reference back to its
    section above for the precise statement.

    Round-2 originals are unmarked; round-3 backfills are marked
    [R3]; round-4 additions are marked [R4].

    ProposerThrottle
      audit_proposalsAvailable_le_capacity
        — per-12h proposal budget is bounded by [capacity], always.
      audit_throttle_consume_success_iff_available
        — [consume] succeeds iff at least one slot of charge remains.
      audit_throttle_consume_revert_iff_no_proposals
        — [consume] reverts iff the available count is below 1.
      audit_throttle_consume_storage_delta
        — successful consume bumps lastUpdated and decrements charge
          by exactly [FIX_ONE / capacity].
      audit_throttle_preserves_validity
        — [consume] preserves [0 <= currentCharge <= FIX_ONE].

    UnstakingManager
      audit_unstaking_claim_then_claim_reverts
        — each lock claimable at most once (one-way claim).
      audit_unstaking_cancel_then_claim_reverts
        — claim after cancel reverts.
      audit_unstaking_claim_before_maturity_reverts
        — time-lock honored: claim before unlockTime reverts.
      audit_unstaking_claim_on_default_reverts
        — claiming a default-zero lock slot reverts.
      audit_unstaking_createLock_preserves_validity
        — createLock preserves length / nextLockId / per-slot shape.
      [R3] audit_unstaking_createLock_conservation
        — successful createLock raises total_active by exactly
          amount (when unlockTime > 0).
      [R3] audit_unstaking_createLock_zero_unlock_no_delta
        — createLock with unlockTime = 0 leaves total_active unchanged.
      [R3] audit_unstaking_cancelLock_conservation
        — successful cancelLock drops total_active by exactly the
          pre-cancel active_amount.
      [R3] audit_unstaking_claimLock_conservation
        — successful claimLock drops total_active by exactly the
          claimed amount.
      [R3] audit_unstaking_total_active_bounded
        — total_active fits in U256 if every per-lock amount does
          and the sum of amounts fits.
      [R4] audit_unstaking_no_double_spend
        — on any reachable state, no lockId is both claimed and
          cancelled.
      [R4] audit_unstaking_no_double_spend_sequence
        — any reachable sequence of state-transitions preserves
          the no-double-spend property.
      [R4] audit_unstaking_no_cancel_then_claim_sequence
        — claim and cancel can never both fire on the same lock.

    OptimisticSelectorRegistry
      audit_selector_isAllowed_iff_member
        — public isAllowed is exactly set membership.
      audit_selector_addSelector_idempotent
        — adding a registered pair is a no-op on the second call.
      audit_selector_remove_nonmember_noop
        — removing an unregistered pair is a no-op.
      audit_selector_addSelector_forbidden_reverts
        — adding a forbidden target reverts.
      audit_selector_addSelector_zero_reverts
        — adding the zero-selector reverts.
      [R3] audit_selector_addSelector_preserves_validity
        — addSelector preserves keys-NoDup, sels-NoDup, pruned-keys.
      [R3] audit_selector_removeSelector_preserves_validity
        — removeSelector preserves the same shape invariants.

    StakingVault — Exchange
      audit_vault_round_trip_floor_bound
        — convertToAssets(convertToShares(a)) <= a (no value created).
      audit_vault_share_rate_monotone_under_accrue
        — share price never falls when rewards accrue.
      audit_vault_deposit_storage_delta
        — deposit storage delta is exact:
          totalDeposited += assets, totalSupply += shares.
      audit_vault_accrue_preserves_share_book
        — accrue only touches the reward bucket.
      [R3] audit_vault_deposit_preserves_validity
        — deposit preserves the solvency invariant.
      [R3] audit_vault_withdraw_preserves_validity
        — withdraw preserves the solvency invariant.
      [R3] audit_vault_accrue_preserves_validity
        — accrue preserves the solvency invariant.
      [R3] audit_vault_never_underwater
        — share/asset bookkeeping never enters an underwater state.

    StakingVault — Rewards
      audit_rewards_index_monotone
        — global rewardIndex is non-decreasing.
      audit_rewards_user_accrued_monotone
        — user accrued balance only grows (no silent loss).
      audit_rewards_claim_zeroes_accrued
        — claim zeroes user.accruedRewards atomically.
      audit_rewards_claim_returns_accrued
        — claim disburses exactly the prior accrued amount.
      audit_rewards_totalClaimed_monotone
        — global totalClaimed is non-decreasing.
      audit_rewards_no_op_when_index_stable
        — accrueUser is a no-op when the index hasn't moved.
      [R3] audit_rewards_conservation
        — balanceAccounted = Σ accrued + totalClaimed at every
          reachable state.

    StakingVault — Delegation
      audit_delegation_transfer_preserves_total_votes
        — transfer conserves the from+to delegate vote sum on both
          ledgers.
      audit_delegation_opt_independent_of_std
        — optimistic ledger evolves only from optimistic state.
      audit_delegation_std_independent_of_opt
        — symmetric independence for the standard ledger.
      audit_delegation_self_transfer_noop
        — same delegates => transfer is a no-op.
      audit_delegation_change_moves_all_balance
        — delegate change moves exactly account's full balance.
      audit_delegation_mint_no_zero_credit
        — minting never credits the zero delegate.
      audit_delegation_burn_no_zero_credit
        — burning never credits the zero delegate.

    ProposalLib
      audit_proposal_id_injective
        — proposalId hash is injective on the proposal key.
      audit_proposal_transition_changes_pid
        — confirmation-prefixed descriptions get a distinct
          proposalId from their optimistic parent.
      audit_proposal_rejects_confirmation_prefix
        — user-submitted descriptions can't start with the
          reserved confirmation prefix.
      audit_proposal_rejects_length_mismatch_tv
        — targets vs values length must match.
      audit_proposal_rejects_length_mismatch_tc
        — targets vs calldatas length must match.
      audit_proposal_rejects_zero_length
        — zero-call proposals are rejected.
      audit_proposal_rejects_already_proposed
        — re-submitting a proposal already in the map reverts.
      audit_proposal_rejects_restricted_proposer
        — [#proposer=ADDR] suffix is enforced.
      audit_proposal_optimistic_role_gate
        — proposeOptimistic requires the optimistic-proposer role.
      audit_proposal_optimistic_call_gate
        — proposeOptimistic requires every (target, selector) to be
          in the allowlist, calldata non-empty, target a contract.
      audit_proposal_pessimistic_votes_gate
        — proposePessimistic requires votes >= proposalThreshold.
      audit_proposal_transition_idempotent
        — optimistic -> pessimistic transition is one-way.
      audit_proposal_transition_terminal
        — once transitioned, any further transition reverts.

    ReserveOptimisticGovernor
      audit_governor_optimistic_execution_iff_succeeded
        — execute_optimistic succeeds iff observable phase is
          PhaseSucceeded.
      audit_governor_veto_threshold_correctness
        — within veto window, defeated iff
          againstVotes >= vetoThresholdTok.
      audit_governor_optimistic_cannot_be_queued
        — optimistic proposals can't enter the slow-path queue.
      audit_governor_execute_standard_requires_queued
        — standard execution requires phase = PhaseStdQueued.
      audit_governor_queue_requires_succeeded
        — queue requires standard proposal in PhaseStdSucceeded.
      audit_governor_execute_twice_reverts
        — execute_optimistic is one-shot.
      audit_governor_propose_requires_throttle
        — propose_optimistic requires a throttle charge.
      audit_governor_propose_requires_allowlist
        — proposal success witnesses allowlist coverage.
      audit_governor_propose_denies_disallowed_call
        — any disallowed (target, selector) reverts the proposal.
      audit_governor_propose_success_witness
        — success implies all gates honored and proposal well-shaped.
      audit_governor_transition_parent_defeated
        — transition_to_pessimistic marks parent PhaseDefeated.
      audit_governor_transition_child_pending
        — transition_to_pessimistic creates a child in PhaseStdPending.
      audit_governor_vetoThresholdTok_floor
        — on-chain vetoThresholdTok >= 1, always.
      audit_governor_propose_preserves_validity
        — propose_optimistic produces a Valid.proposal.
      [R3] audit_governor_cannot_de_escalate_after_transition
        — no veto-vote sequence can re-open a transitioned parent.
      [R3] audit_governor_cannot_observe_active_or_succeeded
        — transitioned parents observe PhaseDefeated forever,
          never PhaseActive / PhaseSucceeded / PhaseSubmitted.
      [R3] audit_governor_transition_sentinel_writes
        — explicit sentinel encoding stamps parent.vetoThresholdTok
          with type(uint256).max.
      [R3] audit_governor_transition_sentinel_unreachable
        — under sentinel encoding, the votes-only Defeated path is
          unreachable.
      [R4] audit_governor_terminal_phase_exclusivity
        — PhaseExecuted and PhaseStdExecuted are mutually exclusive.
      [R4] audit_governor_no_double_execution
        — execute_optimistic and execute_standard cannot both
          succeed on the same proposal along a reachable trace.

    TimelockControllerOptimistic
      audit_timelock_execute_before_maturity_reverts
        — executeBatch on a Waiting op reverts NotReady.
      audit_timelock_no_double_execute
        — executeBatch is one-shot per op (single-transition).
      audit_timelock_cancel_blocks_execute
        — cancel resets to Unset; subsequent execute reverts.
      audit_timelock_bypass_requires_proposer
        — bypass without PROPOSER_ROLE reverts Unauthorized.
      audit_timelock_bypass_preserves_slow_path
        — bypass doesn't reorder, skip, or accelerate the queued
          slow-path ops.
      audit_timelock_bypass_on_scheduled_reverts
        — bypass on an already-scheduled op reverts
          OperationConflict.
      audit_timelock_schedule_preserves_validity
        — scheduleBatch preserves the ts state-shape invariant.
      audit_timelock_execute_preserves_validity
        — executeBatch preserves the ts state-shape invariant.
      audit_timelock_cancel_preserves_validity
        — cancel preserves the ts state-shape invariant.
      audit_timelock_bypass_preserves_validity
        — executeBatchBypass preserves the ts state-shape invariant.
      [R4] audit_timelock_single_shot_no_double_execute
        — along any reachable trace, no two executeBatch calls on
          the same op can both succeed.
      [R4] audit_timelock_execute_count_le_one
        — count of successful executes on any single op in any
          reachable trace is <= 1.
      [R4] audit_timelock_no_two_successful_executes_on_same_id
        — pairwise: no two reachable executes both succeed on the
          same op id.
      [R4] audit_timelock_op_done_persists
        — OpDone state, once reached, persists across all further
          transitions.
      [R4] audit_timelock_done_absorbing
        — Done is an absorbing state for schedule/execute/cancel/
          bypass.

    [R4] Guardian
      audit_guardian_cancel_requires_authorization
        — successful cancel proves admin or guardian role.
      audit_guardian_admin_cancel_unrestricted
        — admin can cancel any proposal, any phase.
      audit_guardian_only_cancel_reverts_on_defeated
        — guardian-only (non-admin) cannot cancel Defeated proposals.
      audit_guardian_admin_cancel_succeeds_on_defeated
        — admin CAN cancel Defeated proposals.
      audit_guardian_cancel_unauthorized
        — unauthorized callers revert before governor checks.
      audit_guardian_grant_requires_manager
        — grant requires manager role.
      audit_guardian_grant_rejects_zero
        — zero-address grants revert.
      audit_guardian_revoke_requires_admin
        — revoke requires admin role.
      audit_guardian_revoke_validates_addresses
        — revoke checks governor and timelock are non-zero contracts.
      audit_guardian_grant_inserts_account
        — successful grant inserts account, leaves other role lists
          untouched.
      audit_guardian_grant_preserves_validity
        — grant preserves role-list NoDup / no-zero invariant.

    [R4] RewardTokenRegistry
      audit_reward_token_isRegistered_iff_member
        — isRegistered is exactly set membership.
      audit_reward_token_register_success_adds
        — successful register makes the token observable.
      audit_reward_token_unregister_success_removes
        — successful unregister removes the token.
      audit_reward_token_register_duplicate_reverts
        — registering an already-registered token reverts.
      audit_reward_token_unregister_nonmember_reverts
        — unregistering a non-member reverts.
      audit_reward_token_register_zero_reverts
        — zero address rejected at register.
      audit_reward_token_register_not_owner_reverts
        — non-owner register reverts.
      audit_reward_token_unregister_not_authorized_reverts
        — unauthorized unregister reverts.
      audit_reward_token_register_preserves_validity
        — register preserves the NoDup invariant.
      audit_reward_token_unregister_preserves_validity
        — unregister preserves the NoDup invariant.

    [R4] VersionRegistry
      audit_version_register_extends_history
        — register appends exactly one entry with caller's input.
      audit_version_register_reregister_reverts
        — re-registering an existing version hash reverts.
      audit_version_getLatest_returns_appended
        — getLatestVersion after register returns the new entry.
      audit_version_register_impl_triple
        — register binds the version hash to the supplied impl triple.
      audit_version_deprecate_sticky
        — deprecation is one-way — a second deprecate reverts.
      audit_version_register_requires_owner
        — non-owner register reverts.
      audit_version_deprecate_requires_role
        — non-owner / non-emergency deprecate reverts.
      audit_version_getLatest_empty_reverts
        — empty registry's getLatestVersion reverts NotConfigured.
      audit_version_register_preserves_validity
        — register preserves the entry-hash + NoDup invariant.
      audit_version_deprecate_preserves_validity
        — deprecate preserves the same invariant.

    Integration theorems
      audit_integration_withdraw_with_lockup_conserves_value
        — vault.totalDeposited drop = manager.total_active gain.
      audit_integration_cancel_drops_total_active
        — cancel of a withdraw-lockup lock drops total_active by
          the full lock amount.
      audit_integration_propose_optimistic_implies_throttle_and_allowlist
        — successful propose_optimistic implies both throttle
          consume AND allowlist coverage.
      audit_integration_escalate_then_queue_then_execute_chain
        — full pessimistic execution chain composes correctly.
      audit_integration_execute_standard_blocked_before_maturity
        — chain is blocked at timelock-maturity gate.
      [R4] audit_integration_no_throttle_bypass
        — propose_optimistic count <= 2 * capacity per 12h window
          (no bypass path exists from governor to throttle).
      [R4] audit_integration_no_throttle_bypass_drain
        — total D18 drain bounded by 2 * FIX_ONE, regardless of
          capacity divisibility.
      [R4] audit_integration_no_throttle_bypass_tight_start
        — if proposer starts at currentCharge = 0, count in the
          first window is bounded by capacity (not 2 * capacity).
      [R4] audit_integration_register_then_authorize_self
        — registerVersion v authorizes upgrades to v's impl.
      [R4] audit_integration_register_two_then_authorize_rejects_old
        — registering v2 rejects upgrades to v1's impl.
      [R4] audit_integration_register_deprecate_then_authorize_rejects
        — deprecation tombstones the upgrade-authorization path.

    Adversarial / negative theorems (Part III index)
      audit_neg_unstaking_no_double_spend
        — UnstakingManager: no lockId both claimed and cancelled.
      audit_neg_unstaking_no_double_spend_after_claim,
      audit_neg_unstaking_no_double_spend_after_cancel
        — pointwise variants of the above.
      audit_neg_governor_terminal_phase_exclusivity
        — Governor: PhaseExecuted and PhaseStdExecuted are exclusive.
      audit_neg_governor_no_double_execution
        — Governor: execute_optimistic and execute_standard cannot
          both succeed on the same proposal.
      audit_neg_governor_cannot_de_escalate
        — Governor: no veto-vote sequence can re-open a transitioned
          parent.
      audit_neg_timelock_no_double_execute
        — Timelock: no two executes succeed on the same op along a
          reachable trace.
      audit_neg_timelock_no_two_successful_executes_on_same_id
        — Timelock: pairwise reachable-state form.
      audit_neg_timelock_done_absorbing
        — Timelock: Done is absorbing under all transitions.
      audit_neg_no_throttle_bypass
        — Composition: propose_optimistic count <= 2 * capacity
          per 12h window.
*)
