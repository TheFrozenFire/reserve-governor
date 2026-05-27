(** ============================================================
    Reserve Governor — formal verification Audit index.

    Audit-facing re-export surface. The goal is to give an auditor a
    single file to read top-to-bottom that surfaces every
    decision-relevant theorem with the calibration / context needed to
    interpret it.

    The audit is organized by component, in the order the protocol
    layers stack:

      1. ProposerThrottle             — per-account proposal frequency cap.
      2. UnstakingManager             — time-locked withdrawal queue.
      3. OptimisticSelectorRegistry   — (target, selector) whitelist.
      4. StakingVault — Exchange       — ERC4626 exchange-rate floor and
                                         deposit/accrue bookkeeping.
      5. StakingVault — Rewards        — multi-token index-based reward
                                         accrual.
      6. StakingVault — Delegation     — dual-track (standard /
                                         optimistic) delegation
                                         conservation and independence.
      7. ProposalLib                   — proposal validation and the
                                         optimistic → pessimistic
                                         transition primitive.
      8. ReserveOptimisticGovernor    — hybrid optimistic/standard
                                         governance escalation state
                                         machine.
      9. TimelockControllerOptimistic — execution queue with
                                         bypass-for-optimistic path.

    Each section imports its component's headline-theorem module and
    re-exports the load-bearing safety lemmas via [Notation] under
    [audit_<feature>] names. The closing section gives a one-screen
    table-of-contents of every [audit_*] name and the property it
    captures, intended as the auditor's entry point.

    See [../README.md] for the dual-track Rocq + CAS verification
    rationale and [../notes/simulation_fidelity_audit.md] for the
    catalog of known divergences between this simulation and the
    production contracts.
*)

(* All proof modules are pulled in by [Require] only, so symbols stay
   namespaced and there is no scope collision between modules that
   each export their own [Valid] submodule. The [Notation]s below
   reference everything by fully-qualified name. *)

Require ReserveGovernor.proofs.ProposerThrottle.
Require ReserveGovernor.proofs.ProposerThrottle_validity.
Require ReserveGovernor.proofs.UnstakingManager.
Require ReserveGovernor.proofs.UnstakingManager_validity.
Require ReserveGovernor.proofs.SelectorRegistry.
Require ReserveGovernor.proofs.StakingVaultExchange.
Require ReserveGovernor.proofs.StakingVaultRewards.
Require ReserveGovernor.proofs.StakingVaultDelegation.
Require ReserveGovernor.proofs.ProposalLib.
Require ReserveGovernor.proofs.ProposalLib_validity.
Require ReserveGovernor.proofs.Governor.
Require ReserveGovernor.proofs.Governor_validity.
Require ReserveGovernor.proofs.Timelock.
Require ReserveGovernor.proofs.Timelock_validity.


(** ============================================================
    === Section: ProposerThrottle ===
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
    === Section: UnstakingManager ===
    ============================================================

    [UnstakingManager] holds the time-locked queue between unstake
    request and asset release. Each user-owned lock has an
    [unlockTime] (the earliest moment it can be claimed) and a
    [claimedAt] timestamp set on successful release.

    Headlines:
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
        lock preserves the structural state invariant (length matches
        [nextLockId], every stored lock is in a well-formed shape).
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


(** ============================================================
    === Section: OptimisticSelectorRegistry ===
    ============================================================

    [OptimisticSelectorRegistry] is the (target, function-selector)
    whitelist that gates optimistic proposals. A call survives the
    optimistic call-validation gate only if the (target, selector)
    pair is registered.

    Headlines:
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


(** ============================================================
    === Section: StakingVault — Exchange surface ===
    ============================================================

    [StakingVault] is an ERC4626 vault over the stake asset. The
    exchange surface mediates between assets and shares; native
    rewards are reflected via [accrue], which raises [totalAssets]
    while leaving [totalSupply] alone (so the share rate is
    non-decreasing).

    Headlines:
      - [audit_vault_round_trip_floor_bound] : converting assets to
        shares and back never returns more than the original input —
        the round-trip is monotonically lossy (in the user's favor
        from the vault's solvency perspective).
      - [audit_vault_share_rate_monotone_under_accrue] : the share
        price never falls when rewards accrue, stated as a
        cross-multiplied inequality to avoid fraction reasoning.
      - [audit_vault_deposit_storage_delta] : the assets/shares
        bookkeeping after a deposit is exactly [totalDeposited +=
        assets, totalSupply += shares].
      - [audit_vault_accrue_preserves_share_book] : [accrue] only
        touches the reward bucket; [totalSupply] and [totalDeposited]
        are invariant.
*)

Notation audit_vault_round_trip_floor_bound :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.round_trip_floor_bound.

Notation audit_vault_share_rate_monotone_under_accrue :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.accrue_share_rate_monotone.

Notation audit_vault_deposit_storage_delta :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.deposit_storage_delta.

Notation audit_vault_accrue_preserves_share_book :=
  ReserveGovernor.proofs.StakingVaultExchange.StakingVaultExchangeProofs.accrue_preserves_share_book.


(** ============================================================
    === Section: StakingVault — Multi-token Rewards ===
    ============================================================

    Reward distribution uses the standard "global index" pattern:
    each token has a per-share [rewardIndex] that strictly grows over
    time, and each user caches the index value at their last accrual
    so their pending rewards are computed as
    [balance * (index - lastIndex)].

    Headlines:
      - [audit_rewards_index_monotone] : the global [rewardIndex] is
        non-decreasing across [updateRewardIndex] — index can never
        ratchet down.
      - [audit_rewards_user_accrued_monotone] : a user's accrued
        balance only grows under [accrueUser]; rewards are never
        silently lost.
      - [audit_rewards_claim_zeroes_accrued] : a successful [claim]
        zeroes the user's accrued bucket atomically.
      - [audit_rewards_claim_returns_accrued] : the claim disburses
        exactly the user's prior accrued balance — no rounding, no
        truncation.
      - [audit_rewards_totalClaimed_monotone] : the global
        [totalClaimed] counter is non-decreasing across claims.
      - [audit_rewards_no_op_when_index_stable] : if the global index
        hasn't moved since the user's last touch, [accrueUser] is a
        no-op (the "remove and re-add LP" property).
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


(** ============================================================
    === Section: StakingVault — Dual Delegation ===
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
        ledgers — votes are neither created nor destroyed in normal
        operation.
      - [audit_delegation_opt_independent_of_std] : the optimistic
        ledger's evolution under [transfer] depends only on the
        optimistic ledger and the balances — the standard ledger
        cannot leak into it (and vice-versa, see [_std_independent_]).
      - [audit_delegation_std_independent_of_opt] : symmetric
        independence in the other direction.
      - [audit_delegation_self_transfer_noop] : a transfer between
        accounts sharing the same delegate on both ledgers leaves
        both vote vectors unchanged.
      - [audit_delegation_change_moves_all_balance] : re-pointing an
        account's optimistic delegate moves the account's full
        balance from the old delegate to the new one, leaving every
        other delegate's vote count untouched.
      - [audit_delegation_mint_no_zero_credit] : minting (from =
        zero_address) never credits the zero delegate.
      - [audit_delegation_burn_no_zero_credit] : burning (to =
        zero_address) never credits the zero delegate.
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


(** ============================================================
    === Section: ProposalLib ===
    ============================================================

    [ProposalLib] is the shared validation entry-point used by both
    [proposeOptimistic] and [proposePessimistic]. It enforces
    well-formedness of the proposal payload (matching lengths, no
    confirmation-prefixed descriptions, suffix-restricted proposer
    if present) and owns the optimistic → pessimistic transition
    primitive.

    Headlines:
      - [audit_proposal_id_injective] : the proposalId hash is
        injective on (targets, values, calldatas, description) — no
        two distinct proposals collide.
      - [audit_proposal_transition_changes_pid] : prepending
        "Confirmation For: " to a description always changes the
        proposalId — the pessimistic-escalation id is never confused
        with its optimistic parent.
      - [audit_proposal_rejects_confirmation_prefix] :
        [validateProposal] refuses any user-submitted proposal whose
        description already starts with the reserved confirmation
        prefix.
      - [audit_proposal_rejects_length_mismatch] : the (targets,
        values) and (targets, calldatas) length checks both fire.
      - [audit_proposal_rejects_already_proposed] :
        [validateProposal] refuses a proposal whose core already has
        [voteStart != 0] (already in the proposal map).
      - [audit_proposal_rejects_restricted_proposer] :
        [validateProposal] refuses a description whose
        [#proposer=ADDR] suffix names someone other than the
        caller.
      - [audit_proposal_optimistic_role_gate] :
        [proposeOptimistic] reverts [NotOptimisticProposer] when the
        proposer lacks the role.
      - [audit_proposal_optimistic_call_gate] :
        [proposeOptimistic] reverts [InvalidCall] when any
        (target, selector) is missing from the registry / has empty
        calldata / targets a non-contract.
      - [audit_proposal_pessimistic_votes_gate] :
        [proposePessimistic] reverts [InsufficientProposerVotes]
        when the proposer's votes are below [proposalThreshold].
      - [audit_proposal_transition_idempotent] : once a proposal has
        transitioned (vetoThreshold = TRANSITIONED sentinel), a
        second [transitionToPessimistic] on it reverts — the
        transition is one-way.
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
    === Section: ReserveOptimisticGovernor ===
    ============================================================

    [ReserveOptimisticGovernor] is the hybrid governance contract.
    Each proposal is either optimistic (auto-passes unless vetoed)
    or standard (requires votes ≥ proposalThreshold and a positive
    tally). The escalation state machine has eight named phases;
    successful execution is captured by reaching [PhaseExecuted] or
    [PhaseStdExecuted].

    Headlines:
      - [audit_governor_optimistic_execution_iff_succeeded] :
        [execute_optimistic] succeeds iff the proposal's observable
        phase at [now] is [PhaseSucceeded] (passed veto window
        without crossing threshold, not canceled, not already
        executed).
      - [audit_governor_veto_threshold_correctness] : within the
        active veto window, the proposal observes [PhaseDefeated]
        iff [againstVotes >= vetoThresholdTok].
      - [audit_governor_optimistic_cannot_be_queued] : optimistic
        proposals cannot enter the slow-path execute queue; only
        standard proposals can be queued.
      - [audit_governor_execute_standard_requires_queued] : standard
        execution requires the proposal to already be in
        [PhaseStdQueued] — there is no fast-path standard execution.
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
        [vetoThresholdTok] is always ≥ 1 (so a zero-supply attack
        can't drop the bar to zero).
      - [audit_governor_propose_preserves_validity] : a successful
        [propose_optimistic] produces a [Valid.proposal] under sane
        numeric inputs.
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


(** ============================================================
    === Section: TimelockControllerOptimistic ===
    ============================================================

    [TimelockControllerOptimistic] is the execution queue. Operations
    are scheduled with a [minDelay], wait through [OpWaiting], become
    [OpReady] once their timestamp matures, and are marked [OpDone]
    (with sentinel timestamp 1) after execution. A bypass path
    (gated by PROPOSER_ROLE) lets optimistic-passed proposals skip
    the delay, but must not affect any independently scheduled
    op on the standard path.

    Headlines:
      - [audit_timelock_execute_before_maturity_reverts] : the time
        lock is honored — [executeBatch] on a still-Waiting op
        reverts NotReady.
      - [audit_timelock_no_double_execute] : a successful
        [executeBatch] makes any subsequent [executeBatch] on the
        same id revert — execution is one-shot.
      - [audit_timelock_cancel_blocks_execute] : after [cancel], the
        op is reset to Unset and any subsequent [executeBatch]
        reverts.
      - [audit_timelock_bypass_requires_proposer] : the bypass path
        reverts Unauthorized when the caller lacks PROPOSER_ROLE,
        regardless of state.
      - [audit_timelock_bypass_preserves_slow_path] : after a bypass
        execution of op B, an independently scheduled op A still has
        its original timestamp and is still Waiting at any [now]
        before its maturity — the bypass does not reorder, skip,
        or accelerate the standard queue.
      - [audit_timelock_bypass_on_scheduled_reverts] : invoking the
        bypass on an op that is already scheduled reverts
        OperationConflict — bypass and slow-path are mutually
        exclusive on a per-op basis.
      - [audit_timelock_schedule_preserves_validity] : [scheduleBatch]
        preserves the state-shape invariant (every stored timestamp
        is either Unset (0), Done (1), or strictly above the Done
        sentinel).
      - [audit_timelock_execute_preserves_validity] : [executeBatch]
        preserves the state-shape invariant.
      - [audit_timelock_cancel_preserves_validity] : [cancel]
        preserves the state-shape invariant.
      - [audit_timelock_bypass_preserves_validity] :
        [executeBatchBypass] preserves the state-shape invariant.
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


(** ============================================================
    === Headlines, at a glance ===
    ============================================================

    Table of contents — every safety theorem exported above, in one
    block, with a one-line natural-language summary. This is the
    auditor's index: pick a property, cross-reference back to its
    section above for the precise statement.

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

    StakingVault — Delegation
      audit_delegation_transfer_preserves_total_votes
        — transfer between distinct non-zero delegates conserves the
          (from-delegate, to-delegate) vote sum on both ledgers.
      audit_delegation_opt_independent_of_std
        — optimistic ledger's evolution under transfer depends only
          on the optimistic ledger and balances.
      audit_delegation_std_independent_of_opt
        — symmetric independence for the standard ledger.
      audit_delegation_self_transfer_noop
        — same delegates on both sides => transfer is a no-op for
          both vote maps.
      audit_delegation_change_moves_all_balance
        — re-pointing an account's optimistic delegate moves exactly
          its full balance between old and new.
      audit_delegation_mint_no_zero_credit
        — minting (from = zero) never credits the zero delegate.
      audit_delegation_burn_no_zero_credit
        — burning (to = zero) never credits the zero delegate.

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
        — the optimistic -> pessimistic transition is one-way.
      audit_proposal_transition_terminal
        — once transitioned, any further transition reverts.

    ReserveOptimisticGovernor
      audit_governor_optimistic_execution_iff_succeeded
        — execute_optimistic succeeds iff observable phase is
          PhaseSucceeded.
      audit_governor_veto_threshold_correctness
        — within the veto window, defeated iff
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
        — success implies throttle, length, allowlist gates all
          honored and resulting proposal is well-shaped.
      audit_governor_transition_parent_defeated
        — transition_to_pessimistic marks parent PhaseDefeated.
      audit_governor_transition_child_pending
        — transition_to_pessimistic creates a child in
          PhaseStdPending.
      audit_governor_vetoThresholdTok_floor
        — on-chain vetoThresholdTok >= 1, always.
      audit_governor_propose_preserves_validity
        — propose_optimistic produces a Valid.proposal.

    TimelockControllerOptimistic
      audit_timelock_execute_before_maturity_reverts
        — executeBatch on a Waiting op reverts NotReady.
      audit_timelock_no_double_execute
        — executeBatch is one-shot per op.
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
*)
