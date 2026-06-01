# Print Assumptions snapshot — milestone roster

Captured for 57 milestones across 14 files.

Counts:

- **axioms_total** — every entry under `Axioms:` for the milestone.
- **axioms_load_bearing** — total minus kernel primitives (`PrimInt63.*`, `of_u256_list`, `of_storable_values`).

| File | Theorem | Module | total | load-bearing | status |
|---|---|---|---:|---:|---|
| AccessControlEnumerable.v | `run_fun_getRoleMemberCount_656_equivalent` | AccessControlEnumerableEquivalence | 22 | 10 | OK |
| AccessControlEnumerable.v | `run_fun_getRoleMember_641_equivalent` | AccessControlEnumerableEquivalence | 22 | 10 | OK |
| Guardian.v | `run_hasRole_equivalent` | GuardianEquivalence | 22 | 10 | OK |
| Guardian.v | `run_grantRole_1468_observed_behavior` | GuardianEquivalence | 1 | 1 | OK |
| Guardian.v | `run_grantRole_1359_equivalent` | GuardianEquivalence | 40 | 28 | OK |
| Guardian.v | `run_revokeRole_1378_equivalent` | GuardianEquivalence | 29 | 17 | OK |
| Guardian.v | `run_cancel_equivalent_make_state` | GuardianEquivalence | 17 | 5 | OK |
| ProposalLib.v | `run_fun__governor_679_equivalent` | ProposalLibEquivalence | 10 | 0 | OK |
| ProposalLib.v | `run_fun__validateProposal_507_equivalent` | ProposalLibEquivalence | 18 | 6 | OK |
| ProposalLib.v | `run_fun__saveProposal_580_equivalent` | ProposalLibEquivalence | 16 | 4 | OK |
| ProposalLib.v | `run_fun_proposeOptimistic_179_equivalent` | ProposalLibEquivalence | 20 | 8 | OK |
| ProposalLib.v | `run_fun_proposePessimistic_288_equivalent` | ProposalLibEquivalence | 18 | 6 | OK |
| ProposalLib.v | `run_fun_transitionToPessimistic_400_equivalent` | ProposalLibEquivalence | 16 | 4 | OK |
| ReserveOptimisticGovernor.v | `run_propose_equivalent` | ReserveOptimisticGovernorEquivalence | 16 | 4 | OK |
| ReserveOptimisticGovernor.v | `run_castVote_equivalent` | ReserveOptimisticGovernorEquivalence | 16 | 4 | OK |
| ReserveOptimisticGovernor.v | `run_execute_equivalent` | ReserveOptimisticGovernorEquivalence | 16 | 4 | OK |
| RewardTokenRegistry.v | `run_isRegistered_equivalent` | RewardTokenRegistryEquivalence | 18 | 6 | OK |
| RewardTokenRegistry.v | `run_registerRewardToken_equivalent_make_state` | RewardTokenRegistryEquivalence | 16 | 4 | OK |
| RewardTokenRegistry.v | `run_unregisterRewardToken_equivalent_make_state` | RewardTokenRegistryEquivalence | 16 | 4 | OK |
| SelectorRegistry.v | `run_registerSelectors_equivalent_make_state` | SelectorRegistryEquivalence | 20 | 8 | OK |
| SelectorRegistry.v | `run_unregisterSelectors_equivalent_make_state` | SelectorRegistryEquivalence | 20 | 8 | OK |
| SelectorRegistry.v | `run_isAllowed_equivalent_make_state` | SelectorRegistryEquivalence | 16 | 4 | OK |
| SelectorRegistry.v | `run_targets_equivalent_make_state` | SelectorRegistryEquivalence | 15 | 3 | OK |
| SelectorRegistry.v | `run_selectorsAllowed_equivalent_make_state` | SelectorRegistryEquivalence | 15 | 3 | OK |
| StakingVaultAdmin.v | `run_setUnstakingDelay_equivalent` | StakingVaultAdminEquivalence | 30 | 18 | OK |
| StakingVaultAdmin.v | `run_setNativeRewardRate_equivalent` | StakingVaultAdminEquivalence | 15 | 3 | OK |
| StakingVaultAdmin.v | `run_grantRole_equivalent` | StakingVaultAdminEquivalence | 14 | 2 | OK |
| StakingVaultAdmin.v | `run_revokeRole_equivalent` | StakingVaultAdminEquivalence | 14 | 2 | OK |
| StakingVaultAdmin.v | `run_renounceRole_equivalent` | StakingVaultAdminEquivalence | 13 | 1 | OK |
| StakingVaultAdmin.v | `run_authorizeUpgrade_equivalent` | StakingVaultAdminEquivalence | 14 | 2 | OK |
| StakingVaultAdmin.v | `run_upgradeToAndCall_equivalent` | StakingVaultAdminEquivalence | 14 | 2 | OK |
| StakingVaultDelegation_methodology.v | `run_delegate_equivalent_methodology` | StakingVaultDelegationMethodology | 1 | 1 | OK |
| StakingVaultDelegation_methodology.v | `run_delegateOptimistic_equivalent_methodology` | StakingVaultDelegationMethodology | 1 | 1 | OK |
| StakingVaultDelegation_methodology.v | `run_delegateBySig_equivalent_methodology` | StakingVaultDelegationMethodology | 4 | 4 | OK |
| StakingVaultDelegation_methodology.v | `run_delegateOptimisticBySig_equivalent_methodology` | StakingVaultDelegationMethodology | 4 | 4 | OK |
| StakingVaultExchange.v | `run_deposit_equivalent` | StakingVaultExchangeEquivalence | 17 | 5 | OK |
| StakingVaultExchange.v | `run_mint_equivalent` | StakingVaultExchangeEquivalence | 17 | 5 | OK |
| StakingVaultExchange.v | `run_withdraw_equivalent` | StakingVaultExchangeEquivalence | 17 | 5 | OK |
| StakingVaultExchange.v | `run_redeem_equivalent` | StakingVaultExchangeEquivalence | 17 | 5 | OK |
| StakingVaultRewards.v | `run_setRewardRatio_equivalent_make_state` | StakingVaultRewardsEquivalence | 18 | 6 | OK |
| StakingVaultRewards.v | `run_poke_equivalent_make_state` | StakingVaultRewardsEquivalence | 18 | 6 | OK |
| StakingVaultRewards.v | `run_claimRewards_equivalent_make_state` | StakingVaultRewardsEquivalence | 19 | 7 | OK |
| ThrottleLib.v | `run_getProposalsAvailable_equivalent_make_state` | MakeStateForm | 22 | 10 | OK |
| ThrottleLib.v | `run_getProposalsAvailable_public_make_state` | MakeStateForm | 22 | 10 | OK |
| ThrottleLib.v | `run_consumeProposalCharge_make_state` | MakeStateForm | 24 | 12 | OK |
| TimelockControllerOptimistic.v | `run_fun_revokeOptimisticProposer_136_equivalent` | TimelockControllerOptimisticEquivalence | 16 | 4 | OK |
| TimelockControllerOptimistic.v | `run_fun_executeBatchBypass_201_equivalent` | TimelockControllerOptimisticEquivalence | 18 | 6 | OK |
| TimelockControllerOptimistic.v | `run_fun_scheduleBatch_1295_equivalent` | TimelockControllerOptimisticEquivalence | 17 | 5 | OK |
| TimelockControllerOptimistic.v | `run_fun_executeBatch_1552_equivalent` | TimelockControllerOptimisticEquivalence | 17 | 5 | OK |
| TimelockControllerOptimistic.v | `run_fun_cancel_1394_equivalent` | TimelockControllerOptimisticEquivalence | 17 | 5 | OK |
| UnstakingManager.v | `run_createLock_make_state` | UnstakingManagerEquivalence | 16 | 4 | OK |
| UnstakingManager.v | `run_cancelLock_make_state` | UnstakingManagerEquivalence | 16 | 4 | OK |
| UnstakingManager.v | `run_claimLock_make_state` | UnstakingManagerEquivalence | 16 | 4 | OK |
| VersionRegistry.v | `run_isDeprecated_equivalent_scaffold` | VersionRegistryEquivalence | 19 | 7 | OK |
| VersionRegistry.v | `run_deployments_equivalent_scaffold` | VersionRegistryEquivalence | 19 | 7 | OK |
| VersionRegistry.v | `run_deprecateVersion_equivalent_make_state` | VersionRegistryEquivalence | 38 | 26 | OK |
| VersionRegistry.v | `run_registerVersion_equivalent_make_state` | VersionRegistryEquivalence | 18 | 6 | OK |
