// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

import { IGovernor } from "@openzeppelin/contracts/governance/IGovernor.sol";
import { IERC20Metadata } from "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";

import { IOptimisticSelectorRegistry } from "@interfaces/IOptimisticSelectorRegistry.sol";
import { IReserveOptimisticGovernor } from "@interfaces/IReserveOptimisticGovernor.sol";
import { IReserveOptimisticGovernorDeployer } from "@interfaces/IDeployer.sol";

import { OptimisticSelectorRegistry } from "@governance/OptimisticSelectorRegistry.sol";
import { ReserveOptimisticGovernor } from "@governance/ReserveOptimisticGovernor.sol";
import { TimelockControllerOptimistic } from "@governance/TimelockControllerOptimistic.sol";
import { ReserveOptimisticGovernorDeployer } from "@src/Deployer.sol";
import { Guardian } from "@src/Guardian.sol";
import { ReserveOptimisticGovernanceVersionRegistry } from "@src/VersionRegistry.sol";
import { StakingVault } from "@src/staking/StakingVault.sol";
import { RewardTokenRegistry } from "@staking/RewardTokenRegistry.sol";

import { OPTIMISTIC_PROPOSER_ROLE } from "@utils/Constants.sol";

import { MockERC20 } from "@mocks/MockERC20.sol";
import { MockRoleRegistry } from "@mocks/MockRoleRegistry.sol";

/// @title ProposerCancelSucceededTest
/// @notice Regression test for adversarial finding SV3: a proposer
///         can cancel an optimistic proposal in Succeeded state
///         (not just Pending).
///
/// @dev `_validateCancel` (ReserveOptimisticGovernor.sol:374-388)
///      lets the proposer cancel any non-Defeated optimistic
///      proposal. Standard OZ governor semantics restrict
///      proposer-cancel to Pending. The attack-surface review
///      flagged this as a censorship vector: a compromised
///      proposer multisig could submit benign proposals, let them
///      survive the veto window (state -> Succeeded), then cancel.
///
///      This test documents the current contract behavior. The
///      assertion fires either way; emit logs surface the actual
///      state transitions so a reviewer can decide whether this is
///      a feature or a bug.
contract ProposerCancelSucceededTest is Test {
    MockRoleRegistry private roleRegistry;
    ReserveOptimisticGovernanceVersionRegistry private versionRegistry;
    RewardTokenRegistry private rewardTokenRegistry;

    MockERC20 private token;
    MockERC20 private reward;

    StakingVault private vault;
    ReserveOptimisticGovernor private governor;
    TimelockControllerOptimistic private timelock;

    uint256 private constant REWARD_HALF_LIFE = 3 days;
    uint256 private constant UNSTAKING_DELAY = 1 weeks;
    uint48 private constant VETO_DELAY = 1 hours;
    uint32 private constant VETO_PERIOD = 2 hours;

    address constant PROPOSER = address(0xCAFE);
    address constant STAKER = address(0xBEEF);
    // A target with code, so the call-validation passes.
    address private target;

    function setUp() public {
        token = new MockERC20("Underlying", "UND");
        reward = new MockERC20("Reward", "RWD");
        // Use a dedicated dummy contract as the target so selector
        // validation passes (target must have code; reward is a
        // convenient one but we want a distinct address).
        target = address(new MockERC20("DummyTarget", "DT"));

        roleRegistry = new MockRoleRegistry(address(this));
        versionRegistry = new ReserveOptimisticGovernanceVersionRegistry(roleRegistry);
        rewardTokenRegistry = new RewardTokenRegistry(roleRegistry);

        address vaultImpl = address(new StakingVault());
        address governorImpl = address(new ReserveOptimisticGovernor());
        address timelockImpl = address(new TimelockControllerOptimistic());
        address registryImpl = address(new OptimisticSelectorRegistry());
        Guardian guardian = new Guardian(address(this), address(0), new address[](0));

        ReserveOptimisticGovernorDeployer deployer = new ReserveOptimisticGovernorDeployer(
            address(versionRegistry),
            address(rewardTokenRegistry),
            address(guardian),
            vaultImpl,
            governorImpl,
            timelockImpl,
            registryImpl
        );

        rewardTokenRegistry.registerRewardToken(address(reward));
        versionRegistry.registerVersion(deployer);

        address[] memory rewardTokens = new address[](1);
        rewardTokens[0] = address(reward);

        // Add target's selector to the registry so the proposal is valid.
        IOptimisticSelectorRegistry.SelectorData[] memory selectorData =
            new IOptimisticSelectorRegistry.SelectorData[](1);
        bytes4[] memory selectors = new bytes4[](1);
        selectors[0] = bytes4(keccak256("doSomething()"));
        selectorData[0] = IOptimisticSelectorRegistry.SelectorData({
            target: target,
            selectors: selectors
        });

        address[] memory proposers = new address[](1);
        proposers[0] = PROPOSER;

        IReserveOptimisticGovernorDeployer.BaseDeploymentParams memory baseParams =
            IReserveOptimisticGovernorDeployer.BaseDeploymentParams({
                optimisticParams: IReserveOptimisticGovernor.OptimisticGovernanceParams({
                    vetoDelay: VETO_DELAY,
                    vetoPeriod: VETO_PERIOD,
                    vetoThreshold: 0.05e18
                }),
                standardParams: IReserveOptimisticGovernor.StandardGovernanceParams({
                    votingDelay: 1 days,
                    votingPeriod: 1 weeks,
                    voteExtension: 1 days,
                    proposalThreshold: 0.01e18,
                    quorumNumerator: 0.1e18
                }),
                selectorData: selectorData,
                optimisticProposers: proposers,
                additionalGuardians: new address[](0),
                timelockDelay: 2 days,
                proposalThrottleCapacity: 12
            });

        IReserveOptimisticGovernorDeployer.NewStakingVaultParams memory newStakingVaultParams =
            IReserveOptimisticGovernorDeployer.NewStakingVaultParams({
                underlying: IERC20Metadata(address(token)),
                rewardTokens: rewardTokens,
                rewardHalfLife: REWARD_HALF_LIFE,
                unstakingDelay: UNSTAKING_DELAY
            });

        (address stakingVaultAddr, address governorAddr, address timelockAddr,) =
            deployer.deployWithNewStakingVault(baseParams, newStakingVaultParams, bytes32(0));
        vault = StakingVault(stakingVaultAddr);
        governor = ReserveOptimisticGovernor(payable(governorAddr));
        timelock = TimelockControllerOptimistic(payable(timelockAddr));

        // Stake so there's a supply for the veto threshold to be
        // computed against.
        uint256 stake = 1000e18;
        token.mint(STAKER, stake);
        vm.startPrank(STAKER);
        token.approve(address(vault), stake);
        vault.depositAndDelegate(stake, STAKER, STAKER);
        vm.stopPrank();

        // Move past the snapshot block AND warp far enough that the
        // proposal throttle has refilled at least one slot. Throttle
        // period is 12h, capacity 12 → 1 slot per hour.
        vm.roll(block.number + 1);
        vm.warp(block.timestamp + 2 hours);
    }


    /// @dev Demonstrates SV3: the proposer can cancel an optimistic
    ///      proposal that has reached Succeeded state.
    function test_SV3_ProposerCanCancelSucceededOptimistic() public {
        address[] memory targets = new address[](1);
        targets[0] = target;
        uint256[] memory values = new uint256[](1);
        values[0] = 0;
        bytes[] memory calldatas = new bytes[](1);
        calldatas[0] = abi.encodeWithSelector(bytes4(keccak256("doSomething()")));
        string memory description = "test proposal";
        bytes32 descriptionHash = keccak256(bytes(description));

        // PROPOSER submits an optimistic proposal.
        vm.prank(PROPOSER);
        uint256 proposalId =
            governor.proposeOptimistic(targets, values, calldatas, description);

        emit log_named_uint("State after propose",
                            uint256(governor.state(proposalId)));
        emit log_string("Expected: Pending (0)");

        // Walk past vetoDelay -> Active.
        vm.warp(block.timestamp + VETO_DELAY + 1);
        emit log_named_uint("State after vetoDelay (vetoPeriod open)",
                            uint256(governor.state(proposalId)));
        emit log_string("Expected: Active (1)");

        // Walk past vetoPeriod with NO veto cast. State -> Succeeded.
        vm.warp(block.timestamp + VETO_PERIOD + 1);
        IGovernor.ProposalState stateAfterVeto = governor.state(proposalId);
        emit log_named_uint("State after vetoPeriod (no veto)",
                            uint256(stateAfterVeto));
        emit log_string("Expected: Succeeded (4)");
        assertEq(uint256(stateAfterVeto), uint256(IGovernor.ProposalState.Succeeded),
                 "after veto window without veto, state should be Succeeded");

        // PROPOSER cancels the Succeeded proposal.
        // SV3 finding: _validateCancel allows this.
        vm.prank(PROPOSER);
        governor.cancel(targets, values, calldatas, descriptionHash);

        IGovernor.ProposalState stateAfterCancel = governor.state(proposalId);
        emit log_named_uint("State after PROPOSER cancel of Succeeded",
                            uint256(stateAfterCancel));
        emit log_string("If cancel succeeded: state is Canceled (2)");

        // This assertion documents the current contract behavior. If
        // _validateCancel were tightened to reject cancel-from-Succeeded,
        // the cancel() call above would revert and this assertion line
        // would never be reached.
        assertEq(uint256(stateAfterCancel), uint256(IGovernor.ProposalState.Canceled),
                 "SV3: proposer can cancel a Succeeded optimistic proposal");
    }

    /// @dev Confirms the asymmetry: standard (pessimistic) proposals
    ///      do NOT allow proposer-cancel after Pending. This is the
    ///      stricter OZ behavior; only optimistic proposals have the
    ///      looser rule.
    function test_SV3_ContextualAsymmetry_StandardProposeCannotBeProposerCanceled() public {
        // STAKER submits a standard (pessimistic) proposal. Use a
        // different selector so it's a different proposalId.
        address[] memory targets = new address[](1);
        targets[0] = target;
        uint256[] memory values = new uint256[](1);
        values[0] = 0;
        bytes[] memory calldatas = new bytes[](1);
        calldatas[0] = abi.encodeWithSelector(bytes4(keccak256("anotherSomething()")));
        string memory description = "standard test proposal";

        vm.prank(STAKER);
        uint256 proposalId = governor.propose(targets, values, calldatas, description);

        // Walk past votingDelay into Active state.
        vm.warp(block.timestamp + 1 days + 1);
        vm.roll(block.number + 1);

        IGovernor.ProposalState stateActive = governor.state(proposalId);
        emit log_named_uint("Standard proposal state after votingDelay",
                            uint256(stateActive));

        // STAKER (the proposer) tries to cancel — should revert because
        // standard proposals only allow proposer-cancel in Pending state.
        bytes32 descriptionHash = keccak256(bytes(description));
        vm.prank(STAKER);
        vm.expectRevert();
        governor.cancel(targets, values, calldatas, descriptionHash);

        emit log_string("Standard cancel from Active reverted, as expected.");
    }
}
