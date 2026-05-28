// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

import { IERC20, IERC4626 } from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";
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

import { MockERC20 } from "@mocks/MockERC20.sol";
import { MockRoleRegistry } from "@mocks/MockRoleRegistry.sol";

/// @title ShareInflationAttackTest
/// @notice Adversarial regression test against the share-inflation
///         attack vector flagged by the multi-agent adversarial
///         review (MV4).
///
/// @dev Three variants exercised. Outcome: MV4 is REFUTED — the
///      attack class is not exploitable against this contract.
///      Detailed findings:
///
///        Variant 1 (classic first-depositor inflation):
///          Attacker deposits 1 wei, donates 1000e18, victim
///          deposits 1000e18. Victim recovers 100% of their deposit
///          (totalAssets does NOT see the donation immediately,
///          since nativeBalanceLastKnown lags). Attacker recovers
///          1 wei. Donation flows to the vault, eventually streaming
///          pro-rata to all share-holders — predominantly the
///          victim, since they hold 1000e18-of-1000e18+1 shares.
///          Attacker gifts the donation to the victim.
///
///        Variant 2 (sole-staker native-rewards roundtrip):
///          Attacker is sole staker (1e18 deposit), donates 1000e18,
///          waits 30 days, withdraws. With two pokes spaced by 30d,
///          the donation streams ~99.9% back to the attacker (since
///          they hold 100% of shares). Net outcome: attacker LOSES
///          ~1e18 — the residue of the half-life stream that didn't
///          complete plus rounding. Attacker cannot extract value.
///
///        Variant 3 (sole-staker conservation):
///          Pure conservation check: attacker stakes 1e18, donates
///          100e18, waits, withdraws. Recovers <= initial outlay.
///
///      The contract's design (native rewards stream via half-life
///      from the nativeBalanceLastKnown - totalDeposited gap) means
///      direct donations are un-capturable by the donor; they
///      distribute pro-rata to share-holders over the decay
///      horizon. This is the inverse of the classical ERC4626
///      share-inflation attack.
contract ShareInflationAttackTest is Test {
    MockRoleRegistry private roleRegistry;
    ReserveOptimisticGovernanceVersionRegistry private versionRegistry;
    RewardTokenRegistry private rewardTokenRegistry;

    MockERC20 private token;
    MockERC20 private reward;

    StakingVault private vault;

    uint256 private constant REWARD_HALF_LIFE = 3 days;
    uint256 private constant UNSTAKING_DELAY = 1 weeks;

    address constant ATTACKER = address(0xA77AC);
    address constant VICTIM = address(0xB1C71);

    function setUp() public {
        token = new MockERC20("Underlying", "UND");
        reward = new MockERC20("Reward", "RWD");

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

        IReserveOptimisticGovernorDeployer.BaseDeploymentParams memory baseParams =
            IReserveOptimisticGovernorDeployer.BaseDeploymentParams({
                optimisticParams: IReserveOptimisticGovernor.OptimisticGovernanceParams({
                    vetoDelay: 1 hours, vetoPeriod: 2 hours, vetoThreshold: 0.05e18
                }),
                standardParams: IReserveOptimisticGovernor.StandardGovernanceParams({
                    votingDelay: 1 days,
                    votingPeriod: 1 weeks,
                    voteExtension: 1 days,
                    proposalThreshold: 0.01e18,
                    quorumNumerator: 0.1e18
                }),
                selectorData: new IOptimisticSelectorRegistry.SelectorData[](0),
                optimisticProposers: new address[](0),
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

        (address stakingVaultAddr,,,) =
            deployer.deployWithNewStakingVault(baseParams, newStakingVaultParams, bytes32(0));
        vault = StakingVault(stakingVaultAddr);

        vm.label(ATTACKER, "Attacker");
        vm.label(VICTIM, "Victim");
        vm.label(address(vault), "Vault");
    }

    // ===========================================================
    // Variant 1: Classic ERC4626 first-depositor inflation
    //
    // Attack: ATTACKER deposits 1 wei → receives 1 share → directly
    //         transfers 1e21 underlying to vault → VICTIM deposits
    //         1e18 underlying → VICTIM gets very few or zero shares
    //         due to inflated share price → ATTACKER redeems their
    //         1 share for most of the inflated pool.
    //
    // Outcome: OZ's ERC4626Upgradeable applies the virtual-shares
    //          mitigation via _decimalsOffset() (default 0, but
    //          combined with the +1 in convertToShares makes the
    //          virtual-shares attack costly). Test measures the
    //          actual loss to the victim.
    // ===========================================================

    function test_Variant1_FirstDepositorInflation() public {
        // ATTACKER deposits 1 wei first.
        token.mint(ATTACKER, 1);
        vm.startPrank(ATTACKER);
        token.approve(address(vault), 1);
        uint256 attackerShares = vault.deposit(1, ATTACKER);
        vm.stopPrank();

        emit log_named_uint("ATTACKER deposit", 1);
        emit log_named_uint("ATTACKER shares", attackerShares);

        // ATTACKER directly transfers 1000e18 underlying — donation.
        uint256 donation = 1000e18;
        token.mint(ATTACKER, donation);
        vm.prank(ATTACKER);
        token.transfer(address(vault), donation);

        emit log_named_uint("Donation (direct transfer)", donation);
        emit log_named_uint("totalAssets after donation", vault.totalAssets());

        // VICTIM deposits 1000e18 underlying. With share price now
        // inflated to ~1000e18 per share, victim might receive 0 or
        // very few shares.
        uint256 victimDeposit = 1000e18;
        token.mint(VICTIM, victimDeposit);
        vm.startPrank(VICTIM);
        token.approve(address(vault), victimDeposit);
        uint256 victimShares = vault.deposit(victimDeposit, VICTIM);
        vm.stopPrank();

        emit log_named_uint("VICTIM deposit", victimDeposit);
        emit log_named_uint("VICTIM shares", victimShares);
        emit log_named_uint("VICTIM share-equivalent assets",
                            vault.previewRedeem(victimShares));

        // Measure attacker's recoverable assets vs cost.
        uint256 attackerRecoverable = vault.previewRedeem(attackerShares);
        emit log_named_uint("ATTACKER recoverable", attackerRecoverable);
        emit log_named_uint("ATTACKER cost (deposit + donation)", 1 + donation);

        // Document the outcome. OZ's mitigation (decimals offset)
        // should make the attack unprofitable.
        //
        // If the test passes assert(victim share value >= 99% of
        // deposit), the contract is safe.
        // If the test FAILS this assert, the attack is live.
        uint256 victimRecoverable = vault.previewRedeem(victimShares);
        assertGe(
            victimRecoverable,
            (victimDeposit * 99) / 100,
            "Victim should recover >= 99% of deposit -- share-inflation attack would be live otherwise"
        );

        // Attacker's recoverable should NOT exceed their total outlay
        // by more than dust. If it does, the donation was capturable.
        assertLe(
            attackerRecoverable,
            1 + donation + 1, // +1 for rounding
            "Attacker should NOT recover more than they put in"
        );
    }

    // ===========================================================
    // Variant 2: Native-rewards stream capture
    //
    // Attack: ATTACKER becomes first depositor (1 wei) → directly
    //         transfers a large amount of underlying → over time,
    //         the half-life stream of that donation is distributed
    //         via _accrueRewards. Since ATTACKER holds 100% of
    //         shares at the moment, they accrue 100% of the
    //         streamed donation. After time passes, withdraw.
    //
    // This is a different mechanism than Variant 1: even with OZ's
    // share-mitigation, the native-rewards path can still credit
    // the streamed donation to whoever holds shares at accrual time.
    // ===========================================================

    function test_Variant2_NativeRewardsCaptureFromDonation() public {
        // ATTACKER becomes the FIRST depositor with a meaningful
        // (but small) stake.
        uint256 attackerDeposit = 1e18;
        token.mint(ATTACKER, attackerDeposit);
        vm.startPrank(ATTACKER);
        token.approve(address(vault), attackerDeposit);
        uint256 attackerShares = vault.deposit(attackerDeposit, ATTACKER);
        vm.stopPrank();

        uint256 attackerBalanceBefore = token.balanceOf(ATTACKER);
        emit log_named_uint("ATTACKER initial deposit", attackerDeposit);
        emit log_named_uint("ATTACKER shares", attackerShares);

        // ATTACKER directly transfers a donation to the vault.
        uint256 donation = 1000e18;
        token.mint(ATTACKER, donation);
        vm.prank(ATTACKER);
        token.transfer(address(vault), donation);

        emit log_named_uint("Donation", donation);
        emit log_named_uint("totalAssets immediately after",
                            vault.totalAssets());

        // FIRST poke: refreshes nativeBalanceLastKnown to include
        // the donation. No actual streaming yet — the prior
        // rewardsBalance was 0.
        vault.poke();
        emit log_named_uint("totalAssets after FIRST poke (refresh only)",
                            vault.totalAssets());

        // Now warp time AGAIN — this gives elapsed > 0 to drive
        // _calculateHandout on the refreshed nativeBalanceLastKnown.
        vm.warp(block.timestamp + 10 * REWARD_HALF_LIFE);

        // SECOND poke: actually streams the donation gap.
        vault.poke();
        emit log_named_uint("totalAssets after SECOND poke (streamed)",
                            vault.totalAssets());

        // Now ATTACKER initiates withdraw. With unstakingDelay > 0,
        // this creates a lock; we need to wait the delay.
        vm.startPrank(ATTACKER);
        vault.redeem(attackerShares, ATTACKER, ATTACKER);
        vm.stopPrank();

        vm.warp(block.timestamp + UNSTAKING_DELAY + 1);

        // Claim the lock. UnstakingManager exposes claimLock(lockId).
        // The first lock will be lockId 0.
        address managerAddr = address(vault.unstakingManager());
        (bool ok,) = managerAddr.call(
            abi.encodeWithSignature("claimLock(uint256)", uint256(0))
        );
        require(ok, "claimLock should succeed");

        uint256 attackerBalanceAfter = token.balanceOf(ATTACKER);
        uint256 attackerProfit = attackerBalanceAfter - attackerBalanceBefore;

        emit log_named_uint("ATTACKER ending balance", attackerBalanceAfter);
        emit log_named_uint("ATTACKER profit over initial deposit",
                            attackerProfit);
        emit log_named_uint("Donation amount (recovered if profit >= donation)", donation);

        // If `attackerProfit >= donation`, the attacker recovered
        // their donation AND captured some of the streamed value.
        // The donation was capturable.
        //
        // If `attackerProfit < donation`, the donation was partially
        // forfeited (left in the vault for future depositors).
        //
        // We assert an upper bound — the attacker should NOT
        // recover more than initialDeposit + donation. If they do,
        // there is a free-money path.
        assertLe(
            attackerProfit,
            attackerDeposit + donation + 1, // +1 for rounding
            "Attacker should not extract more than they put in"
        );

        // Surface what the attacker DID recover from the donation:
        // anything > 0 means the donation streamed to them, since
        // they were the only share-holder.
        if (attackerProfit > attackerDeposit) {
            emit log_named_uint(
                "Donation amount captured by attacker",
                attackerProfit - attackerDeposit
            );
        }
    }

    // ===========================================================
    // Variant 3: Sole-staker donation drain
    //
    // Scenario: ATTACKER becomes the only staker, then sends
    //           additional underlying to the vault directly (not
    //           through deposit). The native-rewards path streams
    //           that donation back as "rewards" — to themselves,
    //           since they hold all shares. They effectively round-
    //           trip the donated tokens after the stream completes.
    //
    // Outcome: This is the LEAST attack-like variant — it's just
    //          "I donated to myself," with no victim. The
    //          regression test confirms it doesn't accidentally
    //          stream MORE than the donation (which would be a real
    //          bug — value creation from nothing).
    // ===========================================================

    function test_Variant3_SoleStakerDonationRoundtrip() public {
        // ATTACKER stakes.
        uint256 deposit = 1e18;
        token.mint(ATTACKER, deposit);
        vm.startPrank(ATTACKER);
        token.approve(address(vault), deposit);
        uint256 shares = vault.deposit(deposit, ATTACKER);
        vm.stopPrank();

        // ATTACKER donates to vault.
        uint256 donation = 100e18;
        token.mint(ATTACKER, donation);
        vm.prank(ATTACKER);
        token.transfer(address(vault), donation);

        // Stream out.
        vm.warp(block.timestamp + 20 * REWARD_HALF_LIFE);
        vault.poke();

        // Withdraw all.
        vm.startPrank(ATTACKER);
        vault.redeem(shares, ATTACKER, ATTACKER);
        vm.stopPrank();

        vm.warp(block.timestamp + UNSTAKING_DELAY + 1);

        address managerAddr = address(vault.unstakingManager());
        (bool ok,) = managerAddr.call(
            abi.encodeWithSignature("claimLock(uint256)", uint256(0))
        );
        require(ok, "claimLock should succeed");

        uint256 ending = token.balanceOf(ATTACKER);
        emit log_named_uint("ATTACKER ending balance", ending);
        emit log_named_uint("Total ATTACKER outlay (deposit + donation)",
                            deposit + donation);

        // Conservation: attacker cannot extract MORE than they put in.
        assertLe(
            ending,
            deposit + donation + 1,
            "Sole-staker roundtrip must not create value from nothing"
        );
    }
}
