// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

import { IVotes } from "@openzeppelin/contracts/governance/utils/IVotes.sol";
import { IERC20Metadata } from "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";

import { IReserveOptimisticGovernorDeployer } from "@interfaces/IDeployer.sol";
import { IOptimisticSelectorRegistry } from "@interfaces/IOptimisticSelectorRegistry.sol";
import { IReserveOptimisticGovernor } from "@interfaces/IReserveOptimisticGovernor.sol";

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

/// @title DelegateOptimisticBySigTest
/// @notice Differential validation of the EIP-712 + ECDSA axioms
///         backing the Rocq side of [delegateOptimisticBySig]
///         coverage. Each test exercises one axiom-shape against
///         OZ's real ECDSA + EIP712 implementation.
///
/// @dev Pairs with:
///        - rocq/mocks/ECDSA.v            (axioms 1-5)
///        - rocq/mocks/Nonces.v           (replay protection)
///        - rocq/simulations/StakingVaultDelegationBySig.v
///        - rocq/proofs/StakingVaultDelegationBySig.v
///
///      Test list:
///        - test_BySig_HappyPath           — signer delegates as expected
///        - test_BySig_ExpiredSig_Reverts  — VotesExpiredSignature
///        - test_BySig_NonceReplay_Reverts — second call with same nonce fails
///        - test_BySig_WrongNonce_Reverts  — supplied nonce != stored
///        - test_BySig_CrossChainReplay_Reverts — chain-id binding
///        - test_BySig_MutatedSig_DoesNotDelegateForKey — signature
///          tampering recovers a different address than the key's
contract DelegateOptimisticBySigTest is Test {
    MockRoleRegistry private roleRegistry;
    ReserveOptimisticGovernanceVersionRegistry private versionRegistry;
    RewardTokenRegistry private rewardTokenRegistry;

    MockERC20 private token;
    MockERC20 private reward;

    StakingVault private vault;

    uint256 private constant REWARD_HALF_LIFE = 3 days;
    uint256 private constant UNSTAKING_DELAY = 1 weeks;

    bytes32 constant OPTIMISTIC_DELEGATION_TYPEHASH =
        keccak256("OptimisticDelegation(address delegatee,uint256 nonce,uint256 expiry)");

    // Test principals — Foundry-derived addresses with known private keys.
    uint256 private constant ALICE_PK = 0xA11CE;
    uint256 private constant BOB_PK = 0xB0B;
    address private alice;
    address private bob;

    function setUp() public {
        alice = vm.addr(ALICE_PK);
        bob = vm.addr(BOB_PK);
        vm.label(alice, "alice");
        vm.label(bob, "bob");

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

        // Give alice some shares so optimistic-vote-weight movement is visible.
        token.mint(alice, 1000e18);
        vm.startPrank(alice);
        token.approve(address(vault), 1000e18);
        vault.deposit(1000e18, alice);
        vm.stopPrank();
    }

    /// Compute the typed-data digest using the vault's own EIP-712
    /// domain separator. OZ's EIP712 surface exposes [domainSeparator()]
    /// via the IERC5267 interface in v5; we reach through it.
    function _digestFor(
        address delegatee, uint256 nonce, uint256 expiry
    ) internal view returns (bytes32) {
        // Use the contract's domain separator. EIP712.eip712Domain()
        // returns the v5 introspection tuple; we reconstruct the
        // separator from it.
        (
            ,
            string memory name,
            string memory version,
            uint256 chainId,
            address verifyingContract,
            ,
        ) = vault.eip712Domain();
        bytes32 domainSeparator = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256(bytes(version)),
                chainId,
                verifyingContract
            )
        );

        bytes32 structHash = keccak256(
            abi.encode(OPTIMISTIC_DELEGATION_TYPEHASH, delegatee, nonce, expiry)
        );
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));
    }

    function _signBySig(
        uint256 pk, address delegatee, uint256 nonce, uint256 expiry
    ) internal view returns (uint8 v, bytes32 r, bytes32 s) {
        bytes32 digest = _digestFor(delegatee, nonce, expiry);
        (v, r, s) = vm.sign(pk, digest);
    }

    // -------- BS-2/BS-3: happy path. --------

    function test_BySig_HappyPath() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);
        (uint8 v, bytes32 r, bytes32 s) = _signBySig(ALICE_PK, bob, nonce, expiry);

        // Anyone can submit; we use a third party (this).
        vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s);

        // Alice's optimistic delegate is now bob — matches the Rocq
        // theorem [bysig_success_sets_signer_delegate].
        assertEq(vault.optimisticDelegates(alice), bob);

        // Alice's nonce incremented by 1 — matches Rocq
        // [bysig_success_increments_signer_nonce].
        assertEq(vault.nonces(alice), nonce + 1);
    }

    // -------- BS-1: expired signatures revert. --------

    function test_BySig_ExpiredSig_Reverts() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);
        (uint8 v, bytes32 r, bytes32 s) = _signBySig(ALICE_PK, bob, nonce, expiry);

        // Advance past expiry.
        vm.warp(expiry + 1);

        vm.expectRevert(abi.encodeWithSelector(IVotes.VotesExpiredSignature.selector, expiry));
        vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s);
    }

    // -------- BS-4: nonce replay reverts. --------

    function test_BySig_NonceReplay_Reverts() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);
        (uint8 v, bytes32 r, bytes32 s) = _signBySig(ALICE_PK, bob, nonce, expiry);

        // First call succeeds.
        vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s);

        // Second call with the SAME (sig, nonce) — alice's stored
        // nonce is now nonce+1, so the supplied nonce mismatches.
        // OZ's _useCheckedNonce reverts with InvalidAccountNonce.
        vm.expectRevert();
        vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s);
    }

    // -------- BS-4b: wrong nonce (out-of-order) reverts. --------

    function test_BySig_WrongNonce_Reverts() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);
        // Sign for nonce + 5 — skipping ahead is not allowed.
        (uint8 v, bytes32 r, bytes32 s) = _signBySig(ALICE_PK, bob, nonce + 5, expiry);

        vm.expectRevert();
        vault.delegateOptimisticBySig(bob, nonce + 5, expiry, v, r, s);
    }

    // -------- BS-5: cross-chain replay. --------

    function test_BySig_CrossChainReplay_Reverts() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);

        // Sign for chain id 999 (not the current chain id).
        bytes32 structHash = keccak256(
            abi.encode(OPTIMISTIC_DELEGATION_TYPEHASH, bob, nonce, expiry)
        );
        (
            ,
            string memory name,
            string memory version,
            ,
            address verifyingContract,
            ,
        ) = vault.eip712Domain();
        bytes32 wrongChainDomain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256(bytes(version)),
                999,
                verifyingContract
            )
        );
        bytes32 wrongDigest = keccak256(abi.encodePacked("\x19\x01", wrongChainDomain, structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ALICE_PK, wrongDigest);

        // The recovered signer will NOT be alice — it will be some
        // arbitrary address whose nonce won't match. The call must
        // revert (either InvalidAccountNonce or ECDSA revert on
        // garbage signature). Alice's delegation must be unchanged.
        address aliceDelegate_before = vault.optimisticDelegates(alice);

        try vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s) {
            // If it didn't revert, the signature was somehow accepted.
            // That can happen if the recovered random address has a
            // matching zero-nonce stored value — but the delegation
            // it would set is on THAT random account, not on alice.
            assertNotEq(vault.optimisticDelegates(alice), bob, "alice delegation must not change");
        } catch {
            // Expected path: cross-chain digest yields a different
            // signer; either ECDSA recovers a wrong address whose
            // nonce doesn't match (revert), or recovers something
            // adjacent to alice but not alice. Either way alice's
            // delegation stays put.
        }
        assertEq(vault.optimisticDelegates(alice), aliceDelegate_before);
    }

    // -------- BS-5b: cross-contract replay. --------

    /// @dev We can't easily deploy a second vault with a different
    ///      address in setUp, so we forge a digest with a different
    ///      verifyingContract and confirm it fails to delegate for
    ///      alice on the current vault.
    function test_BySig_CrossContractReplay_Reverts() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);

        bytes32 structHash = keccak256(
            abi.encode(OPTIMISTIC_DELEGATION_TYPEHASH, bob, nonce, expiry)
        );
        (
            ,
            string memory name,
            string memory version,
            uint256 chainId,
            ,
            ,
        ) = vault.eip712Domain();
        bytes32 wrongContractDomain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak256(bytes(name)),
                keccak256(bytes(version)),
                chainId,
                address(0xDEADBEEF) // wrong contract
            )
        );
        bytes32 wrongDigest = keccak256(abi.encodePacked("\x19\x01", wrongContractDomain, structHash));
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(ALICE_PK, wrongDigest);

        address aliceDelegate_before = vault.optimisticDelegates(alice);
        try vault.delegateOptimisticBySig(bob, nonce, expiry, v, r, s) {
            assertNotEq(vault.optimisticDelegates(alice), bob);
        } catch {
            // Expected revert.
        }
        assertEq(vault.optimisticDelegates(alice), aliceDelegate_before);
    }

    // -------- Signature-tampering: a flipped bit yields a different recovered signer. --------

    function test_BySig_MutatedSig_DoesNotDelegateForKey() public {
        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = vault.nonces(alice);
        (uint8 v, bytes32 r, bytes32 s) = _signBySig(ALICE_PK, bob, nonce, expiry);

        // Flip a bit in r. The recovered signer is now (almost
        // surely) some random address other than alice.
        bytes32 mutated_r = r ^ bytes32(uint256(1));

        address aliceDelegate_before = vault.optimisticDelegates(alice);
        try vault.delegateOptimisticBySig(bob, nonce, expiry, v, mutated_r, s) {
            // If the call somehow succeeds, it's setting some random
            // address's delegation, NOT alice's.
            assertNotEq(vault.optimisticDelegates(alice), bob);
        } catch {
            // Expected — recovered signer is not alice, nonce check fails.
        }
        assertEq(vault.optimisticDelegates(alice), aliceDelegate_before);
        // Alice's nonce remains untouched.
        assertEq(vault.nonces(alice), nonce);
    }
}
