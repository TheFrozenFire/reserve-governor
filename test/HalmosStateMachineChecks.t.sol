// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

/// @title HalmosStateMachineChecks
/// @notice Symbolic-execution checks for the per-lock state machine
///         in UnstakingManager. Mirrors the contract's lifecycle
///         subset — create / cancel / claim — without the external
///         token-transfer paths the production contract uses.
///
/// @dev Halmos cannot symbolically execute through arbitrary ERC20
///      calls (the calldata-shape of safeTransferFrom + reentrancy
///      reasoning blows up the SMT search). The harness below
///      strips those calls and retains the state-machine
///      bookkeeping that determines the lifecycle invariants.
///
///      The Rocq theorems on UnstakingManager prove the same
///      properties on the Gallina simulation with unbounded
///      U256.t arithmetic. This file's symbolic-EVM-arithmetic
///      checks confirm bit-for-bit on the Solidity side.
///
/// Run with:  halmos --match-contract HalmosStateMachineChecks
contract UnstakingManagerLifecycle {
    struct Lock {
        address user;
        uint256 amount;
        uint256 unlockTime;
        uint256 claimedAt;
    }

    uint256 public nextLockId;
    mapping(uint256 => Lock) public locks;

    error Unauthorized();
    error NotUnlockedYet();
    error AlreadyClaimed();

    /// Mirrors UnstakingManager.createLock minus the ERC20 transferFrom.
    function createLock(address user, uint256 amount, uint256 unlockTime)
        external
        returns (uint256 lockId)
    {
        lockId = nextLockId++;
        Lock storage lock = locks[lockId];
        lock.user = user;
        lock.amount = amount;
        lock.unlockTime = unlockTime;
    }

    /// Mirrors UnstakingManager.cancelLock minus the vault.deposit
    /// re-credit.
    function cancelLock(uint256 lockId) external {
        Lock storage lock = locks[lockId];

        if (lock.user != msg.sender) revert Unauthorized();
        if (lock.claimedAt != 0) revert AlreadyClaimed();

        delete locks[lockId];
    }

    /// Mirrors UnstakingManager.claimLock minus the safeTransfer.
    /// The [nowTs] argument stands in for block.timestamp, exposed
    /// explicitly so Halmos can range over it.
    function claimLock(uint256 lockId, uint256 nowTs) external {
        Lock storage lock = locks[lockId];

        if (!(lock.unlockTime <= nowTs && lock.unlockTime != 0)) {
            revert NotUnlockedYet();
        }
        if (lock.claimedAt != 0) revert AlreadyClaimed();

        lock.claimedAt = nowTs;
    }
}

contract HalmosStateMachineChecksTest is Test {
    UnstakingManagerLifecycle internal mgr;

    function setUp() public {
        mgr = new UnstakingManagerLifecycle();
    }

    // ===========================================================
    // Per-call structural properties
    // ===========================================================

    /// After [createLock(user, amount, unlockTime)] returns, the new
    /// lock has the supplied fields and [claimedAt == 0].
    function check_CreateLock_InitializesFields(
        address user,
        uint256 amount,
        uint256 unlockTime
    ) public {
        uint256 lockId = mgr.createLock(user, amount, unlockTime);
        (address lUser, uint256 lAmount, uint256 lUnlock, uint256 lClaimed) =
            mgr.locks(lockId);
        assert(lUser == user);
        assert(lAmount == amount);
        assert(lUnlock == unlockTime);
        assert(lClaimed == 0);
    }

    /// After successful [cancelLock(lockId)], the lock storage is
    /// zeroed. Captures the [delete locks[lockId]] semantics.
    function check_CancelLock_ZeroesStorage(
        address user,
        uint256 amount,
        uint256 unlockTime
    ) public {
        vm.assume(user != address(0));

        uint256 lockId = mgr.createLock(user, amount, unlockTime);

        vm.prank(user);
        mgr.cancelLock(lockId);

        (address lUser, uint256 lAmount, uint256 lUnlock, uint256 lClaimed) =
            mgr.locks(lockId);
        assert(lUser == address(0));
        assert(lAmount == 0);
        assert(lUnlock == 0);
        assert(lClaimed == 0);
    }

    /// After successful [claimLock(lockId, nowTs)], the lock's
    /// [claimedAt] equals [nowTs] and the other fields are unchanged.
    function check_ClaimLock_SetsClaimedAt(
        address user,
        uint256 amount,
        uint256 unlockTime,
        uint256 nowTs
    ) public {
        vm.assume(user != address(0));
        vm.assume(unlockTime != 0);
        vm.assume(unlockTime <= nowTs);

        uint256 lockId = mgr.createLock(user, amount, unlockTime);
        mgr.claimLock(lockId, nowTs);

        (address lUser, uint256 lAmount, uint256 lUnlock, uint256 lClaimed) =
            mgr.locks(lockId);
        assert(lUser == user);
        assert(lAmount == amount);
        assert(lUnlock == unlockTime);
        assert(lClaimed == nowTs);
    }

    // ===========================================================
    // Two-call absorbing-terminal-state properties
    //
    // These are the genuinely-stateful invariants. They confirm
    // that once a lock has reached a terminal state (canceled or
    // claimed), no further mutating call on it can succeed.
    // ===========================================================

    /// Calling [cancelLock] twice on the same lockId reverts the
    /// second call. (After the first cancel, [lock.user == 0], so
    /// the [user == msg.sender] check on the second call fails.)
    function check_DoubleCancel_Reverts(
        address user,
        uint256 amount,
        uint256 unlockTime
    ) public {
        vm.assume(user != address(0));

        uint256 lockId = mgr.createLock(user, amount, unlockTime);

        vm.prank(user);
        mgr.cancelLock(lockId);

        // Second cancel must revert.
        vm.prank(user);
        try mgr.cancelLock(lockId) {
            assert(false); // unreachable: must revert
        } catch {
            // expected
        }
    }

    /// Calling [claimLock] after a successful [cancelLock] on the
    /// same lockId reverts. After cancel, [unlockTime == 0], so the
    /// [unlockTime != 0] precondition fails.
    function check_ClaimAfterCancel_Reverts(
        address user,
        uint256 amount,
        uint256 unlockTime,
        uint256 nowTs
    ) public {
        vm.assume(user != address(0));

        uint256 lockId = mgr.createLock(user, amount, unlockTime);

        vm.prank(user);
        mgr.cancelLock(lockId);

        try mgr.claimLock(lockId, nowTs) {
            assert(false); // unreachable: must revert
        } catch {
            // expected
        }
    }

    /// Calling [claimLock] twice on the same lockId reverts the
    /// second call. After the first claim, [claimedAt != 0], so the
    /// [claimedAt == 0] precondition fails on the second call.
    function check_DoubleClaim_Reverts(
        address user,
        uint256 amount,
        uint256 unlockTime,
        uint256 nowTs
    ) public {
        vm.assume(user != address(0));
        vm.assume(unlockTime != 0);
        vm.assume(unlockTime <= nowTs);

        uint256 lockId = mgr.createLock(user, amount, unlockTime);
        mgr.claimLock(lockId, nowTs);

        try mgr.claimLock(lockId, nowTs) {
            assert(false); // unreachable: must revert
        } catch {
            // expected
        }
    }

    /// Calling [cancelLock] after a successful [claimLock] on the
    /// same lockId reverts. The [claimedAt != 0] check trips.
    function check_CancelAfterClaim_Reverts(
        address user,
        uint256 amount,
        uint256 unlockTime,
        uint256 nowTs
    ) public {
        vm.assume(user != address(0));
        vm.assume(unlockTime != 0);
        vm.assume(unlockTime <= nowTs);

        uint256 lockId = mgr.createLock(user, amount, unlockTime);
        mgr.claimLock(lockId, nowTs);

        vm.prank(user);
        try mgr.cancelLock(lockId) {
            assert(false); // unreachable: must revert
        } catch {
            // expected
        }
    }

    /// Premature [claimLock] (before unlockTime) reverts.
    function check_PrematureClaim_Reverts(
        address user,
        uint256 amount,
        uint256 unlockTime,
        uint256 nowTs
    ) public {
        vm.assume(user != address(0));
        vm.assume(unlockTime != 0);
        vm.assume(nowTs < unlockTime); // strictly before unlock

        uint256 lockId = mgr.createLock(user, amount, unlockTime);

        try mgr.claimLock(lockId, nowTs) {
            assert(false); // unreachable: must revert
        } catch {
            // expected
        }
    }
}
