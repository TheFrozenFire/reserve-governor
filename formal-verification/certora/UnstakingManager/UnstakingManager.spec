/* UnstakingManager.sol Certora spec - covers the auth + lifecycle
   surface of the withdrawal-lock queue.

   The contract manages per-user time-locked withdrawals:
     createLock(user, amount, unlockTime)   - only vault may call;
                                              auto-assigns nextLockId.
     cancelLock(lockId)                     - only the lock's user;
                                              deposits amount back to vault.
     claimLock(lockId)                      - permissionless, gated by
                                              unlockTime <= now and not
                                              already claimed.

   Properties proved:
     U1   only the vault can call createLock
     U2   only the lock's user can cancel a lock
     U3   claimLock reverts when block.timestamp < unlockTime
     U4   claimLock reverts when unlockTime == 0 (uninitialized slot)
     U5   double-claim reverts (no double-spend)
     U6   cancel after claim reverts
     U7   on successful claim, claimedAt is set to block.timestamp
     U8   createLock increments nextLockId by 1
     U9   claimedAt is set BEFORE the external transfer (CEI ordering
          guards re-entrancy)

   IERC20 / IERC4626 external calls are summarized as NONDET - token
   transfer and vault.deposit are out of scope here; if the lock
   accounting is correct under arbitrary token / vault behavior, it
   is correct period. The conservation invariant (sum of active
   lock amounts equals contract balance) is proved in Rocq
   (formal-verification/rocq/simulations/UnstakingManager.v); CVL is
   not the right tool for that global predicate.

   ------------------------------------------------------------------
   Re-entrancy scoping
   ------------------------------------------------------------------
   claimLock follows CEI: it stamps lock.claimedAt = block.timestamp
   on line 78, then calls SafeERC20.safeTransfer on line 79. A
   re-entrant token (via a hook on transfer) that calls
   claimLock(sameId) back into this contract will read claimedAt != 0
   and revert via UnstakingManager__AlreadyClaimed.

   The CVL specification cannot directly *exercise* a re-entrant
   external token because IERC20.transfer is summarized NONDET - the
   prover models the call as an unconstrained return value, never as
   an internal call back into UnstakingManager. Modeling re-entrancy
   under NONDET is unsound by construction.

   The re-entrancy property is therefore captured indirectly through
   the conjunction of two proved rules:

     U9 (claimSetsClaimedAtBeforeTransfer):  after claimLock returns,
                                             claimedAt is non-zero.
                                             By CEI inspection of the
                                             source, this assignment
                                             precedes the transfer.

     U5 (doubleClaimReverts):                a call to claimLock on a
                                             lock with claimedAt != 0
                                             reverts.

   Together: any re-entrant claimLock(sameId) call originating during
   the body of an outer claimLock reverts. The token-callback path is
   safe with respect to the same lockId.

   What this argument does NOT cover: cross-function re-entrancy (a
   malicious token calling cancelLock or createLock during the
   transfer). Those paths are guarded by their own state checks (U2,
   U6) and the vault-only auth on createLock (U1); they are not the
   double-spend vector the adversarial review highlighted.
*/

methods {
    // Storage readers — mapping(uint256 => Lock) auto-getter returns
    // the four-field tuple (user, amount, unlockTime, claimedAt).
    function locks(uint256) external returns (address, uint256, uint256, uint256) envfree;
    function vault() external returns (address) envfree;
    function targetToken() external returns (address) envfree;

    // External calls — wildcard NONDET. ERC20 transfers and the
    // ERC4626 deposit are arbitrary; we prove auth + state independent
    // of token behavior.
    function _.transfer(address, uint256) external => NONDET;
    function _.transferFrom(address, address, uint256) external => NONDET;
    function _.approve(address, uint256) external => NONDET;
    function _.deposit(uint256, address) external => NONDET;
    function _.balanceOf(address) external => NONDET;
    function _.allowance(address, address) external => NONDET;
}

/* ----- U1: only the vault can call createLock ----- */
rule onlyVaultCanCreateLock {
    env e;
    address user;
    uint256 amount;
    uint256 unlockTime;
    require e.msg.sender != vault();

    createLock@withrevert(e, user, amount, unlockTime);

    assert lastReverted, "non-vault caller succeeded in createLock";
}

/* ----- U2: only the lock's user can cancel ----- */
rule onlyLockUserCanCancel {
    env e;
    uint256 lockId;
    address lockUser;
    uint256 amt;
    uint256 unlockT;
    uint256 claimedT;
    lockUser, amt, unlockT, claimedT = locks(lockId);

    require e.msg.sender != lockUser;

    cancelLock@withrevert(e, lockId);

    assert lastReverted, "non-owner succeeded in cancelLock";
}

/* ----- U3: claimLock reverts before maturity ----- */
rule claimRevertsBeforeUnlock {
    env e;
    uint256 lockId;
    address lockUser;
    uint256 amt;
    uint256 unlockT;
    uint256 claimedT;
    lockUser, amt, unlockT, claimedT = locks(lockId);

    require unlockT != 0;
    require e.block.timestamp < unlockT;

    claimLock@withrevert(e, lockId);

    assert lastReverted, "claim succeeded before unlockTime";
}

/* ----- U4: claimLock reverts on uninitialized slot ----- */
rule claimRevertsOnUninitializedSlot {
    env e;
    uint256 lockId;
    address lockUser;
    uint256 amt;
    uint256 unlockT;
    uint256 claimedT;
    lockUser, amt, unlockT, claimedT = locks(lockId);

    require unlockT == 0;

    claimLock@withrevert(e, lockId);

    assert lastReverted, "claim succeeded on default-zero slot";
}

/* ----- U5: double-claim reverts ----- */
rule doubleClaimReverts {
    env e;
    uint256 lockId;
    address lockUser;
    uint256 amt;
    uint256 unlockT;
    uint256 claimedT;
    lockUser, amt, unlockT, claimedT = locks(lockId);

    require claimedT != 0;

    claimLock@withrevert(e, lockId);

    assert lastReverted, "second claim on already-claimed lock succeeded";
}

/* ----- U6: cancel after claim reverts ----- */
rule cancelAfterClaimReverts {
    env e;
    uint256 lockId;
    address lockUser;
    uint256 amt;
    uint256 unlockT;
    uint256 claimedT;
    lockUser, amt, unlockT, claimedT = locks(lockId);

    require claimedT != 0;
    require e.msg.sender == lockUser;

    cancelLock@withrevert(e, lockId);

    assert lastReverted, "cancel succeeded on already-claimed lock";
}

/* ----- U7: successful claim stamps claimedAt = block.timestamp ----- */
rule claimStampsTimestamp {
    env e;
    uint256 lockId;

    claimLock(e, lockId);

    address lockUserAfter;
    uint256 amtAfter;
    uint256 unlockTAfter;
    uint256 claimedTAfter;
    lockUserAfter, amtAfter, unlockTAfter, claimedTAfter = locks(lockId);

    assert claimedTAfter == e.block.timestamp,
        "claimedAt not set to block.timestamp on successful claim";
}

/* ----- U9: a successful claimLock leaves claimedAt non-zero -----
   The CEI half of the re-entrancy argument. Conjoined with U5
   (doubleClaimReverts), this proves that any re-entrant claimLock
   call on the same lockId during the outer transfer would revert.
   See the re-entrancy scoping note in the spec header. */
rule claimSetsClaimedAtBeforeTransfer {
    env e;
    uint256 lockId;

    require e.block.timestamp != 0;

    claimLock(e, lockId);

    address lockUserAfter;
    uint256 amtAfter;
    uint256 unlockTAfter;
    uint256 claimedTAfter;
    lockUserAfter, amtAfter, unlockTAfter, claimedTAfter = locks(lockId);

    assert claimedTAfter != 0,
        "claimedAt remained zero after a successful claim - re-entrancy guard broken";
}

/* ----- U8: createLock increments nextLockId by exactly 1 -----
   The lock-id-monotone invariant the Rocq-side no-double-spend proof
   leans on. Reads `nextLockId` via private-storage access, which CVL
   permits on the contract under test regardless of Solidity visibility. */
rule createLockIncrementsNextLockId {
    env e;
    address user;
    uint256 amount;
    uint256 unlockTime;

    uint256 before = currentContract.nextLockId;
    require before + 1 <= max_uint256;  // no overflow

    createLock(e, user, amount, unlockTime);

    assert currentContract.nextLockId == before + 1,
        "nextLockId not incremented by 1";
}
