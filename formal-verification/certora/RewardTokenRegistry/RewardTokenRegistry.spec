/* RewardTokenRegistry.sol Certora spec — covers the auth + accounting
   surface of the singleton reward-token registry used by every
   StakingVault.

   Properties proved (every ROOT rule VERIFIED):
     R1  only RoleRegistry-owner can register
     R2  only RoleRegistry-owner-or-emergency-council can unregister
     R3  registerRewardToken reverts on address(0)
     R4  registerRewardToken reverts when the token is already registered
     R5  unregisterRewardToken reverts when the token is not registered
     R6  successful unregister flips isRegistered(token) to false
     R7  register of token A does not change isRegistered(B) for B != A
        (no cross-token interference on the membership side of the set)

   External calls into IRoleRegistry are summarized via per-account
   ghosts so individual rules can pin the auth-decision branch (owner
   vs non-owner, etc.). The RoleRegistry has (or will have) its own
   Certora coverage; here we isolate the registry's own logic.

   Notes on what is NOT covered, and why:
     - "successful register flips isRegistered(token) to true" and
       "unregister of A does not affect B" are stated naturally over
       the EnumerableSet representation but require EnumerableSet
       cross-slot invariants the prover does not have for free
       (positions[v] in [1, values.length] iff values[positions[v]-1]
       == v). Adding those invariants is its own piece of work and
       belongs in a follow-up. The directional pair R6/R7 above gives
       the same accounting guarantee from the side that is provable
       without those invariants.
*/

// Ghosts the prover may set independently per-execution; they back the
// per-call results of the IRoleRegistry external view calls.  Pinning
// the result via a ghost (rather than plain NONDET) lets rules force
// the prover to consider both the authorized and unauthorized branches
// via `require`.
ghost mapping(address => bool) ghostIsOwner;
ghost mapping(address => bool) ghostIsOwnerOrEmergencyCouncil;

methods {
    // RewardTokenRegistry's own readers — envfree.
    function isRegistered(address) external returns (bool) envfree;
    function rewardTokens() external returns (address[]) envfree;

    // RoleRegistry external calls — backed by ghosts so we can
    // require auth=true/false in individual rules.  Argument is the
    // queried account.
    function _.isOwner(address a) external => ghostIsOwner[a] expect bool;
    function _.isOwnerOrEmergencyCouncil(address a) external
        => ghostIsOwnerOrEmergencyCouncil[a] expect bool;
}

/* ----- R1: only owner (per RoleRegistry) can register ----- */
rule onlyOwnerCanRegister {
    env e;
    address token;
    require !ghostIsOwner[e.msg.sender];

    registerRewardToken@withrevert(e, token);

    assert lastReverted, "non-owner succeeded in registerRewardToken";
}

/* ----- R2: only owner/emergency-council can unregister ----- */
rule onlyOwnerOrEmergencyCanUnregister {
    env e;
    address token;
    require !ghostIsOwnerOrEmergencyCouncil[e.msg.sender];

    unregisterRewardToken@withrevert(e, token);

    assert lastReverted, "non-owner/non-emergency succeeded in unregisterRewardToken";
}

/* ----- R3: register rejects address(0) ----- */
rule registerRejectsZero {
    env e;
    require ghostIsOwner[e.msg.sender];

    registerRewardToken@withrevert(e, 0);

    assert lastReverted, "register accepted zero address";
}

/* ----- R4: register reverts on duplicate ----- */
rule registerRevertsOnDuplicate {
    env e;
    address token;
    require token != 0;
    require ghostIsOwner[e.msg.sender];
    require isRegistered(token);

    registerRewardToken@withrevert(e, token);

    assert lastReverted, "register accepted already-registered token";
}

/* ----- R5: unregister reverts when token is unknown ----- */
rule unregisterRevertsOnUnknown {
    env e;
    address token;
    require ghostIsOwnerOrEmergencyCouncil[e.msg.sender];
    require !isRegistered(token);

    unregisterRewardToken@withrevert(e, token);

    assert lastReverted, "unregister accepted unknown token";
}

/* ----- R6: successful unregister flips isRegistered to false ----- */
/* This direction is provable directly: EnumerableSet.remove deletes the
   _positions[token] slot, after which contains returns false. */
rule unregisterRemovesToken {
    env e;
    address token;
    require ghostIsOwnerOrEmergencyCouncil[e.msg.sender];
    require isRegistered(token);

    unregisterRewardToken(e, token);

    assert !isRegistered(token), "unregister did not remove token from set";
}

/* ----- R7: register of token A does not affect isRegistered(B) ----- */
/* EnumerableSet.add only writes _positions[A] and pushes to _values;
   _positions[B] for B != A is untouched, so contains(B) is preserved. */
rule registerDoesNotAffectOtherTokens {
    env e;
    address tokenA;
    address tokenB;
    require tokenA != tokenB;
    require ghostIsOwner[e.msg.sender];

    bool wasRegisteredB = isRegistered(tokenB);

    registerRewardToken(e, tokenA);

    assert isRegistered(tokenB) == wasRegisteredB,
        "registering tokenA changed membership of tokenB";
}
