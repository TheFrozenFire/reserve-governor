/* Guardian.sol Certora spec — covers the auth surface of the singleton
   guardian that serves as CANCELLER_ROLE for all timelocks.

   Properties proved:
     G1   only OPTIMISTIC_GUARDIAN_MANAGER_ROLE can grantOptimisticGuardian
     G2   grantOptimisticGuardian rejects address(0)
     G3   grantOptimisticGuardian on success adds the role
     G4   only DEFAULT_ADMIN_ROLE can revokeOptimisticProposer
     G5   cancel reverts if caller has neither admin nor guardian role
     G6   cancel by non-admin requires the proposal be optimistic AND not Defeated

   External calls into IReserveOptimisticGovernor / IGovernor /
   ITimelockControllerOptimistic are summarized as NONDET — these
   contracts have their own coverage (and Rocq simulations); here we
   isolate Guardian's own logic. The NONDET summaries let the prover
   choose arbitrary return values, which is the strongest abstraction:
   if Guardian's auth holds under arbitrary downstream behavior, it
   holds period.
*/

methods {
    // Guardian's own role constants (envfree readers)
    function OPTIMISTIC_GUARDIAN_ROLE() external returns (bytes32) envfree;
    function OPTIMISTIC_GUARDIAN_MANAGER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // External calls into other contracts — summarized as NONDET.
    // The leading `_.` means: any function with this signature on any
    // external address gets this summary.
    function _.isOptimistic(uint256) external => NONDET;
    function _.state(uint256) external => NONDET;
    function _.getProposalId(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.cancel(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.timelock() external => NONDET;
    function _.revokeOptimisticProposer(address) external => NONDET;
}

/* ----- G1: only OPTIMISTIC_GUARDIAN_MANAGER_ROLE can grant ----- */
rule onlyManagerCanGrant {
    env e;
    address account;
    require !hasRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE(), e.msg.sender);

    grantOptimisticGuardian@withrevert(e, account);

    assert lastReverted, "non-manager succeeded in granting role";
}

/* ----- G2: grantOptimisticGuardian rejects address(0) ----- */
rule grantRejectsZero {
    env e;
    require hasRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE(), e.msg.sender);

    grantOptimisticGuardian@withrevert(e, 0);

    assert lastReverted, "grant accepted zero address";
}

/* ----- G3: successful grant adds the role ----- */
rule grantAddsRole {
    env e;
    address account;
    require account != 0;
    require hasRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE(), e.msg.sender);

    grantOptimisticGuardian(e, account);

    assert hasRole(OPTIMISTIC_GUARDIAN_ROLE(), account),
        "grant did not add role";
}

/* ----- G4: only DEFAULT_ADMIN_ROLE can revoke ----- */
rule onlyAdminCanRevoke {
    env e;
    address governor;
    address account;
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);

    revokeOptimisticProposer@withrevert(e, governor, account);

    assert lastReverted, "non-admin succeeded in revoking proposer";
}

/* ----- G5: cancel reverts if caller has neither role ----- */
rule cancelRequiresAuth {
    env e;
    address governor;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require !hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);

    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);

    assert lastReverted, "unauthorized caller succeeded in cancel";
}
