/* Guardian.sol Certora spec — covers the auth surface of the singleton
   guardian that serves as CANCELLER_ROLE for all timelocks.

   Properties proved:
     G1   only OPTIMISTIC_GUARDIAN_MANAGER_ROLE can grantOptimisticGuardian
     G2   grantOptimisticGuardian rejects address(0)
     G3   grantOptimisticGuardian on success adds the role
     G4   only DEFAULT_ADMIN_ROLE can revokeOptimisticProposer
     G5   cancel reverts if caller has neither admin nor guardian role
     G6a  non-admin cancel reverts when proposal is not optimistic
     G6b  non-admin cancel reverts when proposal state is Defeated

   External calls into IReserveOptimisticGovernor / IGovernor /
   ITimelockControllerOptimistic are summarized as ghost-backed reads
   for the three proposal-state-snapshot functions (isOptimistic, state,
   getProposalId) and as NONDET for the rest. The ghost backing makes
   the prover read consistent values across the two checks the Guardian
   performs on the same proposalId — without it, G6a/G6b are unprovable
   because the prover can pick different return values per call site.
   This mirrors the GovernorStateSnapshot threading in the Rocq
   simulation at rocq/simulations/Guardian.v.
*/

// IGovernor.ProposalState enum, ABI-encoded as uint8.
// 0=Pending 1=Active 2=Canceled 3=Defeated 4=Succeeded
// 5=Queued 6=Expired 7=Executed
definition DEFEATED() returns uint8 = 3;

// Ghosts pinning the per-call snapshot the Guardian sees.
// `ghostProposalId` is what getProposalId returns for the call's args;
// `ghostIsOptimistic[pid]` is what isOptimistic(pid) returns;
// `ghostState[pid]` is what state(pid) returns.
ghost uint256 ghostProposalId;
ghost mapping(uint256 => bool) ghostIsOptimistic;
ghost mapping(uint256 => uint8) ghostState;

methods {
    // Guardian's own role constants (envfree readers)
    function OPTIMISTIC_GUARDIAN_ROLE() external returns (bytes32) envfree;
    function OPTIMISTIC_GUARDIAN_MANAGER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // Proposal-state snapshot reads: ghost-backed so the prover reads
    // consistent values across the two checks Guardian.cancel performs.
    function _.isOptimistic(uint256 pid) external =>
        ghostIsOptimistic[pid] expect bool;
    function _.state(uint256 pid) external =>
        ghostState[pid] expect uint8;
    function _.getProposalId(address[], uint256[], bytes[], bytes32) external =>
        ghostProposalId expect uint256;

    // Side-effecting downstream calls — abstracted as NONDET. Their
    // post-state is irrelevant to Guardian's auth properties.
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

/* ----- G6a: non-admin cancel reverts on non-optimistic proposal -----
   The Guardian's optimistic-guardian role is bounded: it can only
   cancel proposals flagged as optimistic by the governor. A
   pessimistic proposal must escape this code path. */
rule cancelNonAdminRequiresOptimistic {
    env e;
    address governor;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    // Caller is an optimistic guardian but NOT an admin.
    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);

    // The proposal the governor reports for these args is NOT optimistic.
    require ghostIsOptimistic[ghostProposalId] == false;

    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);

    assert lastReverted,
        "non-admin guardian canceled a non-optimistic proposal";
}

/* ----- G6b: non-admin cancel reverts on Defeated proposal -----
   Even an optimistic proposal becomes untouchable once the governor
   reports its state as Defeated. The guardian role doesn't extend to
   resurrecting defeated proposals via cancel. */
rule cancelNonAdminRequiresNotDefeated {
    env e;
    address governor;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    require !hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require hasRole(OPTIMISTIC_GUARDIAN_ROLE(), e.msg.sender);

    // The proposal IS optimistic (otherwise G6a applies) but is Defeated.
    require ghostIsOptimistic[ghostProposalId] == true;
    require ghostState[ghostProposalId] == DEFEATED();

    cancel@withrevert(e, governor, targets, values, calldatas, descriptionHash);

    assert lastReverted,
        "non-admin guardian canceled a Defeated optimistic proposal";
}
