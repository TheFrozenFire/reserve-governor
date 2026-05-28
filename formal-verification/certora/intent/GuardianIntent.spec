/* GuardianIntent.spec - intent-derived auth-discriminator rule for
   Guardian.sol.

   See formal-verification/certora/intent/AuthDiscriminator.md for the
   methodology background (intent-derived vs syntactic role-gating).

   Property proved:
     ID1   grantOptimisticGuardian REVERTS even when the caller holds
           DEFAULT_ADMIN_ROLE, as long as the caller does NOT also hold
           OPTIMISTIC_GUARDIAN_MANAGER_ROLE.

   Why this is "intent-derived":
     The existing Guardian.spec G1 proves a missing-manager caller
     reverts. That rule does NOT *enumerate* the admin scenario: the
     manager-less caller could happen to hold the admin role, and G1
     alone leaves open the possibility that a future refactor (e.g. an
     accidental DEFAULT_ADMIN_ROLE bypass in onlyRole, or an admin-
     escape-hatch sibling function) would make admin sufficient. The
     documented Guardian threat model (Guardian.sol:21-25) carves
     DEFAULT_ADMIN_ROLE out of the grant path: admin can cancel any
     proposal but only OPTIMISTIC_GUARDIAN_MANAGER_ROLE can mint new
     OPTIMISTIC_GUARDIAN_ROLE holders. This rule pins that intent.
*/

methods {
    function OPTIMISTIC_GUARDIAN_MANAGER_ROLE() external returns (bytes32) envfree;
    function DEFAULT_ADMIN_ROLE() external returns (bytes32) envfree;
    function hasRole(bytes32, address) external returns (bool) envfree;

    // Side-effecting downstream calls — abstracted away from the auth
    // gate under test. NONDET is sound here: the rule asserts revert
    // before any downstream dispatch fires, so the downstream return
    // value cannot affect the conclusion.
    function _.cancel(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.timelock() external => NONDET;
    function _.revokeOptimisticProposer(address) external => NONDET;
    function _.isOptimistic(uint256) external => NONDET;
    function _.state(uint256) external => NONDET;
    function _.getProposalId(address[], uint256[], bytes[], bytes32) external => NONDET;
}

/* ----- ID1: admin alone cannot grant OPTIMISTIC_GUARDIAN_ROLE -----
   Threat model: a caller holding DEFAULT_ADMIN_ROLE has the break-glass
   power to cancel any proposal — but minting new optimistic guardians
   is a strictly narrower power assigned to OPTIMISTIC_GUARDIAN_MANAGER_ROLE.
   This rule asserts the two roles do not collapse: admin-without-manager
   is rejected by the onlyRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE) gate.
*/
rule adminAloneCannotGrantOptimisticGuardian {
    env e;
    address account;

    require hasRole(DEFAULT_ADMIN_ROLE(), e.msg.sender);
    require !hasRole(OPTIMISTIC_GUARDIAN_MANAGER_ROLE(), e.msg.sender);

    grantOptimisticGuardian@withrevert(e, account);

    assert lastReverted,
        "DEFAULT_ADMIN_ROLE bypassed OPTIMISTIC_GUARDIAN_MANAGER_ROLE on grantOptimisticGuardian";
}
