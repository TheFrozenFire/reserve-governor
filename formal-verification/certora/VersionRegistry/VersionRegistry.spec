/* VersionRegistry.sol Certora spec — covers the auth surface and the
   core state invariants of ReserveOptimisticGovernanceVersionRegistry.

   Properties proved:
     V1   only an owner (per RoleRegistry.isOwner) can registerVersion
     V2   registerVersion rejects a zero deployer
     V3   only owner-or-emergency-council can deprecateVersion
     V4   deprecateVersion reverts when versionHash is already deprecated
     V5   on success, deprecateVersion flips isDeprecated[versionHash] true
     V6   deprecateVersion does not affect the deprecation flag of a
          different versionHash (no cross-key bleed)
     V8   registerVersion rejects re-registration of a versionHash that
          already maps to a non-zero deployer

   Deferred:
     V7   getLatestVersion reverts when no version has ever been
          registered. The function reverts iff
          deployments[latestVersion] == 0, but latestVersion is private
          and CVL's exploration starts from arbitrary storage states.
          Without an inductive invariant tying latestVersion to
          deployments[], we cannot prove "initial state implies revert".
          Would need contract change (public latestVersion) or a
          requireInvariant chain. Left as future work.

   External RoleRegistry calls are summarized via ghost functions so the
   prover can reason deterministically about the auth gate. The deployer
   and Versioned.version() calls do not influence the auth or state
   invariants under test and are summarized as NONDET.
*/

/* Ghost-backed role mappings. The RoleRegistry external calls dispatch
   through these ghosts, so each rule can constrain what isOwner /
   isOwnerOrEmergencyCouncil return for a given caller. */
ghost mapping(address => bool) ghostIsOwner;
ghost mapping(address => bool) ghostIsOwnerOrEC;

methods {
    // VersionRegistry storage readers (envfree).
    function deployments(bytes32) external returns (address) envfree;
    function isDeprecated(bytes32) external returns (bool) envfree;

    // RoleRegistry view calls — route through ghost mappings so rules
    // can pin the return value for the caller under test.
    function _.isOwner(address a) external => ghostIsOwner[a] expect bool;
    function _.isOwnerOrEmergencyCouncil(address a) external =>
        ghostIsOwnerOrEC[a] expect bool;

    // Versioned.version() and deployer impl getters are irrelevant to
    // the properties under test; let the prover pick any value.
    function _.version() external => NONDET;
    function _.stakingVaultImpl() external => NONDET;
    function _.governorImpl() external => NONDET;
    function _.timelockImpl() external => NONDET;
}

/* ----- V1: only owners can register a new version ----- */
rule onlyOwnerCanRegister {
    env e;
    address deployer;
    require !ghostIsOwner[e.msg.sender];

    registerVersion@withrevert(e, deployer);

    assert lastReverted, "non-owner succeeded in registerVersion";
}

/* ----- V2: registerVersion rejects a zero deployer ----- */
rule registerRejectsZeroDeployer {
    env e;
    // Caller is authorized so we exercise the zero-address gate.
    require ghostIsOwner[e.msg.sender];

    address zeroDeployer;
    require zeroDeployer == 0;
    registerVersion@withrevert(e, zeroDeployer);

    assert lastReverted, "register accepted zero deployer";
}

/* ----- V3: only owner-or-emergency-council can deprecate ----- */
rule onlyAuthorizedCanDeprecate {
    env e;
    bytes32 versionHash;
    require !ghostIsOwnerOrEC[e.msg.sender];

    deprecateVersion@withrevert(e, versionHash);

    assert lastReverted, "unauthorized caller succeeded in deprecate";
}

/* ----- V4: deprecateVersion reverts on already-deprecated ----- */
rule deprecateRejectsAlreadyDeprecated {
    env e;
    bytes32 versionHash;
    require ghostIsOwnerOrEC[e.msg.sender];
    require isDeprecated(versionHash);

    deprecateVersion@withrevert(e, versionHash);

    assert lastReverted, "deprecate accepted already-deprecated hash";
}

/* ----- V5: successful deprecate flips the flag ----- */
rule deprecateFlipsFlag {
    env e;
    bytes32 versionHash;
    require ghostIsOwnerOrEC[e.msg.sender];
    require !isDeprecated(versionHash);

    deprecateVersion(e, versionHash);

    assert isDeprecated(versionHash),
        "deprecate did not set isDeprecated";
}

/* ----- V6: deprecate does not affect other versionHash flags ----- */
rule deprecateDoesNotAffectOthers {
    env e;
    bytes32 versionHash;
    bytes32 otherHash;
    require versionHash != otherHash;
    require ghostIsOwnerOrEC[e.msg.sender];

    bool otherBefore = isDeprecated(otherHash);

    deprecateVersion(e, versionHash);

    assert isDeprecated(otherHash) == otherBefore,
        "deprecate leaked to another hash";
}

/* ----- V7 (deferred): getLatestVersion reverts when unset -----
   The function reverts iff deployments[latestVersion] == 0. We cannot
   observe latestVersion from CVL (it's private), and Certora's
   exploration starts from arbitrary storage states, so we cannot rely
   on "latestVersion == 0 initially" without an inductive invariant
   tying it to deployments[]. Deferred: would require either making
   latestVersion public (contract change) or a ghost-tracked invariant.
*/

/* ----- V8: registerVersion rejects re-registration -----
   Cannot pin the keccak hash in CVL, but we can express the property
   as: if every successful registerVersion populates a previously-empty
   slot, then no slot is ever overwritten. We prove that by showing the
   set of non-empty slots only grows: a slot that was non-empty before
   the call is still non-empty (and unchanged) after it.

   Concretely: pick an arbitrary hash h that maps to a non-zero
   deployer; after registerVersion succeeds, deployments[h] is
   unchanged. This implies the function cannot re-register h. */
rule registerDoesNotOverwriteExisting {
    env e;
    address newDeployer;
    bytes32 h;
    require ghostIsOwner[e.msg.sender];
    require deployments(h) != 0;

    address before = deployments(h);

    registerVersion(e, newDeployer);

    assert deployments(h) == before,
        "registerVersion overwrote an existing slot";
}
