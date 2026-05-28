/* OptimisticSelectorRegistry.sol Certora spec.

   The contract maintains a (target, selector) allowlist with two
   coupled set views (_targets and _allowedSelectors), gated behind
   the governor's timelock. The full cross-invariant

      target in _targets  <->  _allowedSelectors[target] is non-empty

   needs ghost state to express directly in CVL (the per-target set
   length is not callable from outside), so we instead verify a set
   of one-step proxy properties on the public surface:

     R1   onlyTimelockCanRegister:   non-timelock callers cannot
                                      registerSelectors
     R2   onlyTimelockCanUnregister: non-timelock callers cannot
                                      unregisterSelectors
     R3   forbiddenTargetSelf:       registerSelectors rejects
                                      target == address(this)
     R3b  forbiddenTargetGovernor:   registerSelectors rejects
                                      target == governor
     R3c  forbiddenTargetTimelock:   registerSelectors rejects
                                      target == timelock
     R3d  forbiddenTargetToken:      registerSelectors rejects
                                      target == token
     R4   zeroSelectorRejected:      registerSelectors rejects the
                                      zero selector
     R5   registerSucceedsOnValidInput: registerSelectors does NOT
                                      revert when called by the
                                      timelock on a non-forbidden
                                      target with a non-zero selector
                                      - the only revert paths are the
                                      auth check and the two validation
                                      checks
     R6   isAllowedAfterUnregister:  a single-selector
                                      unregisterSelectors on a
                                      previously-allowed (target,
                                      selector) leaves
                                      isAllowed(target, selector) = false

   Note on EnumerableSet: a property like "after addSelector,
   isAllowed=true" requires reasoning about OZ EnumerableSet's
   internal length-position invariant (which the prover does not
   pick up automatically — it explores initial states with
   length==MAX_UINT256, causing add() to wrap). The complementary
   R5/R6 pair pins down the surface: a valid call cannot revert (R5),
   and after a remove the selector is gone (R6). Stronger
   post-conditions about set membership are tracked in the Rocq
   simulation at formal-verification/rocq/simulations/SelectorRegistry.v.

   External calls into the governor (`governor.timelock()`,
   `governor.token()`) are summarized as deterministic ghost-backed
   readers — using NONDET would let two reads of `timelock()` return
   different values in the same transaction, breaking the modifier.
   The ghost is unconstrained, so the prover still considers every
   possible timelock/token address; it just sees a stable value
   per environment.
*/

methods {
    function isAllowed(address, bytes4) external returns (bool) envfree;
    function governor() external returns (address) envfree;

    // Deterministic per-call summaries: the prover picks one value
    // for `timelock()` and one for `token()`, but it is the same
    // across all reads inside the same transaction.
    function _.timelock() external => timelockAddr() expect address;
    function _.token()    external => tokenAddr()    expect address;
}

// Ghost-backed deterministic summaries. CVL ghosts persist across
// the call so the modifier and _add see the same timelock address.
ghost timelockAddr() returns address;
ghost tokenAddr()    returns address;

/* ----- R1: only timelock can registerSelectors ----- */
rule onlyTimelockCanRegister {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;

    require e.msg.sender != timelockAddr();

    registerSelectors@withrevert(e, data);

    assert lastReverted, "non-timelock succeeded in registerSelectors";
}

/* ----- R2: only timelock can unregisterSelectors ----- */
rule onlyTimelockCanUnregister {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;

    require e.msg.sender != timelockAddr();

    unregisterSelectors@withrevert(e, data);

    assert lastReverted, "non-timelock succeeded in unregisterSelectors";
}

/* ----- R3: forbidden target rejected (target == self) -----
   We exercise the boundary check by handing in a single-selector
   data entry whose target is the registry itself. */
rule forbiddenTargetSelf {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    bytes4 selector;

    require e.msg.sender == timelockAddr();
    require data.length == 1;
    require data[0].target == currentContract;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;
    require selector != to_bytes4(0);

    registerSelectors@withrevert(e, data);

    assert lastReverted, "registerSelectors accepted self as target";
}

/* ----- R3b: forbidden target rejected (target == governor) -----
   The four forbidden targets in _add() are: self, governor, timelock,
   token. R3 covered self; R3b/R3c/R3d cover the other three. */
rule forbiddenTargetGovernor {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    bytes4 selector;
    address governorAddr;

    require e.msg.sender == timelockAddr();
    require governorAddr == governor();
    // Pin governor != self so we're isolating the governor branch of
    // the check, not the self branch.
    require governorAddr != currentContract;
    require data.length == 1;
    require data[0].target == governorAddr;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;
    require selector != to_bytes4(0);

    registerSelectors@withrevert(e, data);

    assert lastReverted, "registerSelectors accepted governor as target";
}

/* ----- R3c: forbidden target rejected (target == timelock) ----- */
rule forbiddenTargetTimelock {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    bytes4 selector;
    address tlAddr;

    require e.msg.sender == timelockAddr();
    require tlAddr == timelockAddr();
    // Isolate the timelock branch: distinct from self and governor.
    require tlAddr != currentContract;
    require tlAddr != governor();
    require data.length == 1;
    require data[0].target == tlAddr;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;
    require selector != to_bytes4(0);

    registerSelectors@withrevert(e, data);

    assert lastReverted, "registerSelectors accepted timelock as target";
}

/* ----- R3d: forbidden target rejected (target == token) ----- */
rule forbiddenTargetToken {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    bytes4 selector;
    address tokAddr;

    require e.msg.sender == timelockAddr();
    require tokAddr == tokenAddr();
    // Isolate the token branch: distinct from self, governor, timelock.
    require tokAddr != currentContract;
    require tokAddr != governor();
    require tokAddr != timelockAddr();
    require data.length == 1;
    require data[0].target == tokAddr;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;
    require selector != to_bytes4(0);

    registerSelectors@withrevert(e, data);

    assert lastReverted, "registerSelectors accepted token as target";
}

/* ----- R4: zero selector rejected at add boundary ----- */
rule zeroSelectorRejected {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    address target;

    require e.msg.sender == timelockAddr();
    require data.length == 1;
    require data[0].target == target;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == to_bytes4(0);

    // Pin target to a non-forbidden choice so the only revert reason
    // is the zero selector.
    require target != currentContract;
    require target != governor();
    require target != timelockAddr();
    require target != tokenAddr();

    registerSelectors@withrevert(e, data);

    assert lastReverted, "registerSelectors accepted zero selector";
}

/* ----- R5: registerSelectors does not revert on valid input. Proves
   the only revert paths are the auth check (R1) and the two validation
   checks (R3, R4). Together with R1/R3/R4, this characterizes the
   revert surface of registerSelectors. We use a single-element
   data array with non-msg.value calldata to rule out env-level
   reverts; the focus is the contract's own checks. */
rule registerSucceedsOnValidInput {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    address target;
    bytes4 selector;

    require e.msg.value == 0;
    require e.msg.sender == timelockAddr();
    require data.length == 1;
    require data[0].target == target;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;

    require selector != to_bytes4(0);
    require target != currentContract;
    require target != governor();
    require target != timelockAddr();
    require target != tokenAddr();

    registerSelectors@withrevert(e, data);

    assert !lastReverted,
        "registerSelectors reverted on valid (timelock, non-forbidden, non-zero) input";
}

/* ----- R6: after a successful single-selector unregisterSelectors
   on a previously-allowed (target, selector), isAllowed is false.

   Earlier revision lacked `require isAllowed(target, selector);`,
   which made the rule trivially true for pairs that were never
   registered (vacuous-pre satisfaction). The precondition forces
   the prover to exercise the actual remove path through the
   EnumerableSet. */
rule isAllowedAfterUnregister {
    env e;
    IOptimisticSelectorRegistry.SelectorData[] data;
    address target;
    bytes4 selector;

    require e.msg.sender == timelockAddr();
    require data.length == 1;
    require data[0].target == target;
    require data[0].selectors.length == 1;
    require data[0].selectors[0] == selector;

    // Non-trivialize: the pair must have been allowed before the call.
    require isAllowed(target, selector);

    unregisterSelectors(e, data);

    assert !isAllowed(target, selector),
        "selector still visible via isAllowed after unregisterSelectors";
}
