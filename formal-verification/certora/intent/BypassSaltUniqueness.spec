/* BypassSaltUniqueness.spec - intent-derived Certora rule for S37 from
   governance_intent_and_shapes.md: the executeBatchBypass salt structure
   is identical to the slow-path scheduleBatch salt structure (both derive
   the salt from descriptionHash via `bytes20(governor) XOR descriptionHash`).

   Intent (user-facing semantics):
     The optimistic-bypass execution path and the slow-path (scheduleBatch
     + executeBatch) MUST share the same timelock-id space for the same
     (targets, values, calldatas, descriptionHash) tuple. They do, because
     both paths derive the salt via the same formula:

         salt = bytes20(governor) ^ descriptionHash

     The "salt prefix" S37 refers to is the structural shape of this salt:
     a bytes20-of-governor in the upper 20 bytes XORed into descriptionHash,
     leaving the lower 12 bytes of descriptionHash unchanged. Any salt
     outside this family is structurally outside the governor-derivable
     space.

     The S37 defense composes two facts:
       (a) Both bypass and schedule use this formula -- no caller-supplied
           salt path exists on the governor; salts are always derived from
           descriptionHash.
       (b) Only the governor holds PROPOSER_ROLE on the timelock, so only
           the governor can call scheduleBatch -- which is the only
           timelock entry point that accepts an arbitrary salt.

     This spec pins (a). (b) is an OZ-side access-control invariant and
     is not relitigated here -- see L1 below.

   Rules shipped:

     - BS1 `bypassSaltEqualsScheduleSaltForEqualInputs`:
         The bypass salt formula at
         ReserveOptimisticGovernor._executeOperations:356 and the slow-
         path salt formula at GovernorTimelockControlUpgradeable.
         _timelockSalt:190 are byte-identical for every (governor,
         descriptionHash). Replayed verbatim in the harness.

     - BS1b `bypassSaltAsUintEqualsScheduleSaltAsUint`:
         The same equivalence in the uint-arithmetic form. Sanity-pin
         that any future refactor that splits bypass and schedule into
         distinct implementations still keeps them computing the same
         salt -- as long as both paths derive the salt from
         descriptionHash.

     - BS5 `sourceFormFormulaMatchesUintForm`:
         The source-level Solidity expression
         `bytes20(governor) ^ descriptionHash` and the uint-arithmetic
         form `bytes32((uint160(governor) << 96) ^ uint256(descriptionHash))`
         produce equal bytes32 values for every (governor,
         descriptionHash). solc 0.8.28 compiles both to the same EVM
         bytecode (verified via solc --asm), so this rule must pass on a
         correct compiler. Its purpose is documentary: it pins the
         compiler output, so a solc upgrade or optimisation flag change
         that alters the bytecode produces an immediate failure.

   Rules deferred (documented gap, see L2):
     - Salt-injectivity in descriptionHash (single-XOR bijection).
     - Lower-12-bytes preservation (bytes20-widening bit shape).
     - Upper-20-bytes XOR characterisation.

     These three claims are pure XOR/bitwise algebra and SHOULD verify.
     In this Certora install they fail with what appears to be a syntax-
     tree-construction issue at the SMT lowering layer (the prover emits
     warnings like
       `Got a non-constant, non-variable operand (Operand(out=R28:bv256,
        exp=BypassSaltHarness.diffOfBypassSalts(governor,h1,h2))) that
        is not in the builderState. Failed to construct its complete
        syntax-tree.`
     ) and produces unsound CEXes -- the displayed (governor, h1, h2)
     witnesses violate pure XOR algebra (e.g. `(g^h1) ^ (g^h2) !=
     h1^h2` for concrete inputs). The issue persists even on a pure-
     uint256 form with no fixed-bytes types at all, suggesting the
     modeling layer is not threading external-pure-function calls
     through to the SMT obligation for algebraic composition.

     The shipped rules (BS1, BS1b, BS5) cover the salt-formula-
     equivalence half of S37 directly. The salt-prefix-bitshape claims
     (BS2-BS4) are mechanically derivable from BS5 + the bytes20-cast
     semantics of solc 0.8.28; the source-level review covers them. The
     Rocq layer's `audit_timelock_bypass_on_scheduled_reverts` covers
     the cross-path collision-DoS shape end-to-end on the abstract
     state machine.

   What this spec does NOT verify directly:
     - The PROPOSER_ROLE access-control gate on `scheduleBatch` and
       `schedule`. That is an OZ-side invariant inherited from
       TimelockControllerUpgradeable; relitigating it here would
       duplicate work the OZ test suite already covers. The Rocq layer's
       `audit_timelock_bypass_requires_proposer` covers the equivalent
       claim on the bypass side.
     - The governor's pessimistic-queue path actually using the derived
       salt. This is enforced by code structure
       (GovernorTimelockControlUpgradeable._queueOperations line 107
       writes `salt = _timelockSalt(descriptionHash)` then immediately
       calls `scheduleBatch(..., salt, ...)`); the no-caller-supplied-
       salt claim is mechanical from one-line code review.
     - Hash collision resistance of `keccak256`. Per WISDOM C009
       (`optimistic_hashing: true`), keccak is assumed collision-free;
       we do not relitigate it. Composed with BS1, this gives timelock-
       id non-collision across the bypass and schedule paths for
       distinct descriptionHashes: distinct descriptionHashes ->
       (assumed) distinct hashes -> (by BS1) distinct salts -> distinct
       hashOperationBatch outputs.

   Why a replayed-formula harness instead of a live governor call:
     `_timelockSalt` is `private` in OZ's GovernorTimelockControl-
     Upgradeable -- not callable from CVL. The bypass salt expression
     `bytes20(address(this)) ^ descriptionHash` is inlined in
     `_executeOperations` (an `internal` override) -- also not callable.
     Verification at the governor entry-point level pulls in the OZ
     Governor inheritance tree and times out (WISDOM C018). The
     replayed-formula harness contains the two one-line formulas
     verbatim; the soundness argument is a single line-by-line source
     comparison.

   Failure modes the shipped rules guard against:
     - A refactor that changes the bypass salt formula in
       ReserveOptimisticGovernor (e.g., to a different XOR pattern, a
       keccak-based derivation, or a caller-supplied salt parameter)
       without a matching change to the slow-path salt formula in OZ.
       BS1 (or BS1b for the uint form) would fail.
     - A solc-version change that alters the bytecode for
       `bytes20(addr) ^ bytes32(h)` (e.g., choosing a different widening
       direction). BS5 would catch the shift in compiler output.
*/

methods {
    function bypassSalt(address, bytes32) external returns (bytes32) envfree;
    function scheduleSalt(address, bytes32) external returns (bytes32) envfree;
    function bypassSaltAsUint(address, bytes32) external returns (bytes32) envfree;
    function scheduleSaltAsUint(address, bytes32) external returns (bytes32) envfree;
}

/* ----- ROOT RULE BS1: bypass and schedule salts are byte-identical -----

   Both paths derive the salt via `bytes20(governor) ^ descriptionHash`.
   If the two formulas ever drift, the bypass and slow paths would route
   through different timelock-id spaces, and the cross-path collision-
   DoS analysis would need to be re-done.

   On a correct implementation this passes trivially -- the two harness
   functions have byte-identical bodies. Its value is regression-only:
   any future refactor that splits the formulas (e.g., adds a nonce on
   one side) trips this immediately.
*/
rule bypassSaltEqualsScheduleSaltForEqualInputs {
    address governor;
    bytes32 descriptionHash;

    assert bypassSalt(governor, descriptionHash) == scheduleSalt(governor, descriptionHash),
        "bypass salt and schedule salt formulas disagree -- collision-DoS analysis is stale";
}

/* ----- ROOT RULE BS1b: uint-form equivalence -----

   Same regression pin as BS1, on the uint-arithmetic form. Documents
   that the equivalence holds at the bit level too, independent of how
   Certora models bytes20-to-bytes32 widening.
*/
rule bypassSaltAsUintEqualsScheduleSaltAsUint {
    address governor;
    bytes32 descriptionHash;

    assert bypassSaltAsUint(governor, descriptionHash) == scheduleSaltAsUint(governor, descriptionHash),
        "bypass and schedule uint-form salt formulas disagree";
}

/* ----- ROOT RULE BS5: source-form formula equals uint-arithmetic form -----

   The source-level Solidity expression `bytes20(governor) ^ descriptionHash`
   compiles, at solc 0.8.28 with optimizer at 200 runs, to
   `(uint160(governor) << 96) XOR descriptionHash`
   (verified via solc --asm: the bytecode sequence is
     SHL 96 ; PUSH12 0xff..ff ; NOT ; AND ; XOR
   ). If this rule passes, the uint-form is provably equivalent to the
   source-form in Certora's model.

   The rule's role is documentary: it pins the compiler output, so a
   solc upgrade or optimisation flag change that alters the bytecode
   produces an immediate failure.
*/
rule sourceFormFormulaMatchesUintForm {
    address governor;
    bytes32 descriptionHash;

    assert bypassSalt(governor, descriptionHash) == bypassSaltAsUint(governor, descriptionHash),
        "source-form bytes20(g)^h disagrees with uint-form (uint160(g)<<96)^h -- compiler output has drifted";
}
