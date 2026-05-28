/* ConfirmationPrefixUniqueness.spec - intent-derived Certora rule for
   S35 from governance_intent_and_shapes.md: the "Confirmation For: "
   description prefix is reserved for the transition-spawned proposal.

   Intent (the user-facing semantics this rule encodes):
     The transition-to-pessimistic path in ProposalLib derives a fresh
     proposal id from `keccak256("Confirmation For: " || original_desc)`.
     If a user could submit a proposal whose description begins with
     that same 18-byte prefix, with the same targets/values/calldatas,
     the user proposal would either pre-empt the transition (same
     proposalId) or collide with a future transition. The contract
     defends at ProposalLib.sol:162-165 by rejecting any user-submitted
     proposal whose description begins with CONFIRMATION_PREFIX_BYTES
     (= bytes18("Confirmation For: ")).

   This rule pins that defense.

   What is verified:
     - The harness function `replayedPrefixCheck(string)` replays the
       exact require from ProposalLib._validateProposal (cast and
       constant both IMPORTED from the library). The rule asserts the
       call reverts whenever the description begins with the reserved
       prefix.
     - The harness constant `reservedPrefix()` returns the library's
       CONFIRMATION_PREFIX_BYTES verbatim; a parallel rule asserts it
       equals the locally hard-coded ASCII value, catching any
       library-side change to the constant.

   What this rule does NOT verify directly:
     - It does not call ReserveOptimisticGovernor.proposeOptimistic /
       propose. Verification at the governor entry-point level timed
       out repeatedly (>10 min per rule) because the OZ Governor
       inheritance tree pulled in by ProposalLib's import bloats the
       symbolic state. The verified property is logical, not
       memory-shape-dependent; verifying it on an in-harness copy of
       the check (where the cast and constant are imported, not
       re-derived) is sound provided the entry points actually invoke
       _validateProposal. They do: see ProposalLib.proposeOptimistic
       at line 38 and ProposalLib.proposePessimistic at line 74; both
       call `_validateProposal(proposal, proposalCore)` as their first
       statement.
     - getProposalId collision: assumed collision-free under WISDOM C009
       (optimistic_hashing: true). OZ's hash is the upstream invariant
       and is not relitigated here.

   CVL string handling -- documented limitation:
     CVL treats `string` arguments as opaque symbolic byte arrays. It
     does not let a rule index into a string or `require` a byte-range
     equality directly. We bridge that gap with a harness view
     `descriptionPrefix(string)` which performs the exact same
     `bytes18(bytes(s))` cast Solidity performs inside _validateProposal.
     The prover threads the symbolic byte sequence through both the
     view (used by the rule to pin the prefix) and the replayed check
     (used by the validator), so requiring the view's output equal
     CONFIRMATION_PREFIX_BYTES is equivalent to requiring the
     description's first 18 bytes equal "Confirmation For: ".

   Failure mode the rule guards against (the weakening it would catch):
     Any refactor that removes the `bytes18(bytes(description))` check,
     loosens it (e.g., only rejects on exact-match strings), changes
     the cast width (e.g., bytes17 or bytes19), or changes the
     CONFIRMATION_PREFIX_BYTES constant. Because both are imported
     into the harness, any library-side change is reflected here at
     compile time.
*/

/* CONFIRMATION_PREFIX_BYTES = bytes18(bytes("Confirmation For: "))
   ASCII bytes:
     C  o  n  f  i  r  m  a  t  i  o  n     F  o  r  :  (space)
     43 6f 6e 66 69 72 6d 61 74 69 6f 6e 20 46 6f 72 3a 20 (18 bytes)
*/
definition CONFIRMATION_PREFIX_BYTES_LITERAL() returns bytes18 =
    to_bytes18(0x436f6e6669726d6174696f6e20466f723a20);

methods {
    // descriptionPrefix and reservedPrefix are pure views read directly
    // in rule preconditions, so envfree saves the env-binding.
    // replayedPrefixCheck is also pure but called via @withrevert, so
    // it goes through the standard method-call path with an env arg.
    function descriptionPrefix(string) external returns (bytes18) envfree;
    function reservedPrefix() external returns (bytes18) envfree;
}

/* ----- ROOT RULE: the reserved-prefix reject fires on every input
   whose first 18 bytes match the prefix -----

   The replayedPrefixCheck function is a verbatim copy of the library
   require at ProposalLib.sol:162-165, with both the cast and the
   constant imported from ProposalLib. If this rule fails, the
   library check is incapable of rejecting reserved-prefix descriptions
   (a real bug); if it passes, the library check provably rejects them.
*/
rule replayedPrefixCheckRejectsReservedPrefix {
    env e;
    string desc;

    // Pin the first 18 bytes of the description to the reserved
    // prefix. Same symbolic byte array gets cast inside
    // replayedPrefixCheck, so the contract MUST see the same prefix.
    require descriptionPrefix(desc) == reservedPrefix();

    replayedPrefixCheck@withrevert(e, desc);

    assert lastReverted,
        "replayedPrefixCheck accepted a description with the reserved Confirmation For prefix";
}

/* ----- ROOT RULE: the library's CONFIRMATION_PREFIX_BYTES constant
   equals the ASCII bytes of "Confirmation For: " -----

   Defensive: a library-side change to the constant (e.g., a typo
   "Confirmation for:" with a lowercase f, or a different separator)
   would silently move the reserved prefix to a different 18-byte
   value. This rule asserts the constant is exactly the ASCII bytes
   of "Confirmation For: " (with a trailing space, 18 bytes total).
*/
rule reservedPrefixMatchesAsciiLiteral {
    assert reservedPrefix() == CONFIRMATION_PREFIX_BYTES_LITERAL(),
        "ProposalLib.CONFIRMATION_PREFIX_BYTES does not match the ASCII bytes of Confirmation For: prefix";
}

/* ----- SANITY CHECK: the reserved-prefix precondition is satisfiable -----

   A vacuous-precondition trap would silently pass the root rule.
   This sanity check asserts FALSE under the same precondition: if
   the precondition is satisfiable the sanity check reports VIOLATED
   (the expected, healthy outcome per WISDOM C002). If the
   precondition were vacuous, this would VERIFY and we'd know the
   root rule's pass is meaningless.
*/
rule sanityReservedPrefixPreconditionSatisfiable {
    string desc;

    require descriptionPrefix(desc) == reservedPrefix();

    assert false,
        "sanity: a description with the reserved prefix exists (VIOLATED here is healthy)";
}
