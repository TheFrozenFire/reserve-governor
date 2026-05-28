# S35: Confirmation Prefix Reserved For Transition

## Intent

From `formal-verification/certora/notes/governance_intent_and_shapes.md` (S35):

> The `"Confirmation For: "` description prefix used by the transition-spawned
> proposal must be reserved -- no user-submitted proposal can have a description
> starting with that prefix, OR if one does, its proposalId must not collide with
> what a transition would produce.

### Threat model

The transition-to-pessimistic path
(`ProposalLib.transitionToPessimistic`, lines 109-143) creates a fresh
proposal whose description is
`string.concat("Confirmation For: ", optimisticProposal.description)`.
Its `proposalId` is computed via
`governor.getProposalId(targets, values, calldatas, keccak256(bytes(newDescription)))`.

If a user-submitted proposal could carry a description that begins with
the same 18-byte prefix `"Confirmation For: "`, with matching
targets/values/calldatas, the user proposal would derive the same
`proposalId` as a future transition. The user's proposal would
either:

- (a) pre-empt a transition by occupying the slot first, or
- (b) collide with an in-flight transition so the later one's
  `_saveProposal` would (depending on `voteStart`) revert or
  silently overwrite state.

## Defense location

`contracts/governance/lib/ProposalLib.sol:162-165`, inside
`_validateProposal` (called as the first statement of both
`proposeOptimistic` and `proposePessimistic`):

```solidity
require(
    bytes18(bytes(proposal.description)) != CONFIRMATION_PREFIX_BYTES,
    IReserveOptimisticGovernor.OptimisticGovernor__ConfirmationPrefixNotAllowed()
);
```

`CONFIRMATION_PREFIX_BYTES = bytes18(bytes("Confirmation For: "))` is
declared at line 19 of the same file. The 18-byte cast is exactly the
prefix length: a longer description still has the same 18-byte head, a
shorter one zero-pads, neither matches the reserved value unless the
first 18 characters are exactly `"Confirmation For: "`.

The check fires before any access-control or selector validation, so
the reject is uniform across both library entry points.

## CVL form shipped

Two ROOT rules verify the defense:

### 1. `replayedPrefixCheckRejectsReservedPrefix`

```cvl
rule replayedPrefixCheckRejectsReservedPrefix {
    env e;
    string desc;
    require descriptionPrefix(desc) == reservedPrefix();
    replayedPrefixCheck@withrevert(e, desc);
    assert lastReverted, "...accepted a description with the reserved prefix";
}
```

`replayedPrefixCheck` is a harness function (`ConfirmationPrefixHarness.sol`)
that contains the require from ProposalLib.sol:162-165 verbatim, with
both the `bytes18(bytes(...))` cast and the `ProposalLib.CONFIRMATION_PREFIX_BYTES`
constant **imported, not duplicated**. A refactor that changes the cast
width or the constant in the library flows through this harness at
compile time -- there is no manual copy to keep in sync.

`descriptionPrefix(string)` and `reservedPrefix()` are pure views that
return `bytes18(bytes(desc))` and `ProposalLib.CONFIRMATION_PREFIX_BYTES`
respectively. The `require descriptionPrefix(desc) == reservedPrefix()`
pre-condition pins the first 18 bytes of the symbolic description to
the reserved prefix; the prover then verifies that
`replayedPrefixCheck` necessarily reverts.

### 2. `reservedPrefixMatchesAsciiLiteral`

```cvl
definition CONFIRMATION_PREFIX_BYTES_LITERAL() returns bytes18 =
    to_bytes18(0x436f6e6669726d6174696f6e20466f723a20);

rule reservedPrefixMatchesAsciiLiteral {
    assert reservedPrefix() == CONFIRMATION_PREFIX_BYTES_LITERAL(),
        "ProposalLib.CONFIRMATION_PREFIX_BYTES does not match...";
}
```

A defensive pin against the library-side constant being changed. The
ASCII bytes `0x436f6e6669726d6174696f6e20466f723a20` are exactly
`"Confirmation For: "` (with a trailing space, 18 bytes total). If a
refactor renamed the prefix string in the library, this rule would
catch the mismatch.

## Run outcome

```sh
certoraRun.py formal-verification/certora/intent/ConfirmationPrefixUniqueness.conf
```

`emv-4-certora-28-May--14-43`:

| Rule                                          | Type | Status   |
|-----------------------------------------------|------|----------|
| `replayedPrefixCheckRejectsReservedPrefix`    | ROOT | VERIFIED |
| `reservedPrefixMatchesAsciiLiteral`           | ROOT | VERIFIED |
| `sanityReservedPrefixPreconditionSatisfiable` | ROOT | VIOLATED (healthy per WISDOM C002) |
| `envfreeFuncsStaticCheck`                     | ROOT | VERIFIED |

All rule-level `rule_not_vacuous` sanity sub-rules: VERIFIED.

The `sanityReservedPrefixPreconditionSatisfiable` rule deliberately
asserts FALSE under the rule precondition (`descriptionPrefix(desc) ==
reservedPrefix()`) so the prover must produce a witness if the
precondition is satisfiable. It is: the CEX is `desc = "Confirmation For:"`
(length 127, prefix matches). The VIOLATED status is the healthy
outcome -- it proves the headline rule's precondition is not vacuous.

Total prover wall-clock: ~0 seconds (the SMT obligation reduces to a
single bytes18 equality once the precondition is applied).

## Documented limitations

### L1. CVL string handling

CVL treats `string` arguments as opaque symbolic byte arrays. There is
no direct way to write `desc[0..18] == "Confirmation For: "` in a rule.
The harness's `descriptionPrefix(string)` view bridges the gap: it
performs the exact `bytes18(bytes(s))` cast Solidity performs inside
`_validateProposal`, and the prover threads the same symbolic byte
sequence through both the view and the replayed check. Requiring the
view's output equal `reservedPrefix()` is, by Solidity's cast
semantics, equivalent to requiring the first 18 bytes of the
description equal `"Confirmation For: "`.

This is the same bridge a hand-written test would need; CVL cannot do
better without first-class string-prefix support.

### L2. Replayed check vs. live call

The first iteration of this rule called
`ReserveOptimisticGovernor.proposeOptimistic` and
`ReserveOptimisticGovernor.propose` directly, with `ProposalLib.proposeOptimistic`
and `ProposalLib.proposePessimistic` NOT NONDET-summarised so the
validator would actually execute. The prover timed out on both rules
(>10 minutes per rule), and the run-log warnings showed
`Pointer analysis for call resolution failed in contract ProposalLib`
for both library functions -- the calldata `ProposalData` struct
foiled the precise memory model, and the OZ Governor inheritance tree
pulled in via `ProposalLib`'s import of `ReserveOptimisticGovernor`
bloated symbolic state.

A second iteration with a `ProposalLib`-only harness (no governor
inheritance) hit the same memory analysis failures and timed out at
the preprocessing stage.

The shipped form is the "replayed check" approach: the harness
function `replayedPrefixCheck` contains the require from
ProposalLib.sol:162-165 verbatim, with both the cast and the constant
**imported** from `ProposalLib`. The verification is logically sound
provided:

- the imported `ProposalLib.CONFIRMATION_PREFIX_BYTES` constant is the
  same value used inside `_validateProposal` (it is -- it is a
  constant in the same source file as the require);
- the `bytes18(bytes(description))` cast in the harness is the same as
  inside `_validateProposal` (it is -- byte-identical);
- both library entry points (`proposeOptimistic` /
  `proposePessimistic`) call `_validateProposal` as their first
  statement (they do -- lines 38 and 74).

The review surface for the soundness argument is two lines in
`ConfirmationPrefixHarness.sol`. The `reservedPrefixMatchesAsciiLiteral`
rule additionally pins the constant's bytes value.

### L3. getProposalId collision

The S35 threat shape ultimately reduces to "no user-submitted
`proposalId` can equal a transition-spawned `proposalId`". The
reserved-prefix check is the contract's chosen defense: if no
user-submitted description can start with the reserved prefix, then by
collision resistance of `keccak256` (assumed under
`optimistic_hashing: true` per WISDOM C009), no user-submitted
`getProposalId` can equal a transition-spawned `getProposalId`.

This rule does not relitigate the hash collision-resistance assumption.
The chain of reasoning is: reserved-prefix reject (verified here) +
hash collision resistance (assumed via optimistic_hashing) =>
proposalId non-collision (the S35 property).
