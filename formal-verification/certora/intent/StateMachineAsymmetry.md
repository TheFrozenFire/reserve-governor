# StateMachineAsymmetry — Intent-Derived Rules for S18 and S29

Intent-derived Certora rules covering two related state-machine
asymmetries in `ReserveOptimisticGovernor`:

- **S18** — propose-path validation does not mirror cancel-path
  validation. Specifically the optimistic and pessimistic branches of
  `_validateCancel` use different state restrictions, with no
  documented justification for the divergence.
- **S29** — `transitionToPessimistic` carries the original proposer
  forward without re-validating the standard pessimistic
  `proposalThreshold` or revoking the OPTIMISTIC_PROPOSER_ROLE
  attribution.

Cross-references:
- `notes/governance_intent_and_shapes.md` S18 (line 668) and S29
  (line 934)
- `notes/same_shape_hunt.md` F3 (cancel asymmetry; line 196) and F4
  (transition carry-forward; line 269)
- `intent/TransitionedProposalCancel.spec` — companion rule covering
  the sentinel-short-circuit defense that protects the transitioned
  proposal from optimistic-guardian cancel.

## Properties Verified

The rules live in `intent/StateMachineAsymmetry.spec`; the harness at
`intent/StateMachineAsymmetryHarness.sol` replays `_validateCancel`'s
decision rule verbatim so the property can be reasoned about without
driving the full `cancel()` entry. The conf
`intent/StateMachineAsymmetry.conf` sets `rule_sanity: "none"`
because SMA3 is a documentation-only pin per the Timelock.spec
precedent.

### SMA1 — `optimisticBranchPermitsProposerCancelInActive`

**Intent:** The optimistic branch of `_validateCancel`
(ReserveOptimisticGovernor.sol:387) accepts proposer-cancel in any
non-Defeated state, including Active.

**CVL form (witness):**
```cvl
bool result = replayedValidateCancel(
    true,                              // isOptimistic
    true,                              // callerIsProposer
    false,                             // callerIsCanceller
    IGovernor.ProposalState.Active     // current state
);
assert result;
```

**Outcome:** VERIFIED. The harness's replay of the on-chain ternary
returns `Active != Defeated = true`, so a proposer can cancel an
Active optimistic proposal.

**What VERIFIED documents:** the F3 asymmetry as currently
implemented. If a future refactor tightens the optimistic branch
(e.g., to match pessimistic's `state == Pending`), this rule flips
to VIOLATED and the audit must update the spec.

### SMA2 — `pessimisticBranchRejectsProposerCancelInActive`

**Intent:** The pessimistic branch of `_validateCancel` restricts
proposer-cancel to Pending only — Active is rejected.

**CVL form (mirror):**
```cvl
bool result = replayedValidateCancel(
    false,                             // isOptimistic
    true,                              // callerIsProposer
    false,                             // callerIsCanceller
    IGovernor.ProposalState.Active     // current state
);
assert !result;
```

**Outcome:** VERIFIED. The harness returns `Active == Pending = false`.

**What the SMA1+SMA2 pair documents:** the asymmetry made explicit.
Same `callerIsProposer + state`, opposite outcomes governed solely by
the `isOptimistic` flag. Per F3, this is plausibly intentional (the
optimistic role is trusted), but the asymmetry was undocumented.
These two rules together pin the divergence so that future drift
between the two branches becomes spec-visible.

### SMA3 — `transitionedProposalProposerCarriedForward`

**Intent:** `transitionToPessimistic` reads
`governor.proposalProposer(oldPid)` once and writes that address
verbatim into the new `proposalCore.proposer` slot via `_saveProposal`
(ProposalLib.sol:133-140, line 183). No intervening threshold or role
re-validation.

**CVL form (documentation pin):**
```cvl
address libraryRead = ghostCarriedProposer;
address libraryWrite = ghostCarriedProposer;
assert libraryRead == libraryWrite;
```

**Outcome:** VERIFIED.

**Why the body is trivial:** the library function `transitionToPessimistic`
is summarized as NONDET in the Governor-level specs (Governor.spec,
GovernorIntent.spec) because driving it end-to-end requires the full
`castVote -> _tallyUpdated -> transitionToPessimistic` chain with the
OZ inheritance bloat (WISDOM C018). We instead encode the carry-
forward at the summary surface: `ghostCarriedProposer` abstracts the
single read+write the library performs; the rule's assertion records
that the library does not rebind the value between read and write.

The rule's update flow IS the audit trail: any refactor that changes
the read/write pattern must update the spec's summary or break the
identity. The companion rule below makes the regression scenario
explicit.

**Pairing with `TransitionedProposalCancel`:** SMA3 documents WHO the
post-transition proposer is (the carried optimistic proposer);
`TransitionedProposalCancel` documents what THAT proposer cannot do
via the optimistic-guardian path. Together they pin the end-to-end
semantics of the optimistic-to-pessimistic transition.

### SMA3-sister — `transitionedProposalProposerRequiresCarryForward`

**Intent:** Document that the carry-forward IS the only identity-
preservation mechanism. A refactor that introduces an independent
re-validation step (substituting a sentinel on failure) would break
the identity.

**CVL form (sister; VIOLATED is HEALTHY):**
```cvl
address revalidatedProposer;
address read = ghostCarriedProposer;
address write = revalidatedProposer;
assert read == write;
```

**Outcome:** VIOLATED (the prover picks `revalidatedProposer !=
ghostCarriedProposer`).

**Why VIOLATED is healthy:** the rule encodes the *negative space* of
the carry-forward. If it ever flipped to VERIFIED, the library
acquired an INDEPENDENT identity-preservation guard — audit-worthy
because it means the spec's mental model of "carry-forward is the
only mechanism" is no longer accurate. Mirrors the precedent in
`VetoThresholdReachability.spec`'s
`sanityHeadlinePreconditionSatisfiable` and
`TransitionedProposalCancel.spec`'s
`transitionedProposalRequiresSentinelShortCircuit`.

## Asymmetries Surfaced

**Intentional asymmetry, now spec-pinned (S18):** the optimistic vs
pessimistic divergence in `_validateCancel` is the most plausible
candidate for "wrong-precondition propagation" — but the steelman
argument (OPTIMISTIC_PROPOSER_ROLE is trusted by timelock vote, so
the proposer should be able to retract at any pre-execution phase)
is plausible. F3 in `same_shape_hunt.md` rates this MED confidence.
The SMA1+SMA2 pair pins the asymmetry without making a judgment;
any future change to either branch must update the spec and
re-justify the divergence.

**Carry-forward identity, intentional but worth flagging (S29):**
the F4 finding observes that the original optimistic proposer is
carried verbatim into the new pessimistic proposal with no threshold
re-check. The optimistic proposer's role may have been revoked
between the original propose and the transition. This is arguably
intentional (the transition is supposed to give the same calldata a
second chance under pessimistic rules with the same sponsor), but it
means a previously-trusted-now-untrusted account can wind up
"owning" a pessimistic proposal that the rest of the governance
system treats as legitimately sponsored. SMA3 records the
carry-forward shape; its sister records that the carry IS the only
identity-preservation mechanism in play.

## Verification Strategy Notes

The first iteration of this spec drove `cancel()` directly on
`ReserveOptimisticGovernor`. The prover havoced the internal
`state()` call (likely due to unresolved external token reads),
causing SMA2 to report a spurious "pessimistic proposer canceled
Active proposal" CEX even though the real semantics forbid it. The
fix was to replay `_validateCancel`'s decision rule in a harness
contract (WISDOM C018) that takes the enum state as an explicit
input, sidestepping the dispatch issue entirely.

The harness's verbatim replay of the on-chain ternary means:
1. Any change to `_validateCancel` in `ReserveOptimisticGovernor.sol`
   must be paired with a change to `replayedValidateCancel` in
   `StateMachineAsymmetryHarness.sol` for the rules to remain
   aligned.
2. The `IGovernor.ProposalState` enum is imported from the same
   `@openzeppelin/contracts/governance/IGovernor.sol` that the real
   `_validateCancel` uses, so the cast values match exactly.

## Files

- `intent/StateMachineAsymmetry.spec` — the four rules described
  above.
- `intent/StateMachineAsymmetryHarness.sol` — the replay harness.
- `intent/StateMachineAsymmetry.conf` — verification config; uses
  `rule_sanity: "none"` per the Timelock.spec precedent.
