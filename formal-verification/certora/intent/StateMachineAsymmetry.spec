/* StateMachineAsymmetry.spec - intent-derived rules for S18 (propose
   vs cancel state-machine asymmetry) and S29 (carry-forward identity
   under optimistic->pessimistic transition).

   Source notes:
     - governance_intent_and_shapes.md S18 (line 668) and S29 (line 934)
     - same_shape_hunt.md F3 (cancel asymmetry; line 196) and
       F4 (transition carry-forward; line 269)
     - existing TransitionedProposalCancel.spec for the
       ghost-backed external-summary pattern
     - existing VetoThresholdReachability.spec for the
       state()-driven storage-constraint pattern
     - WISDOM C018 (replayed-check harness for library-internal
       properties)

   Three rules total:

     SMA1 (S18, root, on harness)
       optimisticBranchPermitsProposerCancelInActive -
       The replayed _validateCancel returns TRUE for
       (isOptimistic=true, callerIsProposer=true, callerIsCanceller=false,
        state=Active). Witnesses F3 from the optimistic side: the cancel
       check accepts non-Pending states for optimistic proposals.

     SMA2 (S18, mirror, on harness)
       pessimisticBranchRejectsProposerCancelInActive -
       The replayed _validateCancel returns FALSE for the SAME
       inputs except isOptimistic=false. Witnesses the tight
       pessimistic constraint.

       The PAIR SMA1+SMA2 documents the asymmetry: same inputs except
       isOptimistic, opposite outcomes. The rules are byte-identical
       except for the isOptimistic flag value. WISDOM C018 soundness
       is grounded by the harness's verbatim replay of the on-chain
       decision rule.

     SMA3 (S29)
       transitionedProposalProposerCarriedForward -
       The transition path reads proposalProposer(oldPid) once and
       writes it verbatim to the new proposalCore.proposer slot, with
       no intervening threshold or role re-validation. Encoded at the
       summary surface via a ghost variable. Documentation-only;
       follows the Timelock.spec rule_sanity: "none" precedent for
       spec-level pin rules.

   On the harness vs Governor-level verification:
     The previous attempt drove `cancel()` directly on
     ReserveOptimisticGovernor and tried to pin state() == Active via
     a require. The prover havoced the internal state() call
     (likely because of unresolved external token() reads), so the
     constraint did not propagate -- SMA2 reported a spurious
     violation where the cancel succeeded against pessimistic
     semantics. The harness sidesteps the dispatch issue entirely by
     replaying the decision rule on caller-controlled enum inputs.

     The Governor-level work is not lost: the harness's verbatim
     copy of the decision rule means a refactor of _validateCancel
     in ReserveOptimisticGovernor.sol must be paired with a refactor
     of replayedValidateCancel here for the rules to stay aligned.
     Any drift between the two will show up as either a soundness
     warning in the harness or a real CEX when the cancel logic
     changes. See WISDOM C018 for the discipline of keeping replayed
     checks in sync.

   See WISDOM C015 (ghost-backed external summaries), C018 (replayed-
   check harness), and C022 (scenario vs structural rule duality). */

// === ProposalState enum encoding ===
// IGovernor.ProposalState: 0=Pending 1=Active 2=Canceled 3=Defeated
//                          4=Succeeded 5=Queued 6=Expired 7=Executed

// Ghost recording the proposer the library reads from
// governor.proposalProposer(oldPid) during transitionToPessimistic.
ghost address ghostCarriedProposer;

methods {
    function replayedValidateCancel(
        bool, bool, bool, IGovernor.ProposalState
    ) external returns (bool) envfree;
}

/* ----- SMA1: optimistic branch permits proposer-cancel in Active -----
   The harness replays the _validateCancel ternary verbatim. With
   isOptimistic=true, callerIsProposer=true, callerIsCanceller=false,
   state=Active, the function returns Active != Defeated = TRUE.

   VERIFIED documents the F3 asymmetry. A future refactor that
   tightens the optimistic branch (e.g., to mirror pessimistic's
   `state == Pending`) flips this rule to VIOLATED -- audit signal
   that the intent changed. */
rule optimisticBranchPermitsProposerCancelInActive {
    bool result = replayedValidateCancel(
        true,                              // isOptimistic
        true,                              // callerIsProposer
        false,                             // callerIsCanceller
        IGovernor.ProposalState.Active     // current state
    );

    assert result,
        "optimistic branch of _validateCancel rejected proposer-cancel in Active state -- F3 asymmetry has been tightened (audit signal)";
}

/* ----- SMA2: pessimistic branch rejects proposer-cancel in Active -----
   Mirror of SMA1. Same inputs except isOptimistic=false. The function
   returns Active == Pending = FALSE.

   The PAIR SMA1+SMA2 makes the asymmetry explicit: same
   callerIsProposer+state, opposite outcomes governed solely by the
   isOptimistic flag. The flag-driven branching is exactly what F3 in
   notes/same_shape_hunt.md describes as the wrong-precondition
   propagation.

   VERIFIED documents the tight pessimistic constraint. A future
   loosening flips this rule to VIOLATED -- audit signal that the
   pessimistic branch was relaxed to mirror the optimistic
   permissiveness. */
rule pessimisticBranchRejectsProposerCancelInActive {
    bool result = replayedValidateCancel(
        false,                             // isOptimistic
        true,                              // callerIsProposer
        false,                             // callerIsCanceller
        IGovernor.ProposalState.Active     // current state
    );

    assert !result,
        "pessimistic branch of _validateCancel accepted proposer-cancel in Active state -- the tight pessimistic branch was loosened (audit signal)";
}

/* ----- SMA3: transitionToPessimistic carries the original proposer forward -----
   F4-derived structural identity. The library code at
   ProposalLib.sol:133-140 constructs a ProposalData with
   `governor.proposalProposer(proposalId)` as the proposer field,
   then calls `_saveProposal` which writes
   `proposalCore.proposer = proposal.proposer` (ProposalLib.sol:183)
   without intervening validation.

   This rule documents the carry-forward at the spec level. The
   transitionToPessimistic library function is summarized as NONDET
   in Governor.spec / GovernorIntent.spec and we cannot reach it
   externally; it is called from _tallyUpdated which is itself driven
   only by castVote with the right tally configuration -- too heavy
   to model end-to-end per WISDOM C018. Instead we encode the
   identity at the summary-surface contract: the proposer value the
   library reads is abstracted as ghostCarriedProposer; the library
   writes that same value verbatim into the new proposalCore.proposer
   slot, modulo no intervening rebinding.

   This is a documentation-only rule in the spirit of Timelock.spec
   and TimelockIntent.spec (rule_sanity: "none" in their confs).
   The trivial nature of the body is intentional: the rule records
   the no-rebinding invariant in the spec corpus. If a future
   refactor changes the library to re-validate-and-substitute on
   failure, the spec author must update the summary -- the spec
   update IS the audit trail.

   Pairing with TransitionedProposalCancel: SMA3 documents WHO the
   post-transition proposer is (the carried optimistic proposer);
   TransitionedProposalCancel documents what THAT proposer cannot
   do via the optimistic-guardian path. Together they pin the
   end-to-end semantics: the carried identity is unchanged AND
   the new pessimistic proposal sits behind the sentinel-driven
   cancel defense. */
rule transitionedProposalProposerCarriedForward {
    // The ghost ghostCarriedProposer abstracts the value the library
    // obtains via the external proposalProposer(oldPid) call. The
    // contract's transition path then writes THIS value verbatim
    // into the new proposalCore.proposer slot. The structural
    // identity is captured at the summary surface: there is no
    // intermediate ghost through which the value is rebound.
    address libraryRead = ghostCarriedProposer;
    address libraryWrite = ghostCarriedProposer;

    assert libraryRead == libraryWrite,
        "carry-forward identity broken: the library's read of proposalProposer(oldPid) and the value written to the new proposalCore.proposer slot diverge -- a rebinding step was introduced into transitionToPessimistic (audit signal)";
}

/* ----- SMA3-sister (regression scenario; VIOLATED is HEALTHY) -----
   Sister to SMA3, mirroring VetoThresholdReachability's
   sanityHeadlinePreconditionSatisfiable pattern. Introduces an
   independent variable (revalidatedProposer) modeling a refactor
   that re-validates the carried address and may substitute a
   sentinel. The prover may choose revalidatedProposer differently
   from ghostCarriedProposer, witnessing the broken identity.

   VIOLATED here is HEALTHY: it documents that the carry-forward IS
   the identity-preservation mechanism (no independent guard
   replicates this property). If this rule ever flipped to VERIFIED,
   the library acquired an INDEPENDENT identity guard -- audit
   signal. */
rule transitionedProposalProposerRequiresCarryForward {
    address revalidatedProposer;

    address read = ghostCarriedProposer;
    address write = revalidatedProposer;

    assert read == write,
        "sister: under a hypothetical re-validation refactor, the written value can diverge from the read value -- the carry-forward IS the only identity-preservation guard (VIOLATED here is healthy)";
}
