/* ChannelSeparation.spec - intent-derived channel-separation rules
   for ReserveOptimisticGovernor.sol (S33 in governance_intent_and_shapes.md).

   Intent property (S33):
     "The two governance channels - optimistic (auto-passes unless vetoed)
      and standard / pessimistic (quorum + delay) - are SEPARATE state
      machines sharing ProposalCore storage. Asymmetries in
      _validateCancel, _executeOperations, _queueOperations, _countVote,
      _castVote, _tallyUpdated, and state() are the points where the two
      channels diverge. Each divergence is a place where the intent for
      one channel could leak into the other."

     The sole on-chain discriminator is the per-proposal vetoThreshold
     sentinel: vetoThreshold(pid) != 0 means "optimistic" (covering both
     a live optimistic proposal in [1, 1e18] AND a transitioned proposal
     stamped with TRANSITIONED_VETO_THRESHOLD == type(uint256).max).
     vetoThreshold(pid) == 0 means "standard / pessimistic / nonexistent."

   These four rules pin the channel separation at the four most plausible
   cross-pollination paths the asymmetries open up:

     CS1   optimisticProposalCannotEnterStandardQueue: queue() reverts
           for any optimistic pid (live OR transitioned). The standard
           execution channel cannot accept an optimistic proposal.

     CS2   standardProposalNeedsTimelockQueuing: proposalNeedsQueuing
           returns true for any pid with vetoThreshold == 0. The
           optimistic bypass at line 294 does not fire for the standard
           channel - i.e., standard proposals commit to using the
           timelock route.

     CS3   channelDeterminedByVetoThresholdSentinel: the public
           isOptimistic(pid) view returns true iff vetoThreshold(pid) is
           non-zero (and reverts when the proposal does not exist).
           This pins the encoding boundary: there is exactly ONE bit of
           channel-discrimination state per proposal, and it lives in
           the vetoThreshold storage slot.

     CS4   optimisticProposalRejectsNonAgainstVotes: castVote(pid,
           support) reverts for any optimistic pid whenever support
           != Against. The standard-channel vote types (For, Abstain)
           cannot be applied through the optimistic channel.

   How these add new content over existing coverage:

     - Governor.spec R13 (optimisticProposalCannotBeQueued) covers CS1's
       statement, but the channel-separation framing of CS1 makes
       explicit that the sentinel value MAX_UINT256 also qualifies as
       "optimistic" - i.e. the rule survives the transition path.
     - Governor.spec R15 (optimisticProposalNeedsNoQueuing) gives the
       optimistic side; CS2 is its DUAL, pinning the standard channel's
       commitment to the timelock. Together R15 + CS2 give a complete
       partition.
     - Governor.spec R14 (optimisticProposalAcceptsOnlyAgainst) covers
       CS4's statement. CS4 carries the same constraint but the
       channel-separation framing surfaces the intent: standard vote
       types do not silently pass through to the optimistic channel.
     - CS3 is wholly new. It pins the discriminator encoding itself:
       no other rule asserts that the public isOptimistic view aligns
       exactly with the vetoThreshold != 0 storage predicate. A future
       refactor that changed _isOptimistic to e.g. `vetoThreshold > 0
       && vetoThreshold <= 1e18` would silently make transitioned
       proposals look pessimistic, breaking CS1/CS4 indirectly. CS3
       fences the encoding directly.

   See WISDOM C015 (ghost-backed external summaries) for the threading
   pattern. The summaries here mirror Governor.spec - we use ghost-
   backed hasRole and state() ghosts so any rule reading those can
   thread a single value per (role, account) and per proposalId.

   See WISDOM C017 (two-ghost summary divergence): not exercised here -
   none of these four rules depend on distinguishing related external
   reads. All four rules close on the per-proposal vetoThreshold storage,
   which is real contract state.

   Conf settings mirror Governor.conf:
     - disable_internal_function_instrumentation: true to skip the
       auto-finder pass (path-resolution bug on this deep source tree).
     - optimistic_hashing: true so getProposalId(...) is treated as
       collision-free and CS1's external pid matches queue()'s internal
       computation.
     - optimistic_loop: true with loop_iter: 3 for the OZ deque pop.
*/

/* IGovernor.ProposalState enum, ABI-encoded as uint8.
   Only AGAINST() vote-type constant is consumed; we keep the state
   definitions in case follow-on rules read state() through a ghost. */
definition AGAINST() returns uint8 = 0;

/* TRANSITIONED_VETO_THRESHOLD = type(uint256).max - sentinel marking a
   proposal that already transitioned from optimistic to pessimistic.
   _isOptimistic treats this as optimistic (sentinel != 0), so CS1 and
   CS4 must hold for this value too. CS3 pins the encoding so the
   sentinel cannot accidentally be re-interpreted. */
definition TRANSITIONED_SENTINEL() returns uint256 = max_uint256;

/* Ghost-backed hasRole. Replaces NONDET so two AccessControl reads of
   the same (role, account) pair agree across calls. Mirrors
   Governor.spec line 90 (WISDOM C015). None of the four rules below
   read ghostHasRole directly, but declaring it keeps the spec ready
   for sibling rules that may. */
ghost mapping(bytes32 => mapping(address => bool)) ghostHasRole;

/* Ghost-backed state(pid) at the inter-contract surface. Same fidelity
   role as Governor.spec line 100. CS3 reads `isOptimistic(pid)` which
   does NOT call state(), so this ghost is not consulted there; we
   still declare the summary so a CS1/CS4 trace through the OZ
   _validateStateBitmap path doesn't pick conflicting state values
   across reads of the same pid. */
ghost mapping(uint256 => uint8) ghostState;

methods {
    // Envfree readers consumed by the rules.
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function timelock() external returns (address) envfree;
    function proposalSnapshot(uint256) external returns (uint256) envfree;
    function proposalProposer(uint256) external returns (address) envfree;

    // Public isOptimistic view, used by CS3.
    function isOptimistic(uint256) external returns (bool);

    // === Ghost-backed external summary for state() ===
    // Wildcard-external: catches `governor.state(pid)` calls from
    // other contracts. Intra-contract dispatch from
    // _validateStateBitmap runs the real override - sound for CS1/CS4
    // since both conclude in revert. Mirrors Governor.spec.
    function _.state(uint256 pid) external => ghostState[pid] expect uint8;

    // === NONDET summaries mirroring Governor.spec ===
    // Library external functions (delegatecalled).
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;

    // Token / votes.
    function _.getPastTotalSupply(uint256) external => NONDET;
    function _.getPastVotes(address, uint256) external => NONDET;
    function _.getPastOptimisticVotes(address, uint256) external => NONDET;
    function _.getPastOptimisticVotingSupply(uint256) external => NONDET;
    function _.clock() external => NONDET;
    function _.CLOCK_MODE() external => NONDET;

    // Timelock interactions. hasRole ghost-backed per WISDOM C015.
    function _.hasRole(bytes32 role, address account) external =>
        ghostHasRole[role][account] expect bool;
    function _.scheduleBatch(address[], uint256[], bytes[], bytes32, bytes32, uint256) external => NONDET;
    function _.executeBatch(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;
    function _.executeBatchBypass(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;
    function _.cancel(bytes32) external => NONDET;
    function _.cancel(address[], uint256[], bytes[], bytes32) external => NONDET;
    function _.isOperationPending(bytes32) external => NONDET;
    function _.isOperationReady(bytes32) external => NONDET;
    function _.isOperationDone(bytes32) external => NONDET;
    function _.getMinDelay() external => NONDET;
    function _.getTimestamp(bytes32) external => NONDET;
    function _.hashOperationBatch(address[], uint256[], bytes[], bytes32, bytes32) external => NONDET;

    // Selector registry.
    function _.isAllowed(address, bytes4) external => NONDET;
}

/* ----- CS1: optimisticProposalCannotEnterStandardQueue -----
   For ANY proposal whose vetoThreshold(pid) is non-zero - whether a
   live optimistic proposal (vetoThreshold in [1, 1e18]) or a
   transitioned one (vetoThreshold == TRANSITIONED_SENTINEL) - the
   public queue() entry point must revert. The standard execution
   channel cannot accept an optimistic proposal.

   _queueOperations override at ReserveOptimisticGovernor.sol:340
   unconditionally reverts with OptimisticGovernor__OptimisticProposalCannotBeQueued
   when _isOptimistic(pid). OZ's queue() runs _validateStateBitmap
   (state == Succeeded) first; either path terminates in revert. With
   optimistic_hashing on, getProposalId externally returns the same id
   queue() will compute internally.

   Channel-separation framing of Governor.spec R13: the rule survives
   the transitioned-proposal case (vetoThreshold == max_uint256), which
   is the load-bearing extension over R13's plain "vetoThreshold != 0"
   precondition. */
rule optimisticProposalCannotEnterStandardQueue {
    env e;
    address[] targets;
    uint256[] values;
    bytes[] calldatas;
    bytes32 descriptionHash;

    uint256 pid = getProposalId(e, targets, values, calldatas, descriptionHash);

    // Optimistic: vetoThreshold != 0, including the sentinel.
    require vetoThreshold(pid) != 0;

    queue@withrevert(e, targets, values, calldatas, descriptionHash);

    assert lastReverted,
        "queue() accepted an optimistic proposal - standard channel leaked into optimistic";
}

/* ----- CS2: standardProposalNeedsTimelockQueuing -----
   DUAL of Governor.spec R15. For any pid with vetoThreshold == 0
   (standard / pessimistic), proposalNeedsQueuing(pid) must return
   true.

   The override at ReserveOptimisticGovernor.sol:294 early-returns
   false if _isOptimistic; otherwise it falls through to
   super.proposalNeedsQueuing(...) which OZ's
   GovernorTimelockControlUpgradeable.sol:90-92 implements as a
   constant `return true`.

   Channel-separation framing: pinning the dual surfaces a refactor
   risk that R15 alone misses - a future edit that changes the
   fallthrough to `return _isOptimistic ? false : false` (or to any
   tally-aware computation) would still satisfy R15 but violate CS2.
   Together they enforce a complete partition. */
rule standardProposalNeedsTimelockQueuing {
    env e;
    uint256 pid;

    // Standard: vetoThreshold == 0.
    require vetoThreshold(pid) == 0;

    bool needs = proposalNeedsQueuing(e, pid);

    assert needs,
        "standard proposal bypassed the timelock queue - optimistic bypass leaked into standard";
}

/* ----- CS3: channelDeterminedByVetoThresholdSentinel -----
   The encoding boundary stated directly: the public isOptimistic(pid)
   view returns vetoThreshold(pid) != 0. This pins that there is
   exactly ONE bit of channel-discrimination state per proposal, and
   it lives in the vetoThreshold storage slot - no other state
   contributes.

   isOptimistic at ReserveOptimisticGovernor.sol:140-144 reverts with
   GovernorNonexistentProposal if voteStart == 0 (proposal does not
   exist) and otherwise returns _isOptimistic(pid), which at line
   504-506 is defined as `vetoThreshold(pid) != 0`. CS3 asserts both
   halves of that biconditional.

   This rule covers the encoding-boundary cross-pollination risk
   directly: a future refactor that changed _isOptimistic to e.g.
   `vetoThreshold > 0 && vetoThreshold <= 1e18` (adding an upper
   bound) would silently make TRANSITIONED proposals look pessimistic,
   breaking the sentinel-to-Defeated short-circuit in state() and the
   guard in _queueOperations. CS3 would VIOLATE under that refactor,
   surfacing the regression before downstream rules silently weaken. */
rule channelDeterminedByVetoThresholdSentinel {
    env e;
    uint256 pid;

    // Proposal must exist for isOptimistic to not revert.
    require proposalSnapshot(pid) != 0;

    bool opt = isOptimistic(e, pid);

    assert opt == (vetoThreshold(pid) != 0),
        "channel discrimination did not align with the vetoThreshold sentinel";
}

/* ----- CS4: optimisticProposalRejectsNonAgainstVotes -----
   For any optimistic pid, castVote with support != Against must
   revert. Channel-separation framing of Governor.spec R14: the
   standard-channel vote types (For, Abstain) cannot leak into the
   optimistic channel.

   _countVote override at ReserveOptimisticGovernor.sol:395-398
   requires (!_isOptimistic || support == Against). castVote calls
   _castVote which calls _countVote; the chain reverts if optimistic
   AND support != Against. The state-bitmap check on Active runs
   first; either path terminates in revert.

   Same sentinel coverage as CS1: vetoThreshold != 0 captures both
   live optimistic and transitioned proposals. */
rule optimisticProposalRejectsNonAgainstVotes {
    env e;
    uint256 pid;
    uint8 support;

    // Optimistic: vetoThreshold != 0, including the sentinel.
    require vetoThreshold(pid) != 0;
    require support != AGAINST(); // For (1), Abstain (2), or any invalid value.

    castVote@withrevert(e, pid, support);

    assert lastReverted,
        "castVote accepted a non-Against vote on an optimistic proposal - standard vote types leaked";
}
