/* CrossDomainAndActorSet.spec -- S26 (cross-domain validation) and
   S27 (wrong-actor-set check) intent rules for
   ReserveOptimisticGovernor.sol.

   Catalog entries:
     notes/governance_intent_and_shapes.md, S26 and S27.
     notes/cantina_pr36_postmortem.md (the original wrong-population catch).
     notes/same_shape_hunt.md F5 (S27 reference).

   The workhorse here is the two-ghost divergence pattern (WISDOM
   C017): summarize two related external reads to *distinct* ghost
   mappings and constrain them to disagree, then assert the contract
   reads the intended one. The wildcard NONDET form is BLIND to which
   method the contract called; two ghosts make the choice observable.

   --- S26 (cross-domain validation) ---

   Property:  proposalThreshold() returns a {tok} quantity that
              scales linearly with token().getPastTotalSupply(t).
              The function multiplies a D18 fraction by a {tok}
              supply; if a refactor accidentally compared the D18
              fraction directly against votes (a cross-domain
              confusion), the returned value would NOT scale with
              supply.

   CVL form:  Two ghost mappings over the same snapshot timepoint.
              First call to proposalThreshold reads the ghost as S1;
              we vary the ghost to S2 and read again; assert the
              ratio of returned values equals the ratio of supplies
              (modulo the +1 floor / ceil-1 rounding).

   The two-ghost split here is between "supply as {tok}" and "supply
   used as a bare integer in a cross-domain comparison". If the code
   ever drops the supply multiplication, the return value becomes
   constant in supply and the dimensional scaling test fails.

   --- S27 (wrong-actor-set check) ---

   Property:  castVote on an optimistic proposal credits exactly
              getPastOptimisticVotes(account, snapshot) toward
              againstVotes -- NOT getPastVotes(account, snapshot).
              The actor set for optimistic vetoes is the opted-in
              optimistic-delegated population, not the standard
              delegated population.

   CVL form:  Two ghost mappings, one per external read. Force them
              to disagree at the same (account, snapshot) pair.
              Call castVote(pid, AGAINST). Assert that the delta in
              againstVotes equals the OPTIMISTIC ghost reading,
              regardless of the PAST-VOTES ghost reading.

   This is the per-account analogue of the Cantina catch. The
   structural shape is identical (two populations, contract picks
   one); the difference is per-account semantics (vote weight) vs
   per-supply semantics (threshold denominator).

   --- Companion sanity rules ---

   For each headline rule, a sister-VIOLATED-is-healthy rule
   demonstrates that the precondition is satisfiable (per WISDOM
   C002). A vacuous headline silently passes; the sister assert
   false makes precondition reachability explicit.

   See:
     - WISDOM C001 ('^' is XOR; use 1e18 = 10^18 literal)
     - WISDOM C002 (sanity check via assert false)
     - WISDOM C015 (ghost-backed external summaries)
     - WISDOM C017 (two-ghost-divergence pattern)
*/

/* WAD = 1e18. CVL has no '**'; '^' is XOR (WISDOM C001). */
definition WAD() returns uint256 = 1000000000000000000;

/* IGovernor.ProposalState enum, ABI-encoded as uint8.
   0=Pending 1=Active 2=Canceled 3=Defeated
   4=Succeeded 5=Queued 6=Expired 7=Executed */
definition ACTIVE() returns uint8 = 1;

/* GovernorCountingSimple.VoteType, ABI-encoded as uint8.
   0=Against 1=For 2=Abstain */
definition AGAINST() returns uint8 = 0;

/* === Two-ghost cross-domain / wrong-actor-set summaries ===

   ghostPastTotalSupply        - {tok}, the legacy denominator
   ghostPastOptimisticSupply   - {tok}, the opted-in denominator
   ghostPastVotes              - {tok}, per-account legacy weight
   ghostPastOptimisticVotes    - {tok}, per-account opted-in weight

   Each external read maps to ONE ghost. Constraints in each rule
   force the two related ghosts to disagree, so the contract's
   choice of which to read is observable. */
ghost mapping(uint256 => uint256) ghostPastTotalSupply;
ghost mapping(uint256 => uint256) ghostPastOptimisticSupply;
ghost mapping(address => mapping(uint256 => uint256)) ghostPastVotes;
ghost mapping(address => mapping(uint256 => uint256)) ghostPastOptimisticVotes;

methods {
    // Envfree readers.
    function proposalThreshold() external returns (uint256);
    function vetoThreshold(uint256) external returns (uint256) envfree;
    function proposalSnapshot(uint256) external returns (uint256) envfree;
    function proposalVotes(uint256) external returns (uint256, uint256, uint256) envfree;
    function hasVoted(uint256, address) external returns (bool) envfree;
    function timelock() external returns (address) envfree;

    // === Ghost-backed external summaries (WISDOM C015, C017) ===
    function _.getPastTotalSupply(uint256 ts) external =>
        ghostPastTotalSupply[ts] expect uint256;
    function _.getPastOptimisticVotingSupply(uint256 ts) external =>
        ghostPastOptimisticSupply[ts] expect uint256;
    function _.getPastVotes(address a, uint256 ts) external =>
        ghostPastVotes[a][ts] expect uint256;
    function _.getPastOptimisticVotes(address a, uint256 ts) external =>
        ghostPastOptimisticVotes[a][ts] expect uint256;

    // Other external calls: NONDET (the rules do not depend on them).
    function _.clock() external => NONDET;
    function _.CLOCK_MODE() external => NONDET;
    function _.hasRole(bytes32, address) external => NONDET;
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
    function _.isAllowed(address, bytes4) external => NONDET;

    // Library delegatecalls.
    function _.consumeProposalCharge(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.getProposalsAvailable(ThrottleLib.ProposalThrottleStorage storage, address) external => NONDET;
    function _.proposeOptimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage, IReserveOptimisticGovernor.OptimisticGovernanceParams) external => NONDET;
    function _.proposePessimistic(ProposalLib.ProposalData, GovernorUpgradeable.ProposalCore storage) external => NONDET;
    function _.transitionToPessimistic(uint256, IReserveOptimisticGovernor.OptimisticProposalDetails storage, mapping(uint256 => GovernorUpgradeable.ProposalCore) storage) external => NONDET;
}

/* ============================================================
   S26 -- CROSS-DOMAIN VALIDATION

   Headline:  proposalThreshold() is a {tok} quantity computed as
              ceil(proposalThresholdRatio * supply / 1e18).
              The {tok} return value MUST scale linearly with
              supply -- a refactor that compared the D18 fraction
              directly to votes (e.g. dropped the supply multiply)
              would still typecheck but would break dimensional
              scaling.

   Bug shape: if proposalThreshold() returned a value that did NOT
              scale with supply, callers comparing
              proposerVotes >= proposalThreshold()
              would be enforcing a fixed bound regardless of token
              supply -- a cross-domain confusion. ProposalLib at
              line 83 does exactly that comparison.
   ============================================================ */

/* ----- S26.1 HEADLINE: proposalThreshold scales linearly with supply.

   We capture proposalThreshold at two configurations of the same
   ghost. CVL evaluates the function in the current state, where
   the ghost-backed supply read returns whatever the ghost holds.
   To make this a comparative observation we pin two distinct
   timepoints (block.timestamp - 1) values via two env's, and use
   the ratio invariant:

       thr(s1) * s2 ~ thr(s2) * s1     (linear in supply)

   with ~ accounting for the +1 floor (`Math.max(1, supply)`) and
   the CEIL rounding (`+ (1e18 - 1)) / 1e18`).

   We sidestep the floor/ceil by constraining s1, s2 large enough
   that the floor is inactive (supply >= 1) and the CEIL adds
   at most 1 tok. The linearity assertion is then bounded by an
   error <= 1 on each side.
*/
rule proposalThresholdScalesLinearlyWithSupply {
    env e1; env e2;

    // Both envs share msg.sender / msg.value to isolate the supply
    // change as the only varying input. block.timestamp differs --
    // proposalThreshold reads block.timestamp - 1 as the
    // snapshot, so distinct timestamps give distinct ghost reads.
    require e1.msg.sender == e2.msg.sender;
    require e1.msg.value == 0 && e2.msg.value == 0;
    require e1.block.timestamp != e2.block.timestamp;
    require e1.block.timestamp >= 1 && e2.block.timestamp >= 1;

    uint256 ts1 = require_uint256(e1.block.timestamp - 1);
    uint256 ts2 = require_uint256(e2.block.timestamp - 1);

    // Pin distinct timestamps so the ghost keys differ.
    require ts1 != ts2;

    uint256 s1 = ghostPastTotalSupply[ts1];
    uint256 s2 = ghostPastTotalSupply[ts2];

    // Floor inactive: supply >= 1 on both sides so Math.max(1, ...)
    // is the identity. Without this, supplies of 0 collapse to 1
    // and the linearity claim becomes nonlinear at the boundary.
    require s1 >= 1 && s2 >= 1;

    // Tame the search space (avoid solver overflow shrapnel).
    // The proposer-threshold-ratio R is the same across calls
    // because it is stored once in `_proposalThreshold`. Bound the
    // supplies so R * s + (WAD-1) fits in uint256 comfortably.
    require s1 <= 1000000000000000000000000000;  // 1e27 tok
    require s2 <= 1000000000000000000000000000;

    uint256 thr1 = proposalThreshold(e1);
    uint256 thr2 = proposalThreshold(e2);

    // Linearity check (with CEIL rounding tolerance of 1 each side).
    //   thr_i = ceil(R * s_i / WAD)
    //   thr_i * WAD - (R * s_i) is in [0, WAD-1]
    // Cross-multiplying:
    //   thr1 * s2 == thr2 * s1  (within rounding bands)
    //
    // The exact bound is:
    //   | thr1 * s2 - thr2 * s1 | <= (s1 + s2)
    // because each ceil error <= 1 contributes a factor of s2 or s1
    // when cross-multiplied. (Stricter: error <= 1 tok, when
    // cross-multiplied with the other supply, error <= s.)
    mathint lhs = to_mathint(thr1) * to_mathint(s2);
    mathint rhs = to_mathint(thr2) * to_mathint(s1);
    mathint diff = lhs - rhs;
    mathint bound = to_mathint(s1) + to_mathint(s2);

    assert diff <= bound && (-diff) <= bound,
        "proposalThreshold did not scale linearly with supply -- possible cross-domain bug (D18 fraction compared without supply multiply)";
}

/* ----- S26.2 SANITY: the linearity precondition is satisfiable.
   VIOLATED here is the healthy outcome (WISDOM C002). */
rule sanityS26PreconditionSatisfiable {
    env e1; env e2;
    require e1.msg.sender == e2.msg.sender;
    require e1.msg.value == 0 && e2.msg.value == 0;
    require e1.block.timestamp != e2.block.timestamp;
    require e1.block.timestamp >= 1 && e2.block.timestamp >= 1;

    uint256 ts1 = require_uint256(e1.block.timestamp - 1);
    uint256 ts2 = require_uint256(e2.block.timestamp - 1);
    require ts1 != ts2;

    uint256 s1 = ghostPastTotalSupply[ts1];
    uint256 s2 = ghostPastTotalSupply[ts2];
    require s1 >= 1 && s2 >= 1;
    require s1 <= 1000000000000000000000000000;
    require s2 <= 1000000000000000000000000000;

    proposalThreshold(e1);
    proposalThreshold(e2);

    assert false, "S26 sanity: precondition reachable (VIOLATED here is healthy)";
}

/* ============================================================
   S27 -- WRONG-ACTOR-SET CHECK (PER-ACCOUNT VARIANT)

   Headline:  castVote(pid, AGAINST) on an optimistic proposal
              credits exactly getPastOptimisticVotes(account, snapshot)
              to againstVotes -- NOT getPastVotes(account, snapshot).

   Two-ghost catch: pin
       ghostPastVotes[account][snapshot]            = X (random)
       ghostPastOptimisticVotes[account][snapshot]  = Y (random, Y != X)
   Force divergence, run castVote, assert
       againstVotes_after - againstVotes_before == Y.

   If a refactor accidentally swapped to `getPastVotes` for
   optimistic proposals, the delta would equal X, not Y, and the
   rule would VIOLATE.

   This is the per-account analogue of the Cantina catch. The
   structural shape is identical (two related populations, contract
   picks one); the difference is per-account semantics (vote
   weight) vs per-supply semantics (threshold denominator).
   ============================================================ */

/* ----- S27.1 HEADLINE: castVote on optimistic proposal credits
        getPastOptimisticVotes, not getPastVotes.

   Solver-budget shaping (per WISDOM C011/C022): the post-state of
   _castVote runs _tallyUpdated, which invokes state() and possibly
   ProposalLib.transitionToPessimistic. The state() computation
   reads getPastTotalSupply, computes vetoThresholdTok, and the
   threshold-vs-votes comparison branches into transitionToPessimistic
   for the Defeated case. Letting the prover explore all of those
   branches yields a path count ~2^67. We prune by constraining the
   post-vote state to stay Active (against < threshold), which kills
   the transitionToPessimistic dispatch path. The rule remains
   sound: the property tests the WEIGHT CREDITING in _countVote,
   which fires before _tallyUpdated; the post-tally branches do
   not affect the againstVotes counter that the assertion reads. */
rule castVoteOptimisticReadsOptimisticVotes {
    env e;
    uint256 pid;
    uint8 support;

    // The proposal under observation is optimistic (vetoThreshold
    // is set and not the transitioned sentinel). Equivalent to
    // _isOptimistic returning true under a real-supply construction.
    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt < 1000000000000000000000000000000000000;  // exclude sentinel
    require vt <= WAD();                                  // construction invariant

    // Force the optimistic branch in _castVote: support == Against.
    // _countVote rejects non-Against on optimistic proposals so the
    // headline only meaningfully tests Against votes.
    require support == AGAINST();

    // Caller has not voted yet (else _countVote reverts).
    require !hasVoted(pid, e.msg.sender);

    // Snapshot is set (proposal exists) and in the past so
    // _validateStateBitmap(Active) can be satisfied.
    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    // === Two-ghost divergence (WISDOM C017) ===
    // Pin the two related reads at (account, snapshot) to disagree.
    // The contract MUST read the OPTIMISTIC ghost on the optimistic
    // branch; that ghost's value is the credited weight.
    uint256 optWeight = ghostPastOptimisticVotes[e.msg.sender][snapshot];
    uint256 pastWeight = ghostPastVotes[e.msg.sender][snapshot];

    // Force divergence -- otherwise the rule cannot distinguish the
    // two reads. The wildcard-NONDET pre-fix Certora setup was blind
    // here because both reads collapsed to a single fresh choice.
    require optWeight != pastWeight;

    // Tame the search: keep weights bounded so the accumulator does
    // not overflow and the threshold-vs-tally math stays linear.
    require optWeight <= 1000000000000;     // 1e12 tok
    require pastWeight <= 1000000000000;

    // Pre-state: read againstVotes.
    uint256 againstBefore;
    uint256 forBefore;
    uint256 abstainBefore;
    againstBefore, forBefore, abstainBefore = proposalVotes(pid);

    // Headroom for the accumulator add.
    require againstBefore <= 1000000000000;

    // === Path-pruning preconditions ===
    //
    // The post-state of _castVote runs _tallyUpdated -> state(),
    // which reads getPastTotalSupply and compares againstVotes to
    // vetoThresholdTok. Let the supply be huge and the threshold
    // proportionally huge so the post-vote tally stays well below
    // the Defeated threshold. This prunes the transitionToPessimistic
    // dispatch entirely.
    uint256 supplyAtSnapshot = ghostPastTotalSupply[snapshot];
    require supplyAtSnapshot >= 1000000000000000000000000;  // 1e24 tok
    require supplyAtSnapshot <= 1000000000000000000000000000;  // 1e27 tok

    // vetoThresholdTok = max((vt * supplyAtSnapshot) / 1e18, 1).
    // With vt >= 1 (since vt != 0) and supplyAtSnapshot >= 1e24,
    // vetoThresholdTok >= 1e6 -- and we keep votes <= 1e12. To
    // guarantee threshold > all-vote-sum, force vt high enough:
    require vt >= 1000000;  // vt >= 1e6 (in D18), so vt*supply/1e18 >= 1e12
    // Now vetoThresholdTok = vt*supplyAtSnapshot/1e18
    //                     >= 1e6 * 1e24 / 1e18 = 1e12,
    // and againstBefore + optWeight <= 2e12. We need a healthier
    // margin -- bump vt up by another factor of 10:
    require vt >= 10000000;  // 1e7 -> threshold >= 1e13, margin 10x

    castVote(e, pid, support);

    // Post-state.
    uint256 againstAfter;
    uint256 forAfter;
    uint256 abstainAfter;
    againstAfter, forAfter, abstainAfter = proposalVotes(pid);

    // The delta MUST equal the optimistic-ghost value, not the
    // past-votes-ghost value. If the contract read the WRONG ghost
    // for the optimistic branch, this assertion VIOLATES.
    assert to_mathint(againstAfter) - to_mathint(againstBefore)
           == to_mathint(optWeight),
        "castVote on optimistic proposal credited the wrong actor-set's weight";
}

/* ----- S27.2 SANITY: castVote precondition is satisfiable.
   VIOLATED here is healthy (WISDOM C002). Mirrors the headline's
   path-pruning preconditions so both rules share the same
   reachability profile. */
rule sanityS27PreconditionSatisfiable {
    env e;
    uint256 pid;
    uint8 support;

    uint256 vt = vetoThreshold(pid);
    require vt != 0;
    require vt < 1000000000000000000000000000000000000;
    require vt <= WAD();
    require vt >= 10000000;
    require support == AGAINST();
    require !hasVoted(pid, e.msg.sender);

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 optWeight = ghostPastOptimisticVotes[e.msg.sender][snapshot];
    uint256 pastWeight = ghostPastVotes[e.msg.sender][snapshot];
    require optWeight != pastWeight;
    require optWeight <= 1000000000000;
    require pastWeight <= 1000000000000;

    uint256 againstBefore;
    uint256 forBefore;
    uint256 abstainBefore;
    againstBefore, forBefore, abstainBefore = proposalVotes(pid);
    require againstBefore <= 1000000000000;

    uint256 supplyAtSnapshot = ghostPastTotalSupply[snapshot];
    require supplyAtSnapshot >= 1000000000000000000000000;
    require supplyAtSnapshot <= 1000000000000000000000000000;

    castVote(e, pid, support);

    assert false, "S27 sanity: precondition reachable (VIOLATED here is healthy)";
}

/* ----- S27.3 NEGATIVE / SISTER: the dual property under a
   pessimistic proposal would credit getPastVotes, not
   getPastOptimisticVotes. Encoded as the SAME headline but pinned
   to a non-optimistic proposal (vetoThreshold == 0). Documents
   that the auth-discriminator is exactly _isOptimistic == false
   on the alternate branch.

   VERIFIED here documents the dual: castVote on a pessimistic
   proposal correctly reads getPastVotes (the standard actor set).
*/
rule castVotePessimisticReadsPastVotes {
    env e;
    uint256 pid;
    uint8 support;

    // The proposal is pessimistic: vetoThreshold == 0 -> _isOptimistic
    // returns false.
    uint256 vt = vetoThreshold(pid);
    require vt == 0;

    // Pessimistic proposals accept any VoteType (Against / For /
    // Abstain). Pin Against for parity with the optimistic rule.
    require support == AGAINST();
    require !hasVoted(pid, e.msg.sender);

    uint256 snapshot = proposalSnapshot(pid);
    require snapshot != 0;
    require snapshot < e.block.timestamp;

    uint256 optWeight = ghostPastOptimisticVotes[e.msg.sender][snapshot];
    uint256 pastWeight = ghostPastVotes[e.msg.sender][snapshot];
    require optWeight != pastWeight;
    require optWeight < 1000000000000000000000000000;
    require pastWeight < 1000000000000000000000000000;

    uint256 againstBefore;
    uint256 forBefore;
    uint256 abstainBefore;
    againstBefore, forBefore, abstainBefore = proposalVotes(pid);
    require to_mathint(againstBefore) + to_mathint(pastWeight) <= max_uint256;

    castVote(e, pid, support);

    uint256 againstAfter;
    uint256 forAfter;
    uint256 abstainAfter;
    againstAfter, forAfter, abstainAfter = proposalVotes(pid);

    assert to_mathint(againstAfter) - to_mathint(againstBefore)
           == to_mathint(pastWeight),
        "castVote on pessimistic proposal credited the optimistic actor-set's weight -- mirror of S27 catch";
}
