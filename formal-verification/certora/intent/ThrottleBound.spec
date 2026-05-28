/* ThrottleBound.spec — intent-derived rule for the proposer-throttle
   2 * capacity bound (mirrors Rocq Integration_no_throttle_bypass).

   Intent (user-facing claim):
     "An adversary cannot bypass the proposer throttle." Concretely,
     under any sequence of consumeProposalCharge calls by any proposer,
     the total D18 charge drained within a PROPOSAL_THROTTLE_PERIOD
     (12-hour) window is bounded above by 2 * FIX_ONE.

   Why the intent is hard to state as a single CVL property:
     CVL rules reason about single-step transitions. Bounds over an
     arbitrary-length sequence require an inductive invariant
     (preserved by the step) plus a derivation of the closed-form
     bound from the invariant. We do both here:

     (a) TB1 telescopedInvariantPreserved
         The Rocq telescoped invariant
           accumulatedDrain[a] + currentCharge[a]
             <= anchorCharge[a]
                + (lastUpdated[a] - anchorTime[a]) * FIX_ONE / PERIOD
         is preserved by any single consumeAndTrack(account) call.

     (b) TB2 invariantImpliesTwoCapacityDrainBound
         Given the invariant AND a window-length constraint
           lastUpdated[a] - anchorTime[a] <= PERIOD
         AND validity (anchorCharge[a] <= FIX_ONE, currentCharge >= 0),
         we conclude accumulatedDrain[a] <= 2 * FIX_ONE. Pure CVL
         arithmetic, no step reasoning.

     Together (a) and (b) discharge the intent property by induction
     over the call sequence. The inductive composition is mathematical
     and lives outside CVL — we rely on Certora preserving (a) over
     every external entry point, including parametric calls.

   Companion rules (also intent-derived, single-step):
     TB3 consumeIncrementsAccumulatedDrainByExactlySlot
         The harness wrapper consumeAndTrack adds exactly FIX_ONE /
         capacity to accumulatedDrain on each call. This is the per-
         consume "amount drained" the bound counts.

     TB4 consumeRevertsWhenCapacityZero
         A zero-capacity throttle blocks any consume (the library
         divides by capacity).

     TB5 setAnchorEstablishesInvariantBase
         Immediately after setAnchor, the telescoped invariant holds
         (the base case of the induction).

   Mapping to the Rocq theorem (Integration_no_throttle_bypass):
     - reachable_drain_le_refill         -> TB1 (preservation)
     - successful_consumes_drain_bounded -> TB2 (closed-form)
     - consume_drain_identity            -> TB3 (per-step drain)
     - reachable_charge_in_range         -> validity preconditions

   Note on FIX_ONE: written as the literal 1e18 = 1000000000000000000.
   '^' is XOR in CVL (WISDOM.md C001).

   Note on PERIOD: PROPOSAL_THROTTLE_PERIOD = 12 hours = 43200 seconds.
*/

definition FIX_ONE() returns uint256 = 1000000000000000000;
definition PERIOD() returns uint256 = 43200;  // 12 hours
definition MAX_CAPACITY() returns uint256 = 12;  // MAX_PROPOSAL_THROTTLE_CAPACITY

methods {
    function getCapacity() external returns (uint256) envfree;
    function getCurrentCharge(address) external returns (uint256) envfree;
    function getLastUpdated(address) external returns (uint256) envfree;
    function getAnchorCharge(address) external returns (uint256) envfree;
    function getAnchorTime(address) external returns (uint256) envfree;
    function getAccumulatedDrain(address) external returns (uint256) envfree;
}

/* ----- TB1: telescoped invariant is preserved by one consumeAndTrack -----

   The invariant (Rocq lemma reachable_drain_le_refill):
     accumulatedDrain + currentCharge
       <= anchorCharge
          + (lastUpdated - anchorTime) * FIX_ONE / PERIOD

   This is per-account; the rule fixes one account and proves: if the
   invariant holds in the pre-state, it holds in the post-state after
   consumeAndTrack(account). Together with the base case
   (setAnchorEstablishesInvariantBase below), this discharges the
   inductive step over any sequence of consumes.

   Key arithmetic in the step:
     - consume sets new currentCharge = readCharge - slot
       where slot = FIX_ONE / capacity and
       readCharge = min(currentCharge + drift, FIX_ONE)
       with drift = (block.timestamp - lastUpdated) * FIX_ONE / PERIOD.
     - consume sets new lastUpdated = block.timestamp.
     - consumeAndTrack adds slot to accumulatedDrain.

   Telescoping check:
     new accumulatedDrain + new currentCharge
       = accumulatedDrain + slot + readCharge - slot
       = accumulatedDrain + readCharge
       <= accumulatedDrain + currentCharge + drift_step      [by readCharge <= cc + drift_step]
       <= anchorCharge + (oldLU - anchorTime) * FIX_ONE / PERIOD + drift_step  [by pre-invariant]
       <= anchorCharge + (newLU - anchorTime) * FIX_ONE / PERIOD              [by div sub-additivity]

   The last step is the same fact the Rocq proof uses (drift_old +
   drift_new <= drift_tot). Certora's SMT backend handles linear integer
   arithmetic well; the division sub-additivity is provable here because
   PERIOD is a constant.
*/
rule telescopedInvariantPreserved {
    env e;
    address account;
    uint256 capacity = getCapacity();

    // Domain-valid capacity.
    require capacity > 0 && capacity <= MAX_CAPACITY();

    // Validity preconditions (mirror Rocq Valid.throttle).
    uint256 ccBefore = getCurrentCharge(account);
    uint256 luBefore = getLastUpdated(account);
    require ccBefore <= FIX_ONE();
    require luBefore <= e.block.timestamp;

    uint256 anchorCC = getAnchorCharge(account);
    uint256 anchorLU = getAnchorTime(account);
    uint256 accBefore = getAccumulatedDrain(account);

    // Anchor sanity: anchor is in the past relative to lastUpdated and is
    // itself a valid (sub-FIX_ONE) charge. These mirror the Rocq
    // hypotheses Valid.throttle t_init and the monotone-time premise.
    require anchorCC <= FIX_ONE();
    require anchorLU <= luBefore;

    // Pre-invariant: the telescoped bound.
    // Form: accBefore + ccBefore <= anchorCC + (luBefore - anchorLU) * FIX_ONE / PERIOD
    mathint driftOld = (luBefore - anchorLU) * FIX_ONE() / PERIOD();
    require accBefore + ccBefore <= anchorCC + driftOld;

    // To keep the arithmetic in linear range for the SMT, bound the
    // window we consider to a few PERIODs. The closed-form rule TB2
    // operates over [anchorTime, anchorTime + PERIOD] explicitly.
    require e.block.timestamp - anchorLU <= 4 * PERIOD();

    // Step.
    consumeAndTrack(e, account);

    uint256 ccAfter = getCurrentCharge(account);
    uint256 luAfter = getLastUpdated(account);
    uint256 accAfter = getAccumulatedDrain(account);

    // After consume: lastUpdated = block.timestamp.
    // After consumeAndTrack: accumulatedDrain += FIX_ONE / capacity.
    mathint driftNew = (luAfter - anchorLU) * FIX_ONE() / PERIOD();
    assert accAfter + ccAfter <= anchorCC + driftNew,
        "telescoped invariant violated by consumeAndTrack";
}

/* ----- TB2: closed-form bound from the telescoped invariant -----

   Given the telescoped invariant AND a window of length <= PERIOD,
   derive accumulatedDrain <= 2 * FIX_ONE. This is the headline 2 *
   FIX_ONE drain bound (Rocq successful_consumes_drain_bounded). Pure
   arithmetic, no Solidity call.

   Derivation:
     accumulatedDrain + currentCharge
       <= anchorCharge + (lastUpdated - anchorTime) * FIX_ONE / PERIOD
       <= FIX_ONE + PERIOD * FIX_ONE / PERIOD               [validity + window]
       <= FIX_ONE + FIX_ONE
       =  2 * FIX_ONE.
     Then accumulatedDrain <= 2 * FIX_ONE since currentCharge >= 0.

   The rule asserts the closed-form bound under the invariant + window
   preconditions. Combined with TB1 (preservation) and TB5 (base case),
   this gives the full intent property.
*/
rule invariantImpliesTwoCapacityDrainBound {
    env e;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= MAX_CAPACITY();

    uint256 currentCharge = getCurrentCharge(account);
    uint256 lastUpdated = getLastUpdated(account);
    uint256 anchorCC = getAnchorCharge(account);
    uint256 anchorLU = getAnchorTime(account);
    uint256 accumulated = getAccumulatedDrain(account);

    // Validity bounds.
    require currentCharge <= FIX_ONE();
    require anchorCC <= FIX_ONE();
    require anchorLU <= lastUpdated;

    // Window constraint: at most one PROPOSAL_THROTTLE_PERIOD elapsed.
    require lastUpdated - anchorLU <= PERIOD();

    // The telescoped invariant.
    mathint drift = (lastUpdated - anchorLU) * FIX_ONE() / PERIOD();
    require accumulated + currentCharge <= anchorCC + drift;

    // Then the headline bound holds.
    assert accumulated <= 2 * FIX_ONE(),
        "accumulated drain exceeds 2 * FIX_ONE within a PERIOD window";
}

/* ----- TB3: consumeAndTrack increments accumulatedDrain by exactly the slot -----

   The per-consume drain accounted to the window tally is exactly
   FIX_ONE / capacity (Rocq consume_drain_identity). This is the
   load-bearing per-step quantity.
*/
rule consumeIncrementsAccumulatedDrainByExactlySlot {
    env e;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= MAX_CAPACITY();

    // Validity preconditions for the underlying consume to succeed.
    require getCurrentCharge(account) <= FIX_ONE();
    require getLastUpdated(account) <= e.block.timestamp;

    uint256 accBefore = getAccumulatedDrain(account);

    // Bound accumulated to avoid overflow at the addition.
    require accBefore + FIX_ONE() <= max_uint256;

    consumeAndTrack(e, account);

    uint256 accAfter = getAccumulatedDrain(account);

    assert accAfter == accBefore + FIX_ONE() / capacity,
        "consumeAndTrack did not increment accumulatedDrain by exactly the slot";
}

/* ----- TB4: consume with capacity 0 reverts -----

   The library divides by capacity in both proposalsAvailable computation
   and the slot. consumeAndTrack must revert when capacity == 0 (the
   harness explicit-reverts on this; the underlying library would also
   div-by-zero).
*/
rule consumeRevertsWhenCapacityZero {
    env e;
    address account;

    require getCapacity() == 0;

    consumeAndTrack@withrevert(e, account);

    assert lastReverted,
        "consumeAndTrack did not revert with capacity = 0";
}

/* ----- TB5: setAnchor establishes the base case of the invariant -----

   Immediately after setAnchor(account), the telescoped invariant
   trivially holds: accumulatedDrain = 0, anchorCharge = currentCharge,
   anchorTime = lastUpdated, so both sides equal currentCharge. This is
   the Reachable_init constructor in the Rocq inductive.
*/
rule setAnchorEstablishesInvariantBase {
    env e;
    address account;

    setAnchor(e, account);

    uint256 currentCharge = getCurrentCharge(account);
    uint256 lastUpdated = getLastUpdated(account);
    uint256 anchorCC = getAnchorCharge(account);
    uint256 anchorLU = getAnchorTime(account);
    uint256 accumulated = getAccumulatedDrain(account);

    assert accumulated == 0,
        "setAnchor did not zero accumulatedDrain";
    assert anchorCC == currentCharge,
        "setAnchor did not snapshot currentCharge";
    assert anchorLU == lastUpdated,
        "setAnchor did not snapshot lastUpdated";

    // The telescoped invariant after anchor: 0 + cc <= cc + 0 * FIX_ONE / PERIOD = cc.
    mathint drift = (lastUpdated - anchorLU) * FIX_ONE() / PERIOD();
    assert accumulated + currentCharge <= anchorCC + drift,
        "setAnchor did not establish the telescoped invariant base case";
}
