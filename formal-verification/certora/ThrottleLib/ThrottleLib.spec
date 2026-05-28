/* ThrottleLib Certora spec — covers the proposal-throttle math library
   wrapped by a harness contract (ThrottleLibHarness.sol).

   Triple-confirmation target. The headline T1 rule mirrors INV-2 from
   the Rocq proof at formal-verification/rocq/proofs/ProposerThrottle.v
   (audit_throttle_consume_storage_delta) and INV-2 from the CAS witness
   at formal-verification/cas/proposer_throttle/charge_evolution.gp.
   Certora's role is to confirm solc-0.8.28 did not change the integer
   divide direction of the FIX_ONE / capacity slot that the headline
   "2 * capacity" worst-case bound depends on.

   Properties proved:
     T1   consumeStorageDelta:
            after a successful consumeProposalCharge(account):
              currentCharge[account] decreases by exactly FIX_ONE / capacity
              lastUpdated[account]   becomes block.timestamp
     T2   refillLinearity:
            getProposalsAvailable is non-decreasing in block.timestamp
            (proxy for the read-side time-decayed refill).
     T3   exhaustedReverts:
            consumeProposalCharge reverts when proposalsAvailable < 1.
     T4   chargeCappedAfterConsume:
            after consume, currentCharge[account] <= FIX_ONE.
     T5   capacityWriteVisible:
            setCapacity persists the new capacity.

   Notes on CVL form:
     - FIX_ONE is 1e18, written as the literal 1000000000000000000 (CVL
       has no '**', and '^' is XOR — WISDOM.md C001).
     - The library reads block.timestamp internally for the consume
       write to .lastUpdated, so the CVL env must thread the same e.block.timestamp.
*/

definition FIX_ONE() returns uint256 = 1000000000000000000;

methods {
    function getCapacity() external returns (uint256) envfree;
    function getCurrentCharge(address) external returns (uint256) envfree;
    function getLastUpdated(address) external returns (uint256) envfree;
}

/* ----- T1: consume's storage delta is exact (headline triple-conf) -----
   After a successful consumeProposalCharge(account):
     new currentCharge[account] = old read-side charge - FIX_ONE / capacity
     new lastUpdated[account]   = e.block.timestamp

   The "old read-side charge" is the value of (currentCharge after
   time-decayed refill, clipped to FIX_ONE) that the library computes
   internally. We cannot observe it directly because it's a local — but
   we CAN observe getProposalsAvailable(account), and the storage
   delta on currentCharge is equivalent to:

     new currentCharge = (old_charge_after_refill) - slot

   The cleanest CVL form is to assert the equality between:
     (a) the change in currentCharge, and
     (b) (charge_seen_by_consume) - slot

   where charge_seen_by_consume is recovered via getProposalsAvailable
   times FIX_ONE / capacity. But that loses precision because of the
   division-then-multiplication. Instead, we pin a specific initial
   state (currentCharge already in [slot, FIX_ONE], lastUpdated == now,
   so the refill is zero) — then the read-side charge equals the stored
   currentCharge, and we can assert the delta exactly.

   This corresponds to Rocq's consume_success_storage_delta lemma with
   readCharge t now = t.currentCharge (the zero-elapsed-time case).
*/
rule consumeStorageDelta {
    env e;
    address account;
    uint256 capacity = getCapacity();

    // Domain-valid capacity (non-zero, within MAX_PROPOSAL_THROTTLE_CAPACITY).
    require capacity > 0 && capacity <= 12;

    mathint slot = FIX_ONE() / capacity;

    // Pin lastUpdated to now so the refill term is zero. Then the
    // read-side charge equals the stored currentCharge directly.
    uint256 chargeBefore = getCurrentCharge(account);
    require getLastUpdated(account) == e.block.timestamp;
    require chargeBefore <= FIX_ONE();
    // Must have at least one proposal available, otherwise consume reverts.
    // ProposalsAvailable = (capacity * chargeBefore) / FIX_ONE >= 1
    // i.e. capacity * chargeBefore >= FIX_ONE.
    require capacity * chargeBefore >= FIX_ONE();

    consumeProposalCharge(e, account);

    mathint chargeAfter = getCurrentCharge(account);
    uint256 lastUpdatedAfter = getLastUpdated(account);

    assert chargeAfter == chargeBefore - slot,
        "consume did not decrement currentCharge by exactly FIX_ONE / capacity";
    assert lastUpdatedAfter == e.block.timestamp,
        "consume did not set lastUpdated to block.timestamp";
}

/* ----- T2: refill monotonicity in block.timestamp -----
   getProposalsAvailable is monotonically non-decreasing in block.timestamp
   when storage (currentCharge, lastUpdated, capacity) is held fixed.
   This corresponds to the Mono lemma in the Rocq proof
   (readCharge non-decreasing in now) lifted through proposalsAvailable.

   We call getProposalsAvailable with two different envs against the same
   storage and assert later-timestamp >= earlier-timestamp.
*/
rule refillMonotone {
    env e1;
    env e2;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= 12;
    // Storage well-formed: currentCharge <= FIX_ONE.
    require getCurrentCharge(account) <= FIX_ONE();
    // lastUpdated <= both timestamps (block time doesn't run backwards).
    require getLastUpdated(account) <= e1.block.timestamp;
    require e1.block.timestamp <= e2.block.timestamp;

    uint256 availEarly = getProposalsAvailable(e1, account);
    uint256 availLate  = getProposalsAvailable(e2, account);

    assert availLate >= availEarly,
        "getProposalsAvailable decreased with advancing block.timestamp";
}

/* ----- T3: consume reverts when no proposal available -----
   If proposalsAvailable < 1 the consume must revert. This is the
   guarded transition condition from ThrottleLib.sol L20.
*/
rule exhaustedReverts {
    env e;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= 12;

    // Pin lastUpdated to now so no refill applies.
    require getLastUpdated(account) == e.block.timestamp;
    // currentCharge well-formed.
    uint256 ccBefore = getCurrentCharge(account);
    require ccBefore <= FIX_ONE();
    // Force proposalsAvailable < 1: (capacity * ccBefore) / FIX_ONE == 0
    // i.e. capacity * ccBefore < FIX_ONE.
    require capacity * ccBefore < FIX_ONE();

    consumeProposalCharge@withrevert(e, account);

    assert lastReverted,
        "consume succeeded with proposalsAvailable < 1";
}

/* ----- T4: currentCharge stays <= FIX_ONE after consume -----
   The library writes currentCharge = readCharge - slot, where readCharge
   is clipped to FIX_ONE. So the post-state charge cannot exceed FIX_ONE.
*/
rule chargeCappedAfterConsume {
    env e;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= 12;
    // Storage well-formed pre.
    require getCurrentCharge(account) <= FIX_ONE();
    require getLastUpdated(account) <= e.block.timestamp;

    consumeProposalCharge(e, account);

    assert getCurrentCharge(account) <= FIX_ONE(),
        "consume left currentCharge > FIX_ONE";
}

/* ----- T5: setCapacity persists ----- */
rule capacityWriteVisible {
    env e;
    uint256 newCapacity;

    setCapacity(e, newCapacity);

    assert getCapacity() == newCapacity,
        "setCapacity did not persist";
}

/* ----- T6: getProposalsAvailable bounded by capacity -----
   Cap lemma from Rocq: proposalsAvailable <= capacity for any state.
*/
rule proposalsAvailableBoundedByCapacity {
    env e;
    address account;
    uint256 capacity = getCapacity();

    require capacity > 0 && capacity <= 12;
    require getCurrentCharge(account) <= FIX_ONE();
    require getLastUpdated(account) <= e.block.timestamp;

    uint256 avail = getProposalsAvailable(e, account);

    assert avail <= capacity,
        "getProposalsAvailable exceeded capacity";
}
