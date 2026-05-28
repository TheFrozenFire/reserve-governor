// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import { ThrottleLib } from "contracts/governance/lib/ThrottleLib.sol";

/// @notice Intent-derived test harness for the proposer-throttle 2*capacity
/// bound (mirrors Rocq Integration_no_throttle_bypass.no_throttle_bypass).
///
/// This harness extends the ThrottleLib coverage with anchored ghost state
/// that records a "window start" snapshot (anchorCharge, anchorTime) and a
/// running tally of D18 charge consumed since that anchor
/// (accumulatedDrain).
///
/// The intent property — "the throttle cannot be consumed more than
/// 2 * capacity times in a PROPOSAL_THROTTLE_PERIOD window" — bottoms out
/// in two facts the harness exposes:
///   (a) per-consume drain = FIX_ONE / capacity (the slot)
///   (b) refill = (elapsed * FIX_ONE) / PERIOD, clipped at FIX_ONE
///
/// The telescoped invariant the Rocq proof maintains is
///
///   accumulatedDrain[a] + currentCharge[a]
///     <= anchorCharge[a]
///        + (lastUpdated[a] - anchorTime[a]) * FIX_ONE / PERIOD
///
/// which is per-state and per-account; it can be preserved by one external
/// call (one consumeProposalCharge). Once Certora confirms preservation,
/// the closed-form 2 * FIX_ONE drain bound (and 2 * capacity count bound
/// under FIX_ONE mod capacity = 0) follows from a CVL derivation that
/// pins (lastUpdated - anchorTime) <= PERIOD and uses the validity bounds
/// on currentCharge.
contract ThrottleBoundHarness {
    using ThrottleLib for ThrottleLib.ProposalThrottleStorage;

    ThrottleLib.ProposalThrottleStorage internal state;

    // ----- Anchor ghost state (per-account window tracking) -----
    // anchorCharge[a]: snapshot of throttles[a].currentCharge at anchor.
    // anchorTime[a]:   snapshot of throttles[a].lastUpdated at anchor.
    // accumulatedDrain[a]: D18 charge drained by consumes since anchor.
    mapping(address => uint256) public anchorCharge;
    mapping(address => uint256) public anchorTime;
    mapping(address => uint256) public accumulatedDrain;

    // ----- Library wrappers -----

    /// @notice Consume one proposal charge AND increment accumulatedDrain by
    /// the per-consume slot (FIX_ONE / capacity). This is the only path that
    /// drains an account in the harness, so accumulatedDrain stays in sync
    /// with the on-chain charge for any rule using this surface.
    function consumeAndTrack(address account) external {
        uint256 capacity = state.capacity;
        // Mirror the library's revert-on-zero so the slot computation here
        // can't underflow even in degenerate test states.
        require(capacity > 0, "capacity zero");
        state.consumeProposalCharge(account);
        accumulatedDrain[account] = accumulatedDrain[account] + (1e18 / capacity);
    }

    /// @notice Plain consume (without tally update). Useful for rules that
    /// want to test consume-only behavior with no window framing.
    function consumeProposalCharge(address account) external {
        state.consumeProposalCharge(account);
    }

    /// @notice Record the current (charge, lastUpdated) snapshot as the
    /// window anchor and zero the accumulated drain. Calling this from a
    /// CVL rule pins the "start of window" semantics.
    function setAnchor(address account) external {
        anchorCharge[account] = state.throttles[account].currentCharge;
        anchorTime[account] = state.throttles[account].lastUpdated;
        accumulatedDrain[account] = 0;
    }

    function getProposalsAvailable(address account) external view returns (uint256) {
        return state.getProposalsAvailable(account);
    }

    // ----- Storage accessors -----

    function getCapacity() external view returns (uint256) {
        return state.capacity;
    }

    function setCapacity(uint256 newCapacity) external {
        state.capacity = newCapacity;
    }

    function getCurrentCharge(address account) external view returns (uint256) {
        return state.throttles[account].currentCharge;
    }

    function getLastUpdated(address account) external view returns (uint256) {
        return state.throttles[account].lastUpdated;
    }

    function setThrottle(address account, uint256 currentCharge, uint256 lastUpdated) external {
        state.throttles[account].currentCharge = currentCharge;
        state.throttles[account].lastUpdated = lastUpdated;
    }

    function getAnchorCharge(address account) external view returns (uint256) {
        return anchorCharge[account];
    }

    function getAnchorTime(address account) external view returns (uint256) {
        return anchorTime[account];
    }

    function getAccumulatedDrain(address account) external view returns (uint256) {
        return accumulatedDrain[account];
    }
}
