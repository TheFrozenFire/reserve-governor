// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import { ThrottleLib } from "contracts/governance/lib/ThrottleLib.sol";

/// @notice Test harness exposing ThrottleLib for Certora verification.
///
/// ThrottleLib is a Solidity library; libraries have no storage of their
/// own and are not directly verifiable. This harness owns a
/// ProposalThrottleStorage slot and provides external accessors for both
/// the library functions and the underlying state, so CVL rules can
/// observe state.charge / state.lastUpdated before and after each call.
contract ThrottleLibHarness {
    using ThrottleLib for ThrottleLib.ProposalThrottleStorage;

    ThrottleLib.ProposalThrottleStorage internal state;

    // ----- Library wrappers -----

    function consumeProposalCharge(address account) external {
        state.consumeProposalCharge(account);
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
}
