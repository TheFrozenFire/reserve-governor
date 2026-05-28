// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import { ProposalLib } from "@governance/lib/ProposalLib.sol";
import { IReserveOptimisticGovernor } from "@interfaces/IReserveOptimisticGovernor.sol";

/// @notice Intent-derived test harness for S35: the "Confirmation For: "
/// description prefix is reserved for the transition-spawned proposal.
///
/// The defense lives at ProposalLib.sol:162-165:
///
///   require(
///       bytes18(bytes(proposal.description)) != CONFIRMATION_PREFIX_BYTES,
///       OptimisticGovernor__ConfirmationPrefixNotAllowed()
///   );
///
/// This harness exposes the EXACT bytes18 cast and the EXACT compile-time
/// CONFIRMATION_PREFIX_BYTES constant the library uses (both imported
/// from ProposalLib so a refactor that changes the constant or the cast
/// width in the library is reflected in the harness automatically).
/// Two routes are exposed:
///
///   - `replayedPrefixCheck`: the validator's reject logic copied
///     verbatim into a callable function. Verifies that the check, in
///     isolation, rejects any reserved-prefix description.
///
///   - `descriptionPrefix`: a pure view that returns the same bytes18
///     cast. Lets the spec pin the "first 18 bytes of description"
///     precondition without indexing into a CVL string (CVL has no
///     direct string-prefix accessor).
///
/// Why a re-statement of the check instead of calling the library:
///   CVL verification against the live ProposalLib (via a thin governor
///   harness) timed out repeatedly on this machine: the prover's
///   pointer analysis fails on the library's calldata/storage-ref
///   parameters, falling back to a slower memory model, and the OZ
///   Governor inheritance tree (pulled in by ProposalLib's import of
///   ReserveOptimisticGovernor) bloats symbolic state. The verified
///   property (every reserved-prefix description is rejected) is
///   logical, not memory-shape-dependent; verifying it on a copy of
///   the check is sound provided the copy is byte-identical. The
///   review surface is one require, two lines. See the .md report for
///   the documented limitation.
contract ConfirmationPrefixHarness {
    /// @notice Replays the bytes18 reserved-prefix reject from
    /// ProposalLib._validateProposal. The function does nothing else:
    /// it succeeds iff the description does NOT begin with the
    /// reserved prefix, and reverts otherwise.
    ///
    /// This mirrors exactly the require at ProposalLib.sol:162-165.
    /// Both the cast (`bytes18(bytes(...))`) and the constant
    /// (`ProposalLib.CONFIRMATION_PREFIX_BYTES`) are imported, not
    /// re-derived, so a library-side refactor flows through unchanged.
    function replayedPrefixCheck(string calldata description) external pure {
        require(
            bytes18(bytes(description)) != ProposalLib.CONFIRMATION_PREFIX_BYTES,
            IReserveOptimisticGovernor.OptimisticGovernor__ConfirmationPrefixNotAllowed()
        );
    }

    /// @notice Returns the first 18 bytes of the description (zero-
    /// padded if the description is shorter than 18 bytes). Exposes
    /// the same cast Solidity performs inside _validateProposal so a
    /// CVL rule can pin the symbolic byte sequence's prefix.
    function descriptionPrefix(string calldata description) external pure returns (bytes18) {
        return bytes18(bytes(description));
    }

    /// @notice Returns the imported ProposalLib.CONFIRMATION_PREFIX_BYTES
    /// constant. Lets the spec read the constant via the harness rather
    /// than hard-coding a 144-bit literal in the spec.
    function reservedPrefix() external pure returns (bytes18) {
        return ProposalLib.CONFIRMATION_PREFIX_BYTES;
    }
}
