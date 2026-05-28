// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import { IGovernor } from "@openzeppelin/contracts/governance/IGovernor.sol";

/// @notice Intent-derived test harness for the propose-vs-cancel state-machine
/// asymmetry (S18) in ReserveOptimisticGovernor.
///
/// The on-chain `_validateCancel` function at
/// `contracts/governance/ReserveOptimisticGovernor.sol:374-388` reads
/// `vetoThreshold(proposalId) != 0` (the optimistic discriminator),
/// `proposalProposer(proposalId)`, and `state(proposalId)` (the OZ +
/// optimistic-override state machine). Driving the full cancel() entry from
/// CVL drags in OZ's _validateStateBitmap, the timelock's cancel hooks, and
/// the state() override's external token reads -- all of which the prover
/// havocs aggressively, defeating attempts to pin `state == Active` via
/// require.
///
/// This harness replays the exact decision rule of `_validateCancel` against
/// caller-controlled inputs (isOptimistic, callerIsProposer,
/// callerIsCanceller, currentState). It mirrors WISDOM C018 (replayed-check
/// harness for library-internal properties).
///
/// Soundness rests on:
/// 1. `replayedValidateCancel` is a byte-identical replay of
///    `_validateCancel`'s ternary at line 387. The two are kept in sync by
///    reading the source whenever this harness is touched.
/// 2. The IGovernor.ProposalState enum is imported from the same source the
///    real `_validateCancel` uses, so the cast values (Pending=0, Active=1,
///    Defeated=3, etc.) match exactly.
contract StateMachineAsymmetryHarness {
    /// @notice Replayed `_validateCancel` decision (lines 374-388):
    ///   if (callerIsCanceller) return true;
    ///   if (!callerIsProposer) return false;
    ///   return isOptimistic
    ///       ? state != Defeated
    ///       : state == Pending;
    ///
    /// Returns true iff the cancel would be accepted under these inputs.
    function replayedValidateCancel(
        bool isOptimistic,
        bool callerIsProposer,
        bool callerIsCanceller,
        IGovernor.ProposalState state
    ) external pure returns (bool) {
        if (callerIsCanceller) {
            return true;
        }
        if (!callerIsProposer) {
            return false;
        }
        return isOptimistic
            ? state != IGovernor.ProposalState.Defeated
            : state == IGovernor.ProposalState.Pending;
    }
}
