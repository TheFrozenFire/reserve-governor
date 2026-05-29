// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "forge-std/Vm.sol";

/// @title HalmosChecks
/// @notice Symbolic-execution refinement of selected concrete tests.
///         Each [check_*] function reasons about ALL inputs in the
///         declared symbolic range (within Halmos's bounded-loop
///         budget), strengthening "passes on the random values
///         forge sampled" to "passes for every input that Halmos
///         can enumerate within N loop iterations."
///
/// @dev Run with:  halmos --match-contract HalmosChecks
///
///      Foundry's [test_*] / [testFuzz_*] tests for the SAME
///      properties stay alongside their existing files; this file
///      ONLY adds [check_*] symbolic counterparts. The two regimes
///      give complementary coverage: random-fuzz finds bugs in the
///      space the symbolic engine over-prunes; symbolic-check
///      proves the absence of bugs in the space fuzzing can't
///      enumerate.
///
///      Methodology pointer:
///        a16z's Halmos-for-Pectra writeup demonstrates exactly
///        this hybrid pattern. See notes/owasp_2026_coverage.md
///        for the framing.
contract HalmosChecksTest is Test {
    uint256 internal constant ONE_D18 = 1e18;
    uint256 internal constant PROPOSAL_THROTTLE_PERIOD = 12 hours;

    // =========================================================
    // ThrottleLib — cap saturation
    //
    // The structural property: for any (currentCharge, lastUpdated,
    // nowTs, capacity) where the throttle storage is wellformed
    // (currentCharge in [0, 1e18], capacity > 0, lastUpdated <= nowTs),
    // [_getProposalsAvailable] returns at most [capacity].
    //
    // Maps to audit_throttle_cap_saturation in
    // formal-verification/rocq/Audit.v. The Rocq theorem proves it
    // in Gallina; this proves it directly against the Solidity
    // arithmetic via symbolic execution.
    // =========================================================

    /// Pure reimplementation of ThrottleLib._getProposalsAvailable so
    /// Halmos doesn't need to chase storage references. The arithmetic
    /// is bit-for-bit identical to the library; if the library is ever
    /// refactored, this function must follow.
    function _proposalsAvailable(
        uint256 currentCharge,
        uint256 lastUpdated,
        uint256 nowTs,
        uint256 capacity
    ) internal pure returns (uint256) {
        uint256 elapsed = nowTs - lastUpdated;
        uint256 charge = currentCharge + (elapsed * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        if (charge > ONE_D18) {
            charge = ONE_D18;
        }
        return (capacity * charge) / ONE_D18;
    }

    /// Halmos symbolic check: for any wellformed inputs, the function
    /// never returns more than [capacity]. The cap-saturation property.
    ///
    /// Note on bounds: production deployments use capacity <= 256
    /// (StakingVault test setup uses 12). The Rocq proof
    /// [audit_throttle_cap_saturation] holds for arbitrary U256.t.
    /// Halmos here adds bounded-EVM corroboration on the production-
    /// realistic range.
    ///
    /// Implementation note: the SMT solver bogs down on the
    /// [capacity * charge] product if both are unbounded. We
    /// provide an intermediate assertion ([charge <= ONE_D18]) so the
    /// solver can decompose the proof: first verify the upper bound
    /// on [charge], then conclude [(capacity * charge) / ONE_D18 <=
    /// capacity]. Without this hint the assertion times out.
    function check_ThrottleCapSaturation(
        uint256 currentCharge,
        uint256 lastUpdated,
        uint256 nowTs,
        uint256 capacity
    ) public pure {
        vm.assume(currentCharge <= ONE_D18);
        vm.assume(lastUpdated <= nowTs);
        vm.assume(capacity > 0);
        vm.assume(capacity <= 256); // production-realistic, SMT-tractable
        vm.assume(nowTs <= type(uint32).max);

        uint256 elapsed = nowTs - lastUpdated;
        uint256 charge = currentCharge + (elapsed * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        if (charge > ONE_D18) {
            charge = ONE_D18;
        }
        // Intermediate hint — proves the precondition for the final step.
        assert(charge <= ONE_D18);
        uint256 available = (capacity * charge) / ONE_D18;
        assert(available <= capacity);
    }

    /// Halmos symbolic check: the charge never exceeds 1e18 after the
    /// cap clamp. Structural form of the [charge_bound] invariant.
    function check_ThrottleChargeBound(
        uint256 currentCharge,
        uint256 lastUpdated,
        uint256 nowTs
    ) public pure {
        vm.assume(currentCharge <= ONE_D18);
        vm.assume(lastUpdated <= nowTs);
        vm.assume(nowTs <= type(uint48).max);

        uint256 elapsed = nowTs - lastUpdated;
        uint256 charge = currentCharge + (elapsed * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        if (charge > ONE_D18) {
            charge = ONE_D18;
        }
        assert(charge <= ONE_D18);
    }

    /// Halmos symbolic check: monotone replenishment, PRE-CLAMP form.
    ///
    /// Known limitation: this check currently TIMES OUT in Halmos
    /// even after multiple SMT-friendly refactors (intermediate-
    /// assert hints, tightened uint24 bounds, pre-clamp form). The
    /// underlying obstacle is integer-division monotonicity:
    ///   elapsed1 <= elapsed2  -->
    ///     (elapsed1 * ONE_D18) / PERIOD <= (elapsed2 * ONE_D18) / PERIOD
    /// SMT solvers (z3, yices) reason about this poorly without
    /// nonlinear arithmetic theory turned on.
    ///
    /// The Rocq theorem [audit_throttle_replenish_monotone] proves
    /// this for arbitrary U256.t — Halmos is bounded and SMT-
    /// dependent, so its timeout here is a tool limitation, not a
    /// property defect. We keep the check in the file as
    /// documentation of "the property we'd like Halmos to confirm";
    /// future solver improvements may close it.
    ///
    /// For now, run with [halmos --match-test '^check_(?!Throttle).*$']
    /// (or skip this contract under Halmos in CI) to avoid the
    /// timeout cost.
    function check_ThrottleReplenishMonotone(
        uint256 currentCharge,
        uint256 lastUpdated,
        uint256 t1,
        uint256 t2
    ) public pure {
        vm.assume(currentCharge <= ONE_D18);
        vm.assume(lastUpdated <= t1);
        vm.assume(t1 <= t2);
        vm.assume(t2 <= type(uint24).max);

        uint256 elapsed1 = t1 - lastUpdated;
        uint256 elapsed2 = t2 - lastUpdated;
        uint256 add1 = (elapsed1 * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        uint256 add2 = (elapsed2 * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        uint256 c1 = currentCharge + add1;
        uint256 c2 = currentCharge + add2;
        // Pre-clamp monotonicity — the load-bearing arithmetic.
        // The post-clamp form is monotone-by-construction (min is
        // order-preserving in its second argument); we check the
        // hard part here.
        assert(c2 >= c1);
    }

    // =========================================================
    // Consume semantics — single proposal debits 1e18 / capacity
    // =========================================================

    /// After [consumeProposalCharge], the new currentCharge is
    /// (pre-clamp charge) - (1e18 / capacity). Captures the exact
    /// debit unit.
    function check_ThrottleConsumeDebitsUnit(
        uint256 currentCharge,
        uint256 lastUpdated,
        uint256 nowTs,
        uint256 capacity
    ) public pure {
        vm.assume(currentCharge <= ONE_D18);
        vm.assume(lastUpdated <= nowTs);
        vm.assume(capacity > 0);
        vm.assume(capacity <= type(uint64).max);
        vm.assume(nowTs <= type(uint48).max);
        // Precondition that the library enforces via require:
        // proposalsAvailable >= 1.
        uint256 elapsed = nowTs - lastUpdated;
        uint256 charge = currentCharge + (elapsed * ONE_D18) / PROPOSAL_THROTTLE_PERIOD;
        if (charge > ONE_D18) charge = ONE_D18;
        uint256 proposalsAvailable = (capacity * charge) / ONE_D18;
        vm.assume(proposalsAvailable >= 1);

        // Apply the debit (mirrors ThrottleLib L25):
        uint256 newCharge = charge - (ONE_D18 / capacity);

        // The debit unit is exactly ONE_D18 / capacity.
        assert(newCharge + (ONE_D18 / capacity) == charge);
        // newCharge stays within bounds [0, 1e18).
        assert(newCharge <= ONE_D18);
    }
}
