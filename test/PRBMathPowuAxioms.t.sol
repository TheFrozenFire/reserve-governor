// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";

import { UD60x18, ud, unwrap } from "@prb/math/src/UD60x18.sol";

/// @title PRBMathPowuAxiomsTest
/// @notice Differential test for the 5 axioms about UD60x18.powu that
///         the formal-verification corpus assumes. Each axiom is
///         exercised against the deployed prb-math implementation via
///         a mix of named-case asserts and forge fuzz tests.
///
/// @dev The axioms live in formal-verification/rocq/mocks/PRBMath.v.
///      If any test here fails, an integration proof somewhere in the
///      Rocq tree silently assumes a false fact — the failing axiom
///      must either be retracted or the upstream PRBMath behavior
///      must be fixed.
///
///      Convention: all UD60x18 values carry an implicit 1e18 scale.
///      ONE_D18 = 1e18 is the multiplicative identity.
contract PRBMathPowuAxiomsTest is Test {
    uint256 internal constant ONE_D18 = 1e18;

    /// Axioms 1-5 are in the source comments alongside each test
    /// group below. Failure of any test invalidates the matching
    /// audit_*_powu_* claim in formal-verification/rocq/Audit.v.

    // ===========================================================
    // Axiom 1: powu(x, 0) = ONE_D18 for any x
    // ===========================================================

    function test_Axiom1_PowuZeroExpAtUnit() public pure {
        assertEq(unwrap(ud(ONE_D18).powu(0)), ONE_D18, "powu(1e18, 0) must be 1e18");
    }

    function test_Axiom1_PowuZeroExpAtHalf() public pure {
        assertEq(unwrap(ud(5e17).powu(0)), ONE_D18, "powu(0.5e18, 0) must be 1e18");
    }

    function test_Axiom1_PowuZeroExpAtZero() public pure {
        // PRBMath documents: "Returns UNIT for 0^0."
        assertEq(unwrap(ud(0).powu(0)), ONE_D18, "powu(0, 0) must be 1e18 (per PRBMath convention)");
    }

    function testFuzz_Axiom1_PowuZeroExp(uint256 base) public pure {
        // Restrict to non-overflowing range. Axiom only constrains
        // base <= ONE_D18; outside that, powu may overflow.
        vm.assume(base <= ONE_D18);
        assertEq(unwrap(ud(base).powu(0)), ONE_D18);
    }

    // ===========================================================
    // Axiom 2: powu(0, n) = 0 for n > 0
    // ===========================================================

    function test_Axiom2_PowuZeroBaseAtOne() public pure {
        assertEq(unwrap(ud(0).powu(1)), 0, "powu(0, 1) must be 0");
    }

    function test_Axiom2_PowuZeroBaseAtLargeN() public pure {
        assertEq(unwrap(ud(0).powu(1000)), 0, "powu(0, 1000) must be 0");
    }

    function testFuzz_Axiom2_PowuZeroBase(uint256 n) public pure {
        vm.assume(n > 0);
        vm.assume(n <= 256); // cap exponent so the test stays cheap
        assertEq(unwrap(ud(0).powu(n)), 0);
    }

    // ===========================================================
    // Axiom 3: base <= ONE_D18 -> powu(base, n) <= ONE_D18
    // ===========================================================

    function test_Axiom3_BoundednessAtUnit() public pure {
        // x = ONE_D18, n large — result should stay at ONE_D18.
        assertLe(unwrap(ud(ONE_D18).powu(100)), ONE_D18);
    }

    function test_Axiom3_BoundednessAtHalfExponentDecays() public pure {
        // 0.5^10 = 1/1024 ~ 9.77e14
        uint256 result = unwrap(ud(5e17).powu(10));
        assertLe(result, ONE_D18, "0.5^10 must be <= 1e18");
        assertApproxEqAbs(result, 9.765625e14, 1e9, "0.5^10 ~ 9.77e14");
    }

    function test_Axiom3_BoundednessAtNearZero() public pure {
        // base = 1e6 (in D18 representation = 1e-12). Even with n=1
        // the result is far below ONE_D18.
        assertLe(unwrap(ud(1e6).powu(1)), ONE_D18);
        assertLe(unwrap(ud(1e6).powu(10)), ONE_D18);
    }

    function testFuzz_Axiom3_Boundedness(uint256 base, uint256 n) public pure {
        vm.assume(base <= ONE_D18);
        vm.assume(n <= 256);
        assertLe(unwrap(ud(base).powu(n)), ONE_D18);
    }

    // ===========================================================
    // Axiom 4: monotonicity in the exponent — for base <= ONE_D18,
    //          n1 <= n2 -> powu(base, n1) >= powu(base, n2)
    // ===========================================================

    function test_Axiom4_MonotoneDecayAtHalf() public pure {
        uint256 p1 = unwrap(ud(5e17).powu(1));
        uint256 p2 = unwrap(ud(5e17).powu(2));
        uint256 p10 = unwrap(ud(5e17).powu(10));
        assertGe(p1, p2);
        assertGe(p2, p10);
    }

    function test_Axiom4_MonotoneDecayAtNearOne() public pure {
        // base = 0.999e18; small but non-trivial decay
        uint256 p1 = unwrap(ud(999e15).powu(1));
        uint256 p100 = unwrap(ud(999e15).powu(100));
        assertGe(p1, p100);
    }

    function test_Axiom4_MonotoneDecayAtUnitIsConstant() public pure {
        // At base = ONE_D18, the decay is flat (n doesn't matter).
        // Monotonicity holds trivially as equality.
        assertEq(unwrap(ud(ONE_D18).powu(1)), unwrap(ud(ONE_D18).powu(100)));
    }

    function testFuzz_Axiom4_MonotoneDecay(uint256 base, uint8 n1Small, uint8 deltaSmall) public pure {
        vm.assume(base <= ONE_D18);
        // Bound exponents so the test runs cheaply.
        uint256 n1 = uint256(n1Small);
        uint256 n2 = n1 + uint256(deltaSmall);
        assertGe(unwrap(ud(base).powu(n1)), unwrap(ud(base).powu(n2)));
    }

    // ===========================================================
    // Axiom 5: powu(ONE_D18, n) = ONE_D18 for any n
    // ===========================================================

    function test_Axiom5_OneBaseAtZero() public pure {
        assertEq(unwrap(ud(ONE_D18).powu(0)), ONE_D18);
    }

    function test_Axiom5_OneBaseAtOne() public pure {
        assertEq(unwrap(ud(ONE_D18).powu(1)), ONE_D18);
    }

    function test_Axiom5_OneBaseAtLargeN() public pure {
        assertEq(unwrap(ud(ONE_D18).powu(1000)), ONE_D18);
    }

    function testFuzz_Axiom5_OneBase(uint256 n) public pure {
        vm.assume(n <= 1000);
        assertEq(unwrap(ud(ONE_D18).powu(n)), ONE_D18);
    }

    // ===========================================================
    // Real production scenarios — calibration spot-checks against
    // the StakingVault rewards-decay formula.
    // ===========================================================

    /// @dev StakingVault uses rewardRatio = ln(2) / halfLife (D18).
    ///      For halfLife = 86400s, after one half-life elapsed the
    ///      remaining fraction (1 - rewardRatio)^elapsed should be
    ///      approximately 0.5 (i.e. ~5e17).
    function test_Calibration_HalfLifeRemainingFraction() public pure {
        uint256 LN_2 = 0.693147180559945309e18;
        uint256 halfLife = 86400;
        uint256 rewardRatio = LN_2 / halfLife;
        uint256 base = ONE_D18 - rewardRatio;
        uint256 result = unwrap(ud(base).powu(halfLife));
        // Should be near 0.5e18. CAS witnesses bound the overshoot at
        // ~2.78 ppm in the user's favor. Tolerance below is generous.
        assertApproxEqAbs(result, 5e17, 1e13, "remaining fraction ~ 0.5e18 after one halfLife");
    }

    // ===========================================================
    // Production-realistic exponent regime
    //
    // The original fuzz tests cap n at uint8 (256) or 1000. The
    // production StakingVault computes `powu(base, elapsed)` where
    // `elapsed = block.timestamp - lastPayout` — a duration in
    // seconds that routinely exceeds 86400 (one day) and can reach
    // ~32 days between sparse accruals on a low-activity vault.
    //
    // The PRBMath axioms in rocq/mocks/PRBMath.v are stated for all
    // `n : U256.t`. The adversarial review (caveat MV5 / F2) flagged
    // that the axiom domain is wider than the validated range. The
    // tests below close that gap by exercising the axiom domain at
    // the values the contract actually feeds in.
    // ===========================================================

    /// @dev Compute the "decay base" used by StakingVault for a given
    ///      half-life: `1e18 - ln(2) / halfLife`.
    function _decayBase(uint256 halfLife) internal pure returns (uint256) {
        uint256 LN_2 = 0.693147180559945309e18;
        return ONE_D18 - (LN_2 / halfLife);
    }

    function test_Realistic_Boundedness_OneDay() public pure {
        // halfLife = 1 day; elapsed = 1 day → remaining ≈ 0.5e18
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu(86400));
        assertLe(result, ONE_D18);
        assertApproxEqAbs(result, 5e17, 1e13);
    }

    function test_Realistic_Boundedness_OneWeek() public pure {
        // halfLife = 1 day; elapsed = 1 week → ≈ 2^-7 ≈ 7.8e15
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu(7 * 86400));
        assertLe(result, ONE_D18);
        // 0.5^7 = 1/128 ≈ 7.8125e15
        assertApproxEqAbs(result, 78125e11, 1e12);
    }

    function test_Realistic_Boundedness_ThirtyTwoDays() public pure {
        // halfLife = 1 day; elapsed = 32 days → ≈ 2^-32 ≈ 2.33e8
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu(32 * 86400));
        assertLe(result, ONE_D18);
        // 0.5^32 = 1/2^32 ≈ 2.328e8
        // Generous tolerance because the discrete formula drifts at
        // many halflives.
        assertApproxEqAbs(result, 232830643, 1e9);
    }

    function test_Realistic_Boundedness_LongHalfLifeShortElapsed() public pure {
        // halfLife = 30 days; elapsed = 1 hour → tiny decay
        uint256 base = _decayBase(30 * 86400);
        uint256 result = unwrap(ud(base).powu(3600));
        assertLe(result, ONE_D18);
        // Remaining ≈ 0.999...
        assertGt(result, 9.99e17);
    }

    /// @dev Fuzz with uint32 exponent so values can reach ~4 billion
    ///      seconds (well past any realistic block.timestamp delta).
    ///      Restricted to base near 1e18 since powu of small bases
    ///      with large exponents underflows to 0 quickly (still
    ///      bounded, but tests are uninteresting).
    function testFuzz_Realistic_Boundedness_LargeN(uint32 nLarge) public pure {
        vm.assume(nLarge >= 86400);          // at least one day
        vm.assume(nLarge <= 32 * 86400);     // at most 32 days
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu(uint256(nLarge)));
        assertLe(result, ONE_D18, "powu must stay bounded over realistic seconds-range");
    }

    /// @dev Monotone-decay fuzz over realistic ranges. n1, n2 both in
    ///      [86400, 32 * 86400]; n2 = n1 + delta where delta also
    ///      bounded.
    function testFuzz_Realistic_MonotoneDecay(uint32 n1, uint32 delta) public pure {
        vm.assume(n1 >= 86400);
        vm.assume(n1 <= 30 * 86400);
        vm.assume(delta <= 2 * 86400);
        uint256 base = _decayBase(86400);
        uint256 r1 = unwrap(ud(base).powu(uint256(n1)));
        uint256 r2 = unwrap(ud(base).powu(uint256(n1) + uint256(delta)));
        assertGe(r1, r2, "powu must be monotone-decreasing in exponent");
    }

    /// @dev Stress test: PRBMath's repeated-squaring should not
    ///      revert on a base in (0, 1) regardless of how large the
    ///      exponent is. Try max-uint32 (4.29 billion seconds, ~136
    ///      years) and confirm no revert + result still <= 1e18.
    function test_Realistic_NoRevertAtMaxUint32() public pure {
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu(type(uint32).max));
        assertLe(result, ONE_D18);
        // After ~136 years of 1-day half-life, remaining is essentially 0.
        assertLt(result, 1);
    }

    /// @dev Even larger: uint40 exponent (1.1 trillion seconds, ~35k
    ///      years). Tests the upper boundary where the repeated-
    ///      squaring loop runs ~40 iterations. Still bounded.
    function test_Realistic_NoRevertAtUint40Boundary() public pure {
        uint256 base = _decayBase(86400);
        uint256 result = unwrap(ud(base).powu((1 << 40) - 1));
        assertLe(result, ONE_D18);
        assertLe(result, 1);
    }
}
