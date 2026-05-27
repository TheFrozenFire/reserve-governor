// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Smoke-test contract for the solc-rocq toolchain — no external imports,
/// concrete (not abstract), with a tiny piece of state + one public mutator.
/// Used to verify the end-to-end pipeline: solc-rocq emits Rocq IR, the IR
/// references the rocq-of-solidity library, and the result type-checks
/// under Coq 8.20.
contract Smoke {
    uint256 public counter;

    function bump(uint256 delta) external {
        counter += delta;
    }
}
