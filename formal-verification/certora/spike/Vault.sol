// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// Tiny Certora spike contract — a single-asset escrow vault with
/// per-user balances. Three operations: deposit (msg.value), withdraw
/// (caller balance check), and a deliberately-broken `withdrawBuggy`
/// that updates the user's balance but forgets the ETH transfer, so the
/// vault accumulates "phantom" debt. Certora should accept the safe
/// invariants and flag the buggy variant.
contract Vault {
    mapping(address => uint256) public balances;
    uint256 public totalDeposited;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
        totalDeposited += msg.value;
    }

    function withdraw(uint256 amount) external {
        require(balances[msg.sender] >= amount, "insufficient");
        balances[msg.sender] -= amount;
        totalDeposited -= amount;
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
    }

    /// Buggy variant — leaves user balance dangling.
    /// Decrements totalDeposited without touching balances[msg.sender],
    /// so Σ balances no longer equals totalDeposited.
    function withdrawBuggy(uint256 amount) external {
        require(balances[msg.sender] >= amount, "insufficient");
        totalDeposited -= amount;
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
    }
}
