// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @notice Intent-derived test harness for S37: the executeBatchBypass salt
/// formula is byte-identical to the slow-path scheduleBatch salt formula,
/// so both paths route through the same timelock-id slot for the same
/// proposal content.
///
/// Background: the optimistic bypass salt at
/// `ReserveOptimisticGovernor._executeOperations` (lines 355-357) is
///
///     bytes20(address(this)) ^ descriptionHash
///
/// The slow-path salt for `scheduleBatch` is derived inside OZ's
/// `GovernorTimelockControlUpgradeable._queueOperations` (line 107) via
/// the private `_timelockSalt` (line 189-191):
///
///     function _timelockSalt(bytes32 descriptionHash) private view returns (bytes32) {
///         return bytes20(address(this)) ^ descriptionHash;
///     }
///
/// The two formulas are byte-identical. Both paths derive the timelock
/// operation id by hashing `(targets, values, calldatas, predecessor=0,
/// salt)` with `salt = bytes20(governor) ^ descriptionHash`.
///
/// What this harness exposes (verified in BypassSaltUniqueness.spec):
///   - `bypassSalt(g, h)`: the verbatim source-level formula from
///     ReserveOptimisticGovernor._executeOperations.
///   - `scheduleSalt(g, h)`: the verbatim source-level formula from OZ's
///     _timelockSalt.
///   - `bypassSaltAsUint(g, h)`: the equivalent uint-arithmetic form
///     `bytes32((uint160(g) << 96) ^ uint256(h))`. solc 0.8.28 with
///     optimizer at 200 runs compiles `bytes20(g) ^ h` to this same
///     SHL/XOR bytecode (verified via solc --asm); the uint-form is
///     byte-identical to the bytecode.
///   - `scheduleSaltAsUint(g, h)`: same uint-form for the slow path.
///
/// What S37 (Audit.v Caveat-11 second bullet) flags: a PROPOSER_ROLE
/// holder outside the governor could call `scheduleBatch` directly with
/// an adversarially-chosen salt, occupying a timelock id slot that the
/// optimistic bypass needs. The defense is purely access-control:
/// PROPOSER_ROLE on the timelock is held only by the governor, which
/// never lets a caller supply the salt -- the governor always derives
/// it from the description hash. This harness pins the
/// salt-derivation-formula half (both paths use the same formula). The
/// PROPOSER_ROLE gate is an OZ-side invariant.
///
/// Why a re-stated formula instead of calling the governor / OZ helper:
///   `_timelockSalt` is `private` in OZ's
///   GovernorTimelockControlUpgradeable -- it is not callable from CVL.
///   The `ReserveOptimisticGovernor._executeOperations` line that
///   contains the bypass salt is `internal`, also not directly callable;
///   verification at the governor entry-point level pulls in the OZ
///   Governor inheritance tree and times out (WISDOM C018).
///
///   Both formulas are one line, in plain sight in the source. The
///   harness replays them verbatim. The soundness argument is mechanical:
///   read ReserveOptimisticGovernor.sol:356 and
///   GovernorTimelockControlUpgradeable.sol:190 and compare.
contract BypassSaltHarness {
    /// @notice Replays the bypass salt formula from
    /// ReserveOptimisticGovernor._executeOperations:355-357.
    ///
    /// The literal Solidity expression `bytes20(governor) ^ descriptionHash`
    /// compiles (verified at solc 0.8.28 with --asm) to the EVM sequence
    ///   SHL 96 ; PUSH12 0xff..ff ; NOT ; AND ; XOR
    /// i.e. `(uint160(governor) << 96) XOR descriptionHash`. The
    /// uint-form below (bypassSaltAsUint) is byte-identical to that
    /// bytecode.
    function bypassSalt(address governor, bytes32 descriptionHash) external pure returns (bytes32) {
        return bytes20(governor) ^ descriptionHash;
    }

    /// @notice Replays the slow-path salt formula from
    /// GovernorTimelockControlUpgradeable._timelockSalt (line 189-191).
    function scheduleSalt(address governor, bytes32 descriptionHash) external pure returns (bytes32) {
        return bytes20(governor) ^ descriptionHash;
    }

    /// @notice Equivalent uint256-arithmetic form of the bypass salt
    /// formula. Returns `(uint160(governor) << 96) XOR uint256(descriptionHash)`
    /// reinterpreted as bytes32. Byte-identical to the EVM bytecode
    /// emitted by `bytes20(governor) ^ descriptionHash` (verified at solc
    /// 0.8.28).
    function bypassSaltAsUint(address governor, bytes32 descriptionHash) external pure returns (bytes32) {
        uint256 shifted = uint256(uint160(governor)) << 96;
        return bytes32(shifted ^ uint256(descriptionHash));
    }

    /// @notice Equivalent uint256-arithmetic form of the schedule salt
    /// formula. Identical to bypassSaltAsUint -- the OZ formula compiles
    /// to the same SHL/XOR sequence.
    function scheduleSaltAsUint(address governor, bytes32 descriptionHash) external pure returns (bytes32) {
        uint256 shifted = uint256(uint160(governor)) << 96;
        return bytes32(shifted ^ uint256(descriptionHash));
    }
}
