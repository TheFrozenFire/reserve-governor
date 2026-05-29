# `rocq/proofs/equivalence/` — sim ↔ generated-IR equivalence

This directory holds the equivalence proofs that close the
"hand-written simulation vs actual contract" gap documented in
`Audit.v` Caveat-5.

Each file proves that a particular hand-written simulation under
`rocq/simulations/<Name>.v` denotes the same state transitions
as the generated Yul IR under `rocq/generated/<Name>.v`. Once
landed for a contract, the existing `audit_*` theorems on that
contract's simulation formally transfer to the contract itself
by composition.

## Shape of an equivalence file

```coq
Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Require ReserveGovernor.simulations.<ContractName>.
Require ReserveGovernor.generated.<ContractName>.

Module <ContractName>Equivalence.

  Theorem run_<operation>_matches_simulation :
    forall (storage : ...) (args : ...),
      ReserveGovernor.generated.<ContractName>.<Module>.run_<operation> args storage
      ≈
      ReserveGovernor.simulations.<ContractName>.<operation> args (proj storage).
  Proof.
    (* ... *)
  Qed.

End <ContractName>Equivalence.
```

The `≈` relation captures observational equivalence between
Yul-runtime state evolution and the simulation's pure transition.
Its exact form depends on how much of the Yul runtime semantics
the proof needs to expose; the protocol repo's
`proofs/RocqOfSolidity/` notes are the working precedent.

## Build prerequisite

This tier requires the generated IR to be present in
`rocq/generated/`. Before building, run:

```sh
bash formal-verification/scripts/ir-rocq-coverage
```

This populates `rocq/generated/<Name>.v` for every contract that
declares an equivalence file here. The `_RocqProject` build
loads simulations and proofs unconditionally; equivalence
files are listed in a tier below them and are skipped in clean
checkouts that haven't run the regen step.

## Target ordering

The realistic order — smallest substantive contracts first —
is:

1. **ThrottleLib** (~90 KB of generated IR) — pure arithmetic,
   single mutating operation, ideal proof-of-method target.
2. **UnstakingManager** (~280 KB) — per-lock state machine
   with three operations.
3. **VersionRegistry**, **RewardTokenRegistry** (~260 KB each)
   — owner-gated registries with simple invariants.
4. **Guardian** (~740 KB) — two-tier cancellation auth.

The heavyweight contracts (StakingVault, ReserveOptimisticGovernor,
ProposalLib, OptimisticSelectorRegistry) inline substantial
OpenZeppelin machinery and would each be a multi-week proof
engineering effort. They stay parked until the methodology is
established on the small targets.

## Status

No equivalence proofs landed yet. This directory exists so the
target paths are stable; the work is staged but not begun.
