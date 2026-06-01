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

## Status (current)

Every contract listed in `notes/equivalence_phase4_decision.md` is a
work target. The heavyweights (StakingVault, ReserveOptimisticGovernor,
ProposalLib, OptimisticSelectorRegistry, TimelockControllerOptimistic)
are in scope alongside the smaller contracts.

Per-file status:

- **Closed (per-mutator Qeds via composite-walker-axiom + R055/R059/R067/R069/R070/R071/R095/R103):**
  ThrottleLib, UnstakingManager (createLock/claimLock + Phase A for
  cancelLock), VersionRegistry, RewardTokenRegistry, Guardian
  (grantRole, revokeRole, cancel), AccessControlEnumerable,
  TimelockControllerOptimistic, OptimisticSelectorRegistry, StakingVaultAdmin.
- **Partial / in progress:** ProposalLib (4/5 walkers closed; final 4
  in flight via #308), ReserveOptimisticGovernor (T2.3 GovernorBase
  wired; R087 Blockers 1/3/4 remain), StakingVaultExchange (Phase A
  closed via R100/R101; Phase B needs sim extension for unmodeled
  slots), UnstakingManager cancelLock (T-VAULT trust obligation per
  R102 needs resolution).
- **Framework primitives:** R082 (staticcall) in `StaticCallBridge.v`,
  R083 (memory + ERC-7201 anchors) and R088 (arbitrary-U256-slot
  storage) in `FrameworkExtensions.v`, R091 (delegatecall) and R093
  (SafeERC20 absorbing bridge) in `StaticCallBridge.v` / `AbiEncoding.v`.

## Reusable apparatus

- `ThrottleLib_Leaves.v` — `declare_or_assign_pair_cons_step`,
  `declare_or_assign_Z_cons_step`, `two_sstores_pass_through_nonmatch`,
  the storage-slot lemmas. The same shape transfers to any
  struct-valued mapping.
- `Common.v` — `set_eq_at_role`, `set_eq_in_registry` (R059
  membership equivalence for EnumerableSet swap-and-pop).
- `StaticCallBridge.v`, `AbiEncoding.v`, `FrameworkExtensions.v` —
  absorbing primitives for external calls, ABI encoding/decoding,
  and arbitrary slot access. Extend these when a new framework gap
  surfaces; don't introduce per-contract trust axioms when the
  underlying primitive could be added here once.

## Methodology references

Read these `WISDOM.md` entries before designing a closure path for a
new contract:

- R082 / R091 / R093 — absorbing primitives for staticcall,
  delegatecall, and SafeERC20.
- R083 / R088 — memory anchors and arbitrary-slot storage primitives.
- R099 — Parameter→Definition refactor for `proj_post_X` (eliminates
  the Skolem-mismatch barrier across `proj_sim` and `sstore_post_storage`).
- R100 — modifier-wrapper sub-axiom narrowing for inner-body walkers.
- R103 — deterministic-post-storage wrappers (the canonical template
  for inheritor-walker discharge).
