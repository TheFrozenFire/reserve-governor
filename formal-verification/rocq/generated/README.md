# `rocq/generated/` — rocq-of-solidity outputs

This directory holds the `--ir-rocq` output of every governor
contract — the Rocq encoding of each contract's Yul-translated
semantics produced by the `rocq-of-solidity` solc fork.

The outputs are **regenerable** from the current contract
sources, and are therefore **gitignored**. The directory and
its documentation are checked in so the path
`rocq/generated/<ContractName>.v` is stable and equivalence
proofs can reference it without conditional logic.

## Regenerating

```sh
bash formal-verification/scripts/ir-rocq-coverage
```

The script compiles every `.sol` declaring a `contract` or
`library` (interfaces excluded) through `solc-rocq --ir-rocq`,
writing each output to `rocq/generated/<ContractName>.v`. It
exits non-zero on any compilation failure, so it can be wired
into CI as a regression check.

Pass `--include-oz` to additionally sweep the curated
OpenZeppelin allowlist (the files our contracts directly
import). OZ outputs land under `rocq/generated/oz/<RelPath>.v`
to avoid colliding with the governor sweep. The OZ subtree is
fully gitignored. OZ failures are reported but do not gate
the script's exit code; the OZ tier is diagnostic and feeds
`notes/shallow_embed_oz_gaps.md`.

See [`../../notes/ir_rocq_coverage.md`](../../notes/ir_rocq_coverage.md)
for the current pass/fail matrix and the two prior issues
(rocq-of-solidity `std::length_error`, Foundry remapping
plumbing) that the working setup depends on.

## Why the outputs aren't committed

They're large (≈36 MB across all contracts) and they decay
the moment any contract source changes. The canonical
artefact is the regeneration script, not a frozen snapshot.

The four heaviest outputs (Deployer, ReserveOptimisticGovernor,
OptimisticSelectorRegistry, ProposalLib) are bloated by
inlined OpenZeppelin machinery and would each diff in the
thousands of lines on any unrelated contract change. The
smaller outputs (ThrottleLib at ~90 KB, UnstakingManager at
~280 KB, etc.) are the realistic equivalence-proof targets.

## How equivalence proofs will reference this

Once a contract has an equivalence proof, that proof lives at

```
formal-verification/rocq/proofs/equivalence/<ContractName>.v
```

and `Require`s both the hand-written simulation and the
generated IR:

```coq
Require ReserveGovernor.simulations.<ContractName>.
Require ReserveGovernor.generated.<ContractName>.
```

The build script's tier order then enforces:

1. `scripts/ir-rocq-coverage` (populates this directory)
2. `scripts/rocq-build` (builds simulations, proofs, then equivalence proofs)

Until any equivalence proofs land, this directory exists
purely as a stable target — no Rocq file in the build
currently `Require`s anything from here.
