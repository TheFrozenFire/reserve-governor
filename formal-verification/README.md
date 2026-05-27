# Dual-track verification: Rocq + CAS for Reserve Governor

The Reserve Governor implements a hybrid optimistic / standard
governance flow on top of an OpenZeppelin `Governor` foundation, a
custom ERC4626 `StakingVault` with dual delegation, a time-locked
`UnstakingManager`, and a single `TimelockControllerOptimistic` that
covers both proposal paths.

This directory holds the formal-verification scaffold: a Rocq 8.20.1
proof tree (`rocq/`), a CAS-witness layer (`cas/`), and per-component
audit notes (`notes/`).

## Why two layers

A formal verification effort has two distinct failure modes:

1. **Logical unsoundness**: the proof has a hole, the lemma chain
   doesn't actually establish what it claims. Caught by an
   interactive theorem prover (Rocq, Lean).
2. **Modeling error**: the proof is impeccable, but the abstract
   model the proof reasons about doesn't faithfully capture what the
   production code does. Caught by running both models on calibrated
   inputs and checking they agree.

These are **orthogonal**. The dual-track pattern brackets the same
property from two sides:

- The **Rocq layer** (`rocq/`) proves *logical soundness*: under the
  assumptions of the model, the invariant holds for all inputs.
- The **CAS layer** (`cas/`) validates *faithfulness*: the claimed
  identities and bounds actually agree with concrete computation
  across calibrated parameters.

The pattern is borrowed verbatim from the protocol repo's
`formal-verification/` (see the sister tree under
`reserve/formal-verification/protocol/formal-verification/`). The
governance-side properties differ in kind from the protocol-side
financial math, but the verification machinery is the same.

## What each layer covers, governor-side

| Domain | Rocq | CAS | Why |
|---|---|---|---|
| StakingVault: exchange-rate evolution under deposit/redeem | ✓ | ✓ | ERC4626 arithmetic with rounding; CAS sweeps the rounding-direction boundary, Rocq pins the monotonicity invariant. |
| StakingVault: dual-delegation checkpoint independence | ✓ | – | OZ `ERC20Votes` checkpoint book over two ledgers (standard + optimistic). Each ledger updates independently on transfer; the joint invariant is a Rocq composition theorem. |
| StakingVault: multi-token rewards accounting | ✓ | ✓ | Per-token reward index advances against vault share supply; CAS checks the rounding bound on `earned`. |
| UnstakingManager: time-locked withdrawal queue | ✓ | – | FIFO queue with `availableAt` timestamps. Mirrors the StRSR draft queue but per-account. |
| ProposalLib: proposer throttle (12h sliding window) | ✓ | ✓ | Throttle math on top of `block.timestamp`. CAS sweeps the rate-limit boundary. |
| OptimisticSelectorRegistry: `(target, selector)` whitelist | ✓ | – | EnumerableSet-backed set membership. Membership-preservation lemma. |
| ReserveOptimisticGovernor: fast-vote → slow-vote escalation | ✓ | – | State-machine transition from optimistic proposal under veto to standard proposal under confirmation vote. |
| TimelockControllerOptimistic: bypass vs scheduleBatch ordering | ✓ | – | Two execution paths through one timelock; the bypass path must preserve the slow path's queue ordering. |
| Reentrancy / access control | – | – | Out of scope. Production relies on OZ `nonReentrant` and role-gated modifiers. Modeling the call graph would require the Yul-equivalence layer. |

(✓ = applies; – = doesn't apply yet, or out of scope)

## Where to start

| If you want to... | Read |
|---|---|
| See the headline theorems | [`rocq/Audit.v`](rocq/Audit.v) |
| Understand a specific component's math | `rocq/simulations/<Component>.v` (e.g. `StakingVault.v` once added) |
| Audit the modeling fidelity | [`notes/simulation_fidelity_audit.md`](notes/simulation_fidelity_audit.md) |
| Reproduce the CAS sweeps | `bash cas/run-check.sh` |
| Build the whole Rocq tree | `bash scripts/rocq-build` |

## Toolchain

- **Coq 8.20.1** (`coq-hammer-tactics`, `coq-coqutil`,
  `coq-record-update`)
- **rocq-of-solidity** at `$HOME/git/reserve/_tools/rocq-of-solidity`
  (shared with the protocol repo — single checkout, two consumers).
  Both the Rocq library and the `solc-rocq` solc fork are pre-built;
  the governor scripts reuse those artifacts via the `ROCQ_TREE` env
  var.
- **PARI/GP** (`gp` on PATH) for the CAS layer
- **GNU coreutils** for `timeout`/`gtimeout` (already required by the
  protocol repo's build script — same prereq)
- **colima** (`colima start rocq`) — the `solc-rocq` solc fork is an
  amd64 ELF binary, run via Docker on `linux/amd64` through Apple
  Silicon's QEMU emulation. The governor's `solc-rocq` script defaults
  to the `colima-rocq` Docker context; override via `DOCKER_CONTEXT`.

See the protocol repo's `formal-verification/README.md` for platform
install instructions; the governor repo uses the same toolchain.

## Smoke test

A minimal end-to-end check of the toolchain lives at
`contracts/Smoke.sol` → `rocq/generated/Smoke.v`. After Colima is
running and rocq-of-solidity is built:

```sh
bash scripts/solc-rocq --ir-rocq formal-verification/contracts/Smoke.sol \
  > formal-verification/rocq/generated/Smoke.v
bash formal-verification/scripts/rocq-build generated/Smoke.v
```

The full build runs the smoke target by default (it's listed in
`rocq/_RocqProject`).

### Cost model and known limitations

`solc-rocq` runs natively on linux/x86_64 hosts (auto-detected;
override with `SOLC_ROCQ_MODE=docker` to force the container path).
On macOS / arm64 it falls back to a `coqorg/coq` container with
`--platform=linux/amd64`, which is functional but ~1000× slower
than native because the amd64 solc binary runs under QEMU
emulation. As reference points on a Ryzen-class native amd64 host:

- `Smoke.sol` (12 lines, no imports): ~11 ms.
- `Guardian.sol` (124 lines + `AccessControlEnumerable` import):
  ~250 ms, 23 k-line Rocq IR.
- Heavy OZ-integrated contracts (`StakingVault`,
  `ReserveOptimisticGovernor`, `TimelockControllerOptimistic`,
  `ProposalLib`): fast (sub-second) but the rocq-of-solidity fork's
  Rocq printer throws `std::length_error` on them. Regular `--ir`
  (Yul) and `--bin` (bytecode) succeed on the same inputs — so the
  front-end is fine; the Rocq codegen pass has a known bug on these
  shapes.

Even for contracts that emit Rocq IR successfully, the generated
file appends a top-level `Definition codes` per included unit, so
`coqc` rejects multi-import files with `codes already exists`. The
fix would be to either dedupe `codes` definitions or compile each
unit into its own module — both upstream-fork fixes.

The practical implication mirrors the protocol repo's experience:
**hand-written simulations in `rocq/simulations/` are the primary
verification path**, and `--ir-rocq` cross-checks are an
opportunistic parked workstream — useful when they work, but not
blocking.

## Build-script env vars

The build scripts pick up overrides from the environment:

| Var | Default | What it controls |
|---|---|---|
| `ROCQ_TREE` | `$HOME/git/reserve/_tools/rocq-of-solidity` | Where the shared rocq-of-solidity checkout lives. |
| `REPO_TREE` | self-located from script | The governor repo root (the parent of `formal-verification/`). |
| `OPAM_SWITCH` | unset | If set, `eval $(opam env --switch=$OPAM_SWITCH)` is run before `coqc`. |
| `RB_TIMEOUT` | `180` | Per-file `coqc` timeout in seconds. |
