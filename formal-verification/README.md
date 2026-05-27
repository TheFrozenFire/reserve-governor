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
  (shared with the protocol repo — single checkout, two consumers)
- **PARI/GP** (`gp` on PATH) for the CAS layer
- **GNU coreutils** for `timeout`/`gtimeout` (already required by the
  protocol repo's build script — same prereq)

See the protocol repo's `formal-verification/README.md` for platform
install instructions; the governor repo uses the same toolchain.

## Build-script env vars

The build scripts pick up overrides from the environment:

| Var | Default | What it controls |
|---|---|---|
| `ROCQ_TREE` | `$HOME/git/reserve/_tools/rocq-of-solidity` | Where the shared rocq-of-solidity checkout lives. |
| `REPO_TREE` | self-located from script | The governor repo root (the parent of `formal-verification/`). |
| `OPAM_SWITCH` | unset | If set, `eval $(opam env --switch=$OPAM_SWITCH)` is run before `coqc`. |
| `RB_TIMEOUT` | `180` | Per-file `coqc` timeout in seconds. |
