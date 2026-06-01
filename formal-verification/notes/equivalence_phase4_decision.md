# Heavyweight equivalence-proof scope

All heavyweight contracts are work targets. Pursue equivalence closure
for each one until the per-mutator obligations are Qed Lemmas (no
`Admitted` artifacts beyond well-characterized framework primitives
documented in `WISDOM.md`).

## Scope

| Contract                       | Status          | Tracking                              |
|--------------------------------|-----------------|---------------------------------------|
| `ProposalLib`                  | Largely closed  | R070 + R103 deterministic-post-storage; final 4 walkers in flight via #308 |
| `OptimisticSelectorRegistry`   | Closed          | R069 nested EnumerableSet + LowM.Loop; 5 functions Qed |
| `TimelockControllerOptimistic` | Closed          | R071 + R095 executeBatch Skolem; 5 walkers Qed |
| `ReserveOptimisticGovernor`    | In progress     | T2.3 GovernorBase wire; R087 Blockers 1/3/4 remain |
| `StakingVault` (4 paths)       | In progress     | StakingVaultAdmin closed; StakingVaultExchange Phase A done (R100/R101), Phase B needs sim extension (~5-8k LOC) |
| OZ `Governor` base             | In progress     | Wired into ROG closure path                       |
| OZ `TimelockController` base   | Closed          | Closed alongside `TimelockControllerOptimistic`   |
| OZ `ERC4626`                   | In scope        | Needed for StakingVaultExchange Phase B closure   |
| OZ `ERC20Votes`                | In scope        | Needed for StakingVault delegation path           |
| OZ `Checkpoints` / `Trace208`  | Closed          | R035, already mechanized                          |

## How to approach the work

- The framework extensions (`StaticCallBridge.v`, `AbiEncoding.v`,
  `FrameworkExtensions.v`) are reusable primitives — extend them when
  you hit a new framework gap rather than creating per-contract trust
  axioms.
- Sim extensions are allowed and expected. StakingVaultExchange Phase B
  explicitly needs the sim's `State.t` to grow to cover unmodeled
  storage slots.
- Trust budgets are inspected via `Print Assumptions` and tracked in
  `print_assumptions_snapshot/baseline/`. New trust axioms are
  acceptable when they capture a well-characterized framework
  primitive (e.g., R082 staticcall, R091 delegatecall). They are not
  acceptable when they paper over per-contract residual work — those
  should be Qed Lemmas.
- The methodology corpus you need is documented in `WISDOM.md`
  entries R082, R083, R088, R091, R093, R099, R103. Read those before
  designing a closure path for a new contract.

## Working order

Landed waves:

1. ProposalLib walker discharges (R070 + R103) → enables ROG composition.
2. TimelockControllerOptimistic walkers (R071 + R095) → R087 Blocker 4 dependency satisfied.
3. StaticCallBridge R091 (delegatecall) → R087 Blocker 2 closed.
4. StakingVaultAdmin (R083 anchors) and StakingVaultExchange Phase A (R100/R101) → validates absorbing-primitive pattern for vault paths.

Remaining waves (can be parallelized except where noted):

5. ProposalLib R103 follow-up (#308 in flight) — closes ProposalLib fully.
6. UnstakingManager Phase B inner-body walkers (R098/R099 follow-on) plus T-VAULT trust resolution.
7. StakingVaultExchange Phase B sim extension → unblocks exchange-rate, rewards, delegation, pause/admin paths.
8. ROG R087 Blockers 1, 3, 4 → ROG mutators close.
9. `RunO_let_compose` structural lemma closure → discharges remaining framework Admitted across the corpus.

OZ libraries that show up as dependencies (Governor base, ERC4626,
ERC20Votes) get mechanized as part of the dependent-contract closure,
not as separate workstreams.

## Per-contract effort estimates

These are the original effort estimates from a static cost analysis.
They describe the size of the work, not its prioritization.

| Contract                       | Generated IR | OZ deps                                                        | Estimated effort |
|--------------------------------|-------------:|----------------------------------------------------------------|-------------------|
| `ProposalLib`                  | 194 476      | none (pure lib)                                                | ~2-4 weeks (mostly slot-packing) |
| `OptimisticSelectorRegistry`   | 194 476      | EnumerableSet (×2: Bytes32Set + AddressSet)                    | ProposalLib + ~1 week |
| `TimelockControllerOptimistic` | 63 215       | TimelockController (AccessControl + EnumerableSet)             | ~1-2 months       |
| `StakingVault`                 | 107 364      | ERC4626, ERC20Votes, ReentrancyGuard, AccessControl            | ~2-4 months       |
| `ReserveOptimisticGovernor`    | 194 476      | Governor (2000+ LOC abstract), Votes, Nonces, AccessControl    | ~3-6 months       |

(`Deployer` is largest at 324 940 lines but is constructor-only —
out of scope for runtime-equivalence proofs.)

## What each closure delivers

Each completed equivalence proof closes `Audit.v` Caveat-5 for one
contract — i.e., upgrades the per-domain `audit_*` claims from
"against the hand-written simulation" to "against the actual deployed
bytecode." The contracts most prone to sim-vs-bytecode drift are the
storage-heavy ones (StakingVault's reward accounting, ROG's proposal-
state slot packing) and the OZ-inheriting ones (Governor across OZ
upgrades). Those are also the ones with highest cost per the table
above; the effort and value scale together.
