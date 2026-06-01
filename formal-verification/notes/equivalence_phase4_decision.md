# Phase 4 decision: heavyweight equivalence proofs

> **REVERSED 2026-05-31.** This memo originally parked the heavyweight
> contracts behind a cost/benefit argument. That parking decision is
> reversed. Direction from the user (verbatim): "tokenmaxxing until we
> get full equivalence coverage. The phase 4 decision was one you made,
> out of fear of cost. I want you to do it all."
>
> The cost analysis below remains accurate, but the conclusion no
> longer holds: all five heavyweight contracts are now in scope. Active
> work is dispatched across 6 parallel agents covering Governor base,
> TimelockController base, ERC20Votes, ERC4626, ReserveOptimisticGovernor
> mutators, and shallow_embed.py upstream fixes (the rate-limiting step
> for StakingVault / Governor shallow forms).
>
> StakingVault is Wave 2 — dispatched once Wave 1's upstream fixes land.

---

(Historical analysis preserved below.)

This memo answers task #184 (Phase 4 — decision point on heavyweight
contracts) by assessing each large contract's equivalence-proof cost
against its audit value.

The five contracts considered:

| Contract                    | Generated IR | Stub LoC | OpenZeppelin deps |
|-----------------------------|-------------:|---------:|-------------------|
| `ProposalLib`               | 194 476      |  ~6.4 MB | none (pure lib)   |
| `OptimisticSelectorRegistry`| 194 476      |  ~6.4 MB | EnumerableSet     |
| `ReserveOptimisticGovernor` | 194 476      |  ~6.4 MB | Governor, Votes, Nonces, AccessControl |
| `StakingVault`              | 107 364      |  ~3.5 MB | ERC4626, ERC20Votes, ReentrancyGuard, AccessControl |
| `TimelockControllerOptimistic` | 63 215    |  ~2.0 MB | TimelockController (AccessControl + EnumerableSet) |

(`Deployer` is largest at 324 940 lines but is constructor-only —
out of scope for runtime-equivalence proofs.)

## Cost driver: OZ surface area

For Phases A-3.3 (ThrottleLib, UnstakingManager, VersionRegistry,
RewardTokenRegistry, Guardian), the per-contract effort was roughly
proportional to the **non-OZ** body size. The OZ surface was either
absent (ThrottleLib, UnstakingManager) or bypassed via trust-boundary
documentation (Guardian).

The heavyweight contracts cannot bypass OZ — every operation either
mutates inherited OZ storage or calls inherited OZ functions whose
behaviour is load-bearing. Therefore the closure cost is
**equal to the cost of mechanizing the OZ libraries themselves**,
which is multi-person-months.

Per-contract OZ requirements:

- `ProposalLib`: no OZ — pure library. Smallest OZ-free heavyweight,
  but the body is genuinely 194k lines of generated IR and includes
  the full proposal-state encoding (uint8 enum packed with 4 uint48
  timestamps and 1 address into 2 storage slots). Equivalence proof
  effort: ~2-4 weeks, mostly slot-packing.
- `OptimisticSelectorRegistry`: needs OZ EnumerableSet.Bytes32Set
  AND EnumerableSet.AddressSet (two distinct instances). Phase 3.2
  scaffold's positions_map approach generalizes. Effort beyond
  ProposalLib: +1 week.
- `ReserveOptimisticGovernor`: inherits OZ Governor (a 2000+ line
  abstract base contract), Votes, Nonces, AccessControl. Each one
  is its own equivalence-proof workstream. Effort: ~3-6 months.
- `StakingVault`: ERC4626 (deposit/withdraw share math), ERC20Votes
  (Trace208 checkpoint history), ReentrancyGuard, AccessControl.
  Effort: ~2-4 months.
- `TimelockControllerOptimistic`: extends OZ TimelockController.
  Effort: ~1-2 months, mostly because TimelockController itself
  is a relatively self-contained 500-line base contract.

## Audit value assessment

Each equivalence proof closes Caveat-5 for one contract — i.e.,
upgrades the per-domain `audit_*` claims from "against the sim" to
"against the actual deployed bytecode" for that contract.

The marginal value depends on how much the **on-chain layout**
differs from the sim's natural representation. Two extremes:

- **Mechanical refactoring risk**: low for pure functions
  (ProposalLib, ThrottleLib), high for storage-heavy contracts where
  Solidity's slot-packing introduces opportunities for divergence
  (StakingVault's reward accounting across reentrancy guard slots,
  Governor's proposal-state packing).
- **Operational risk**: high for any contract where an OZ upgrade
  changes semantics. Governor inherits from `Governor` which is
  routinely updated; a hand-written sim that's correct against OZ
  v5.0 might diverge against v5.2.

By that measure, **StakingVault** and **Governor** are the most
valuable equivalence targets — their on-chain behaviour is most
likely to drift from a hand-written sim, and the cost of drift is
highest (multi-day audit reviews to re-check).

But their effort is also highest (months, not weeks).

## Recommendation

**Do not pursue full closure of any heavyweight contract in the
current workstream.** Instead:

1. **Tier 1 (close as follow-up):** ThrottleLib, UnstakingManager,
   VersionRegistry, RewardTokenRegistry. All have scaffolds in
   place; the remaining work is closing the body-tactical Admits
   under WISDOM R022. Estimated remainder: 1-2 weeks once R022's
   typeclass-projection workaround is dialed in.
2. **Tier 2 (treat as trusted base):** Guardian, OZ AccessControl,
   OZ EnumerableSet. Document the trust boundary in Audit.v
   Caveat-5; rely on OZ's audit trail.
3. **Tier 3 (genuinely parked):** ProposalLib, SelectorRegistry,
   Governor, StakingVault, Timelock. Revisit only if:
   - A serious sim/contract divergence is found by another method
     (e.g., a Certora rule violation, a Halmos differential test,
     an audit finding).
   - The OZ libraries themselves get mechanized upstream by another
     team.

## Why not pursue Tier 3 anyway

Two reasons:

1. **Diminishing marginal value.** The audit story is already
   strong: every `audit_*` notation has CAS witnesses + Certora
   rules + Foundry differential tests + the sim-level proof. The
   equivalence proof is one more layer on top — useful but not
   transformative.
2. **Opportunity cost.** Per-month spent on heavyweight equivalence,
   alternative uses include closing real bug-finding work (the 29
   pending P0-P2 backlog items from earlier rounds) or extending
   coverage to new attack classes. Both have higher expected value
   per unit time.

## What this leaves Caveat-5 saying

Updated language for [Audit.v] Caveat-5:

> Equivalence-tier coverage:
>
>   - ThrottleLib, UnstakingManager, VersionRegistry,
>     RewardTokenRegistry: scaffolded; closure pending one more
>     refinement pass on the Coq 8.20 tuple-Eq typeclass-projection
>     workaround (WISDOM R022).
>   - Guardian: trust-boundary scaffold; depends on OZ
>     AccessControlEnumerable correctness as a folklore axiom.
>   - ProposalLib, SelectorRegistry, Governor, StakingVault, Timelock:
>     parked. Coverage is sim-level only; Caveat-5 trust applies
>     fully.

That's the honest current state. Caveat-5 is partially closed for
the small contracts; the heavyweights remain trust-based until
upstream OZ mechanization makes them feasible.

## Tracking

This decision is recorded under task #184. The Tier 1 closure work
remains under tasks #173 (ThrottleLib mutator), #174 (audit
transfer), #176 (UnstakingManager body), #180/#181 (closure pass on
registry equivalence). Tier 3 contracts are not tracked — they get
new tasks only when a concrete need surfaces.
