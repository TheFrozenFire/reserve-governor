# Adversarial review synthesis (2026-05-27)

Six sub-agents reviewed the formal-verification corpus from six
distinct vantages. This memo records the cross-vantage findings,
graded by how many agents converged on each gap, and lists the
follow-up actions taken in response.

## Vantages

1. **Coverage critic** — read `Audit.v` and the 8 `notes/` memos.
   Asked: what audit-narrative claims aren't backed by theorems?
2. **Attack surface analyst** — read the 9 main `.sol` contracts.
   Asked: where are the on-chain attack vectors, ignoring the proofs?
3. **Simulation fidelity adversary** — read sim/contract pairs.
   Asked: where does the simulation diverge from the contract in
   ways that invalidate proofs?
4. **Recent-work skeptic** — read commits `2474c36..7c6f4df`. Asked:
   what's vacuous, cherry-picked, or sleight-of-hand?
5. **End-to-end existence theorem auditor** — read the two
   lifecycle-exists files. Asked: are the witnesses degenerate?
6. **Trust-boundary auditor** — read `mocks/`, axioms, oracle
   parameters. Asked: which trust assumption, if violated, breaks
   the most theorems?

## Multi-vantage findings (3+ agents converged)

### MV1 — Guardian oracle TOCTOU (CATASTROPHIC)

`Guardian.cancel` (simulations/Guardian.v:288-319) takes
`is_optimistic_oracle : ProposalId -> bool` and
`proposal_state_oracle : ProposalId -> ProposalState` as pure
functions. On chain these are external SLOADs against mutable
Governor storage between three external calls; they can race with
`transitionToPessimistic` and `_tallyUpdated`. The model lets a
guardian-cancel succeed against a proposal that has already
transitioned. Model says safe; chain says stuck.

- Trust-boundary auditor flagged as F1 catastrophic
- Attack-surface analyst flagged as #9 (Guardian TOCTOU with
  _tallyUpdated)
- Sim-fidelity adversary flagged G4 (cancel ignores _validateCancel
  rules)

Fix path: thread Governor state through `is_optimistic_oracle` /
`proposal_state_oracle` calls; either pass `State.t` explicitly or
make the oracle take `State.t -> ProposalId -> ...`.

### MV2 — AccessControl mock is decorative (SERIOUS)

The new `mocks/AccessControl.v` (committed in this session) is
unused by Guardian / VersionRegistry / RewardTokenRegistry.
Identifier namespaces don't share: mock uses Coq inductives
(`RAdmin | RManager | RGuardian`); production uses keccak hashes.
Cross-contract "only Timelock can call X" claims cannot be stated.

- Coverage critic #6
- Trust-boundary auditor F5
- Recent-work skeptic #12

Fix path: per-domain rewiring (Guardian, VersionRegistry,
RewardTokenRegistry) to consume `AccessControl.State`. Per memo
`notes/access_control_threading.md`, estimated 4-6h per domain.

### MV3 — WF_accrue is conservation-as-hypothesis (SERIOUS)

`rewards_conservation` inducts on `Reachable`, which requires
`step_well_formed` at every step. The `WF_accrue` constructor
bounds the per-user accrual delta by exactly the gap whose
non-negativity is the conservation conclusion. Operationally
tautological until first-principles discharge lands.

- Coverage critic #1
- Recent-work skeptic #4

Fix path: per `notes/wf_accrue_discharge.md`, extend `UserReward.t`
with a balance-shares field, thread supply-consistency through
`Reachable`, prove delta-accounting and gap-monotonicity invariants.

### MV4 — ERC4626 share-inflation / donation attack outside model (CRITICAL)

`convertToShares` with `supply=0` uses 1:1 (no virtual-shares
mitigation). Concrete attack: deposit 1-wei share → directly
transfer underlying → the native-rewards stream over the donation
gap accrues almost entirely to the attacker.

- Coverage critic #2 (theoretical)
- Attack-surface analyst #2 (concrete mechanism via _calculateHandout)

Fix path: Foundry regression test confirming presence/absence of
mitigation against actual `StakingVault`. If unmitigated, escalate.

### MV5 — PRBMath axiom domain wider than tested (SERIOUS)

`powu_bounded` claims `base <= 1e18 → powu base n <= 1e18` for all
`n : U256.t`. Production reverts for sufficiently large `n`. The
Foundry differential tests cap at `n <= 256` (some at `<= 1000`);
production `elapsed = block.timestamp - lastPayout` routinely
exceeds 86400. Axiom is silently broader than tested.

- Trust-boundary auditor F2
- Recent-work skeptic #6

Fix path: extend Foundry fuzz to production-realistic exponents
(86400 * 32 ≈ 2.8M). Add named cases at halfLife multiples.

### MV6 — ERC20 mock excludes deployed reward-token classes (HIGH)

USDT/USDC (blacklist), stETH (rebasing), PAXG (fee-on-transfer),
ERC777 (callback). All concrete, all unmodeled, all common reward
candidates.

- Attack-surface analyst #3 (reentrancy via hookable underlying)
- Trust-boundary auditor F4

Fix path: documentation + per-token sanity checks in deployment
config. Strict modeling is out of scope for the formal layer; this
is a trust-assumption-disclosure issue.

## Single-vantage but high-impact

### SV1 — End-to-end existence theorems are decorative (SERIOUS)

`EndToEnd_optimistic_flow` and `EndToEnd_standard_flow` are not
referenced in `Audit.v`. Standard flow uses an oracle step
(`advance_to_std_active`) outside the per-domain `Reachable`
inductive. Witness constants picked for vm_compute (vetoThreshold=10,
supply=100). Time monotonicity is `<=` with an unused `t2`,
permitting `t1=t2=t3` collapse.

- End-to-end theorem auditor

Decision: either kill the files or rebuild against the per-domain
`Reachable` relations with realistic contention. Tracked as #137.

### SV2 — `add_veto` is total in the sim (SERIOUS)

No phase check, no support-type check. Contract rejects via
`_validateStateBitmap(Active)` and `_countVote(Against only)`.
The "no de-escalation" theorem holds for transitions the contract
refuses to make.

- Sim-fidelity adversary G3

Fix path: add phase/state preconditions to `add_veto`. Tracked
as #135.

### SV3 — Proposer can cancel a Succeeded optimistic proposal (HIGH)

`_validateCancel` blocks only Defeated. Proposer waits for veto
window to pass without veto, then cancels — burning the throttle
slot. DoS / unilateral censorship by the original proposer.

- Attack-surface analyst #1 (with sim-fidelity G4 corroborating
  the cancel-rule gap)

Fix path: Foundry regression test, then either contract change or
explicit documentation. Tracked as #133.

### SV4 — `executeBatchBypass` salt-collision DoS (MEDIUM)

Pre-scheduled op with same `id = bytes20(governor) ^ descriptionHash`
blocks bypass forever. Currently PROPOSER_ROLE-gated to governor
only, but a latent footgun if proposers expand.

- Attack-surface analyst #5

Fix path: document the constraint; possibly check `_timestamps[id]
== 0` semantics more carefully.

### SV5 — `add_veto_preserves_validity_typed` is a vacuous rename (LOW but embarrassing)

Takes `Valid.delta delta` as hypothesis and immediately discards
(`intros Hv _ Hbound`). `Valid.delta` is an alias for
`U256.Valid.t`. The "typed entry point" framing is dressing on a
no-op forward. Tracked as #134.

### SV6 — Guardian's `cancel_preserves_validity` is `P → P` (LOW but embarrassing)

Proofs: `intros Hv _. exact Hv.` Stated as preserves-validity
lemmas but the conclusion has the same state as the hypothesis.
Honest commit message acknowledges this, but the audit-surface
claim ("preserves validity") misrepresents the operation. Tracked
as #134.

## Cross-cutting structural concerns

### CC1 — Simulations under-constrain preconditions relative to contracts

Sim-fidelity G3, G4, U1, S1, S2 all share this shape: the
simulation accepts inputs the contract rejects. Theorems about
"after op, state is X" hold in the sim but the contract never
reaches that branch. This is the broadest concern across the
agent reports.

### CC2 — Inherited operations silently absent from simulations

Guardian's admin-driven `grantRole(role, 0)` is reachable but
unmodeled. Timelock's `revokeOptimisticProposer` (CANCELLER_ROLE-
gated, state-mutating) is entirely absent. Timelock's open-executor
mode is structurally absent. The recently-added `revokeRole` /
`renounceRole` (#119) closed part of this for Guardian but not for
the others.

### CC3 — Audit-narrative names overstate the theorems

"Rewards conservation" is conditional. "No throttle bypass" is
per-account. "Upgrade authorized" excludes the admin gate.
"Lifecycle exists" isn't even referenced. The names read as
system-safety claims; the theorems are local. Mitigation: the new
"Coverage caveats" section in `Audit.v` makes this explicit.

### CC4 — Protocol-level attacks structurally unreachable to the formal model

Reentrancy (no transaction-level model), token callbacks (ERC20
axioms exclude), TOCTOU between external storage reads (oracles
are pure), proxy initializer front-running, governance double-vote
via re-delegation around snapshots, off-canonical-deployment risk.
The formal layer cannot reach these; Foundry-level fuzz/invariant
tests are the right surface.

## Action plan (in order taken)

1. [#130] Audit.v honesty pass — coverage-caveats section added.
2. [#131] PRBMath fuzz extension to realistic exponents.
3. [#132] ERC4626 share-inflation regression test.
4. [#133] Proposer-cancel-of-Succeeded regression test.
5. [#134] Clean up vacuous lemmas.
6. [#135] Governor sim: phase/state preconditions on add_veto and
   cancel.
7. [#136] Guardian oracle TOCTOU refactor.
8. [#137] Decide on EndToEnd existence theorems.

## Cross-references

- Coverage critic report and recent-work skeptic report are
  reflected in this synthesis but not stored as standalone files;
  the agents' full text is available in the conversation
  transcripts.
- The per-domain caveat list in `Audit.v` is the canonical
  audit-facing surface for these gaps.
