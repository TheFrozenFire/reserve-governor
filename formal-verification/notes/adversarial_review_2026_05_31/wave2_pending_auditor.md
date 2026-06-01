# Wave-2-pending audit

HEAD: `a7767d8` (rebased from `dbf4844` after sibling auditor commit;
source-file state for the Wave-2-pending files unchanged).
Investigated every file under
`formal-verification/rocq/proofs/equivalence/` and cross-checked agent
claims in `WISDOM.md` and `Audit.v::Caveat-5` against the actual proof
state (file:line scoreboard + `Print Assumptions` runs on the headline
milestones via `/tmp/probe_*.v` against the live `coqc 8.20.1`
binary).

The headline finding is that the build is green and the milestone
theorems are `Qed`, but the closures rest on a sequence of escape
hatches — opaque post-storage `Parameter`s, observational-bridge
`Axiom`s of the trivial reflexive shape `storage_equiv X X`, opaque
shallow-form `Parameter`s aliasing nothing, and abstract `Section`
parameterizations — that should be tightened now that the upstream
dependencies (GovernorBase, ERC4626, ERC20Votes, TimelockController
base, MapToArray) have all landed.

## Per-file scoreboard

(Counts use the exact patterns `^\s*Qed\.`, `^\s*Admitted\.`,
`^\s*Axiom\s+\w+`, `^\s*Parameter\s+\w+`. Some Qed counts exceed
the lemma count because subproofs end in their own Qed.)

| File | Qed | Admitted | Axiom | Parameter | Headline claim accurate? |
|---|---:|---:|---:|---:|---|
| AbiEncoding.v | 8 | 0 | 8 | 0 | yes (WISDOM: "6 Qed, 7 trust axioms" — close) |
| AccessControlEnumerable.v | 13 | 0 | 2 | 0 | yes |
| Checkpoints.v | 0 | 0 | 0 | 0 | yes (header only) |
| Common.v | 2 | 0 | 0 | 0 | yes |
| ECDSA.v | 2 | 0 | 0 | 0 | yes |
| ERC20Votes.v | 12 | 0 | 0 | 0 | yes |
| ERC4626.v | 18 | 0 | 0 | 0 | yes |
| EnumerableSet.v | 5 | 0 | 0 | 0 | yes |
| GovernorBase.v | 61 | 0 | 0 | 0 | yes (74 fwd-grep `Qed.` includes subproofs) |
| Guardian.v | 137 | 0 | 21 | 3 | **partial** — 1 retired body still `Admitted` (line 5417) |
| Nonces.v | 5 | 0 | 0 | 0 | yes |
| ProposalLib.v | 30 | **3** | 22 | 17 | **NO** — Audit.v says "All 5 public functions Qed"; the 3 admits are R047 walker-pattern helpers that the milestones don't depend on, but the file is not 0-admit |
| ReentrancyGuard.v | 5 | 0 | 0 | 0 | yes |
| **ReserveOptimisticGovernor.v** | 29 | 0 | 13 | 7 | **stale claim** — Wave-2-pending markers point at GovernorBase landing, but GovernorBase landed FIRST (see below) |
| RewardTokenRegistry.v | 39 | 0 | 11 | 4 | yes |
| Sandbox.v | 9 | 0 | 0 | 0 | yes |
| SelectorRegistry.v | 9 | 0 | 13 | 10 | yes |
| **StakingVaultAdmin.v** | 7 | 0 | 18 | 11 | yes (under heavily opaque trust) |
| **StakingVaultDelegation.v** | 28 | 0 | 0 | 0 | **misleading** — milestones are `Section`-parameterized; no inheritor instantiates the Section so `Print Assumptions` shows only `deployment_id` because every reachable obligation is a `Variable`/`Hypothesis` discharged by Section closure |
| **StakingVaultExchange.v** | 21 | 0 | 12 | 14 | **NO** — milestones reference opaque `fun_<op>_op` Parameters; WISDOM (line 2076) says these become Notations aliasing shallow forms when `StakingVault_shallow.v` is wired, and `StakingVault_shallow.v` IS in `_RocqProject` (line 266) but the Parameters are still Parameters; theorem body is decoupled from the actual generated Yul |
| **StakingVaultRewards.v** | 20 | 0 | 17 | 11 | yes — actually binds to `fun_setRewardRatio_1036` from the shallow form and posts to `proj_sim_concrete (set_reward_ratio_sim ...)` (the strongest of the four StakingVault files) |
| StaticCallBridge.v | 6 | 0 | 0 | 0 | yes |
| ThrottleLib.v | 25 | 0 | 1 | 0 | yes |
| ThrottleLib_Leaves.v | 29 | 0 | 0 | 0 | yes |
| TimelockControllerBase.v | 51 | 0 | 0 | 0 | yes — WISDOM says "52 Qed lemmas"; 56 lemmas/theorems declared, 51 `Qed.` (the rest are `Definition`/closed in subsections); 0 admits |
| TimelockControllerOptimistic.v | 5 | 0 | 13 | 10 | yes |
| UnstakingManager.v | 20 | **3** | 0 | 0 | **acknowledged in Audit.v** — explicitly flagged "proof bodies Admitted with closure documentation" |
| VersionRegistry.v | 42 | 0 | 9 | 0 | yes |
| Votes.v | 21 | 0 | 0 | 0 | yes |

## Files with mismatched claims

### 1. ReserveOptimisticGovernor.v — the most egregious

`WISDOM.md:88` reads:
> R077: ReserveOptimisticGovernor mutator equivalence (Wave 1 — sim
> Qed + walker scaffold; Wave 2 binding pending GOV-BASE)

`WISDOM.md:1300-1311` (R077 entry) explicitly frames the file as
"scaffolds AHEAD of those dependencies", listing GOV-BASE
(GovernorBase.v) as a Wave-2 dependency.

**Reality:** GovernorBase landed at `e7a6909` (commit *before*
`c29f094` which created `ReserveOptimisticGovernor.v`). When the
ROG-scaffold agent ran, GovernorBase WAS available. The file still:

- Does NOT `Require Import` GovernorBase.v anywhere (grep on the
  whole file: 16 hits, every one is a comment of the form "When
  GovernorBase.v lands…" / "Wave 2: instantiate the GovernorBase
  projection here").
- Carries three explicit "Wave 2 binding placeholder" comment
  blocks at `ReserveOptimisticGovernor.v:1394-1443`.
- States the three milestone observational bridges as
  `storage_equiv (proj_post_<fn> ...) (proj_post_<fn> ...)` — i.e.,
  the trivial reflexive `X = X` shape (file:line 804-828). The
  audit-time obligation to derive a *real* projection from
  GovernorBase's lens is deferred verbatim ("that refinement
  requires the inherited Governor base's slot-anchor projection,
  which lands in Wave 2 alongside GovernorBase.v", lines 800-802).
- Defines its own `storage_equiv := =` (line 244), so the three
  trivial observation Axioms are literally `forall ..., x = x`.

`Print Assumptions` on `run_propose_equivalent` /
`run_castVote_equivalent` / `run_execute_equivalent` (the three
Section-6 milestone Qeds) returns:

```
ReserveOptimisticGovernorEquivalence.run_fun_propose_389_at_proj_sim
ReserveOptimisticGovernorEquivalence.proj_post_propose_389
ReserveOptimisticGovernorEquivalence.now_timestamp
RocqOfSolidity.Memory.of_u256_list
RocqOfSolidity.Storage.of_storable_values
PrimInt63.* (10 entries)
Theory: Set is impredicative
```

That **matches the agent's claim** in WISDOM (R077 entry). But the
agent's bigger framing — "Wave 2 binding pending GOV-BASE" — is
stale: the binding is now possible. The three "documentation-only"
optimistic-branch axioms (`castVote_optimistic_branch_post`,
`execute_optimistic_branch_post`, `execute_standard_branch_post`,
`castVote_optimistic_transition_branch`) are all `storage_equiv X X`
shape too (file:line 1289-1391) — they convey no information.

### 2. StakingVaultExchange.v — opaque-Parameter shell

`WISDOM.md:2076` claims:

> Total: 13 axioms / parameters … 4 opaque Yul-body Parameters
> (`fun_<op>_op`, become Notations aliasing the shallow form when
> `StakingVault_shallow.v` is activated in `_RocqProject`).

**Reality:** `StakingVault_shallow.v` IS active in `_RocqProject`
(line 266, uncommented). The Parameters at lines 964-971 of
`StakingVaultExchange.v` are still `Parameter`s — the Notation
aliasing has not been applied. The header text (lines 947-962) acknowledges
this with a *comment* but the code itself is not updated.

Probe of `Print Assumptions
StakingVaultExchangeEquivalence.run_deposit_equivalent`:

```
StakingVaultExchangeEquivalence.run_fun_deposit_4312_at_storage_base
StakingVaultExchangeEquivalence.proj_post_deposit_4312
StakingVaultExchangeEquivalence.fun_deposit_4312_op   ← opaque Yul body!
StakingVaultExchangeEquivalence.now_timestamp
RocqOfSolidity.Memory.of_u256_list
RocqOfSolidity.Storage.of_storable_values
PrimInt63.*
Set is impredicative
```

`fun_deposit_4312_op : U256.t -> U256.t -> M.t U256.t` is an
opaque Parameter under the headline Qed. This means the milestone
theorem `run_deposit_equivalent` does NOT establish anything about
the actual `fun_deposit_4312` shallow body — it speaks about an
abstract monadic function.

ERC4626.v has been landed (`6f06ba7`, four commits before this
file) with a Section template (`ERC4626EquivalenceTemplate`, lines
525-590+ of `ERC4626.v`) that exposes a `project_erc4626 :
SimulatedStorage.t -> ERC4626.State` lens. But
`StakingVaultExchange.v:681-690` redeclares its own opaque `Module
Type ERC4626_AbstractSurface`:

```coq
Module Type ERC4626_AbstractSurface.
  Parameter ERC4626_State : Set.
  Parameter project_erc4626 : SimulatedStorage.t -> ERC4626_State.
  Parameter asset_address : SimulatedStorage.t -> U256.t.
End ERC4626_AbstractSurface.
```

The comment at line 681 reads "When the Wave 1 ERC4626 equivalence
file lands, this Module Type is replaced by a Notation alias." — but
ERC4626.v has landed. Per-target observational bridge Axioms
(lines 864-893) are all the trivial `eq_at_<slot>_<op> X X` shape.

### 3. StakingVaultDelegation.v — Section-parameterized milestones

The file's headline milestones (`run_delegate_equivalent`,
`run_delegateOptimistic_equivalent`, `run_delegateBySig_equivalent`,
`run_delegateOptimisticBySig_equivalent`, lines 1313-1421) live
inside `Section StakingVaultDelegationSection` (line 982).

The Section declares **every** load-bearing identifier as a
Variable:

```
slot_std_delegatee, slot_std_delegate_ckpt,
slot_opt_delegatee, slot_opt_delegate_ckpt, slot_nonces, slot_std_total_ckpt
project_sim : SimulatedStorage.t -> SimState.t
proj_post_delegate, proj_post_delegateOptimistic, proj_post_delegateBySig, proj_post_delegateOptimisticBySig
Codes, Env, Walker, State          (abstract Sets!)
hoare                              (abstract Hoare-triple relation)
walker_delegate, walker_delegateOptimistic, walker_delegateBySig, walker_delegateOptimisticBySig
make_state : SimulatedStorage.t -> State
```

with `Hypothesis` declarations supplying the load-bearing closures
(`run_fun_delegate_at_proj_sim`, etc., as `Hypothesis` — not
`Axiom`).

`Print Assumptions` on `run_delegate_equivalent` returns:
```
ECDSA.ECDSA.Domain.deployment_id : Set
Set is impredicative
```

The result looks fantastic until you notice: ZERO contract-specific
axioms — because every contract-specific symbol is a Section
Variable, eliminated by Section closure into universally-quantified
hypotheses. The theorem proves "for ANY abstract notion of Walker
and Hoare triple satisfying the listed hypotheses, the milestone
holds" — vacuously true if no inheritor instantiates the Section.

The file has **no inheritor instantiation**: no
`Module Concrete := StakingVaultDelegationEquivalence …` or
`Definition project_sim := …` filling in the Variables. The
abstract Section closes; nothing concrete uses it. WISDOM R080
(lines 910-1085) doesn't mention this Section-abstract design at
all — it describes the file as if the milestones are direct
contract-binding theorems.

The closest analogue is GovernorBase.v's
`GovernorBaseEquivalenceTemplate` Section, which is honest about
being a *template* for inheritors. StakingVaultDelegation.v's
Section is presented as the inheritor itself, but is structurally a
template.

### 4. StakingVaultAdmin.v — opaque-Parameter post-storage

Milestone theorems (e.g. `run_setUnstakingDelay_equivalent`,
line 867) close to `storage_equiv storage_post
(proj_post_setUnstakingDelay_750 storage_base delay)` where
`proj_post_setUnstakingDelay_750` is an opaque `Parameter` (the
file has 11 Parameters). The post-state is the Parameter applied to
the inputs — under `storage_equiv := =` this is trivially
`storage_post = proj_post_<fn> storage_base delay`, which witnesses
existence given the walker axiom but makes no observable constraint
about what the resulting storage actually looks like.

This is honest under R070's "Skolemized post-storage" recipe — the
audit obligation is the walker axiom itself — but WISDOM R081
(file:line 1085) doesn't quote the equivalence-relation as `eq` and
doesn't flag the trivial-reflexive shape.

### 5. Guardian.v — R052 Option 2 not yet adopted

`WISDOM.md:1273-1326` claims R052 Option 2 (`MapToArray` upstream
primitive) "LANDED UPSTREAM" — and the upstream MapToArray
landing IS reflected in the most recent commit (`dbf4844`).
`Audit.v:282-305` Caveat-5 echoes this:

> The pre-existing four Guardian-local Option 1 axioms … remain on
> the books pending a structural refactor of [proj_sim] that places
> the MapToArray at slot index 1 … the refactor is mechanical
> (~330 references)…

This is honest. The 5 Option 1 axioms (`run_sload_role_values_length_at_proj_sim`,
`run_sstore_role_values_length_at_proj_sim`,
`run_sstore_role_values_body_at_proj_sim`,
`run_sload_role_values_length_at_proj_sim_post`,
`run_sload_role_values_body_at_proj_sim`) still live at lines
1340-1452 of `Guardian.v`. The smoke test
(`MapToArrayLengthSmokeTest`, line 1199) proves composition cleanly;
the refactor itself was deferred to a separate task and that is
documented. **This claim is accurate** — the Option-2 "follow-on"
framing matches.

The single body-`Admitted.` at line 5417 is a retired stub for
`run_fun__grantRole_1468` — its docstring (lines 5404-5416) reads
"RETIRED post-R046 fix. … this theorem's `Result.Ok 0` claim is
stale on that branch. The proper target is
`run_grantRole_1359_equivalent` (the intended mutator equivalence
below)." But `run_grantRole_1359_equivalent` is itself Qed
elsewhere in the file (the file's high Qed count comes from the
role-branch explosion: 3 roles × 2 membership states × 3
entrypoints). The retired-Admitted lemma is not referenced by any
downstream proof.

### 6. UnstakingManager.v — explicitly acknowledged

Audit.v explicitly flags this: "Shallow form compiles; proof bodies
Admitted with closure documentation. Closure pending a focused
session." 3 admits, all consistent with the audit statement.

### 7. ProposalLib.v — 3 helper-tier admits

3 Admitted bodies at lines 477, 510, 518:
- `run_fun__governor_679_equivalent` — walker pattern around
  Stdlib.address with let_state/strong_let_state tower. Documented
  as a walker-pattern residual.
- `run_fun_toUint48_7536_within_bound` — same R047 walker pattern.
- `run_fun_toUint32_7592_within_bound` — same.

`Audit.v::Caveat-5` line 222 says "ProposalLib: All 5 public
functions Qed." That refers to the FIVE public-mutator milestones
(`proposeOptimistic`, `proposePessimistic`, `vetoProposal`,
`transitionToPessimistic`, `cancel`), all of which ARE Qed. The
three helper-lemma admits don't break the milestone closures
because the milestones get the walker discharge via the composite
axioms instead of these helpers. The claim "All 5 public functions
Qed" is true at the milestone level but the file itself has 3
admits.

## Tractable Wave-2 bindings (dependencies have landed; binding is now possible)

Each of these is a follow-on task where the inheritor file should
adopt the now-landed upstream primitives. They are listed in order
of "highest mismatch with current scoreboard claims":

1. **ROG → GovernorBase wiring (top priority).** `GovernorBase.v`
   (`e7a6909`) exposes `GovernorBaseEquivalenceTemplate` Section
   with `project_base : SimulatedStorage.t -> State.t` lens and
   slot-lemmas (`proposalSnapshot_unfold`, etc.). ROG's three
   "Wave 2 binding placeholder" comment blocks
   (`ReserveOptimisticGovernor.v:1394-1443`) describe the exact
   shape this binding should take:
   - `Variable project_governor_base : SimulatedStorage.t -> Governor.State.t`
     supplied at the ROG slot anchors.
   - The three observational bridges (`proj_post_propose_389_observes`
     etc., currently `storage_equiv X X`) refined to assert the
     post-storage equals `storage_base` with the
     `_proposals[pid]` / `_proposalVotes[pid]` /
     `optimisticProposalDetails[pid]` slots updated to a shape
     keyed off `Governor.propose_optimistic`/`Governor.castVote`/
     `Governor.execute_optimistic` sim transitions.
   - The composite walker axioms (`run_fun_propose_389_at_proj_sim`
     etc.) extended to case-split on `_isOptimistic` via
     GovernorBase's state lens.

2. **StakingVaultExchange → ERC4626 + ERC20Votes wiring.**
   ERC4626.v's `ERC4626EquivalenceTemplate` Section exposes
   `project_erc4626 : SimulatedStorage.t -> ERC4626.State`. The
   `Module Type ERC4626_AbstractSurface` at
   `StakingVaultExchange.v:684-690` should be replaced by an
   instantiation of ERC4626EquivalenceTemplate at StakingVault's
   slot anchors. Same goes for `ERC20Votes.v`.

   Equally, the four `Parameter fun_<op>_op` declarations at
   lines 964-971 should be replaced with `Notation fun_<op>_op :=
   StakingVault_1721.StakingVault_1721_deployed.fun_<op>_<id>` so
   the milestone theorems actually constrain the shallow form. The
   header comment block (lines 947-962) already describes how to
   do this — the change is mechanical.

3. **StakingVaultDelegation → ERC20Votes instantiation.** The
   abstract `Section StakingVaultDelegationSection` should grow a
   sibling Module that instantiates the Variables with concrete
   shallow-form-derived values. ERC20Votes.v (`453f8dd`, landed
   before this file) exposes the Trace208 layout that the
   inheritor's `proj_post_delegate` should witness against.
   Without this concrete instantiation, the "milestone Qeds" are
   abstract schemas, not contract-level claims.

(Notable lower-priority bindings:)

4. SVAdmin's observational bridges should witness post-storage as
   a slot-by-slot mutation of `storage_base` rather than an opaque
   Parameter.

5. Guardian.v's R052 Option 1 axioms (5 of them) should be
   downgraded to lemmas under a `proj_sim` refactor that places
   `MapToArray` at slot 1. The smoke test
   (`MapToArrayLengthSmokeTest.run_length_smoke`, line 1199)
   demonstrates the upstream primitive composes; the work is the
   ~330 reference renames.

## Audit.v Caveat-5 fidelity

**Stale on the heavyweights.** Caveat-5 (lines 200-315) reads:

> `ReserveOptimisticGovernor      Parked (phase 4: requires OZ`
> `                              Governor base mechanization).`
> `StakingVault                   Parked (phase 4: requires ERC4626`
> `                              + ERC20Votes + ReentrancyGuard`
> `                              stacks).`

But `notes/equivalence_phase4_decision.md` opens (lines 3-16) with
the parking reversal as of 2026-05-31:

> REVERSED 2026-05-31. ... all five heavyweight contracts are now
> in scope.

and the subsequent commit log shows all of R076 (ERC4626), R078
(ERC20Votes), R079 (GovernorBase), R080 (SVDelegation), R081
(SVAdmin), R083 (SVRewards), R077 (ROG) have landed. Caveat-5 has
not been updated. The actual current state is:

- **ROG**: Wave-1 scaffold landed; bindings to GovernorBase NOT
  wired; three milestone Qeds rest on opaque post-storage
  Parameters with trivial-reflexive observation Axioms (which
  Caveat-5 doesn't acknowledge).
- **StakingVaultExchange**: scaffold landed; milestone theorems
  speak about opaque Yul-body Parameters, not the shallow form.
- **StakingVaultDelegation**: scaffold landed; milestone theorems
  are Section-abstract schemas, no concrete instantiation.
- **StakingVaultRewards**: substantively wired to the shallow form
  (this is the strongest file of the four).
- **StakingVaultAdmin**: scaffold landed; opaque-Parameter
  post-storage with trivial bridges.

The Caveat-5 text needs to drop the "Parked" framing and replace
it with a scoreboard of what's actually closed (and how trivially).

**Other Caveat-5 inaccuracies:**
- "ProposalLib: All 5 public functions Qed." — true for the
  milestone-level public functions, but 3 helper lemmas
  (`run_fun__governor_679_equivalent`,
  `run_fun_toUint48_7536_within_bound`,
  `run_fun_toUint32_7592_within_bound`) are `Admitted` (lines
  477/510/518). Audit.v doesn't acknowledge.
- "13 contracts/modules whose equivalence files all build Qed are
  at that bar" — needs to subtract ProposalLib (3 helper admits)
  and add 5 contracts (ERC4626, ERC20Votes, GovernorBase,
  TimelockControllerBase, Votes) and the StakingVault* /
  ROG scaffolds. The literal claim "all build Qed" is correct
  (the tree builds green); the trust-budget framing is wrong
  because the heavyweight closures stand on much thinner
  abstractions than the OZ-4 lightweights.

The R052 sub-paragraph (lines 282-305) accurately describes the
Option-2 follow-on framing.

## Recommendations

In order of urgency (highest first):

1. **Refresh `Audit.v::Caveat-5`** to match actual state:
   - Drop "Parked (phase 4)" for ROG and StakingVault.
   - Replace with per-file status: "Wave-1 scaffold closed; Wave-2
     binding pending [specific tightening]." Specifically call out
     that the abstract-Section / opaque-Parameter shape means the
     milestone Qeds prove existence under trust-axiom witnesses
     but do not constrain the post-storage shape against the sim.
   - Acknowledge ProposalLib's 3 helper-Admitted (low-severity
     since milestones don't depend on them).

2. **Refresh `WISDOM.md` R077 framing.** Drop the "Wave 2 binding
   pending GOV-BASE" line at WISDOM:88 and replace with "Wave 1
   scaffold; tightening to GovernorBase lens is the next step
   (GovernorBase landed at `e7a6909`)." The R077 long-form entry
   (lines 1256-1334) similarly needs the "scaffolds AHEAD of
   those dependencies" framing updated.

3. **Schedule the actual binding work as new tasks** (one task
   each):
   - ROG → GovernorBase wiring (the file already documents the
     exact hook points in Section 9, lines 1394-1443).
   - StakingVaultExchange Parameter → Notation flip + ERC4626
     instantiation. The header docstring is explicit about how.
   - StakingVaultDelegation concrete inheritor instantiation
     (Module satisfying the Section's Variables).

4. **Audit the headline Qeds for vacuity.** Specifically the
   `storage_equiv X X` reflexive-bridge axioms in
   `ReserveOptimisticGovernor.v` (lines 804-828, 1289-1391) and
   the `eq_at_<slot>_<op> X X` reflexive bridges in
   `StakingVaultExchange.v` (lines 864-893). These are documented
   as "Wave 1 trivial — Wave 2 tightens" but they are presented in
   `Print Assumptions` output as full axioms (because they're
   universally quantified — the body is reflexive but the
   declaration is a `forall`). A casual reader of `Print
   Assumptions` may not realize the axiom body is `x = x`.

5. **Distinguish "Section-abstract" from "concrete" milestones in
   WISDOM.** StakingVaultDelegation.v is fundamentally different
   from StakingVaultRewards.v in trust profile — the WISDOM
   entries (R080 vs R083) don't distinguish them, but the former
   proves a Section schema and the latter proves concrete-contract
   binding. This affects the "30 axioms" trust-budget summary in
   the WISDOM R083 entry — that count is meaningful, but the
   analogous Section-abstract files report misleadingly low
   axiom counts (SVDelegation: 0 Axiom/Parameter at the file
   level — but the Section has 11+ Variable/Hypothesis lines
   that act exactly like axioms within the Section's scope).

---

## Summary

- **Files with mismatched claims: 5** (ROG, SVExchange,
  SVDelegation, SVAdmin trivial-bridge framing, ProposalLib
  3-admit). Worst offender: **ReserveOptimisticGovernor.v** —
  Wave-2-pending markers still in place despite GovernorBase
  having landed before the ROG scaffold was committed.
- **Tractable Wave-2 bindings: 5** (top 3: ROG↔GovernorBase,
  SVExchange↔ERC4626+ERC20Votes, SVDelegation concrete
  instantiation).
- **Audit.v fidelity verdict: stale on heavyweights.** Caveat-5
  describes ROG and StakingVault as "Parked (phase 4)" but the
  Phase-4 parking decision was reversed on 2026-05-31 and Wave-1
  scaffolds for all of them have landed. The reversal is recorded
  in `notes/equivalence_phase4_decision.md` but Caveat-5 was
  not refreshed. The R052 sub-paragraph is current. The ProposalLib
  "all 5 Qed" claim is true at the milestone level but masks 3
  helper-tier Admitted in the file.
