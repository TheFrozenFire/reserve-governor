# Multi-base composition audit

**Reviewer vantage:** Multi-base composition auditor.
**HEAD:** `dbf4844 fv(R052): upstream MapToArray landing + smoke test + audit refresh` (at start of audit; latest review-tier work landed at 0fbe13e).
**Method:** rocq-mcp interactive probing of every Hypothesis / Axiom / Variable in the multi-base equivalence files, plus careful reading of mocks and sim modules.

## TL;DR — what's load-bearing and what isn't

The R072 / R078 "slot-agnostic Section + lens" methodology, as instantiated in this corpus, has a systematic problem: the **lens-correctness Hypotheses are tautologies** — they say nothing about the inheritor's actual storage. They are universally satisfied by ANY function `SimulatedStorage.t -> State.t`, because both sides of the equality are syntactically the same record-field selectors composed with the (abstract) projection. The walker proofs that close on top of them therefore inherit only the substantive obligations from the `run_fun_*_at_proj_sim` axioms, but the **lens-discharge step at instantiation time is a no-op**: a malicious instantiator can supply `project_sim := fun _ => empty_state` and still discharge every lens-correctness Hypothesis by `reflexivity`.

A second systematic problem: the "per-target observational bridge axioms" of the R070-shape files (StakingVaultExchange, StakingVaultAdmin, ReserveOptimisticGovernor) have the form `storage_equiv x x` — pure reflexivity. They are **vacuous axioms**. They contribute zero content to the trust budget; their job (per the file commentary) is to encode an audit obligation that ties the Skolemized post-storage to the sim's post-state, but that obligation isn't actually stated — only its trivial reflection. Same with `checkRole_*_succeeds` and `versionRegistry_*_returns` axioms whose conclusion is `True`.

Net effect: the *equivalence layer* leans entirely on the `run_fun_*_at_proj_sim` walker axioms. Everything else in the trust budget is either tautological (provable by `reflexivity` for any instantiation) or vacuous (conclusion `True`). The walker axioms themselves are universally quantified over Skolem projections and post-storages that have no semantic constraints — an obviously-wrong instantiation can pass every Section parameter and discharge every Hypothesis.

## Per-file findings

### ERC20Votes.v (`proofs/equivalence/ERC20Votes.v`)

**Section: `ERC20VotesEquivalenceTemplate`** (lines 507-634)

Six lens Hypotheses. ALL SIX are provable for any `project_erc20votes` by `reflexivity`:

| # | Hypothesis | LHS | RHS | Probe verdict |
|---|---|---|---|---|
| 1 | `lens_balances_correct` (541) | `balanceOf (project storage) a` | `ERC20.balanceOf (project storage).(State.erc20) a` | **TAUTOLOGY** — `ERC20Votes.balanceOf` is `fun s a => ERC20.balanceOf s.(State.erc20) a` |
| 2 | `lens_totalSupply_correct` (546) | `totalSupply (project storage)` | `(project storage).(State.erc20).(ERC20.totalSupply)` | **TAUTOLOGY** |
| 3 | `lens_allowance_correct` (551) | `allowance (project storage) o sp` | `ERC20.allowance (project storage).(State.erc20) o sp` | **TAUTOLOGY** |
| 4 | `lens_delegatee_correct` (558) | `delegates (project storage) a` | `(project storage).(State.votes).(Votes.State.delegatee) a` | **TAUTOLOGY** — `delegates` is `Votes.delegates`, which projects to the field |
| 5 | `lens_delegate_ckpt_correct` (563) | `getVotes (project storage) a` | `Trace208.latest ((project storage).(State.votes).(Votes.State.delegate_ckpt) a)` | **TAUTOLOGY** |
| 6 | `lens_total_ckpt_correct` (569) | `getTotalSupplyVotes (project storage)` | `Trace208.latest (project storage).(State.votes).(Votes.State.total_ckpt)` | **TAUTOLOGY** |

Verified by direct Coq probe:

```coq
Lemma probe_lens_balances_tautological :
  forall (project : SimulatedStorage.t -> ERC20Votes.State.t) (storage : SimulatedStorage.t) (account : ERC20Votes.Address),
    ERC20Votes.balanceOf (project storage) account
    = ERC20.balanceOf (project storage).(ERC20Votes.State.erc20) account.
Proof. intros. reflexivity. Qed.
```

All six accepted by `reflexivity` for arbitrary `project`. The hypotheses constrain `project_erc20votes` only by its codomain type — any function returning a valid `State.t` will pass.

The **seventh Hypothesis `lens_voting_units_eq_balance`** (lines 582-585) IS substantive — it relates two distinct record fields (`State.votes.voting_units` and `State.erc20.balances`). But this is a sim-state coupling, not a storage-layout constraint: it's preserved automatically if the projection lands in a state satisfying `Valid.t` (since `Valid.t` already requires `voting_units_eq_balance`). So even this one doesn't bind the projection to the inheritor's actual storage — it only constrains the projection to land in `Valid` states.

**Mock-side check.** I confirmed that `mocks/ERC20Votes.update` correctly composes ERC20-side and Votes-side mutations into a single atomic mutator. The composed `update s from to value` calls `erc20_update_pure` then `Votes.transferVotingUnits` — and the mock's `Valid.t.voting_units_eq_balance` is preserved across this composite (a Qed in the mock). So the **mock layer is sound**; the problem is purely in the equivalence-layer lens contract.

**Could a malicious inheritor satisfy `lens_voting_units_eq_balance` while having mismatched `lens_balances_correct`?**
Yes, trivially — both Hypotheses are satisfied by literally any projection function. The first six are tautologies; the seventh only restricts the projection to a Valid range.

**Does the `_update` walker write atomically?** This question has no answer at this file because no `_update` walker is bound here — the file ends at the sim-level lemmas + Section declaration. ERC20Votes.v consumers (StakingVault) would have to bind the walker; StakingVault's exchange file does so (`run_fun_deposit_4312_at_storage_base`) but as a *bundled* axiom whose post-storage is a Skolem function — there's no commitment to the actual order of ERC20-side vs Votes-side writes.

### Votes.v (`proofs/equivalence/Votes.v`)

**Section: `VotesEquivalenceTemplate`** (lines 480-538)

Three lens Hypotheses, all **TAUTOLOGIES**:

| # | Hypothesis | Probe verdict |
|---|---|---|
| 1 | `lens_delegatee_correct` (500) | `Votes.delegates (project storage) a = (project storage).(State.delegatee) a` — reflexivity |
| 2 | `lens_delegate_ckpt_correct` (505) | `Trace208.latest ((project storage).(State.delegate_ckpt) a) = Votes.getVotes (project storage) a` — reflexivity |
| 3 | `lens_total_ckpt_correct` (510) | `Trace208.latest (project storage).(State.total_ckpt) = Votes.getTotalSupply (project storage)` — reflexivity |

Note `walker_obs_getVotes` and `walker_obs_getTotalSupply` (529-536) close by `reflexivity` *without* citing the lens hypotheses — the Section's "walker observation" lemmas already collapse to identities. Confirming that the lens layer is doing no work.

### StakingVaultExchange.v (`proofs/equivalence/StakingVaultExchange.v`)

**Section `StakingVaultExchangeLens`** (lines 553-619). The `project_exchange` definition (573-597) actually reads three concrete slot indices via `List.nth_error`, which is a meaningful projection — that part is genuinely structural. The two helper Qeds `lens_totalSupply` and `lens_totalDeposited` close by `reflexivity` after `rewrite Hs`. This Section is **NOT** tautological — it does constrain the lens via the slot-indexed reads.

**Axioms** (Section 7, lines 824-890): **four `proj_post_<fn>_observes` axioms, all of the form `storage_equiv x x` — `reflexivity`-trivial.** Verified by probe:

```coq
Lemma probe_observes_provable :
  forall (storage_base : SimulatedStorage.t) (caller assets receiver now_ : U256.t),
  storage_equiv
    (proj_post_deposit_4312 storage_base caller assets receiver now_)
    (proj_post_deposit_4312 storage_base caller assets receiver now_).
Proof. intros. reflexivity. Qed.
```

`Print Assumptions probe_observes_provable` shows only `proj_post_deposit_4312 : (Parameter)` and `Set is impredicative`. The Axiom adds zero content.

**Callee-spec axioms** (Section 8, lines 915-937): four axioms `previewDeposit_callee_succeeds` etc. whose conclusion is `True`. **Vacuous.**

**Composite walker axioms** (Section 9, lines 1043-onwards): the actual load-bearing trust. `run_fun_deposit_4312_at_storage_base` (1043-1065) does NOT reference:
- `StaticCallBridge` — the asset.transferFrom external staticcall is bundled opaquely into `proj_post_deposit_4312`. There's no precondition that the asset's `balanceOf(vault)` increases by `assets`; the post-storage is a free Skolem.
- `with_nonReentrant` — the `nonReentrant` modifier sandwich is acknowledged in commentary (lines 718-735) but not reflected in the axiom statement. The reentrancy guard's invariants (status enter/exit) are not threaded through the walker.

So:
1. **Asset state binding is unconstrained.** The Skolem `proj_post_deposit_4312 storage_base caller assets receiver now` could be `storage_base` literally unchanged — the axiom still holds. Nothing in the proof tree forces the asset's balance to actually move.
2. **Reentrancy guard sandwich is not proven.** The `with_nonReentrant` wrapper is genuinely proven in `proofs/equivalence/ReentrancyGuard.v` (REN-1..6 of that file are Qed), but the StakingVaultExchange walker doesn't compose with it. The "ReentrancyGuard dependency" stays a comment.

### StakingVaultRewards.v (`proofs/equivalence/StakingVaultRewards.v`)

**Lens Hypotheses (Section 4, lines 615-639):**
- `eq_at_rewardRatio_refl/trans` — Axioms about an abstract `Parameter eq_at_rewardRatio_concrete`. Since the predicate is unconstrained, an inheritor can define it as `eq` and discharge `refl/trans` by `Qed` — but as Axioms here they contribute one trust line per slot family per relation.
- `accessControl_checkRole_returns` (827): `forall caller, is_admin caller = true -> True`. **VACUOUS.** Provable by `exact (fun _ _ => I)`.
- `rewardTokenRegistry_isRegistered_returns` (687): `forall token, is_registered token = true -> True`. **VACUOUS.**
- `keccak256_tuple2_offset_bound` (564), `keccak256_nested_offset_bound` (573): these are real upper-bound axioms about keccak; substantive.

**Composite walker axioms (Section 6):**
`run_fun_claimRewards_1010_at_proj_sim` bundles the whole claim path into one Hoare triple landing at `proj_sim_post_claimRewards_concrete sim caller tokens`. The sim's post-state model is `claim_sim_concrete = claim_each_token_concrete (accrue_all_tokens_concrete sim caller) caller tokens` — a sequential fold over tokens.

**Reentrancy zero-first defense (Section 8, lines 1190-1310):**
The OWASP SC08 closure is mechanized in `proofs/StakingVaultRewardsReentrancy.v` against the sim model `reentrancy_step` — which is a **hand-written interleaving** of outer/inner calls. The five theorems REN-1..5 are genuinely Qed (no axioms beyond the standard `Set is impredicative`). However:

**Critical disconnect.** The walker axiom `run_fun_claimRewards_1010_at_proj_sim` lands at `claim_sim_concrete` (the sequential fold), NOT at any composition of `reentrancy_step`. The reentrancy theorems are about a **parallel** model with no proven link to the on-chain walker. The "zero-first ordering at line 359 of StakingVault.sol" remains unverified at the equivalence layer — it's only proven about an abstract interleaving model where the zero-first ordering is hardcoded into the sim definition.

So: the reward-index slots vs share-token slots projection separation IS clean at the sim layer (projections distinguish `perToken`, `perUser`, `rewardRatio`, etc.), but the **zero-first defense is "assumed" via the sim's interleaving model rather than "proven" against the Yul walker's actual execution order.**

### StakingVaultDelegation.v (`proofs/equivalence/StakingVaultDelegation.v`)

**Section `StakingVaultDelegationSection`** (lines 982-1414).

**Lens Hypothesis (line 1015):** `lens_deterministic : forall s1 s2, s1 = s2 -> project_sim s1 = project_sim s2`. **TAUTOLOGY** — every Coq function is `Proper` w.r.t. `eq` (`f_equal`).

**Post-state Hypotheses (5.1-5.4):** four `proj_post_<fn>_well_formed` hypotheses (lines 1052, 1066, 1083, 1099). These have substantive shape:
```
forall sim account new_d storage_pre,
  sim = project_sim storage_pre ->
  exists storage_post,
    proj_post_delegate sim account new_d = storage_post
    /\ project_sim storage_post = sim_delegate sim account new_d
```
This says: "for every input, there exists a successor storage whose projection matches the sim's transition". This IS substantive — but discharged trivially if `project_sim` is surjective onto `SimState.t` and `proj_post_delegate` is the inverse map. The Hypothesis does NOT pin `project_sim` to the actual Yul storage layout — only requires the existence of an inverse witness.

**Composite walker axioms (6.1-6.4):** four `run_fun_<fn>_at_proj_sim` Hypotheses (1196, 1226, 1260, 1285). These are bundled trust axioms. They're stated abstractly over `Walker, State, hoare, make_state` (lines 1127-1145) — so the milestone Qeds (lines 1313-1412) are universally quantified over these and prove nothing concrete until instantiated.

**No instantiator found.** Grep for `run_fun_delegate_at_proj_sim` outside this file returns nothing. The Section is opened, the four milestone Qeds close — but no downstream file instantiates the Section's parameters against the concrete StakingVault shallow form. The "milestone Qed" terms are universally quantified over the projection lens, the Hoare-triple predicate, and the four walker axioms. `Print Assumptions run_delegate_equivalent` returns only `ECDSA.Domain.deployment_id : Set` plus `Set is impredicative` — confirming the milestone is a parametric Π that delivers no concrete commitment.

**Dual-axis Trace208 separation (sim-level):**
- `sim_delegate_preserves_opt` (line 585-597) is Qed: standard-side mutation leaves optimistic substate intact.
- `sim_delegateOptimistic_updates_opt_delegatee` (644-660) is Qed: optimistic-side mutation hits `State.opt.delegatee`.

These prove dual-axis independence at the **sim** layer. But the lens / walker layer does not require `project_sim` to actually carve up `SimulatedStorage` along the two axes — an adversarial `project_sim := fun _ => some_constant_sim_state` would still discharge the four well-formed Hypotheses if `sim_delegate` is the identity at that constant state.

### StakingVaultAdmin.v (`proofs/equivalence/StakingVaultAdmin.v`)

**Vacuous trust:**
- `checkRole_default_admin_succeeds` (166): `forall caller, has_DEFAULT_ADMIN_ROLE caller = true -> True`. **VACUOUS.**
- `versioned_version_returns_hash` (195), `versionRegistry_getLatestVersion_returns` (199), `versionRegistry_getImplementationsForVersion_returns` (204): all conclude `True`. **VACUOUS.**

**Reflexive trust:**
- All seven `proj_post_<fn>_observes` axioms (328-373) have the form `storage_equiv x x`. **All `reflexivity`-trivial.** Confirmed by probe.

**Role-check enforcement:** `has_DEFAULT_ADMIN_ROLE` is a `Parameter` (158). The Hypothesis `has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true` appears in the walker axioms' preconditions, but `has_DEFAULT_ADMIN_ROLE` is NOT tied to any actual AccessControl-slot read. It's an opaque oracle. The walker axiom does not say "the storage at slot AC-anchor at (DEFAULT_ADMIN_ROLE, caller) is set". The role check is effectively a hand-waved precondition.

**upgradeToAndCall — three staticcalls:**
`run_fun_upgradeToAndCall_2829_at_proj_sim` (831-848) bundles `_authorizeUpgrade`'s three external staticcalls (`Versioned.version`, `versionRegistry.getLatestVersion`, `versionRegistry.getImplementationsForVersion`) plus the EIP-1967 implementation-slot write plus the optional `delegatecall` to the new implementation. The axiom has NO callee-spec preconditions — the three staticcalls' return values are not constrained. The audit obligation is the entire bundled trust line, with no per-call sequencing requirement.

The three "audit witnesses" `versioned_version_returns_hash` etc. (which are `-> True`) are explicitly noted as "NOT load-bearing for the [Print Assumptions]" (line 163) — that comment is correct, but the implication is that the trust is in the bundled walker axiom, which itself has no sequencing constraint.

### ReserveOptimisticGovernor.v (`proofs/equivalence/ReserveOptimisticGovernor.v`)

**Vacuous trust:**
- `checkRole_proposer_succeeds`, `checkRole_executor_succeeds`, `checkRole_canceller_succeeds` (218-231): all `-> True`. **VACUOUS.**

**Reflexive trust:**
- `proj_post_propose_389_observes`, `proj_post_castVote_4378_observes`, `proj_post_execute_4145_observes` (804-828): all `storage_equiv x x`. **All reflexivity-trivial.** Confirmed by probe.

**Branch-shape axioms (Section 7, 1289-1349) — the optimistic vs pessimistic case-split:**
Four axioms:
- `castVote_optimistic_branch_post` (1291)
- `execute_optimistic_branch_post` (1312)
- `execute_standard_branch_post` (1332)
- `castVote_optimistic_transition_branch` (1365)

All four have the form `storage_equiv (proj_post_<fn> ...) (proj_post_<fn> ...)` where the LHS and RHS are SYNTACTICALLY IDENTICAL terms in the same Skolem. The "branch distinction" is documented in commentary but NOT reflected in the formula.

This means: **the optimistic branch's post-storage and the pessimistic branch's post-storage are claimed equal to themselves, never to different reference shapes.** A walker that always lands at `storage_base` (literally unchanged) satisfies all four.

**The `_isOptimistic` case-split is hidden behind a too-permissive axiom:**
`run_fun_castVote_4378_at_proj_sim` (line 992-1018) takes `weight : U256.t` as a **free parameter** — no precondition forces `weight` to be `_getOptimisticVotes(voter, snapshot)` on the optimistic branch or `_getVotes(voter, snapshot, params)` on the pessimistic branch. The walker axiom claims the function lands at `proj_post_castVote_4378 storage_base proposalId voter support weight now_timestamp` for **any** weight. So whatever the on-chain dispatch computes, the audit doesn't constrain.

The walker axiom has a `H_optimistic_gate` precondition (line 1007-1010): `p_sim.(Proposal.isOptimistic) = true -> support = 0`. This is correct — for optimistic proposals, only Against (support=0) is allowed by `_countVote`. But that's a statement about the sim-side proposal, not a statement about what storage shape the contract lands at.

### GovernorBase.v (`proofs/equivalence/GovernorBase.v`)

**THE WORST CASE — degenerate lens Hypotheses (Section 11, lines 1295-1308):**

```coq
Hypothesis lens_proposals_correct :
  forall (storage : SimulatedStorage.t) (pid : ProposalId),
    (project_base storage).(State.proposals) pid
    = (project_base storage).(State.proposals) pid.    (* x = x *)

Hypothesis lens_governance_call_correct :
  forall (storage : SimulatedStorage.t),
    (project_base storage).(State.governance_call)
    = (project_base storage).(State.governance_call).  (* x = x *)

Hypothesis lens_clock_correct :
  forall (storage : SimulatedStorage.t),
    (project_base storage).(State.clock)
    = (project_base storage).(State.clock).            (* x = x *)
```

All three hypotheses are **literally `x = x`** — the LHS and RHS are SYNTACTICALLY THE SAME TERM. Provable for any `project_base` by `intros; reflexivity`. They contribute zero content.

This is a copy/paste error or oversight. The intent was presumably:

```coq
Hypothesis lens_proposals_correct :
  forall storage pid,
    (project_base storage).(State.proposals) pid
    = <something derived from storage>(pid).      (* the inheritor's actual storage lookup *)
```

But what's there is `x = x`. Confirmed by probe.

## Cross-cutting findings

### Pattern 1 — "lens hypothesis" is a no-op

In ALL multi-base files (`Votes.v`, `ERC20Votes.v`, `GovernorBase.v`), the lens-correctness Hypotheses are tautologies provable by `reflexivity` for any projection function. They constrain `project_*` only by its codomain type. This is **systematic** — the methodology template (R072) was instantiated incorrectly.

The intended shape (per R072's prose) is "the projected substate's field equals the inheritor's storage at the right slot". The actual shape is "the projected substate's field equals the projected substate's field". The latter is universally true and adds nothing.

### Pattern 2 — `storage_equiv x x` observational bridges

In ALL R070-shape files (StakingVaultExchange, StakingVaultAdmin, ReserveOptimisticGovernor), the per-target observational bridge axioms have the form `storage_equiv x x`. They're declared `Axiom` but provable by `reflexivity` from the `Parameter` declaration of the corresponding `proj_post_*`. They claim to encode an audit obligation tying the Skolem post-storage to a "reference shape derived from the sim's post-state" — but the reference shape never appears in the formula.

A future tightening pass needs to replace these with non-trivial obligations of shape:
```coq
Axiom proj_post_deposit_4312_observes :
  forall (storage_base : SimulatedStorage.t) (caller assets receiver now_ : U256.t),
    (* concrete characterization: post = base with slot updates *)
    proj_post_deposit_4312 storage_base caller assets receiver now_
    = update_slot_3 (...) (update_slot_12 (...) (update_slot_13 (...) storage_base)).
```

As stated today, every "observational bridge axiom" is a no-op.

### Pattern 3 — `-> True` audit witnesses

`checkRole_*_succeeds`, `versioned_*_returns`, `versionRegistry_*_returns`, `accessControl_checkRole_returns`, `rewardTokenRegistry_isRegistered_returns` — all have conclusion `True`. They are documented as "not load-bearing" in the file commentary, which is correct (Print Assumptions on the milestone theorems doesn't show them). But they DO appear in the trust ledger as `Axiom` declarations — they should be `Definition foo := fun _ _ => I.` since they're literally `True` lemmas.

The risk: a reader scanning `Axiom` declarations gets a false impression of substantive obligations. The number of axioms reported in the trust budget is inflated by vacuous declarations.

### Pattern 4 — bundled walker axioms swallow sequencing constraints

Every `run_fun_*_at_proj_sim` axiom in the StakingVault* and ReserveOptimisticGovernor files bundles a long chain of Yul body operations into a single Hoare triple landing at an opaque `proj_post_*` Skolem. There is no:

- Per-step ordering constraint (which is critical for the reentrancy zero-first defense and for the three-staticcall sequencing in `_authorizeUpgrade`).
- Per-staticcall callee-spec hypothesis (the asset.transferFrom in `deposit`, the three staticcalls in `_authorizeUpgrade`, the `_getOptimisticVotes` staticcall in `castVote`).
- Branch case-split discharge (the `_isOptimistic` dispatch in `castVote` and `execute`).

These are all noted as "Wave 2" tightening targets in the file commentary. Until they land, the milestone Qeds carry no semantic commitment beyond what the bundled axioms claim.

### Pattern 5 — sim-level safety properties not bound to walker behavior

The reentrancy zero-first defense (`reentrancy_step` model, REN-1..5) is proven about an abstract interleaving sim that hardcodes the zero-first ordering. The walker axiom (`run_fun_claimRewards_1010_at_proj_sim`) lands at a DIFFERENT sim model (`claim_sim_concrete`, a sequential fold). There's no proven bridge between the two. The OWASP SC08 closure is conditional on the assumption that the Yul body actually executes its operations in the zero-first order — and that assumption is encoded in the sim definition, not in the equivalence proof.

### Pattern 6 — Sections opened but never instantiated

- `Section ERC20VotesEquivalenceTemplate` in `ERC20Votes.v` — never instantiated anywhere.
- `Section VotesEquivalenceTemplate` in `Votes.v` — never instantiated anywhere.
- `Section StakingVaultDelegationSection` in `StakingVaultDelegation.v` — never instantiated. The milestone Qeds become universally quantified over the Section parameters.
- `Section GovernorBaseEquivalenceTemplate` in `GovernorBase.v` — never instantiated.

Grep confirms no downstream file binds these Section parameters to concrete shallow-form values. The "slot-agnostic methodology" delivers methodology but not yet a binding.

## CRITICAL findings

A "cross-contamination path that lets an honest-looking instantiation produce wrong behavior":

### CRITICAL-1 — GovernorBase.v lens Hypotheses are syntactically `x = x`

All three lens hypotheses in `Section GovernorBaseEquivalenceTemplate` (lines 1295-1308) have the form:
```coq
forall storage, project_base storage's_field = project_base storage's_field.
```

That is, LHS and RHS are SYNTACTICALLY identical. There is no constraint on `project_base` whatsoever. A future inheritor (ReserveOptimisticGovernor or any consumer of GovernorBase) opens this Section and discharges all three by `reflexivity` while supplying a `project_base` that has NO connection to the inheritor's actual SimulatedStorage. This is the most degenerate case I found — the others are at least "tautological under the unfolds", but here both sides are the *same term*.

### CRITICAL-2 — `_isOptimistic` case-split is not discharged in any branch axiom

The four optimistic/pessimistic branch axioms in `ReserveOptimisticGovernor.v` (Section 7) all assert `storage_equiv (proj_post_castVote_4378 ...) (proj_post_castVote_4378 ...)` or `storage_equiv (proj_post_execute_4145 storage_base pid TRUE now) (proj_post_execute_4145 storage_base pid TRUE now)` and similarly for `FALSE`. They claim to characterize the per-branch post-storage but only state `x = x`. **The optimistic branch's post-storage and the pessimistic branch's post-storage are NEVER claimed to differ.** A walker that always lands at `storage_base` unchanged satisfies all four.

Combined with the fact that `_isOptimistic(pid)` is defined as `vetoThreshold(pid) != 0` (line 1434-1437 of ReserveOptimisticGovernor.v) and that `vetoThreshold` is read from the OG-specific `optimisticProposalDetails[pid]` slot — there is no proof that the dispatch actually case-splits on this slot. A malicious inheritor could supply walker axioms where the optimistic branch and the pessimistic branch land at the same opaque post-storage, and the milestone theorem still closes.

### CRITICAL-3 — ERC20Votes coupling at the lens layer is weaker than at the mock layer

The mock's `Valid.t.voting_units_eq_balance` is preserved by `update` (Qed). But the Section-level `lens_voting_units_eq_balance` Hypothesis (line 582-585) does NOT say "the projection of the inheritor's storage at the voting-units slot agrees with the projection at the balances slot." It only says "the `voting_units` field of the projected state agrees with the `balanceOf` of the projected state." For ANY function `project : SimulatedStorage.t -> State.t` that happens to land in a Valid sim state, this is automatic.

So if a malicious inheritor's actual on-chain storage has voting_units at slot 7 holding 100 while balances at slot 0 holds 200, the inheritor can still discharge `lens_voting_units_eq_balance` by supplying a `project_erc20votes` that returns a sim state where both fields are 0 (or any other coupled pair). The mismatch between sim-level "coupling" and storage-level "coupling" is invisible to the equivalence layer.

### CRITICAL-4 — asset.transferFrom external state binding is unproven

`run_fun_deposit_4312_at_storage_base` produces a `proj_post_deposit_4312 storage_base ... assets receiver ...` post-storage with no claim about what happens to the asset's `balanceOf(vault)`. The reference shape documented in the comment (line 1029-1031) — "asset.balanceOf(vault) += assets, asset.balanceOf(caller) -= assets, asset.allowance[caller][vault] -= assets" — is in the comment, not in the axiom.

So: even if the milestone Qed `run_deposit_equivalent` closes, it does NOT prove that the user's tokens actually moved to the vault. The Skolem `proj_post_deposit_4312` could be `storage_base` literally unchanged — and the audit signs off.

### CRITICAL-5 — Reentrancy guard sandwich is in the comment, not the proof

The `with_nonReentrant` wrapper from `proofs/equivalence/ReentrancyGuard.v` is genuinely proven (with_nonReentrant_post_status_not_entered, with_nonReentrant_nested_enter_reverts, etc.). But NO walker axiom in StakingVaultExchange.v, StakingVaultAdmin.v, or StakingVaultRewards.v actually uses `with_nonReentrant`. The reentrancy guard's enter/exit invariants are documented but not threaded.

So: the exchange paths `deposit`, `mint`, `withdraw`, `redeem` are declared `nonReentrant` in commentary but the equivalence proof never proves the lock is taken on entry or released on exit. A reentrancy attack would not be visible to the proof.

## Recommendations

### Recommendation 1 — fix the lens hypothesis pattern

Every `lens_*_correct` Hypothesis should have a substantive RHS. Replace:
```coq
Hypothesis lens_balances_correct :
  forall storage account,
    balanceOf (project storage) account = ERC20.balanceOf (project storage).(State.erc20) account.
```
with:
```coq
Hypothesis lens_balances_correct :
  forall storage account,
    balanceOf (project storage) account
    = match List.nth_error storage slot_balances with
      | Some (StorableValue.U256 m) => (* mapping lookup *)
      | _ => 0
      end.
```

The exchange-rate file's `project_exchange` (Section 2 of StakingVaultExchange.v, lines 573-597) is the right shape — `nth_error storage slot_*` reads. Every multi-base file's lens should follow that template.

### Recommendation 2 — eliminate `storage_equiv x x` axioms

Either:
- Replace with `Definition foo := fun _ _ => storage_equiv_refl.` (downgrade Axiom → Qed-grade Definition), to honestly reflect that they're not audit obligations.
- Replace the RHS with the actual reference shape (storage_base with the relevant slot anchors updated), making the axiom a real obligation.

### Recommendation 3 — eliminate `-> True` axioms

The audit witnesses with `-> True` conclusions (`checkRole_*_succeeds`, `versioned_*_returns`, `versionRegistry_*_returns`) should be Definitions, not Axioms. They contribute nothing to the trust budget and inflate the axiom count.

### Recommendation 4 — add branch-distinguishing axioms for `_isOptimistic`

The four branch axioms in ReserveOptimisticGovernor.v Section 7 should differ in their RHS. Specifically:

```coq
Axiom castVote_optimistic_branch_post :
  forall storage_base proposalId voter weight ...,
    p_sim.(isOptimistic) = true ->
    storage_equiv
      (proj_post_castVote_4378 storage_base proposalId voter 0 weight now_timestamp)
      (* the optimistic-branch reference: storage_base with +weight on vetoVotes slot *)
      (slot_update VETO_VOTES storage_base (+ weight)).

Axiom castVote_pessimistic_branch_post :
  forall storage_base proposalId voter support weight ...,
    p_sim.(isOptimistic) = false ->
    storage_equiv
      (proj_post_castVote_4378 storage_base proposalId voter support weight now_timestamp)
      (* the pessimistic-branch reference: storage_base with +weight on the relevant tally slot *)
      ...
```

As stated, the two branches collapse to the same Skolem with no distinction.

### Recommendation 5 — bind `with_nonReentrant` into the walker axioms

The composite walker axioms for `deposit`, `mint`, `withdraw`, `redeem`, `claimRewards`, `setRewardRatio`, `setUnstakingDelay`, `_authorizeUpgrade`, `upgradeToAndCall`, `grantRole`, `revokeRole`, `renounceRole` should be restated as:

```coq
Axiom run_fun_deposit_4312_with_nonReentrant :
  ...
  status_at_entry = NotEntered ->
  with_nonReentrant
    (project_reentrancy_guard storage_base)
    (fun s_entered =>
       (* deposit body — must produce its post-state from s_entered *)
       ...)
  = Result.Success (post_state, return_value).
```

This threads the enter/exit invariants through the walker.

### Recommendation 6 — fix GovernorBase.v lines 1295-1308

The three `x = x` Hypotheses should be replaced with substantive lens correctness statements. Likely intended:

```coq
Hypothesis lens_proposals_correct :
  forall storage pid,
    (project_base storage).(State.proposals) pid
    = lookup_proposal_at_slot storage slot_proposals pid.
```

As written, they constrain `project_base` by literally nothing.

### Recommendation 7 — connect reentrancy_step to claim_sim_concrete

The OWASP SC08 closure should include a proven bridge:
```coq
Theorem claim_sim_via_reentrancy :
  forall sim caller token,
    (* the single-token claim composes the outer-then-inner-then-outer of reentrancy_step *)
    claim_each_token_concrete sim caller [token]
    = reentrancy_step_to_sim sim caller token
       (StakingVaultRewardsReentrancy.reentrancy_step
          (get_reward_info sim token)
          (get_user_reward sim token caller)).
```

Without this bridge, REN-1..5 are about a parallel model that the walker never visits.

### Recommendation 8 — surface callee-spec preconditions in the upgrade path

`run_fun_upgradeToAndCall_2829_at_proj_sim` should take three callee-spec hypotheses (one per staticcall) tying the return values to the post-storage shape. Without them, the bundled axiom doesn't enforce the sequencing of `Versioned.version` → `getLatestVersion` → `getImplementationsForVersion` → revert if mismatch.

## Summary counts

| Category | Count |
|---|---|
| Tautological lens hypotheses (provable by `reflexivity` for any projection) | 12 (6 in ERC20Votes.v, 3 in Votes.v, 3 in GovernorBase.v) |
| `storage_equiv x x` observational-bridge axioms | 14 (4 in StakingVaultExchange.v, 7 in StakingVaultAdmin.v, 3 in ReserveOptimisticGovernor.v) |
| `-> True` "callee witness" axioms | 8 (3 in StakingVaultAdmin.v, 3 in ReserveOptimisticGovernor.v, 1 in StakingVaultRewards.v `accessControl_checkRole_returns`, 1 in StakingVaultRewards.v `rewardTokenRegistry_isRegistered_returns`) |
| Branch-shape axioms that collapse to a single Skolem | 4 in ReserveOptimisticGovernor.v Section 7 |
| Sections opened but never instantiated | 4 (ERC20Votes / Votes / StakingVaultDelegation / GovernorBase Section templates) |
| Vacuous Hypotheses (e.g. `lens_deterministic`) | 1 in StakingVaultDelegation.v |

**Total no-op / vacuous trust-budget items:** ~43 across the multi-base files.

## Single most concerning composition pattern

**The `storage_equiv x x` observational-bridge axiom + branch-axiom pattern in ReserveOptimisticGovernor.v Section 7.**

This is the single most concerning composition pattern because:

1. It claims to characterize the `_isOptimistic` case-split — the crucial multi-base composition between `GovernorBase` (which defines `state()` as a function of `_proposals[pid]`) and `ReserveOptimisticGovernor` (which adds an `optimisticProposalDetails[pid].vetoThreshold` slot whose nonzero value flips `_isOptimistic` to true).
2. The four branch axioms have IDENTICAL Skolem terms on both sides of `storage_equiv`. They do not say the optimistic branch lands somewhere DIFFERENT from the pessimistic branch.
3. The optimistic-branch axiom and the pessimistic-branch axiom for `execute` (`execute_optimistic_branch_post` and `execute_standard_branch_post`) both assert `storage_equiv (proj_post_execute_4145 storage_base proposalId b now_timestamp) (proj_post_execute_4145 storage_base proposalId b now_timestamp)` with different values of `b` (true vs false). Each axiom is independently a tautology, but together they leave the case-split entirely uncommitted: nothing forces the optimistic branch to bypass the timelock while the pessimistic branch dispatches through it. They could both produce the same opaque Skolem.

This is the canonical "lens hypothesis is too weak to constrain both substates simultaneously" pattern from the task: the `GovernorBase` substate (slots `_proposals`, `_governanceCall`) and the `OptimisticGovernor` substate (slots `optimisticProposalDetails`) need to be jointly constrained so that `_isOptimistic(pid) = true` *iff* the OG-side slot is nonzero — but the lens does no such joint constraining, and the walker axioms don't either.

If a real adversary supplied a `proj_post_castVote_4378` that ignored `_isOptimistic` entirely and always counted votes through the pessimistic tally, every axiom in this file would still discharge. The veto-counting walker's post-state could be IDENTICAL to the standard-counting walker's post-state, and the proof tree would not notice.
