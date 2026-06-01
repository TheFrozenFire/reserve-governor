# Skolemization-soundness audit

**Date:** 2026-05-31
**Auditor vantage:** Skolemization-soundness
**HEAD:** `dbf4844` (`thefrozenfire/feature/formal-verification`)
**Method:** `Print Assumptions` on every milestone theorem, then read each
load-bearing Parameter / Axiom and determine whether an adversarial
instantiation can satisfy it without committing to the intended semantics.

The audit asks one question per milestone: *if I'm an adversarial
inheritor who must supply concrete Definitions for every Parameter and
prove every Axiom, can I pick degenerate values (`identity`, `True`,
`empty_storage`) and still close the milestone?* If yes -> VACUOUS. If
constrained but still allows obviously-wrong instantiations -> WEAK. If
the post-storage is pinned to a concrete shape (Definition or
constrained Parameter) -> TIGHT / PROVABLE.

## Inventory of milestone theorems by Skolemization status

| File / Theorem | Post-storage shape | Load-bearing bridge axiom | Classification |
|---|---|---|---|
| `Guardian.run_grantRole_1359_equivalent` | Concrete `Dict.declare_or_assign` post built from per-slot sstore axioms; statement uses `observationally_eq_storage storage' (proj_sim sim')` with a real `Definition`-based predicate | n/a (per-slot sload/sstore axioms; Qed-closed) | **TIGHT** (Qed) |
| `Guardian.run_revokeRole_1378_equivalent` | `set_eq_at_role storage' (proj_sim sim')` (concrete Definition) | `run_fun__revokeRole_736_at_proj_sim_member` constrains existential `storage_post` via `set_eq_at_role` | **TIGHT** |
| `Guardian.run_cancel_equivalent_make_state` | `observationally_eq_storage storage' (proj_sim sim)` -- storage UNCHANGED | `run_fun_cancel_238_at_proj_sim_{admin,guardian}` directly assert post-storage = `proj_sim sim` | **TIGHT** (but see VAC-G1 below -- `proposalId` is forall-bound) |
| `VersionRegistry.run_deprecateVersion_equivalent_make_state` | `Definition proj_sim_post_deprecate sim hash := [Map ...; Map (declare_or_assign ...); U256 ...]` -- closed form | `proj_sim_deprecate_at_observes` ties this to `proj_sim (deprecate_at sim i)` under concrete `observationally_eq_storage_vr` | **PROVABLE** |
| `VersionRegistry.run_registerVersion_equivalent_make_state` | `Definition proj_sim_post_register` -- closed form | `proj_sim_register_at_observes` ties to `proj_sim new_sim` under concrete predicate | **PROVABLE** |
| `RewardTokenRegistry.run_registerRewardToken_equivalent_make_state` | `Parameter proj_sim_post_register_reward_token` | `proj_sim_register_reward_token_observes` asserts `set_eq_in_registry post (proj_sim new_sim)` -- `set_eq_in_registry` is a `Definition` reading slot-1 | **WEAK** (slot 1 constrained; slots 0, 2+ free -- but milestone conclusion only claims `set_eq_in_registry`, so consistent with stated abstraction) |
| `RewardTokenRegistry.run_unregisterRewardToken_equivalent_make_state` | symmetric | symmetric | **WEAK** (same shape) |
| `ReserveOptimisticGovernor.run_propose_equivalent` | `Parameter proj_post_propose_389 : SimulatedStorage.t -> ... -> SimulatedStorage.t` | reflexive: `storage_equiv (proj_post X args) (proj_post X args)` -- NOT load-bearing | **VACUOUS** |
| `ReserveOptimisticGovernor.run_castVote_equivalent` | symmetric | reflexive | **VACUOUS** |
| `ReserveOptimisticGovernor.run_execute_equivalent` | symmetric | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_setUnstakingDelay_equivalent` | `Parameter proj_post_setUnstakingDelay_750` | reflexive (not load-bearing) | **VACUOUS** |
| `StakingVaultAdmin.run_setNativeRewardRate_equivalent` | `Parameter proj_post_setRewardRatio_1036` | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_grantRole_equivalent` | `Parameter proj_post_grantRole_13574` | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_revokeRole_equivalent` | `Parameter proj_post_revokeRole_13593` | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_renounceRole_equivalent` | `Parameter proj_post_renounceRole_13616` | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_authorizeUpgrade_equivalent` | `Parameter proj_post_authorizeUpgrade_1574` | reflexive | **VACUOUS** |
| `StakingVaultAdmin.run_upgradeToAndCall_equivalent` | `Parameter proj_post_upgradeToAndCall_2829` | reflexive | **VACUOUS** |
| `StakingVaultRewards.run_setRewardRatio_equivalent_make_state` | `Parameter proj_sim_post_setRewardRatio_concrete` | `proj_sim_setRewardRatio_observes_concrete` uses `eq_at_rewardRatio_concrete` -- itself a free `Parameter : Storage -> Storage -> Prop` constrained only by refl + trans | **VACUOUS** (predicate degeneratable to `fun _ _ => True`) |
| `StakingVaultRewards.run_poke_equivalent_make_state` | symmetric | symmetric | **VACUOUS** |
| `StakingVaultRewards.run_claimRewards_equivalent_make_state` | symmetric | symmetric | **VACUOUS** |
| `StakingVaultExchange.run_deposit_equivalent` | `Parameter proj_post_deposit_4312`, **AND `fun_deposit_4312_op` is itself a free Parameter** (shallow form not bound) | reflexive | **VACUOUS²** (function and post-state both free) |
| `StakingVaultExchange.run_mint_equivalent` | symmetric | reflexive | **VACUOUS²** |
| `StakingVaultExchange.run_withdraw_equivalent` | symmetric | reflexive | **VACUOUS²** |
| `StakingVaultExchange.run_redeem_equivalent` | symmetric | reflexive | **VACUOUS²** |
| `StakingVaultDelegation.run_delegate_equivalent` | Section-bound `Variable proj_post_delegate` | Section `Hypothesis proj_post_delegate_well_formed`: `project_sim post = sim_delegate sim ...` -- universally quantified at closure | **TIGHT (parameterized)** -- cannot be vacuously instantiated; inheritor must supply concrete walker + lens + post-storage + prove the hypothesis |
| `StakingVaultDelegation.run_delegateOptimistic_equivalent` | symmetric | symmetric | **TIGHT (parameterized)** |
| `StakingVaultDelegation.run_delegateBySig_equivalent` | symmetric | symmetric | **TIGHT (parameterized)** |
| `StakingVaultDelegation.run_delegateOptimisticBySig_equivalent` | symmetric | symmetric | **TIGHT (parameterized)** |

**Counts**: VACUOUS=14 - WEAK=2 - TIGHT=3 - TIGHT(parameterized)=4 - PROVABLE=2 - Total milestones=25

## VACUOUS findings (highest priority)

### VAC-ROG-{1,2,3} -- `ReserveOptimisticGovernor` propose / castVote / execute

**What the milestone claims** (text of `run_propose_equivalent`,
lines 1119-1164):

```coq
let state := make_state env state_base memory storage_base in
exists state' result,
  {{? codes, env, Some state | fun_propose_389 ... -> Result.Ok result | state' ?}}
  /\ (exists memory',
      state' = Some (make_state env state_base memory'
                       (proj_post_propose_389 storage_base pid
                          env.(Environment.caller) votingDelay votingPeriod now_timestamp))
      /\ storage_equiv
           (proj_post_propose_389 storage_base pid ...)
           (proj_post_propose_389 storage_base pid ...)).
```

**What it actually constrains** -- the storage clause is literally
`storage_equiv X X` where `storage_equiv := eq`. The Qed body discharges
it with `apply storage_equiv_refl`. The clause is **structurally
tautological**: it would hold for **any** instantiation of
`proj_post_propose_389`, including `fun _ _ _ _ _ _ => []` (empty
storage) or `fun s _ _ _ _ _ => s` (identity / no-op).

The actual content lives in `run_fun_propose_389_at_proj_sim` (the
composite walker axiom). That axiom states a Hoare triple
about the concrete shallow form's `fun_propose_389`, whose conclusion
post-state is `proj_post_propose_389 storage_base pid ...`. Because
`proj_post_propose_389` is a free Parameter, an adversarial
instantiation can:

  1. Pick `proj_post_propose_389 := fun s _ _ _ _ _ => s` (identity).
  2. Assert `run_fun_propose_389_at_proj_sim` (the axiom is now: "for
     any inputs `fun_propose_389` reaches `Result.Ok` with storage
     unchanged"). This is a *postulate*, never proved.
  3. The milestone closes trivially.

The audit reader has **no signal** from the milestone statement that
`fun_propose_389` mutates `_proposals[pid]`, writes voting delay /
voting period, etc. The advertised semantics live entirely in
docstrings (lines 850-895) which are not machine-checked.

Three documentation-only axioms `castVote_optimistic_branch_post`,
`execute_optimistic_branch_post`, `execute_standard_branch_post` and
the side-exit `castVote_optimistic_transition_branch` were intended
to expose per-branch shape. Each is `storage_equiv (proj_post X) (proj_post X)`
-- also reflexive, also vacuous, also not load-bearing.

**Suggested fix**: replace each reflexive bridge axiom with the
GovernorBase-projection bridge already flagged in the file's Wave 2
comments (lines 1405-1417). Concretely, instantiate
`project_governor_base : SimulatedStorage.t -> Governor.State.t` (or
import it once `GovernorBase.v` lands) and state:

```coq
Axiom proj_post_propose_389_observes :
  forall storage_base pid proposer votingDelay votingPeriod now,
    project_governor_base
      (proj_post_propose_389 storage_base pid proposer votingDelay votingPeriod now)
    = sim_propose (project_governor_base storage_base) pid proposer
                  votingDelay votingPeriod now.
```

Then route the milestone conclusion through this bridge (as
`StakingVaultDelegation` does via the `well_formed` hypotheses), so an
identity instantiation falsifies the bridge.

### VAC-ADMIN-{1..7} -- `StakingVaultAdmin` seven mutators

Same pattern as VAC-ROG. Each of `run_setUnstakingDelay_equivalent`,
`run_setNativeRewardRate_equivalent`, `run_grantRole_equivalent`,
`run_revokeRole_equivalent`, `run_renounceRole_equivalent`,
`run_authorizeUpgrade_equivalent`, `run_upgradeToAndCall_equivalent`
ends its storage clause with `storage_equiv (proj_post X) (proj_post X)`.

**Empirical confirmation** -- `Print Assumptions
StakingVaultAdminEquivalence.run_grantRole_equivalent` returns exactly:

  - `run_fun_grantRole_13574_at_proj_sim` (composite walker axiom)
  - `proj_post_grantRole_13574` (free Parameter)
  - `has_DEFAULT_ADMIN_ROLE` (caller-side gate Parameter)
  - + framework axioms (Memory/Storage encoding, PrimInt63)

**The seven `proj_post_<fn>_observes` axioms are NOT in the assumption
list.** They are documentation-only, by construction.

**Particular danger** -- `grantRole` / `revokeRole` are the headline
AccessControl mutators. The audit chain "AccessControl flips bit at
keccak slot" lives entirely in the docstring (lines 512-569) and the
inheritor-of-Guardian R055/R059/R068 lemmas which the docstring
*claims* discharge under abstract storage_base. The milestone itself
asserts nothing about the AccessControl namespace slot.

**Suggested fix** -- for each mutator, replace the reflexive
`_observes` axiom with a per-slot Definition pinning the relevant
namespace. For `setUnstakingDelay`, this is concrete and easy:

```coq
Definition proj_post_setUnstakingDelay_750
    (storage_base : SimulatedStorage.t) (delay : U256.t) : SimulatedStorage.t :=
  set_slot_u256 storage_base SLOT_unstakingDelay delay.

Lemma proj_post_setUnstakingDelay_750_pins_slot_5 :
  forall sb d, slot_at (proj_post_setUnstakingDelay_750 sb d) 5 = SValue.U256 d.
Proof. reflexivity. Qed.
```

For `grantRole` / `revokeRole`, lift the existing R055/R059 closed
lemmas from `Guardian.v` (which already prove the closed-form slot
shape under the right preconditions) and instantiate them at the
StakingVault `storage_base` lens.

### VAC-REW-{1,2,3} -- `StakingVaultRewards` setRewardRatio / poke / claimRewards

Worse than VAC-ROG/VAC-ADMIN: the file *appears* to have real
observational bridges, but they're stated over abstract Parameters.

```coq
Parameter eq_at_rewardRatio_concrete  : SimulatedStorage.t -> SimulatedStorage.t -> Prop.
Parameter eq_at_reward_info_concrete  : SimulatedStorage.t -> SimulatedStorage.t -> Address -> Prop.
Parameter eq_at_user_reward_concrete  : SimulatedStorage.t -> SimulatedStorage.t -> Address -> Address -> Prop.

Axiom eq_at_rewardRatio_refl  : forall s,     eq_at_rewardRatio_concrete s s.
Axiom eq_at_rewardRatio_trans : ... (transitivity).
(same for the other two)
```

The bridge axiom `proj_sim_setRewardRatio_observes_concrete` asserts:

```coq
eq_at_rewardRatio_concrete
  (proj_sim_post_setRewardRatio_concrete sim halfLife)
  (proj_sim_concrete (set_reward_ratio_sim sim halfLife))
```

**Adversarial instantiation**:

  - `eq_at_rewardRatio_concrete := fun _ _ => True` -- satisfies
    reflexivity and transitivity trivially.
  - `eq_at_reward_info_concrete  := fun _ _ _ => True` -- ditto.
  - `eq_at_user_reward_concrete  := fun _ _ _ _ => True` -- ditto.
  - `proj_sim_post_setRewardRatio_concrete := fun _ _ => []` -- empty
    storage; bridge collapses to `True`.
  - `proj_sim_concrete := fun _ => []` -- also empty; the milestone's
    inner clauses all reduce to `True`.

The milestone conclusion `eq_at_X_concrete storage_post (proj_sim_concrete new_sim)` becomes `True` in every clause. Vacuous.

The walker axioms `run_fun_setRewardRatio_1036_at_proj_sim` etc. are
the only non-vacuous content; they assert a Hoare triple about the
real shallow form's `fun_setRewardRatio_1036`. But because
`proj_sim_post_setRewardRatio_concrete` is free, the same identity
trick from VAC-ADMIN applies: the trust budget admits a no-op
instantiation.

**Suggested fix** -- promote the three predicates from `Parameter` to
`Definition`. The intended definitions are even sketched in the
docstring (lines 591-602): `eq_at_rewardRatio s1 s2 := slot-3 read equal`,
etc. Concretely:

```coq
Definition eq_at_rewardRatio_concrete (s1 s2 : SimulatedStorage.t) : Prop :=
  slot_u256_at s1 3 = slot_u256_at s2 3.

Definition eq_at_reward_info_concrete (s1 s2 : SimulatedStorage.t) (t : Address) : Prop :=
  forall offset : Z, 0 <= offset < 5 ->
    slot_at s1 (reward_info_anchor t + offset) =
    slot_at s2 (reward_info_anchor t + offset).

(* and similarly for eq_at_user_reward_concrete *)
```

That collapses the soundness gap to a single audit-time obligation
(the per-mutator `_observes_concrete` axiom would then carry real
content).

### VAC-EX-{1..4} -- `StakingVaultExchange` deposit / mint / withdraw / redeem

The full vacuity pattern from VAC-ADMIN, PLUS an additional layer:
`fun_deposit_4312_op : U256.t -> U256.t -> M.t U256.t` is itself a
`Parameter`, not bound to the shallow form. Confirmed in
`Print Assumptions`:

```
StakingVaultExchangeEquivalence.fun_deposit_4312_op :
  RocqOfSolidity.U256.t -> RocqOfSolidity.U256.t -> M.t RocqOfSolidity.U256.t
```

The composite walker axiom `run_fun_deposit_4312_at_storage_base`
therefore asserts a Hoare triple about an ABSTRACT function. An
adversary picks:

  - `fun_deposit_4312_op := fun _ _ => M.pure 0` (no-op returning 0).
  - `proj_post_deposit_4312 := fun s _ _ _ _ => s` (identity).

Both Parameters satisfy their types; the composite walker axiom is a
trivially-true Hoare triple ("the no-op walker reaches Result.Ok with
storage unchanged"). The milestone closes.

The file has a comment (lines 947-963) explicitly acknowledging this:
*"the shallow form is gated in `_RocqProject` behind a comment block ...
For this Wave 2 scaffold we accept the four Yul entry-points as opaque
[M.t U256.t] Parameters; when the shallow form is activated, the
Parameters become Notations aliasing the shallow-form Definitions."*
The `_RocqProject` does in fact include `StakingVault_shallow.v` (line
266), and `StakingVaultAdmin.v` and `StakingVaultRewards.v` both
`Require Import` the shallow form -- but `StakingVaultExchange.v` does
not. **So this Wave-2 wiring did not land in `StakingVaultExchange`,
and the `_op` Parameters remain free.**

**Suggested fix** -- add `Require Import
ReserveGovernor.generated.StakingVault_shallow.` and replace the four
`Parameter fun_<op>_op` with `Definition` aliases to the real shallow
functions (`Definition fun_deposit_4312_op := fun_deposit_4312.`). This
forces the composite walker axiom to assert a property of the real
shallow function. Combined with the VAC-ADMIN fix, this removes the
double-degeneracy.

### VAC-G1 -- `Guardian.run_cancel_equivalent_make_state` walker axiom shape

A subtler soundness issue: the two cancel walker axioms have shape

```coq
Axiom run_fun_cancel_238_at_proj_sim_admin :
  forall codes env state_base sim memory governor
         ... (proposalId : U256.t),
    ... preconditions ... ->
    exists memory',
      {{? ... | fun_cancel_238 governor ... -> Result.Ok proposalId | ... (proj_sim sim) ?}}.
```

`proposalId` is **forall-bound** in the axiom, not existential. The axiom
asserts: "for every chosen `proposalId : U256.t`, there exists an
execution of `fun_cancel_238` that returns that exact value."

This is incompatible with deterministic Yul semantics (the function's
return value is determined by the staticcall to `governor.getProposalId`),
and as an axiom it postulates a non-deterministic walker. As a postulate,
it is *stronger than the truth*. The milestone uses `getProposalId_oracle key`
as the chosen value, so the milestone's particular Hoare triple is
recovered.

The companion `igovernor_getProposalId_returns_pid` axiom is
`True`-conclusioned (literally `forall _ _ _, True`), so it imposes no
constraint on the staticcall return.

The milestone is therefore TIGHT on storage (the walker pins
`proj_sim sim`), but WEAK on return-value: the axiom is broader than
the real function's actual behavior. The Print Assumptions trace
confirms this is the load-bearing axiom for `run_cancel_equivalent_make_state`.

**Suggested fix** -- replace the universal `proposalId` quantifier with
an existential (or condition the equality on the staticcall's
deterministic return):

```coq
Axiom run_fun_cancel_238_at_proj_sim_admin :
  forall codes env state_base sim memory governor ... key,
    ... preconditions ... ->
    exists memory',
      {{? ... | fun_cancel_238 ... -> Result.Ok (getProposalId_oracle key) | ... ?}}.
```

This pins the return value to the oracle's deterministic output.

## WEAK findings

### WEAK-RTR-{1,2} -- `RewardTokenRegistry` register / unregister

The bridge `set_eq_in_registry` is a real `Definition` reading slot 1
(the positions map). The bridge axiom asserts `set_eq_in_registry post
(proj_sim new_sim)`. This constrains the post-storage's slot 1 to agree
on membership with the sim post-state.

**Adversarial instantiation that passes the bridge but corrupts slots
0, 2+**:

  - `proj_sim_post_register_reward_token sim token :=
       [garbage ; correct_slot_1_only ; garbage ; ...]`

where `correct_slot_1_only` is computed to satisfy
`contains_in_registry token = true` after the register. The bridge
holds; the milestone closes; but the SimulatedStorage layout that the
walker is asserted to produce is wrong on every slot except 1.

This is consistent with the milestone's stated conclusion
(`set_eq_in_registry storage_post (proj_sim new_sim)` -- only membership
asserted), so the milestone's contract is honored. But the trust
budget extends through the *composite walker axiom*, which asserts a
Hoare triple producing this same `proj_sim_post_register_reward_token`
post-storage. An adversary's identity-on-slots-0+2 instantiation makes
the composite walker axiom assert: "after register, the walker reaches
storage [garbage; correct_slot_1; garbage; ...]". This is **not** what
the real shallow form does -- but the auditor has no in-Coq way to
detect it.

The milestone is honestly stated (only claims membership); the trust
budget item is the gap. A future tightening should either:

  - **(a)** state a stronger bridge axiom that also constrains slots 0,
    2+ (mirror the VersionRegistry shape: an `observationally_eq_storage`
    predicate over a closed-form `proj_sim_post_register` Definition);
    or
  - **(b)** explicitly document that the trust extends only to slot-1
    correctness (which is sufficient for the downstream
    `isRegistered`-via-membership query but does NOT support
    cross-mutator independence claims that read other slots).

## TIGHT findings -- for completeness

### TIGHT-G -- Guardian.v (Qed-closed)

`Guardian.run_grantRole_1359_equivalent` is the canonical example. The
file does NOT use the R070 Skolemized-post-storage Parameter pattern;
instead it uses **per-slot sstore axioms** (`run_sstore_role_*_at_proj_sim`)
each with concrete `Dict.declare_or_assign` conclusion. The
post-storage is built by the proof tactic via repeated sstore steps,
not Skolemized.

`run_grantRole_1359_equivalent`'s Print Assumptions surface 12 axioms
(per-slot sloads / sstores + role-distinctness + keccak bounds + the
DEFAULT_ADMIN constants), none of which is a free post-storage
Parameter. **TIGHT** (Qed-closed since R055/R059).

`run_revokeRole_1378_equivalent` closes Qed against the R068
composite axiom `run_fun__revokeRole_736_at_proj_sim_member`, which
asserts an EXISTENTIAL `storage_post` constrained by
`set_eq_at_role storage_post (proj_sim (revoke_role_sim role sim account))`.
The existential is properly constrained by a concrete predicate over
the sim's post-state.

`run_cancel_equivalent_make_state` closes Qed against the two cancel
walker axioms (admin and guardian paths). Their post-storage is
`proj_sim sim` (UNCHANGED -- cancel doesn't mutate Guardian storage),
which is concrete. (Modulo the VAC-G1 caveat on the return-value
quantifier.)

### TIGHT-DEL -- `StakingVaultDelegation.{delegate, delegateOptimistic, delegateBySig, delegateOptimisticBySig}_equivalent`

The four delegation milestones are inside `Section
StakingVaultDelegationSection`. The Section variables include:

  - `project_sim : SimulatedStorage.t -> SimState.t` (the lens)
  - `proj_post_<fn> : SimState.t -> ... -> SimulatedStorage.t`
  - `Hypothesis proj_post_<fn>_well_formed` carrying the real
    constraint: `project_sim post = sim_<fn> sim args`.
  - `Hypothesis run_fun_<fn>_at_proj_sim` (the composite walker
    hypothesis).

When the Section closes, all variables and hypotheses become
universal quantifiers / premises on the theorem. So
`run_delegate_equivalent`'s closed signature is:

```
forall (project_sim : ...) (proj_post_delegate : ...)
       (proj_post_delegate_well_formed : ...) (Codes Env Walker State : Set)
       (hoare : ...) (walker_delegate : Walker) (make_state : ...)
       (run_fun_delegate_at_proj_sim : ...),
  forall codes env storage_pre account new_d,
  exists state_post, ...  /\
  state_post = make_state (proj_post_delegate (project_sim storage_pre) account new_d) /\
  exists storage_post,
    proj_post_delegate (project_sim storage_pre) account new_d = storage_post /\
    project_sim storage_post = sim_delegate (project_sim storage_pre) account new_d.
```

An adversarial *consumer* of this theorem must supply all the
universal arguments -- including a proof of
`proj_post_delegate_well_formed` (which constrains the post-storage to
agree with the sim mutator under the lens) AND a proof of the walker
hypothesis. The hypothesis chain *forces* the post-storage to be
semantically faithful: identity instantiations fail the
`well_formed` hypothesis, no-op walker instantiations fail the
walker hypothesis.

`Print Assumptions
StakingVaultDelegationEquivalence.run_delegate_equivalent` returns
only `ECDSA.ECDSA.Domain.deployment_id : Set` plus the impredicative-Set
flag -- no free axioms beyond the framework. **TIGHT (parameterized)**.

Caveat: at instantiation time (in a future inheritor file) the
inheritor must supply concrete witnesses for every Section variable
and discharge every Hypothesis. **The audit of the inheritor file is
the load-bearing step** -- until that exists, these four theorems are
templates with no concrete content.

## PROVABLE -- for completeness

### PROV-VR-{1,2} -- `VersionRegistry.run_{deprecateVersion, registerVersion}_equivalent_make_state`

Post-storage is a closed-form `Definition`:

```coq
Definition proj_sim_post_deprecate sim hash : SimulatedStorage.t := [
  StorableValue.Map (deployments_map sim.(VersionRegistry.State.history));
  StorableValue.Map (Dict.declare_or_assign
                       (isDeprecated_map sim.(VersionRegistry.State.history))
                       hash 1);
  StorableValue.U256 (latestVersion_value sim)
].
```

No `Parameter proj_post_*`. The bridge `proj_sim_deprecate_at_observes`
asserts `observationally_eq_storage_vr (proj_sim (deprecate_at sim i))
(proj_sim_post_deprecate sim hash)`. Both `observationally_eq_storage_vr`
and `proj_sim` are real Definitions. The audit-time obligation is to
prove the bridge -- which the file flags as TODO, mechanical (lines
1307-1312).

**PROVABLE** in the strongest sense: there are no Skolemized
post-storages, only concrete shapes; the bridge is the remaining
mechanical work.

## Recommendations

Listed in priority order (rough effort estimate in parentheses).

  1. **Wire the shallow form into `StakingVaultExchange.v`** (~30
     min). Add `Require Import
     ReserveGovernor.generated.StakingVault_shallow.` and replace the
     four `Parameter fun_<op>_op` with `Definition` aliases. This
     removes the most flagrant degeneracy (the `fun_deposit_4312_op`
     etc. being free Parameters means the composite walker axiom
     constrains *nothing*).

  2. **Promote the three `eq_at_*_concrete` Parameters in
     `StakingVaultRewards.v` to Definitions** (~2 hr). The intended
     definitions are sketched in the file's docstring (lines 591-602).
     This converts the three milestones from VACUOUS to WEAK-or-TIGHT
     depending on the exact predicate shape.

  3. **Add per-slot Definitions for the seven `proj_post_*` Parameters
     in `StakingVaultAdmin.v` and the three in
     `ReserveOptimisticGovernor.v`** (~1-2 days). Mirror
     `VersionRegistry`'s approach: closed-form post-storages built from
     `Dict.declare_or_assign` and `set_slot_*` primitives, with
     `observationally_eq_storage`-shaped bridges asserting the closed
     form matches the sim mutator's projection. For `grantRole` /
     `revokeRole` / `renounceRole`, lift the existing R055/R059/R068
     lemmas from `Guardian.v` (already concrete) and re-state at the
     StakingVault `storage_base` lens.

  4. **Fix the return-value quantifier in
     `run_fun_cancel_238_at_proj_sim_{admin,guardian}`** (~15 min):
     change `forall proposalId` to a fixed value
     `(getProposalId_oracle key)` (or equivalent), eliminating the
     non-determinism in the cancel walker axiom.

  5. **Promote the documentation-only `proj_post_<fn>_observes` axioms
     to actual bridges across all StakingVault / ROG files** (~2-3
     days). At a minimum, each Skolemized `proj_post_<fn>` should have
     ONE bridge stating a real equation against the storage_base with
     the relevant slots updated. Until this lands, the `Print
     Assumptions` trace gives a false sense of security: the bridges
     ARE in the assumption list when load-bearing, but currently they
     are not load-bearing because the Qed close uses
     `apply storage_equiv_refl` against the trivial form.

  6. **Add a CI / smoke-test that asserts each milestone's
     `Print Assumptions` trace** (~1 day). The audit catches today's
     state but a future refactor could silently regress a TIGHT
     theorem to VACUOUS by replacing a constrained bridge with a
     reflexive one. A snapshot test prevents this.

Empirical scope guard: an audit reader can verify each VACUOUS finding
in this report in < 1 minute via the following loop (run with the
`rocq820` opam switch loaded):

```bash
cd formal-verification/rocq && cat > /tmp/check.v <<EOF
From ReserveGovernor Require Import proofs.equivalence.<FILE>.
Print Assumptions <Module>.<theorem>.
EOF
coqc -impredicative-set -w -stdlib-vector \
  -R $HOME/git/reserve/formal-verification/rocq-of-solidity/rocq/RocqOfSolidity RocqOfSolidity \
  -R . ReserveGovernor /tmp/check.v
```

For every VACUOUS finding, the output will NOT mention the corresponding
`proj_post_<fn>_observes` axiom -- confirming the bridge is non-load-bearing.
