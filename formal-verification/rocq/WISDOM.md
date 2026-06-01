# Rocq proof discipline (Reserve formal-verification)

Patterns and gotchas captured while authoring the proof tree under
`formal-verification/rocq/`. This file is a **reference**, not a
changelog — it's organized by pattern category, with each entry
showing the canonical shape an agent should reach for. R-numbers
are kept for traceability against git history but are not the
primary index.

For the chronological narrative (what landed in which commit), see
`git log --oneline formal-verification/rocq/`. For methodology
decisions and architectural memos, see `formal-verification/notes/`.

## How to use this file

1. Skim the index below; jump to whichever section matches your blocker.
2. Each entry: ~10-40 lines, includes a canonical code snippet.
3. Cross-references use `→ Rxx`. Resolved issues are marked `(RESOLVED)`.
4. When you discover a new pattern, append a new R-number at the end.
   Keep entries terse — no diary content. Reserve the chronology for git.

## Index

### Tooling and environment
- R009: Don't commit auto-translated harness `.v` files
- R012: Per-file build timeout (`RB_TIMEOUT`)
- R013: Avoid two-version operations
- R016: Logical-path naming
- R039: rocq-mcp interactive setup

### Coq 8.20 quirks
- R011/R015: Parser quirks on nested intro patterns
- R014: `simpl` aggressively unfolds `Z.eqb` — use `cbn -[Z.eqb]`
- R017: `destruct ... eqn:H` doesn't substitute through `set`-bound lets
- R018: `cbn -[Z.div Z.mul SCALAR DEC18]` over bare `simpl`/`cbn`
- R022: `Dict.Eq.eqb` typeclass projection (RESOLVED via `change`)
- R030: `cbn; lia` over `10^18` pathologically slow — use `change A with B`
- R031: `destruct (expr) eqn:H` requires identical syntactic form

### Tactical primitives
- R001/R010: Mark FixLib operations `Opaque` before destructs
- R002: `injection ... as ...; subst x` over `inversion H; subst`
- R003: Do NOT install `Z.to_euclidean_division_equations` zify hook
- R005: Re-export with `Notation`, not `Theorem name := body`
- R006: `vm_compute; reflexivity` for numerical witnesses
- R007: List-output domains need `Forall` lifting
- R008: Storage-state preservation needs the call-boundary hypothesis

### Walker patterns (RunO Hoare triple)
- R024: `l. { c. { apply leaf } ... }` canonical step-through
- R025: `pe` (PureEq) leaves two subgoals
- R026: `let~ '` desugars to `M.strong_let_`, not `LowM.Let`
- R027: `eapply RunO.Call` two-subgoal split — pose-once
- R028: Walker unfold list must include `M.let_`
- R029: Checked-arithmetic precondition direction matters
- R036: Upfront-pose for evar-scope problems
- R037: `idtac G; fail` diagnostic for silent walker arm mismatches
- R038: Slot-discriminated walker arms for storage reads
- R040: Wrapper-shape leaves for sstore
- R044: Two outer-wrapper proof patterns
- R047: Case-split BEFORE `eexists` for if-then-else divergence
- R053: Outer-walker composition layer

### Bit / Z arithmetic
- R019: `Dict.Eq.eqb` on tuple keys (RESOLVED)
- R023: `Z.lor` on if-then-else arguments (RESOLVED)
- R032/R033: Bridging if-then-else with `RunO.PureEq`
- R034: `Dict.declare_or_assign` chains (RESOLVED)

### Methodology — observational equality + projections
- R049: Multi-slot `proj_sim` cons-to-front Map2 encoding
- R054: `observationally_eq_storage` per-slot pointwise equality
- R059: `set_eq_at_role` membership equivalence
- R051: Composite-axiom shape for milestone Qeds
- R052: Honest `mapping(K => T[])` primitive (`StorableValue.MapToArray`)
- R072: Abstract-base-class equivalence — slot-agnostic helpers + lens
- R075: OZ TimelockController equivalence methodology — timestamp-as-state-encoding + AccessControl interaction
- R076: ERC4626 equivalence — share-asset arithmetic + inflation defense
- R078: ERC20Votes equivalence — multi-base composition (ERC20 + Votes)
- R079: OZ Governor abstract base equivalence (virtual functions as explicit args)
- R080: StakingVault dual delegation + bySig — dual-axis Trace208 push composition
- R081: StakingVault pause/admin equivalence + upgrade-authorization integration

### The R050 staticcall recipe
- R063: `staticcall` as composite of existing primitives
- R064: `AbiEncoding.v` module
- R065-R071: Per-mutator composite-walker recipe (validated on 12 mutators across 6 contracts)
- R077: ReserveOptimisticGovernor mutator equivalence (Wave 1 — sim Qed + walker scaffold; Wave 2 binding pending GOV-BASE)
- R083: Framework extensions — ERC-7201 namespace lens (`run_sload_map2_u256_at_anchor`) + memory absorption (`run_mstore_absorbing_at_make_state`, `run_mload_absorbing_at_make_state`)
- R084: T3.3 trust-redistribution decomposition for OZ EnumerableSet remove — replace monolithic walker+bridge axiom with Skolemized walker witness + set-equivalence bridge axiom + 3 inverse-op framework axioms

### Common pitfalls
- R020: `Stdlib.timestamp` semantics (RESOLVED)
- R021: `RunO.CallContract` rule (RESOLVED)
- R035: `shallow_embed.py` mis-embeds nested control flow (RESOLVED)
- R041: missing `linkersymbol` (RESOLVED)
- R042: `M.monadic` ident trap (RESOLVED)
- R045: OZ modifier mocks — symbolic `with_X body`
- R046: `shallow_embed.py` drops sstore in `_grantRole` (RESOLVED)
- R048: R045 variant for pure-function libraries
- R060: Verify contract surface against actual source
- R073: `shallow_embed.py` emits Rocq keyword `fun` as a Yul ident (RESOLVED)
- R074: `shallow_embed.py` zero-inits a tuple binder as scalar `0` (RESOLVED)

---

# Section 1: Tooling and environment

## R009: Don't commit auto-translated harness `.v` files

Generated Rocq IR (shallow forms, deep forms) is gitignored at
`rocq/generated/`. The directory is checked in (with `.gitignore` +
README); the `.v` outputs are local artifacts regenerable from
current source via `scripts/shallow-embed-sweep` or
`scripts/ir-rocq-coverage`.

**Fix:** equivalence-proof workflow first action is to copy generated
files from a known-good location:
`cp /path/to/main/.../generated/*.v rocq/generated/`.

## R012: Per-file build timeout (`RB_TIMEOUT`)

`scripts/rocq-build` wraps each `coqc` invocation in `timeout`
(default 180s, configurable via `RB_TIMEOUT`). Mandatory because
tactic explosions can spin at 100% CPU indefinitely (typically
under R001 conditions).

On macOS: install `coreutils` via brew to get `gtimeout`. When the
timeout fires, revisit Opaque scoping (→ R001), `change` vs `cbn`
(→ R030), and walker shape (→ R028).

## R013: Avoid two-version operations

If an operation has two versions (e.g., `cancel` and
`cancel_with_governor_state`), the older becomes a maintenance trap.
**Discipline:** when introducing a refined variant, document the
older as deprecated and migrate callers.

## R016: Logical-path naming

The protocol repo originally had files at both `simulations/X.v`
and `proofs/X.v` colliding under one `-R` binding. Our governor repo
uses `-R . ReserveGovernor` so files appear as
`ReserveGovernor.simulations.X` / `ReserveGovernor.proofs.X` — no
ambiguity. Always-qualify imports across simulation/proof boundaries.

## R039: rocq-mcp interactive setup

`rocq-mcp v0.2.1` provides interactive inspection (`rocq_start`,
`rocq_check`, `rocq_step_multi`, `rocq_get_state_at_position`).
10x faster than edit-build-fail-guess on walker failures.

**Setup:**
- workspace: `/Users/jmart/git/reserve/formal-verification`
  (parent containing both `governor/` and `rocq-of-solidity/`)
- PATH: `/Users/jmart/.opam/rocq820/bin` first — `pet` matches Coq 8.20.1
- `_CoqProject` at workspace root with `-R` to both repos
- First call: `force_restart=true` to clear stale state

**Usage:** on any walker stop, `rocq_start` at the theorem position,
`rocq_step_multi` through tactics, inspect goal state. `Show Existentials`
for evar diagnosis.

---

# Section 2: Coq 8.20 quirks

## R011 / R015: Parser quirks on nested intro patterns

Coq 8.20 fails on `destruct H as [a [b [c d]]]` with
"Syntax error: '|' or ']' expected (in [or_and_intropattern])".

**Workaround:** use the `&` conj-pattern:

```coq
destruct H as (a & b & c & d).
```

Same fix when destructing pair-tuples with nesting following.

## R014: `simpl` aggressively unfolds `Z.eqb`

`simpl` rewrites `Z.eqb x y` into the compare-and-branch form,
breaking subsequent `rewrite Z.eqb_refl` / `Z.eqb_eq`.

**Fix:** `cbn -[Z.eqb]` instead of bare `simpl`.

## R017: `destruct ... eqn:H` and `set`-bound lets

```coq
set b := some_complex_expr.
destruct (b =? 0) eqn:Hb.
```

After this, `Hb : b =? 0 = true|false`. The `set` doesn't unfold
inside Hb's RHS.

**Fix:** `unfold b in Hb` after the destruct, or skip `set` and
destruct on the literal expression.

## R018: `cbn` arithmetic blacklist

For arithmetic involving `SCALAR`, `DEC18`, `Z.div`, `Z.mul`:

```coq
cbn -[Z.div Z.mul SCALAR DEC18].
```

vs bare `cbn` which inlines `SCALAR = 10^21` and `DEC18 = 10^18`,
ballooning goal size before `lia` runs (→ R030).

## R022: `Dict.Eq.eqb` typeclass projection (RESOLVED)

`Dict.Eq.eqb` is a typeclass method. Bare `cbn`/`simpl`/`hauto`
can't unfold past the projection.

**Fix:** explicit `change`:

```coq
change (Dict.Eq.eqb OGM_BR OGM_BR) with (OGM_BR =? OGM_BR).
rewrite Z.eqb_refl.
```

## R030: `cbn; lia` over `10^18` is pathologically slow

`cbn` reduces `Z.pow 10 18` by 18-step unrolling, expanding the
goal to ~9MB. A 2-second proof becomes 27 seconds.

**Fix:** replace with `change`:

```coq
change ProposerThrottle.FIX_ONE with 1000000000000000000.
```

`change` does kernel convertibility (O(1)) + syntactic substitution.

**Detection:** `coqc -time <file>.v 2>&1 | awk '/secs$/' | sort -gr | head`.

## R031: `destruct (expr) eqn:H` syntactic-form trap

If the expression is unfolded asymmetrically (literal in goal,
reduced in hypothesis), the eqn-bound hypothesis won't match.

**Fix:** introduce `set b := <expr>` before the destruct so both
sites refer to the same `b`. Or `change` on the hypothesis.

---

# Section 3: Tactical primitives

## R001 / R010: Mark FixLib operations `Opaque` before destructs

`FixLib.powu`, `FixLib.mulu_toUint`, `FixLib.divrnd` contain
`Z.to_nat (Z.log2 _)` which Coq reduces eagerly during `inversion`,
exploding the goal-term size and OOMing the kernel.

**Workaround:** before any `injection`/`destruct` of such hypotheses:

```coq
Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd.
```

**Scoping (R010):** Mark Opaque inside the proof file where the
destruct happens, not in the simulation file. Too broad and downstream
`Compute`/`vm_compute` witnesses break.

## R002: `injection ... as ...; subst x` over `inversion H; subst`

`inversion H; subst` does maximal substitution and reduces all RHS
expressions, including heavy arithmetic.

**Fix:** named injection:

```coq
injection Hpair as Hs'_eq Hamt_eq.
subst s'.
```

## R003: Do NOT install `Z.to_euclidean_division_equations` zify hook

The hook registers globally and breaks unrelated proofs. Install
in a tight scope only when needed:

```coq
{ Z.to_euclidean_division_equations. nia. }
```

## R005: Re-export with `Notation`, not `Theorem`

```coq
Notation audit_throttle_consume_storage_delta :=
  ProposerThrottleProofs.consume_storage_delta.
```

The `Notation` form is a pure alias; `Theorem ... := body` forces
re-elaboration and bloats compile time.

## R006: `vm_compute; reflexivity` for numerical witnesses

For cross-check proofs computing concrete values:

```coq
Lemma xcheck_first_accrual_index :
  cal_rinfo_after_one_accrual.(RewardInfo.rewardIndex) = 10^33.
Proof. vm_compute. reflexivity. Qed.
```

`vm_compute` runs through the bytecode VM, much faster than `cbv`
for arithmetic-heavy goals.

## R007: List-output domains need `Forall` lifting

When a domain operation returns `list X`, validity-preservation
proofs need `Forall (fun e => valid e) result`. Use `Forall_app`,
`Forall_cons`, `Forall_map` for discharge.

## R008: Storage-state preservation needs the call-boundary hypothesis

When proving storage projection is preserved across external calls,
need an explicit hypothesis that the callee doesn't modify your
contract's slots. State as `H_callee_disjoint` or fold into the
callee-spec axiom (→ R063 staticcall bridge).

---

# Section 4: Walker patterns

## R024: `l. { c. { apply leaf } ... }` canonical step-through

```coq
unfold fun_outer.
lu.  (* LetUnfold opens the let-block *)
l. { c. { apply run_leaf1. } }
l. { c. { apply run_leaf2. } }
...
pe; reflexivity.
```

vs. the ad-hoc `s. cu.` interleaving which fails under M-monad
wrapping. When "Unable to unify LowM.Let ... with M.call ...",
back to the canonical pattern.

## R025: `pe` (PureEq) leaves two subgoals

`apply RunO.PureEq` (alias `pe`) splits into:
1. Output equality (often closed by `reflexivity`)
2. State equality

If `apply pe; reflexivity` leaves one subgoal, remember to discharge
the state side — typically `reflexivity` or
`apply CanonizeState.with_current_storage_twice_eq`.

## R026: `let~ '` desugars to `M.strong_let_`

```coq
let~ '(p) := e in k
```

desugars to `M.strong_let_ e (fun pat => k)` which wraps in
`match result with Ok/Return/Revert`. When walker stops at
`LowM.Call (M.strong_let_ ...) _`, unfold first:

```coq
unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
```

then the inner `LowM.Let` becomes visible to `l`.

## R027: `eapply RunO.Call` two-subgoal split

```coq
eapply RunO.Call; [exact Hmia | apply RunO.Pure].
```

vs the named-tactic `c;` form which fails on `[ltac_use_default]`
parse errors in Coq 8.20. Reach for explicit `eapply RunO.Call`
when the named tactic glitches.

## R028: Walker unfold list

Before any lazymatch walker fires, prelude must unfold:

```coq
unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
```

Skipping `M.let_` is a common error — walker stops at outer-let
goals and falls through to `s` (the fallback).

## R029: Checked-arithmetic preconditions

`checked_sub x y` requires `y <= x` (else underflow).
`checked_add x y` requires `x + y < 2^256`.

Get the direction right or leaf application fails. Common mistake:
writing `x <= y` for `checked_sub x y` when actually `y <= x` needed.

## R036: Upfront-pose for evar-scope problems

If `apply leaf_lemma; [exact Hwitness | ...]` complains "cannot
instantiate ?state_inter1 because w0' is not in its scope", the
metavariable was created before the witness binding.

**Fix:** pose-and-destruct upfront in the proof prelude:

```coq
pose proof (LeafLemmas.run_mapping_index_access ... witness) as Hmia.
destruct Hmia as (w0' & w1' & rest' & Hmia).
(* Now Hmia is in scope BEFORE any walker eexists creates metavariable *)
```

Then walker arm uses `exact Hmia` directly:

```coq
eapply RunO.Call; [exact Hmia | apply RunO.Pure]
```

## R037: `idtac G; fail` diagnostic

When a walker terminates unexpectedly (last `s` arm fires when you
expected a specific leaf), add a diagnostic arm:

```coq
| |- ?G => idtac "Unmatched goal:" G; fail
```

then re-run. Coq prints the goal at the unmatched site, revealing
the fully-qualified function name (which often differs from your
lazymatch pattern).

## R038: Slot-discriminated walker arms for storage reads

When multiple sloads at different slots fire, generic arms over
`run_sload_slot_offset_0_t_uint256 _` leave an `?account` evar.
Discriminate by slot pattern BEFORE the generic fallback:

```coq
| |- {{? _, _, _ |
      LowM.Call
        (... read_from_storage_split_offset_0_t_uint256 (Pure.add 0 0)) _
      ⇓ _ | _ ?}} =>
    c; [ apply run_read_capacity_from_make_state | ]
| |- {{? _, _, _ |
      LowM.Call
        (... read_from_storage_split_offset_0_t_uint256
              (Pure.add (keccak256_tuple2 _ _) 0)) _
      ⇓ _ | _ ?}} =>
    c; [ apply run_read_currentCharge_from_make_state | ]
```

## R040: Wrapper-shape leaves for sstore

Upstream `Storage.run_sstore_*` conclusions wrap in
`match List.update_nth ... with Some => {{? ?}} | None => True end`.
Direct `eapply` fails past the match.

**Fix:** wrapper lemma that bakes in the concrete list shape:

```coq
Lemma run_update_storage_offset_0_at_two_slot_list
    codes env state_before
    (cap : U256.t) (map : Dict.t (U256.t * U256.t) U256.t)
    (slot : U256.t) (v : U256.t)
    (H_off : ...) (H_v : ...) :
  {{? codes, env, Some ... |
    update_storage_value_offset_0_t_uint256_to_t_uint256 slot v
      ⇓ Result.Ok BlockUnit.Tt
  | Some ... ?}}.
Proof.
  pose proof (Storage.run_sstore_... [U256 cap; MapStruct map]) as Hsstore.
  simpl List.update_nth in Hsstore.
  ...
Qed.
```

Walker arms then apply the wrapper directly.

## R044: Two outer-wrapper proof patterns

**Pattern A (generic call-let arm):** for outer wrappers calling an
inner function with body inlined:

```coq
| |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
```

Add BEFORE more specific function-named arms.

**Pattern B (subst before destruct):** when inner closure binds a
value via `let` and walker's `destruct` needs the unsubstituted form:

```coq
subst expected.  (* expose the intro-let-bound name *)
subst positions_value.
destruct (positions_value =? 0); reflexivity.
```

## R047: Case-split BEFORE `eexists` for if-then-else divergence

When an outer walker has if-then-else with diverging `BlockUnit`
modes (e.g., `Tt` vs `Return`), case-split BEFORE `eexists state'`:

```coq
destruct (cond) eqn:Hcond.
- (* then *) eexists state_then. ...
- (* else *) eexists state_else. ...
```

vs. `eexists state'; destruct (cond)` which creates a metavariable
shared across branches that can't be unified.

## R053: Outer-walker composition layer

For OZ-style modifier-then-body wrappers (`onlyRole(R) internalBody()`),
proof composes:
1. Phase 1: modifier (admin/role check)
2. Phase 2: inner-body composite walker axiom
3. Phase 3: outer wrapper combining 1+2 with post-state

Pattern: pose Phase 1's discharge upfront (→ R036), walk outer body
with arms targeting Phase 1's success + Phase 2's composite axiom.

---

# Section 5: Bit / Z arithmetic

## R019: `Dict.Eq.eqb` on tuple keys (RESOLVED)

See R022. The typeclass projection on `Dict.Eq.ITuple2` is the
underlying cause.

## R023: `Z.lor` on if-then-else arguments (RESOLVED)

Goal `Z.lor a (if b then x else y) = if b then Z.lor a x else Z.lor a y`
doesn't reduce automatically.

**Fix:** case-split on `b` first; both sides become concrete `Z.lor`s.

## R032 / R033: Bridging if-then-else metavariable sharing

When two branches of a Yul if-then-else share a metavariable via
`eexists state'` at proof top, `apply RunO.Pure` in each branch
fails to unify.

**Fix:** use `RunO.PureEq` with a side equality bridging the
two output forms:

```coq
apply RunO.PureEq.
+ (* outputs equal *)
  assert (E : Z.min 1e18 raw = raw) by (apply Z.min_r; exact Hle_raw).
  rewrite E. reflexivity.
+ (* states equal *)
  reflexivity.
```

Use `Z.min_l` / `Z.min_r` to bridge clamped vs unclamped cases.

## R034: `Dict.declare_or_assign` chains (RESOLVED)

Goal: `Dict.declare_or_assign (Dict.declare_or_assign d k1 v1) k2 v2 = ...`
where the inner step shouldn't fire. Direct `simpl` doesn't collapse.

**Fix:** `rewrite Hkneb; simpl` cascade where `Hkneb : k1 =? k2 = false`:

```coq
apply Z.eqb_neq in Hkne as Hkneb.
rewrite declare_or_assign_pair_cons_step. rewrite Hkneb. simpl.
(* repeat for nested levels *)
```

The `simpl` after each rewrite normalizes `false && _` → `false`,
then `if false then _ else _` → else branch, in one step.

---

# Section 6: Methodology — observational equality + projections

## R049: Multi-slot `proj_sim` cons-to-front Map2 encoding

For OZ EnumerableSets, the projection is multi-slot:

```coq
Definition proj_sim (sim : SimState) : SimulatedStorage.t :=
  [ U256 (admin_field sim)
  ; MapStruct (positions_map sim)  (* role -> account -> position *)
  ; U256 (length_field sim)
  ; ...
  ].
```

Insertion cons-prepends to the per-role positions list. The
projection-update lemma states post-state's positions slot equals
the prepended form:

```coq
Lemma proj_sim_post_grant_observes :
  forall sim role account,
    set_eq_at_role role
      (proj_sim_post_grant sim role account)
      (proj_sim (add_role_member sim role account)).
```

## R054: `observationally_eq_storage` per-slot pointwise equality

Direct Dict structural equality is too strong when state shapes
diverge. Per-slot lookup-equality predicate:

```coq
Definition observationally_eq_storage (a b : SimulatedStorage.t) : Prop :=
  forall slot key,
    map_get_u256 a slot key = map_get_u256 b slot key.
```

Theorem post-state clauses use `observationally_eq_storage state_post
(make_state ... (proj_sim sim') ...) ...` instead of structural equality.

## R059: `set_eq_at_role` membership equivalence

Per-slot observational predicate fails for OZ EnumerableSet's
swap-and-pop deletion: sim's order-preserving `remove_role` produces
different values-array layout than OZ's swap-and-pop. They're equal
as SETS but not as LISTS.

**Predicate:**

```coq
Definition set_eq_at_role
    (role : U256.t) (storage_a storage_b : SimulatedStorage.t) : Prop :=
  forall account,
    contains_at_role role account storage_a <->
    contains_at_role role account storage_b.
```

where `contains_at_role` checks `positions[role][account] > 0`.

**When to use:** any OZ EnumerableSet mutator whose post-state depends
on internal layout. The contract's public API exposes only membership
(`hasRole`, `_contains`), so membership equivalence is the right
abstraction level.

Carries to: AccessControl (grantRole/revokeRole), AccessControlEnumerable
view-fns, RewardTokenRegistry (`set_eq_in_registry` — unkeyed),
SelectorRegistry (nested per-target Bytes32Set).

## R051: Composite-axiom shape for milestone Qeds

The methodology used for every R050-blocked mutator Qed: bundle the
function's walker into a single Hoare-triple axiom keyed on the
pre-state, with the post-state via a Skolemized Parameter:

```coq
Parameter proj_post_<fn> : SimState -> <args> -> SimulatedStorage.t.

Axiom <fn>_observes :
  forall sim args,
    observational_relation (proj_post_<fn> sim args)
                           (proj_sim (sim_<fn> sim args)).

Axiom run_fun_<fn>_at_proj_sim :
  forall codes env state caller sim args,
    <preconditions> ->
    {{? codes, env, Some (make_state ... (proj_sim sim) ...) |
      fun_<fn> args ⇓ Result.Ok output
    | Some (make_state ... (proj_post_<fn> sim args) ...) ?}}.

Theorem run_<fn>_equivalent_make_state :
  ...
  Qed.  (* composes the above into the milestone *)
```

The composite axiom is the audit-time obligation. Trust budget per
mutator: 2-4 axioms.

## R052: Honest `mapping(K => T[])` primitive (`StorableValue.MapToArray`)

OZ's [EnumerableSet] and any other Solidity `mapping(K => T[])`
consumer lay out per-key dynamic-array storage in a shape distinct
from the framework's nested-keccak Map/Map2/MapStruct primitives:

```text
slot[keccak(key, baseSlot)]              = array length
slot[keccak(keccak(key, baseSlot)) + i]  = values[i]
```

Pre-R052 the framework had no native carrier for this layout, and
consumers wrote per-contract trust axioms equating array-shape
expressions with framework-shape nested keccaks ("Option 1" — false
in any honest model, accepted as parametric trust). R052 landed the
honest framework primitive (Option 2) and the single-input keccak
helper (Option 3, already done):

**Option 3 (upstream, landed earlier):** `keccak256_single` /
`run_keccak256_single` — the proof-side counterpart to OZ's
`mstore(0, anchor); keccak256(0, 0x20)` data-area derivation.

**Option 2 (upstream, R052 main payload):** a new constructor on
`StorableValue.t`:

```coq
| MapToArray (value : Dict.t U256.t (list U256.t))
```

with four `Admitted` framework lemmas mirroring the `Map` / `Map2` /
`MapStruct` axiom family:

- `Storage.run_sload_maptoarray_length` — length read at
  `keccak(key, index)`
- `Storage.run_sload_maptoarray_elem` — body read at
  `keccak(keccak(key, index)) + i`
- `Storage.run_sstore_maptoarray_length` — length write (resize,
  zero-fill on grow / truncate on shrink)
- `Storage.run_sstore_maptoarray_elem` — body element write at
  `keccak(keccak(key, index)) + i`

plus four `apply_run_*` Ltacs and an `IsStorable.IMapToArray`
typeclass instance.

**Trust:** the four lemmas are `Admitted` in the framework — exactly
the same audit status as the existing `Map` / `Map2` / `MapStruct`
primitives. The trust transfers ONCE to the framework rather than
being re-asserted per-consumer.

**Governor-side status (Guardian.v):** the upstream primitive is in
place and verified to compose (smoke test
`MapToArrayLengthSmokeTest.run_length_smoke` in
`proofs/equivalence/Guardian.v`). The pre-existing four R052 Option
1 axioms (`run_sload_role_values_length_at_proj_sim`,
`run_sstore_role_values_length_at_proj_sim`,
`run_sstore_role_values_body_at_proj_sim`,
`run_sload_role_values_length_at_proj_sim_post`,
`run_sload_role_values_body_at_proj_sim`) remain in place — their
elimination requires a structural refactor of `proj_sim` to put
`MapToArray` at slot index 1 (the keccak shape that matches OZ's
`keccak(role, 1)` length anchor). That refactor touches ~330
references across Guardian.v's bridge lemmas and is scoped as a
follow-on task; the upstream landing unblocks it.

**Cross-references:**

- Constructor / lemmas: `rocq-of-solidity/rocq/RocqOfSolidity/proofs/RocqOfSolidity.v`
- Smoke test: `Guardian.v::MapToArrayLengthSmokeTest`
- Remaining Option 1 axioms: `Guardian.v::run_sload_role_values_*` /
  `run_sstore_role_values_*`
- Audit trail: `Audit.v` Caveat-5 (Resolved upstream blockers list)

## R072: Abstract-base-class equivalence — slot-agnostic helpers

Some OZ bases are **abstract**: they declare storage slots and methods
but never deploy standalone — every method is inlined by Solc into an
inheriting contract's shallow form. Examples in this corpus:

- `AccessControl` / `AccessControlEnumerable` (consumed by Guardian)
- `Nonces`, `ReentrancyGuard`, `EnumerableSet` (pure-fn library)
- `Votes` (consumed by `ERC20Votes`, planned: StakingVault)
- `Checkpoints.Trace208` (storage primitive, consumed by Votes)

There's no `<base>_shallow.v` from solc for these — the Yul translation
lands in the inheritor's shallow form, with slot indices fixed by the
inheritor's storage layout.

**Pattern** (Option 2 from `notes/votes_equivalence_methodology.md`):

1. The `proofs/equivalence/<Base>.v` file is **slot-agnostic**: it
   states sim-level lemmas about `mocks/<Base>.v` that hold
   independently of where the inheritor lays out the base's slots.
2. The file declares a Section parameterized by the slot indices
   and a projection lens (`project : SimulatedStorage.t -> Base.State.t`).
3. Lens-correctness hypotheses are declared as Section variables;
   inheritors discharge them by `reflexivity` at instantiation.
4. Walker-arm shapes are documented as comments — they can't be
   made concrete without a shallow form to point at.

**When this matters:**

- ERC20Votes (#241), StakingVault delegation paths (#256), Governor
  inheritance chain (#244) — all consume Votes; Votes.v gives them
  the sim-level reasoning surface as a reusable layer.
- Future ERC721Votes consumers would re-use the same Votes.v
  helpers, supplying a different voting-units lens (token count
  instead of balance).

**How it composes with R055/R059/R063:**

- R055 (membership equivalence): applies when the abstract base
  uses an EnumerableSet (AccessControlEnumerable does; Votes does
  not — Votes uses Maps).
- R059 (set_eq_at_role): same caveat as R055.
- R063 (staticcall): applies at the *Governor* side when the
  Governor calls a Votes-bearing token externally (e.g.
  `IVotes(token).getPastVotes(...)`). The Votes-side helpers
  compose under the staticcall as a sub-Hoare-triple.

**Trust:** zero new axioms. The slot-agnostic helpers close as
pure-Coq facts about the mock; the lens hypotheses are discharged
locally at instantiation time. Total trust budget per inheritor
remains the standard R051/R055/R063 budget (2-4 composite axioms
per mutator).

**Existing precedents (all Qed today):**

- `proofs/equivalence/EnumerableSet.v` — 7 sanity lemmas
- `proofs/equivalence/Nonces.v` — `with_useCheckedNonce` wrapper + 5 lemmas
- `proofs/equivalence/Checkpoints.v` — 7 sanity lemmas (Trace208)
- `proofs/equivalence/Votes.v` — 17 sim-level lemmas + Section
  template + walker documentation
- `proofs/equivalence/ERC4626.v` — 20+ sim-level lemmas + Section
  template with asset-balance lens (see R076)
- `proofs/equivalence/TimelockControllerBase.v` — 52 sim-level
  lemmas + Section template + walker documentation (R075)
- `proofs/equivalence/ERC20Votes.v` — 24 sim-level lemmas + composed
  Section template + walker documentation (multi-base composition,
  see R078 below)

## R076: ERC4626 equivalence (share-asset arithmetic + inflation defense)

OZ's `ERC4626` (`token/ERC20/extensions/ERC4626.sol`) is an
abstract base extending `ERC20`. It bridges a **shares** ERC20
(issued by the vault) with an **assets** ERC20 (external,
referenced by the immutable `_asset` address). Four conversion
functions — `convertToShares` / `convertToAssets` / `previewMint` /
`previewWithdraw` / `previewRedeem` / `previewDeposit` —
implement `Math.mulDiv` between the two ledgers with explicit
rounding direction.

The structural challenge: `totalAssets()` reads the external
asset's balance via a `staticcall` to `IERC20(asset).balanceOf(this)`.
There are two equivalent strategies — see top of
`proofs/equivalence/ERC4626.v` modeling note.

**Methodology decisions (slot-agnostic, Option 2 per R072):**

1. **`_asset` opaque address — state field, not Section parameter.**
   The vault carries `asset_address : Address` directly on its
   sim state. Equivalence threads `lens_asset_address_correct` as
   a hypothesis. Inheritor discharges by `reflexivity` at
   instantiation. Same shape as `voting_units` in `mocks/Votes.v`.

2. **`totalAssets()` — Section-parameter `project_asset_balance` +
   R063 discharge.** The mock carries `total_assets : U256.t` as a
   snapshot field. The equivalence file declares a
   `project_asset_balance : SimulatedStorage.t -> U256.t` Section
   parameter and a `lens_total_assets_correct` hypothesis. At
   instantiation, the inheritor discharges the hypothesis by a
   single R063 staticcall-bridge lemma (`StaticCallBridge.sc_word`).
   This factors the staticcall away from the conversion-function
   walkers entirely: every `convertToShares` / `convertToAssets`
   walker becomes a closed-form muldiv against the projected
   asset balance.

3. **Rounding-direction semantics — `Rounding` enum + `muldiv`
   primitive.** OZ's `Math.Rounding` has four constructors; the
   mock ports them verbatim. The `muldiv` primitive computes
   `floor(x*y/d)` with an optional `+1` bump when the rounding
   mode is `Ceil`/`Expand` and the remainder is non-zero. Since
   the sim is Z-valued, this is exact (no 512-bit arithmetic
   needed). The four public functions select their rounding to
   always **favor the vault**:
     - `previewDeposit`  → `_convertToShares` Floor
     - `previewMint`     → `_convertToAssets` Ceil
     - `previewWithdraw` → `_convertToShares` Ceil
     - `previewRedeem`   → `_convertToAssets` Floor

4. **`_decimalsOffset` virtual — `nat` state field bounded ≤ 77.**
   The virtual is fixed at construction in OZ; the mock carries
   `decimals_offset : nat` on state. The `Valid.t` invariant
   bounds it at ≤ 77 (since `10^77 < 2^256 < 10^78`). The
   inflation-attack defense formula `shares = assets *
   (totalSupply + 10^offset) / (totalAssets + 1)` is then the
   direct definition of `_convertToShares`.

**Headline inflation-attack property (`inflation_attack_bound`):**

At `totalSupply = 0` (the empty vault), the first depositor's
share count is

  `convertToShares s assets = floor(assets * 10^offset / (totalAssets + 1))`

regardless of any donation that has inflated `totalAssets`. The
`10^offset` virtual-shares multiplier in the numerator is
**static** — the attacker's donation cannot reduce it. This
caps the attacker's profit at the cost of `10^offset` virtual
shares per round.

At `offset = 0` (the OZ default), the bound collapses to the
trivial single-virtual-share defense; at `offset = 6` (a typical
recommendation), the attacker pays `10^6` virtual shares of
dilution per round. The defense's strength scales exponentially
with offset.

**Composition with downstream contracts:**

- `StakingVault` (#256) inherits `ERC4626 + ERC20Votes`. The
  ERC4626 equivalence file's Section is the bridge: the
  inheritor instantiates `project_erc4626`, `project_asset_balance`,
  and discharges the three lens-correctness hypotheses.
  Composing with `proofs/equivalence/Votes.v` is straightforward —
  the two Sections are independent (no slot overlap).

- The R063 staticcall discharge happens once, in the inheritor's
  storage-projection setup, and is then reused across all four
  conversion functions and `maxWithdraw`.

**Trust:** zero new framework axioms. All sim-level lemmas are
Qed against `mocks/ERC20.v` and `mocks/ERC4626.v`. The four lens
correctness hypotheses are Section parameters discharged at
instantiation time. Total trust budget for an inheritor's
ERC4626 walkers: 1 R063 staticcall bridge + 3 `reflexivity`-grade
lens lemmas, same shape as Votes.

## R080: StakingVault dual delegation + bySig — dual-axis Trace208 + ECDSA + Nonces composition

**Status (post Task #280, 2026-05-31 audit response):** the file
documenting this methodology was renamed from
`proofs/equivalence/StakingVaultDelegation.v` to
`proofs/equivalence/StakingVaultDelegation_methodology.v` to make
its abstract Section-bound status explicit at the filesystem +
module + theorem-name layers. The four headline theorems are now
`run_<fn>_equivalent_methodology` (suffix `_methodology` on each)
and close inside a Section whose Variables abstract the entire
Hoare-triple carrier — no concrete inheritor instantiates it.
The methodology theorems are universally quantified at Section
closure and carry no semantic content against the deployed
contract until instantiated; see Audit.v Caveat-5 + the file's
header banner for the audit-honest framing. The ~22 sim-level Qed
lemmas in the file (outside the Section) remain genuine and
consumed by sim-side validators.

`proofs/equivalence/StakingVaultDelegation_methodology.v` (1.7k LOC) mechanizes
the four delegation entrypoints — `delegate`, `delegateOptimistic`,
`delegateBySig`, `delegateOptimisticBySig` — of StakingVault via
the R051+R072 composite-axiom + slot-agnostic instantiation pattern.

**The dual-axis insight:** StakingVault carries TWO parallel Votes-
inheritance bookkeeping layers — the standard ERC20Votes one
(`_delegatee` map + `_delegateCheckpoints` Trace208 + total-supply
Trace208) AND a contract-local optimistic one
(`optimisticDelegatees` map at slot 0x0a + `optimisticDelegateCheckpoints`
Trace208 at slot 0x0b). Both are touched on EVERY `_update` (transfer/
mint/burn), but the public `delegate*` entrypoints each touch ONLY
ONE axis:

- `delegate(delegatee)` → `_delegate(msg.sender, delegatee)` → standard
  axis only
- `delegateOptimistic(delegatee)` → `_delegateOptimistic(msg.sender,
  delegatee)` → optimistic axis only
- `delegateBySig(...)` → `_delegate(signer, delegatee)` → standard
  axis only (signer comes from ECDSA.recover)
- `delegateOptimisticBySig(...)` → `_delegateOptimistic(signer,
  delegatee)` → optimistic axis only

This is the "dual-axis independence" property — the slot layout
ensures the two ledgers operate on disjoint storage regions, so
each entrypoint's walker can decompose along its single axis.

**Joined SimState carrier:**

```coq
Module SimState.
  Record t : Set := {
    base       : StakingVaultDelegation.State.t;  (* dual latest-side *)
    std_traces : TraceMap;                        (* standard Trace208 *)
    opt_traces : TraceMap;                        (* optimistic Trace208 *)
    nonces     : Nonces.Map;                      (* OZ Nonces book *)
    domain     : ECDSA.Domain.t;                  (* EIP-712 domain *)
    clock      : U256.t;                          (* block.timestamp *)
  }.
End SimState.
```

**Trace208 push composition at delegation transitions:**

For each `_move*DelegateVotes(from, to, amount)`:
- Short-circuit if `from = to || amount = 0`.
- If `from != 0`: push `(clock, latest(from_trace) - amount)` onto
  `from`'s Trace208 (decrement).
- If `to != 0`: push `(clock, latest(to_trace) + amount)` onto
  `to`'s Trace208 (increment).

The mock's `Trace208.latest_after_push` lemma chains directly: after
the push, querying `latest` at the new key returns the pushed value.
This is the load-bearing read for the Governor's veto-tally code
path (`getPastOptimisticVotes(account, snapshot)` →
`Trace208.upperLookupRecent` against the optimistic trace).

**EIP-712 + ECDSA + Nonces composition (BySig variants):**

```
fun_delegateBySig_15249(delegatee, nonce, expiry, v, r, s):
  if timestamp > expiry: revert VotesExpiredSignature(expiry)
  struct_hash := keccak256(abi.encode(
                   DELEGATION_TYPEHASH, delegatee, nonce, expiry))
  typed_hash  := _hashTypedDataV4(struct_hash)
                 (* folds in domain_separator(chain, contract, dep) *)
  signer      := ECDSA.recover(typed_hash, v, r, s)
  _useCheckedNonce(signer, nonce)   (* reverts on mismatch *)
  _delegate(signer, delegatee)      (* same body as direct delegate *)
```

Each component composes via its respective foundation-tier
equivalence proof:
- `ECDSA.v` for `recover`, `typed_data_hash`, `optimistic_delegation_struct_hash`
- `Nonces.v` for `useCheckedNonce` (replay protection)
- `Checkpoints.v` for `Trace208.push` / `Trace208.latest`
- `Votes.v` for `_delegate` decomposition

The `OPTIMISTIC_DELEGATION_TYPEHASH` (0x... at L48 of StakingVault.sol)
vs `DELEGATION_TYPEHASH` (OZ inherited) is the only constant that
distinguishes the two BySig variants — same composition shape,
different typehash → different signed digest → bound to a different
axis. The struct-hash injectivity axiom (`struct_hash_injective`
from mocks/ECDSA.v) is what prevents a `delegateBySig` signature
from being lifted to a `delegateOptimisticBySig` even with the same
(delegatee, nonce, expiry) triple — they hash to different digests.

**Sim-vs-Yul slot layout:**

```
SimState field          | Yul storage slot
------------------------|---------------------------------
base.std.delegatee a    | slot_std_delegatee (mapping by `a`)
base.opt.delegatee a    | 0x0a (mapping by `a`)
std_traces[a]           | slot_std_delegate_ckpt (mapping by `a`)
opt_traces[a]           | 0x0b (mapping by `a`)
nonces a                | slot_nonces (mapping by `a`)
domain                  | virtual — folded into DOMAIN_SEPARATOR
                        | via chain_id + verifying contract addr
```

Per R072, slot indices are Section parameters; the inheritor
discharges lens-correctness obligations at instantiation by
`reflexivity` against the concrete shallow form.

**File structure (1.6k LOC, all Qed except 4 Section hypotheses):**

- Section 0: SimState carrier (record, ~30 LOC)
- Section 1: sim-level Qed helpers — set_*_delegate decompositions,
  std-side checkpointed-delegate analog of the optimistic-side
  proof, push lemmas mirroring CHK-1/CHK-3 (~200 LOC, all Qed).
- Section 2: joined-state mutators — `sim_delegate`,
  `sim_delegateOptimistic`, `sim_delegateBySig`,
  `sim_delegateOptimisticBySig` (~200 LOC).
- Section 3: 14 Qed lemmas characterizing each mutator's
  field-by-field post-state (3 sim_delegate updates, 7 preservers,
  3 sim_delegateOptimistic updates, 7 preservers, dual-axis
  independence, 4 BySig expired/replay/signer/nonce facts) (~500 LOC).
- Section 4: slot-agnostic Section (Variables + Hypotheses) (~30 LOC).
- Section 5: per-fn post-state projection Variables + well-formedness
  Hypotheses (~150 LOC).
- Section 6: per-fn Hoare-triple closure Hypotheses (~150 LOC).
- Section 7: milestone Qed theorems (4 theorems, one per entrypoint).
- Section 8: vm_compute sanity-check examples (8 examples, all Qed).
- Section 9: walker-template commentary.
- Section 10: trust budget summary.

**Trust budget per `Print Assumptions`:**

- All Qed lemmas in Sections 1-3: zero new axioms beyond the
  pre-existing `ECDSA.Domain.deployment_id : Set` parameter.
- BySig milestones: additionally pull in `ECDSA.recover`,
  `ECDSA.typed_data_hash`, `ECDSA.optimistic_delegation_struct_hash`
  as the *mock-side* Parameters (not new axioms — they're the
  underlying interpretation surface that mocks/ECDSA.v exposes).

**Handoff notes for inheritor / Wave 2 follow-up:**

- Adding `generated/StakingVault_shallow.v` to the default
  `_RocqProject` tier (uncommenting line 262 of that file) is
  the prerequisite for closing the per-fn composite walker
  Hypotheses with concrete walker tactics.
- The Section is parameterized over `Codes`, `Env`, `Walker`,
  `State`, `hoare`, `make_state`, and the four `walker_*`
  function constants. The inheritor binds:
  - `Walker := M.t unit`
  - `hoare := fun W codes env state_pre state_post =>
              {{? codes, env, Some state_pre | W ⇓ Result.Ok BlockUnit.Tt | Some state_post ?}}`
  - `walker_delegate := fun_delegate_15192 delegatee` (specialized)
  - `walker_delegateOptimistic := fun_delegateOptimistic_422 delegatee`
  - `walker_delegateBySig := fun_delegateBySig_15249 d n e v r s`
  - `walker_delegateOptimisticBySig := fun_delegateOptimisticBySig_480 d n e v r s`
- The four per-fn well-formedness Hypotheses discharge by composing
  `set_std_delegate_checkpointed` / `set_opt_delegate_checkpointed`
  output projection vs the concrete `proj_sim`'s post-storage.
- The four per-fn Hoare-triple Hypotheses are the R051 audit-time
  obligations; their walker tactics follow the documented Phase 1-7
  outline in Section 6 of the file.

**Composition with adjacent contracts:**

- `castVoteBySig` / `castVoteWithReasonAndParamsBySig` on the
  Governor (#244) reuse the EIP-712 + ECDSA + Nonces composition
  pattern; the per-fn axiom shape is identical, with
  `Vote.DELEGATION_TYPEHASH` swapped for `Governor.BALLOT_TYPEHASH`.
- `transfer` / `_update` on StakingVault (#256 transfer path, not
  in this file) calls BOTH `_moveDelegateVotes` AND
  `_moveOptimisticDelegateVotes` per the dual-axis sim's
  `transfer` mutator; the composition is exactly the conjunction
  of the two per-axis walker bodies.

---

## R081: StakingVault pause/admin equivalence + upgrade-authorization integration

StakingVault.sol (task #257, Wave 2) has seven AccessControl-gated
admin mutators across three tiers:

  Tier-1 (direct admin entry-points):
    - [setUnstakingDelay] — onlyRole(DEFAULT_ADMIN_ROLE);
      require delay ≤ MAX_UNSTAKING_DELAY (2419200s = 4 weeks);
      sstore at literal slot 5.
    - [setRewardRatio]   — onlyRole(DEFAULT_ADMIN_ROLE);
      require half-life in [86400, 1209600];
      sstore at literal slot 3; wrapped in accrueRewards modifier.
    - [_authorizeUpgrade] — UUPS hook; onlyRole(DEFAULT_ADMIN_ROLE);
      three external R063 staticcalls against the VersionRegistry.

  Tier-2 (inherited AccessControl mutators):
    - [grantRole] / [revokeRole] / [renounceRole] — same R055/R068
      shape as Guardian, gated by the admin chain of the role.

  Tier-3 (proxy entry-point):
    - [upgradeToAndCall] — modifier_onlyProxy + _authorizeUpgrade +
      ERC1967Utils sstore at IMPLEMENTATION_SLOT + opaque
      delegatecall(data) into the new impl.

NOTE: StakingVault.sol does NOT expose [pause]/[unpause] or
[setNativeRewardRate] entry-points — the task brief's "pause/admin"
labels are abstract category names. The contract's pause-equivalent
surface is the [setUnstakingDelay] hook (a zero value collapses the
lockup) plus the [addRewardToken]/[removeRewardToken] surface
(managed by DEFAULT_ADMIN_ROLE for emergency reward-stream pause).
Native asset() rewards auto-accrue from the contract's underlying
balance — there is no admin lever for the native reward rate. R060
"verify contract surface against actual source" applied: the file
records this disposition under [Pause / unpause (sim-level
disposition)].

**Methodology decision:** R070 abstract-storage_base recipe
(Skolemized post-storage Parameter + composite walker Axiom +
reflexive observational bridge under `storage_equiv := eq`),
mirroring [TimelockControllerOptimistic.v] verbatim. This was the
right call because:

  1. StakingVault inherits TEN OpenZeppelin namespaces (ERC4626 +
     ERC20Upgradeable + ERC20Permit + ERC20Votes + AccessControl +
     AccessControlEnumerable + Initializable + UUPS + Nonces +
     EIP712), each at an ERC-7201 keccak-derived storage anchor.
     Concretizing the on-chain layout slot-by-slot would require
     re-mechanizing each namespace's per-slot projection — months
     of work for a config-surface proof that doesn't need it.

  2. The admin-surface theorems characterise WHICH slots are touched
     (one literal slot for [setUnstakingDelay]/[setRewardRatio]; one
     keccak-derived AccessControl slot for grantRole/revokeRole; one
     EIP-1967 slot for upgradeToAndCall) — but the FULL-state
     post-condition is only meaningful relative to the inheritor-of-
     OZ namespace projections, which are best deferred to per-domain
     equivalence files (e.g. StakingVaultRewards for the
     accrueRewards sub-walker reached by setRewardRatio).

  3. The audit-time obligation reduces to: "each composite walker
     axiom's Yul-body assembly closes mechanically against the per-
     step primitives already mechanized" — same shape as
     ProposalLib's R070 close.

**Upgrade-authorization integration (R063 composition):** The
[_authorizeUpgrade] hook is the load-bearing integration point with
VersionRegistry. Its three staticcalls:

  1. Versioned(stakingVaultImpl).version() : string
     — selector 0x54fd4d50. Returns the impl's version string.
       Walker keccak256s it → var_versionHash_1520.

  2. versionRegistry.getLatestVersion() : (bytes32, string, address, bool)
     — selector 0x0e6d1de9. Walker extracts versionHash (comp 1) and
       deprecated (comp 4). Require !deprecated; require
       versionHash == latestVersionHash, else revert
       Vault__VersionDeprecated / Vault__NotLatestStakingVault.

  3. versionRegistry.getImplementationsForVersion(versionHash)
       : (address, address, address)
     — selector 0x6ce67d8c. Walker extracts stakingVaultImpl
       (comp 1). Require stakingVaultImpl == argument, else revert
       Vault__NotLatestStakingVault.

The audit's reason for accepting an upgrade: (a) the impl's version
hashes to the registry's latest version hash; (b) the version is
not deprecated; (c) the registry's stakingVaultImpl for that
version matches the upgrade target. This is the dual to
VersionRegistry's [registerVersion] mutator (R066) — the registrar
side records the (hash, impl) pair; the authorizer side reads it
back.

**AccessControl role-check composition:** Every admin mutator's
modifier_onlyRole gate composes with the sim-side
[has_DEFAULT_ADMIN_ROLE caller = true] precondition via the
[checkRole_default_admin_succeeds] documentation-only axiom. The
composite walker axiom carries the gate discharge directly via the
role precondition — the documentation-only axiom is NOT load-bearing
for the milestone theorem's [Print Assumptions].

For grantRole/revokeRole/renounceRole, the inner sub-walker
encapsulates Guardian.v's R055/R059/R068 closed lemmas (the
AccessControl member-map flip + AccessControlEnumerable
EnumerableSet add/remove). Under the abstract storage_base, the
inheritor of those closed lemmas is the composite walker axiom
itself — auditors verify the assembly mechanically.

**Trust budget:**
  - 7 composite walker axioms (one per public function — R067).
  - 7 Skolemized post-storage Parameters (R070).
  - 7 observational bridge axioms (reflexive under storage_equiv := eq).
  - 1 has_DEFAULT_ADMIN_ROLE Parameter (shared with sim-side gating).
  - 1 now_timestamp Parameter (same shape as
    TimelockControllerOptimistic).
  - 4 True-conclusion documentation axioms (checkRole_default_admin
    + 3 callee-spec witnesses for the _authorizeUpgrade staticcalls)
    — NOT load-bearing for any [Print Assumptions].

Each milestone theorem's [Print Assumptions] shows ONLY:
  - Its own composite walker axiom.
  - Its Skolemized post-storage Parameter.
  - The has_DEFAULT_ADMIN_ROLE Parameter (or H_self_confirm for
    renounceRole) + now_timestamp Parameter.
  - The framework-level
    [RocqOfSolidity.Memory.of_u256_list],
    [RocqOfSolidity.Storage.of_storable_values],
    [Set is impredicative], and PrimInt63 family.

Pattern is reusable for ReserveOptimisticGovernor's admin surface
(task #260) once that contract's pause-equivalent gates land.

## R073: `shallow_embed.py` emits Rocq keyword `fun` as a Yul ident (RESOLVED)

`name_to_rocq` only rewrote `end`, `mod`, `return`. Solc emits an
internal-function-pointer dispatcher
`function dispatch_internal_in_N_out_M(fun, ...)` whose first
parameter is literally named `fun`. The shallow output became
`Definition dispatch_internal_in_2_out_1 (fun : U256.t) ...` which
fails parsing because `fun` is Rocq's lambda keyword. Manifests on
StakingVault (its internal-function-pointer use creates the
dispatcher) and any future contract that takes
`function (...) internal returns (...)` as a callback.

**Fix:** broaden the `reserved_names` list in `name_to_rocq` to include
`fun` (plus a defensive set of other Rocq keywords). Names in the list
are suffixed with `_`, so the dispatcher becomes
`Definition dispatch_internal_in_2_out_1 (fun_ : U256.t) ...`.
References inside the body (`let δ := [[ fun ]]`) follow the same
rename.

Pushed on `TheFrozenFire/rocq-of-solidity:fix/r073-r074-shallow-embed`.

## R074: `shallow_embed.py` zero-inits a tuple binder as scalar `0` (RESOLVED)

`YulVariableDeclaration` with no initializer falls back to the literal
string `"0"`, ignoring the binder arity. For a single binder this is
fine; for an N-tuple binder it becomes
`let~ '(a, b, c, d) := [[ 0 ]] in`, which Rocq rejects with
"Found a constructor of inductive type prod while a constructor of Z
is expected." Manifests on StakingVault (Yul lowering of
`(bytes32, string memory, address, bool)` ABI-decode-into-tuple
destructurings) — and on any contract that returns a struct from an
external view.

**Fix:** fan out the implicit zero across the binder arity. For an N-
tuple binder, emit `(0, 0, ..., 0)` with N zeros, mirroring the
already-correct `function_definition_to_rocq` path for returnVariables.

Pushed on `TheFrozenFire/rocq-of-solidity:fix/r073-r074-shallow-embed`
in the same commit as R073.

## R077: ReserveOptimisticGovernor mutator equivalence

The hybrid optimistic/pessimistic Governor inherits from a large
chain of OZ abstract bases (`GovernorUpgradeable`,
`GovernorSettingsUpgradeable`, `GovernorPreventLateQuorumUpgradeable`,
`GovernorCountingSimpleUpgradeable`, `GovernorVotesUpgradeable`,
`GovernorVotesQuorumFractionUpgradeable`,
`GovernorTimelockControlUpgradeable`) plus `Versioned` + `UUPS`. The
three full-mutator equivalence targets (`propose`, `castVote`,
`execute`) ride the R070/R071 composite-walker recipe with three
OG-specific wrinkles:

**Wrinkle 1 — optimistic-route branch.** `castVote` and `execute`
both check `_isOptimistic(proposalId)` (defined as
`vetoThreshold(pid) != 0` — slot read at
`optimisticProposalDetails[pid].vetoThreshold`). They dispatch
between:
- The bespoke optimistic path: against-only voting (`_countVote`
  reverts on `support != Against`); execute-bypass via
  `TimelockControllerOptimistic.executeBatchBypass`.
- The inherited super-chain: standard For/Against/Abstain voting;
  execute through OZ Timelock.

The composite walker axiom packs both branches into a single
post-storage existential. Per-branch shapes are exposed as
documentation axioms (Section 7 of `ReserveOptimisticGovernor.v`).

**Wrinkle 2 — veto-counting walker (sentinel handling).** Optimistic
`castVote`'s `_tallyUpdated` step checks if the just-incremented
`againstVotes` crossed the threshold. On success, the contract
spawns a standard child via `ProposalLib.transitionToPessimistic`,
which writes `vetoThreshold := UINT256_MAX` (the sentinel) to make
`_isOptimistic(pid)` return true AND `observe` return Defeated
forever after. The sim mirrors this as `phase := PhaseDefeated`.

The sentinel handling forces a stickiness-of-Defeated lemma in the
sim layer: `observe_defeated_sticky_at_threshold` proves that once
`phase = PhaseDefeated` AND `againstVotes >= vetoThresholdTok`,
`observe` returns Defeated for any future `now`. (The
contract-side variant — where the sentinel write makes the
threshold check unsatisfiable — would require modeling the
sentinel directly in the sim's `Proposal.t`, which the simulation
deliberately abstracts away.)

**Wrinkle 3 — Wave-1 vs Wave-2 split.** The mechanization scaffolds
ahead of two deps:
- UPSTREAM-SHALLOW (shallow_embed.py fix for OZ Governor base
  modifier dispatch).
- GOV-BASE (mechanizing the OZ Governor abstract base at
  `proofs/equivalence/GovernorBase.v`).

The file structure puts Wave-2 hooks at the boundary where the
walker axiom statements bind to inherited modifier wrappers and
the `_isOptimistic` case-split. The Wave-1 sim-level layer is
fully Qed; the walker axioms are stated against the inheritor's
storage layout with reflexive observational bridges.

**Trust budget:** 6 composite walker axioms (3 milestone +
3 branch-documentation) + 1 transition-side-exit axiom + 3
Skolemized post-storage parameters + 1 sim-environment parameter
(`now_timestamp`) + 3 role-spec axioms with `True` conclusions
(not load-bearing for milestone `Print Assumptions`).

Milestone `Print Assumptions` shows: the composite walker axiom,
the Skolemized post-storage parameter, `now_timestamp`, framework
primitives (`PrimInt63.*`, `Memory.of_u256_list`,
`Storage.of_storable_values`), and `Set is impredicative` (all
pre-existing in the corpus).

Sim-level lemma `Print Assumptions` shows ONLY `Set is impredicative`
— no contract-specific axioms.

**LOC:** ~1450 across `proofs/equivalence/ReserveOptimisticGovernor.v`,
covering R077 docstring + Section 1 (sim-level Qeds, ~480 LOC) +
Sections 3-5 (Skolemized params + observational bridges + composite
walkers, ~280 LOC) + Section 6 (milestone Qeds, ~140 LOC) +
Sections 7-9 (branch docs + transition axiom + Wave-2 hooks,
~120 LOC).

---

## R075: OZ TimelockController equivalence methodology

A specific application of R072 to the OZ `TimelockController` abstract
base (governance/TimelockController.sol, OZ v5.4.0). The base is
consumed by the Reserve corpus via `TimelockControllerOptimistic` (the
upgradeable variant); its storage layout lands at the inheritor's
EIP-7201 namespace anchor for `TimelockControllerStorage`
(`$._timestamps`, `$._minDelay`).

**Timestamp-as-state-encoding.** OZ packs the 4-state
`OperationState` enum ({Unset, Waiting, Ready, Done}) into a single
`mapping(bytes32 => uint256) _timestamps` using sentinel values:

    _timestamps[id] = 0              <=> Unset
    _timestamps[id] = 1              <=> Done (the magic _DONE_TIMESTAMP)
    _timestamps[id] > 1, > now       <=> Waiting
    _timestamps[id] > 1, <= now      <=> Ready

This packing is the single most important methodological pattern for
the abstract base: every public function reads it via
`getOperationState(id)`, every mutator writes it via a single sstore.
The four post-state observation lemmas
(`schedule_post_state_waiting`, `execute_post_state_done`,
`cancel_post_state_unset`, plus the `getOperationState_{zero,done,
waiting,ready}` discriminator lemmas) discharge the state-projection
walker arms once and are reused by every concrete inheritor.

**`isOperation*` family as iff lemmas.** Because the four boolean
predicates (`isOperation`, `isOperationPending`, `isOperationReady`,
`isOperationDone`) are thin projections on `getOperationState`, we
expose each as an iff-correctness lemma. Walker proofs rewrite in both
directions: forward to discharge the require-condition arms (e.g.
`cancel_revert_not_pending`), backward to confirm post-state
observations.

**Interaction with AccessControl.** The mock layers
`TimelockController.State` on top of `AccessControl.State` rather than
duplicating role storage. The role gates (`PROPOSER_ROLE`,
`EXECUTOR_ROLE`, `CANCELLER_ROLE`) are dispatched through
`has_role` / `has_role_or_open`, where the latter implements OZ's
`onlyRoleOrOpenRole` pattern: `hasRole(role, msg.sender) ||
hasRole(role, address(0))`. The open-role short-circuit is
load-bearing for the `EXECUTOR_ROLE` gate inside `execute` (it enables
permissionless execution after the role is granted to address(0)).

**Mock vs. existing concrete sim.** The Reserve corpus already has a
narrower Timelock sim at `simulations/Timelock.v` used by
`proofs/equivalence/TimelockControllerOptimistic.v`. That sim has
exactly the surface the upgradeable variant needs (no
`schedule`-single, no `updateDelay`, no `OperationState` projection).
The new mock at `mocks/TimelockController.v` carries the full
abstract-base surface — including `OperationState`, `updateDelay`,
single-op `schedule` / `execute`, and the predecessor chain — so
inheritors that need them have a sim-level Qed surface to lift onto.

The two coexist without conflict: the existing
`TimelockControllerOptimistic.v` proofs remain valid (they bind walker
axioms against the narrower sim's transition functions). A future
revision of those proofs may choose to migrate to the broader mock,
trading the existing 5 R071 milestone theorems for the slot-agnostic
layer's reusable lift theorems. This is an opt-in refactor — the
sim-level surface in the new mock has been chosen to be a strict
superset of the existing one in terms of public-method coverage.

**Print Assumptions.** Every Qed in
`proofs/equivalence/TimelockControllerBase.v` closes under the global
context: no new axioms beyond what the foundation tier already
imports.

---

## R078: ERC20Votes equivalence (multi-base composition)

ERC20Votes is the first OZ abstract base in this corpus to inherit
from TWO other abstract bases simultaneously: `ERC20` (token ledger)
and `Votes` (delegation + checkpoint history).  Its critical
override is `_update(from, to, value)`:

```solidity
function _update(address from, address to, uint256 value) internal virtual override {
    super._update(from, to, value);                  // ERC20 ledger half
    if (from == address(0)) {
        uint256 supply = totalSupply();
        if (supply > _maxSupply()) revert ERC20ExceededSafeSupply(...);
    }
    _transferVotingUnits(from, to, value);           // Votes-side half
}
```

Every motion of ERC20 balance MUST mirror in the Votes checkpoint
history — the override is what enforces the "_getVotingUnits = balanceOf"
coupling at runtime.  This is the multi-base composition R075 documents.

**Dual-storage update pattern:**

The composed `_update` performs TWO writes against two disjoint
storage regions in a single Yul fragment:

- ERC20 side: `_balances[from] -= value`, `_balances[to] += value`,
  `_totalSupply += value` (mint) / `_totalSupply -= value` (burn).
- Votes side: push `+value` or `-value` onto `_totalCheckpoints`
  (mint/burn only), and call `_moveDelegateVotes(delegates[from],
  delegates[to], value)` to update the per-delegate
  `_delegateCheckpoints` history.

The two sides operate on disjoint slot indices and don't read each
other's outputs (Votes' `_transferVotingUnits` reads its own
`voting_units` snapshot, not the just-updated ERC20 `balanceOf`).
So at the walker level the two halves compose as sequential Yul
fragments — no aliasing concern.

**Mock composition (`mocks/ERC20Votes.v`):**

`State.t` is a record combining `ERC20.State` and `Votes.State.t`:

```coq
Module State.
  Record t : Set := {
    erc20 : ERC20.State;       (* balances/totalSupply/allowances *)
    votes : Votes.State.t;     (* delegatee/delegate_ckpt/total_ckpt/voting_units/clock *)
  }.
End State.
```

The composed mutator `update s from to value` calls both halves
in one step.  The coupling invariant `_getVotingUnits = balanceOf`
is encoded in `Valid.t`:

```coq
voting_units_eq_balance :
  forall a, s.(State.votes).(Votes.State.voting_units) a
          = ERC20.balanceOf s.(State.erc20) a;
```

Three Votes-side `transferVotingUnits_total_ckpt_*` lemmas
(`_mint`, `_burn`, `_pure`) are proven inline in the mock — the
proofs/equivalence/Votes.v versions can't be re-used because they
live in the proof file, and mocks must not depend on proofs.

**Section composition (single combined Section, NOT two stacked):**

`Section ERC20VotesEquivalenceTemplate` declares Variables for the
union of ALL slot indices:

```coq
Variable slot_balances    : nat.    (* ERC20 side *)
Variable slot_allowances  : nat.
Variable slot_totalSupply : nat.
Variable slot_delegatee     : nat.  (* Votes side *)
Variable slot_delegate_ckpt : nat.
Variable slot_total_ckpt    : nat.

Variable project_erc20votes : SimulatedStorage.t -> State.t.
```

And Hypotheses for BOTH sides' lens correctness — `lens_balances_correct`,
`lens_totalSupply_correct`, `lens_delegatee_correct`,
`lens_delegate_ckpt_correct`, `lens_total_ckpt_correct`, plus the
critical `lens_voting_units_eq_balance` coupling.

**Why one Section, not two:** an alternative (REJECTED) is to stack
two inherited sections — one inheriting `VotesEquivalenceTemplate`
and one inheriting (a hypothetical) `ERC20EquivalenceTemplate`.
That forces the consumer to reason about TWO independent state
projections that must satisfy a cross-state coupling invariant
*manually*.  Combining them into a single Section lets the lens
carry the coupling as a Section-level Hypothesis (discharged once
at instantiation time, by `reflexivity` on the inheritor's `proj_sim`
constructor).

**Walker arms — two halves, disjoint slots:**

The composed `_update` walker reads exactly like two stacked Yul
fragments operating on disjoint slot indices.  Walker tactics that
already work for single-base equivalence (R040 for sstore-wrappers,
R047 for case-splits, R033 for if-then-else PureEq) apply to each
half independently.  Trust budget per call site is the SAME as
single-base (2-4 composite axioms) — multi-base composition does
NOT inflate the axiom count.

**Composition with existing methodology:**

- R072 (abstract-base equivalence): ERC20Votes IS an instance of
  R072, but with two parents.  The "slot-agnostic Section + lens"
  shape still applies.
- R055/R059 (set / role membership): not applicable — ERC20Votes
  uses Maps + Trace208, not EnumerableSet.
- R063 (staticcall): applies at Governor side when the Governor
  calls a token's `getPastVotes` externally.  Composes with the
  per-mutator ERC20Votes lemmas as a sub-Hoare-triple.

**Trust budget:** zero new axioms.  All 24 sim-level lemmas close
as `Qed` with `Set is impredicative` as the sole assumption.

**Handoff to StakingVault (#256):**

StakingVault inherits ERC20Votes.  To instantiate the methodology:

1. In StakingVault's equivalence file, `Require Import` ERC20Votes.
2. Build `proj_sim_erc20votes : SimulatedStorage.t -> ERC20Votes.State.t`
   that projects the StakingVault storage into the composed
   ERC20Votes state.  The StakingVault state layout is `_balances`
   at slot 0, `_allowances` at slot 1, `_totalSupply` at slot 2,
   `_delegatee` at slot 7 (after StakingVault's own dual-delegation
   slots), `_delegateCheckpoints` at slot 8, `_totalCheckpoints` at
   slot 9 (subject to revision after R046 lands).
3. Open `Section ERC20VotesEquivalenceTemplate` and supply slot
   indices + lens.
4. Discharge each `lens_*_correct` Hypothesis by `reflexivity`
   on the projection lambda.
5. The composed walker lemmas (`mint_increases_totalSupply`,
   `delegate_sets_delegatee`, etc.) are now in scope.
6. For each StakingVault method that overrides ERC20Votes (e.g.
   `_update` for slashing accounting), compose the standard walker
   recipe (R040 + R047 + R033) against the StakingVault's own Yul
   body, citing this file's lemmas as the post-state predicates.

---

## R079: OZ Governor abstract base equivalence — virtual functions as explicit args

The OZ `Governor` base (governance/Governor.sol, OZ v5.4.0, ~820
lines) is the largest abstract base in this corpus. It carries TWO
storage slots (`_proposals` map, `_governanceCall` queue) and has
~15 `virtual` functions an inheriting governor overrides. The
equivalence methodology is the same Option 2 / Section-parameterized
shape as Votes, but the `virtual` surface deserves its own pattern
entry.

**Handling virtual functions — three buckets:**

(A) **Explicit arguments to mock entry points.** The view-only /
    state-extending virtuals (`votingDelay`, `votingPeriod`,
    `quorum`, `_quorumReached`, `_voteSucceeded`, `_getVotes`,
    `_queueOperations`, `_executor`) are passed as `Z` / `bool` /
    `U256.t` arguments to the relevant mock functions. This keeps
    each lemma a closed function of `(state × hook_outputs)` without
    committing to a concrete inheritor's schedule.

    Example: `propose s a proposer votingDelay votingPeriod` takes
    `votingDelay` and `votingPeriod` as values, not as functions of
    `s`. The OZ source reads them at call time via `votingDelay()` /
    `votingPeriod()`; the mock sees only the evaluation.

(B) **Section parameters at the equivalence layer.** The
    `GovernorBaseEquivalenceTemplate` Section in
    `proofs/equivalence/GovernorBase.v` declares `votingDelay_fn`,
    `votingPeriod_fn`, `getVotes_fn`, etc. as `Variable`s.
    Inheritor walker proofs supply concrete witnesses (e.g.
    `ReserveOptimisticGovernor`'s `votingDelay` is `1 day`).

(C) **Out of scope.** `_tallyUpdated` (empty default in OZ), the
    receive() / onERC1155Received() token-receiver surface, and
    the EIP-712 / SignatureChecker path are not modeled at the
    abstract level. They compose orthogonally: signature paths
    layer through `Nonces.v` + `ECDSA.v`; `_tallyUpdated` overrides
    chain as a post-state predicate.

**Tally surface for `_countVote`:** carried as an opaque
`VoteTally` record (`voters`, `against_w`, `for_w`, `abstain_w`).
Concrete inheritors with richer counting modules (e.g.
GovernorCountingSimple's `ProposalVote` struct, or
ReserveOptimisticGovernor's `vetoVotes` aggregate) extend / project
through this surface. The `castVote_records_vote` + `_replay_reverts`
+ `_preserves_valid` triad already captures the
"no-double-voting" property at the base level.

**Re-entrancy queue (`_governanceCall`):** modeled as a
`Bytes32Set` (consumed by `_checkGovernance` via `governance_call_contains`).
OZ uses a `Bytes32Deque` but the FIFO ordering is observationally
irrelevant for the equivalence theorems — only membership matters
for the revert condition.

**The `state` 8-state cascade:** lifted as
`state_unfold` (definitional fold) plus 7 per-phase
characterizing lemmas (`state_executed_terminal`,
`state_canceled_terminal`, `state_nonexistent_reverts`,
`state_pending_when_snapshot_ge_now`, `state_active_when_in_window`,
`state_defeated_when_quorum_or_vote_fails`,
`state_succeeded_when_no_eta`, `state_queued_when_eta_set`).
Once-executed-stays-executed is a downstream theorem
(`execute_leads_to_executed_state`); once-canceled-stays-canceled
similarly (`cancel_leads_to_canceled_state`).

**Inheritor handoff (ReserveOptimisticGovernor):**

1. Open the `GovernorBaseEquivalenceTemplate` Section in the
   inheritor's `proofs/equivalence/ReserveOptimisticGovernor.v`.
2. Supply the inheritor's concrete `proj_sim` lens to
   `project_base : SimulatedStorage.t -> GovernorBase.State.t`.
3. Discharge the three lens-correctness hypotheses
   (`lens_proposals_correct`, `lens_governance_call_correct`,
   `lens_clock_correct`) — typically by `reflexivity` after the
   `proj_sim` slot indices are fixed.
4. For each public Governor entry point, the walker arms decompose
   as documented in Section 12 of `proofs/equivalence/GovernorBase.v`
   (one comment block per entry point — propose / castVote / queue /
   execute / cancel / relay).
5. Where ReserveOptimisticGovernor overrides a virtual function (e.g.
   `_quorumReached` checks `vetoVotes >= vetoThresholdTok`), the
   override's Z-level value is fed into the corresponding mock entry
   point's `quorum_reached` argument. The walker proof shows the
   Yul-level call to the override evaluates to the same `bool`.

**Trust:** zero new framework axioms; the existing
`hashProposal_fn` declared `Parameter` in `mocks/GovernorBase.v`
is the same pattern as keccak in upstream `Common.v`.
`Print Assumptions` on every closed lemma shows only
`Set is impredicative` and `hashProposal_fn` (the latter only when
the lemma directly references `hashProposal`; pure
`State`-arithmetic lemmas like `state_unfold` show only the theory
primitive).

**Sizing:** `mocks/GovernorBase.v` ~600 LOC,
`proofs/equivalence/GovernorBase.v` ~1600 LOC. Total ~2200 LOC,
within the 3000-5000 budget allocated to the largest abstract base
in the corpus.

---

# Section 7: The R050 staticcall recipe

## R063: `staticcall` as composite of existing primitives

Yul's `staticcall` is defined upstream in
`rocq-of-solidity/.../simulations/RocqOfSolidity.v:1110`:

```coq
Definition staticcall (g a in_ insize out outsize : U256.t) : M.t U256.t :=
  match precompile_output a [] with
  | Some _ => call_precompile a in_ insize out outsize
  | None =>
    let* input := LowM.Primitive (Primitive.MLoad in_ insize) M.pure in
    let* result := LowM.CallContract a 0 input true false M.pure in
    let* output := LowM.Primitive Primitive.RLoad M.pure in
    LowM.Primitive (Primitive.MStore out (List.firstn (Z.to_nat outsize) output))
      (fun _ => M.pure result)
  end.
```

R050 is NOT new framework — it's **bridge lemmas + walker arms**
for the composite. Existing infrastructure:
- `LowM.CallContract` + `RunO.CallContract` (cc tactic, R021)
- `Primitive.MLoad` / `Primitive.RLoad` / `Primitive.MStore`

**Bridge lemma** (`StaticCallBridge.v`) folds the composite into a
single Hoare triple keyed by the callee's return value. Walker tactic
(`sc_word`):

```coq
| |- {{? _, _, _ |
      LowM.Call (Stdlib.staticcall _ _ _ _ _ 32) _ ⇓ _ | _ ?}} =>
    StaticCallBridge.sc_word 1 H_not_precompile
```

## R064: `AbiEncoding.v` — abi-encoding leaves

Companion leaves for the abi-encoding step wrapping a staticcall:

```
mstore(0, selector_shift_224)
mstore(4, encoded_args_tuple)
staticcall(...)
returndatasize()
returndatacopy(0, 0, 32)
let v := mload(0)
```

`AbiEncoding.v` provides:
- `run_shift_left_224`, `run_mstore_with_shift_left_224`
- `run_allocate_unbounded`, `run_finalize_allocation_size_32`
- `run_abi_encode_tuple_t_address__to_t_address__fromStack_aligned`
- `run_returndatasize_at_post_bridge`
- `run_abi_decode_tuple_t_bool_fromMemory_aligned`
- `run_iszero_nonzero`

6 are Qed (PrimInt63-only); 7 are documented trust axioms (abi
encode/decode tuples + the bridge + memory model). Trust axioms
are reusable across all R050-blocked mutators.

## R082: CRIT-A composite-walker discharge — VersionRegistry.deprecateVersion

The 2026-05-31 adversarial review's SYNTHESIS flagged the composite
walker Axioms (R065-R071) as the load-bearing trust commitments to
retire first.  Task #283 (T3.2 in the remediation plan) targets
VersionRegistry's `deprecateVersion_187` body — the simplest target
(no EnumerableSet, no external staticcall in the body proper apart
from the role-registry check, single mapping update + bytes32 sstore).

**Architectural change** (committed at this revision):

1. The composite `Axiom run_fun_deprecateVersion_187_at_proj_sim` is
   converted to an `Admitted Lemma` with a **strengthened
   precondition signature**. New explicit hypotheses (vs the original
   axiom):
     - `role_registry_addr`, `account` — the loadimmutable witness.
     - `H_account` — the account is bound at `env.(Environment.address)`
       in the initial state's accounts dict.
     - `H_immutable` — the role-registry's address sits at the
       `0x3331...0000` immutable slot.
     - `H_not_precompile` — the role-registry isn't a precompile.
     - `H_free_ptr_aligned` — `memory[2] = 0x80` (canonical Solidity
       free-pointer layout).

2. The milestone theorem
   `run_deprecateVersion_equivalent_make_state` threads these new
   preconditions through to the walker and **weakens the post-state**:
   instead of `state' = Some (make_state env state_base memory' storage')`
   it asks for `state' = Some (make_state env state_base' memory'
   storage')`, allowing the post-state's [state_base'] to differ from
   the input [state_base].  This generalization is needed because the
   staticcall bridge's `<| State.return_data := bytes |>` override
   persists through the entire post-bridge prefix.

3. A new framework axiom in `AbiEncoding.v`:

   ```coq
   Axiom make_state_with_rd_eq :
     forall env state_base memory storage (rd : list Z),
     (make_state env state_base memory storage)
       <| State.return_data := rd |> =
     make_state env (state_base <| State.return_data := rd |>) memory storage.
   ```

   Folds the rd-override into the `state_base` argument so existing
   `make_state`-shape leaves apply unchanged.  Closed in the same
   spirit as `CanonizeState.update_memory_eq` (Admitted upstream;
   relies on the opacity of `with_current_storage`).

**Residual work**: the walker Lemma's body is `Admitted`.  The 18-step
mechanical discharge follows the per-step recipe documented in
`VersionRegistry.v::run_fun_deprecateVersion_187_at_proj_sim`'s
comment block.  Each step closes via an existing leaf:
- S1: `StaticCallBridge.run_loadimmutable` (with H_account / H_immutable)
- S2: pure binding (`apply RunO.Pure`)
- S3: `convert_t_contract_to_address` — chain of three identity
  conversions under H_role_bound (cleanup_t_uint160 returns the
  value masked at 160 bits = value itself when 0 ≤ v < 2^160)
- S4-S5: caller primitive, allocate_unbounded (with H_free_ptr_aligned)
- S6-S7: shift_left_224, mstore (memory[4] := selector_shifted)
- S8: abi_encode_tuple_t_address (memory[5] := caller)
- S9: `AbiEncoding.staticcall_make_state_bridge` (call_result = 1)
- S10: `iszero(1) = 0` → Shallow.if_ default branch
- S11-S13: post-bridge if-decode: returndatasize=32, finalize_allocation
  (memory[2] := _22+32 = 160), abi_decode_tuple_t_bool_fromMemory (=1)
- S14: require_helper_t_error_10_VersionRegistry__InvalidCaller(1) succeeds
- S15-S17: mapping_index_access(1, hash), sload+extract via
  run_read_isDeprecated_offset_0_at_proj_sim (=0 by H_lookup), iszero+cleanup,
  require_helper_t_error_16_VersionRegistry__AlreadyDeprecated(1) succeeds
- S18-S19: second mapping_index_access(1, hash), update_storage via
  run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim
  (the load-bearing sstore producing proj_sim_post_deprecate)
- S20: log2 = M.pure tt
- S21: final M.pure tt — closes via RunO.PureEq + make_state_with_rd_eq

The state-shape transition at S9 (staticcall bridge produces a state
with `<| return_data := bytes |>` override) propagates through S10-S20.
Companion `with_rd` versions of the AbiEncoding axioms (S11-S13) would
be needed to walk through this prefix cleanly.  Alternative: use the
`make_state_with_rd_eq` commutation at the final M.pure to "absorb"
the rd field into the state_base argument.

**Per-mutator cost** (updated): the original R065 axiom's discharge
is now ~500-1500 LOC mechanical assembly.  This is meaningful but
bounded work.

## R083: Framework extensions — ERC-7201 namespace lens + memory absorption

Two upstream-framework gaps were blocking walker discharges across
multiple OZ mutators (StakingVaultAdmin's grantRole / revokeRole /
renounceRole, TimelockControllerOptimistic's TimelockController
gate walks, ProposalLib's role reads).  T3.1's diagnosis was that
both gaps were structural and reusable.  R083 adds two minimal
framework primitives that close them:

### Gap 1 — ERC-7201 namespaced storage lens

**Symptom.** OZ AccessControl / AccessControlEnumerable / UUPS /
ERC20Permit / Initializable / ReentrancyGuard all store at
keccak-derived ERC-7201 namespace anchors (e.g. AccessControl at
`0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800`).
Upstream's `Storage.run_sload_map2_u256` axiom pins the inner-keccak
slot expression to `Z.of_nat <small_nat>`, which CANNOT unify with
a 256-bit keccak output.

**Pre-R083 state.** Walker discharges through `_checkRole` /
`_hasRole` / similar were blocked at the
`sload(keccak256_tuple2 account (keccak256_tuple2 role anchor))`
step.  Files punted with focused gate axioms like
`run_fun__checkRole_<id>_succeeds_under_admin` (monolithic Axioms
covering the whole gate walk).

**Fix.** Add a slot-anchor-agnostic Storage primitive in
`proofs/equivalence/FrameworkExtensions.v`:

```coq
Parameter IsNamespaceAnchor :
  list StorableValue.t -> nat -> U256.t -> Prop.

Axiom run_sload_map2_u256_at_anchor :
  forall codes environment state values index anchor
         (map : Dict.t (U256.t * U256.t) U256.t) key1 key2,
  IsNamespaceAnchor values index anchor ->
  List.nth_error values index = Some (StorableValue.Map2 map) ->
  {{? codes, environment, Some state |
    Stdlib.sload (keccak256_tuple2 key2 (keccak256_tuple2 key1 anchor)) ⇓
    Result.Ok (StorableValue.map_get_u256 map (key1, key2))
  | Some state ?}}.
```

Companion `run_sload_struct_field_at_anchor` (for the
[mapping(K => Struct)] anchored shape) and
`run_sstore_map2_u256_at_anchor` (for writes) follow the same
template.

**Per-contract binding.** Each contract declares one Axiom of the
form:

```coq
Axiom accessControl_namespace_binding :
  forall sb, IsNamespaceAnchor sb slot_accessControl 0x02dd...
```

This is the audit-time obligation: the abstract projection MUST
pin the designated slot to the keccak-derived anchor.  Same
discipline as the existing R040 wrapper-shape audit obligations.

**Soundness.** Upstream's `Storage.of_storable_values` is
`Admitted`, so the framework leaves the projection function
unspecified beyond the existing `run_sload_*`/`run_sstore_*`
axioms.  Adding more axioms about the projection's behaviour at
OTHER slot expressions is consistent so long as no two axioms
force contradictory values at the same slot.  The new
`IsNamespaceAnchor`-gated axiom describes the projection at the
namespaced shape `keccak256_tuple2 k1 (keccak256_tuple2 k2 anchor)`,
and per-contract binding axioms ensure no two anchors route to
the same list index.

### Gap 2 — Memory absorption for event-emission tails

**Symptom.** Upstream's `Memory.run_mload` / `run_mstore` require
per-index `nth_error memory index = Some _` hypotheses.  For
walker tails where the memory result doesn't matter (event
emission: `allocate_unbounded -> mstore -> log1`), the per-index
bookkeeping is onerous and brittle.  In particular, the
event-emission tail writes at a free-memory-pointer address
(`mload(64)`), which is RUNTIME-DERIVED and can't be pinned to a
literal `32 * Z.of_nat _` shape.

**Pre-R083 state.** T3.1's `run_fun__setUnstakingDelay_773_at_storage_base`
left two `nth_error`-shaped goals as `Admitted` (the
`allocate_unbounded` mload and the abi-encode mstore).

**Fix.** Add absorbing variants in
`proofs/equivalence/FrameworkExtensions.v` with Skolemized
post-state shapes:

```coq
Parameter mstore_post_memory :
  Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t -> U256.t -> SimulatedMemory.t.

Axiom run_mstore_absorbing_at_make_state :
  forall codes environment state_base memory storage offset value,
  {{? codes, environment,
      Some (make_state environment state_base memory storage) |
    Stdlib.mstore offset value ⇓ Result.Ok tt
  | Some (make_state environment state_base
            (mstore_post_memory environment state_base memory storage
                                offset value)
            storage) ?}}.
```

The Skolemized form lets `apply` unify directly against the
post-state of an enclosing `eapply RunO.Call` step, without
threading per-index `nth_error` hypotheses.  Companion
`run_mload_absorbing_at_make_state` returns a Skolemized
`mload_witness` value.

**Soundness.** In Solidity practice every Yul mstore/mload writes
at a 32-aligned address (free-memory pointer is `0x80 + k*32`;
scratch space is at `0` and `0x20`).  Under the 32-aligned
convention, `update_bytes (of_u256_list memory) offset
(u256_as_bytes value)` is expressible as `of_u256_list memory'`
for some `memory'`.  The Skolem function `mstore_post_memory`
points at that witness.

The AUDIT-TIME OBLIGATION per use site: the contract's mstore
offsets are aligned.  All governor contracts pass this audit
(every Yul mstore in the emitted IR is either at a literal
32-aligned address or at `allocate_unbounded() + k*32`).

The alternative — threading per-index alignment preconditions
through every walker — would explode the precondition surface;
the absorber localises the soundness obligation to per-contract
audit review of the source's mstore shapes.

### Composition with existing methodology

R083 framework extensions compose cleanly with:

- **R040** (wrapper-shape sstore): unchanged.  R040 wraps the
  upstream `Storage.run_sstore_u256` with the contract's concrete
  slot index; R083's `run_sload_map2_u256_at_anchor` is the
  namespaced sibling for reads through ERC-7201 anchors.
- **R067 / R070** (per-mutator composite walker recipe):
  unchanged.  Composite walker axioms can now be derived as
  `Qed` Lemmas if the namespace-lens + memory-absorbing
  primitives close the gate walk + memory tail.
- **R055 / R059** (Guardian role-membership patterns):
  unchanged.  Guardian's slot-0 role storage uses the literal-slot
  primitives; namespace-anchored contracts (StakingVaultAdmin,
  TimelockControllerOptimistic, etc.) now use R083's anchor
  variants.

### Validation — T3.1 closure

R083 validated by closing T3.1's two residuals at
`proofs/equivalence/StakingVaultAdmin.v`:

1. `run_fun__setUnstakingDelay_773_at_storage_base` — was
   `Admitted` with two `nth_error` residuals.  Now `Qed`, with
   the memory tail discharged via
   `run_mload_absorbing_at_make_state` /
   `run_mstore_absorbing_at_make_state`.

2. `run_fun__checkRole_13513_succeeds_under_admin` — was a
   monolithic `Axiom`.  Now a `Qed` `Lemma` derived from:
     - `FrameworkExtensions.run_sload_map2_u256_at_anchor`
     - Two focused audit-time facts:
         (a) `accessControl_namespace_binding` (per-projection
             namespace pinning),
         (b) `admin_role_membership_at_storage_base` (sim-side
             witness that `has_DEFAULT_ADMIN_ROLE caller = true`
             implies `map_get_u256 m (0, caller) = 1` in the
             slot-15 Map2).

**Trust budget impact** (per `Print Assumptions`):
- Before R083: 2 monolithic sub-axioms +
  upstream framework primitives.
- After R083: 0 contract-level sub-axioms;
  2 new R083 framework primitives (reusable across all
  ERC-7201-namespaced OZ inheritors);
  2 audit-time facts (specific to StakingVault's AccessControl
  projection);
  2 Skolemization parameters (`mload_witness`,
  `mstore_post_memory`).

The contract-level axioms have been REPLACED by reusable framework
primitives plus narrower per-projection audit facts.  Net effect:
trust is REDISTRIBUTED from per-mutator gate axioms to per-framework
primitives + per-projection bindings.  This pays off across all
OZ-AccessControl-inheriting contracts (T3.3 grantRole/revokeRole/
renounceRole, TimelockControllerOptimistic's gate walks,
ProposalLib's role reads).

### Where to use R083 framework primitives

- **Namespace-anchored sload** (`run_sload_map2_u256_at_anchor`,
  `run_sload_struct_field_at_anchor`): any walker reading through
  an ERC-7201 namespace.  Use in T3.3 for the grantRole / revokeRole
  / renounceRole gate walks; TimelockControllerOptimistic for its
  AccessControl gate; ProposalLib's vote storage reads; etc.

- **Namespace-anchored sstore** (`run_sstore_map2_u256_at_anchor`):
  any walker writing through an ERC-7201 namespace.  Use in T3.3
  for the grantRole / revokeRole role-flag writes;
  TimelockControllerOptimistic for its scheduling Map2 writes.

- **Absorbing mload / mstore** (`run_mload_absorbing_at_make_state`,
  `run_mstore_absorbing_at_make_state`): any walker tail that
  emits events, reads the free-memory pointer, or writes scratch
  buffers without per-index memory shape requirements.

See also: R040 (wrapper-shape sstore), R055 (membership
equivalence), R067 (composite-walker template), R070 (per-mutator
recipe), R072 (abstract-base-class slot-agnostic helpers).

## R084: T3.3 trust-redistribution decomposition for OZ EnumerableSet remove

T3.3's mandate was to discharge
`run_fun__revokeRole_736_at_proj_sim_member` — the monolithic
walker+bridge axiom for the OZ EnumerableSet swap-and-pop remove —
into a real walker proof.  R084 records the trust-redistribution
methodology applied in this commit.

### The structural challenge

`fun__remove_1698` (the OZ EnumerableSet `_remove` body) has TWO
nested branches whose post-storage shapes differ:

```
fun__remove_1698(set_slot, value):
  position := sload(positions[role][value])
  if position == 0: return 0     // not a member — impossible under H_member
  valueIndex := position - 1
  lastIndex := sload(set_slot) - 1
  if valueIndex != lastIndex:
    // SWAP CASE: move tail into the freed slot
    lastValue := sload(values[role][lastIndex])
    sstore(values[role][valueIndex], lastValue)
    sstore(positions[role][lastValue], position)
  array_pop(values[role])         // ALWAYS: clears tail, decrements length
  sstore(positions[role][value], 0) // ALWAYS: zero out position
  return 1
```

The walker thus has 5 storage writes in the swap case (slot 1 ×2,
slot 2, slot 3 ×2) and 3 writes in the last-element case (slot 1,
slot 2, slot 3).  A full Coq walker proof requires:

- 3 NEW framework axioms for the INVERSE storage operations
  (set-to-zero variants of the existing forward sstore axioms,
  plus array_pop which combines two writes — see below).
- A ~300-500 LOC walker proof covering both branches of the inner
  switch, with the `position - 1 = lastIndex` arithmetic discharged.
- A bridge lemma from the post-storage's slot-1 lookup to
  `Guardian.remove_role` (the order-preserving filter on the sim side).
- Role-specialized variants of the bridge for DEFAULT / OG / OGM.

Per the original task brief (`T3.3` in the adversarial review
remediation plan), the expected scale is 500-1500 LOC.  In one
session, full discharge is a stretch goal.

### The R084 decomposition

R084's contribution is to **redistribute trust** out of the monolithic
walker+bridge axiom into smaller, cleaner-shaped axioms.  Three new
INVERSE framework axioms land in this commit and are the audit-shape
sibling of the existing R051.c slot-1/2/3 forward axioms:

1. **`run_storage_set_to_zero_t_bytes32_at_proj_sim`** — sets the
   body slot at index `idx` to 0.  Inverse of
   `run_sstore_role_values_body_at_proj_sim`.

2. **`run_array_pop_at_proj_sim`** — clears `values[oldLen-1]`,
   decrements `length` from `oldLen` to `oldLen-1`.  Inverse of
   `run_array_push_at_proj_sim` (which is a Qed Lemma; the pop
   variant is parametric trust since the panic-guard arithmetic
   doesn't reduce against the abstract length map).

3. **`run_storage_set_to_zero_t_uint256_at_positions_proj_sim`** —
   sets the positions slot at `(role, value)` to 0.  Inverse of
   `run_sstore_role_positions_at_proj_sim`.

These three axioms have the SAME parametric-trust footprint as the
forward R051.c siblings.  No new audit obligations — they restate
the projection's behavior at the same OZ-actual slot expressions.

### Walker-vs-bridge decomposition

The big axiom is replaced by **two smaller axioms** plus a Qed
composition Lemma:

```coq
(* Was: monolithic axiom returning (storage_post, set_eq, walker). *)
Axiom run_fun__revokeRole_736_at_proj_sim_member : ...

(* Now: Skolemize the post-storage via three parameters. *)
Parameter post_positions_after_remove : ...
Parameter post_length_after_remove : ...
Parameter post_body_after_remove : ...
Definition revoke_post_storage role sim account :=
  [ Map2 (declare_or_assign role_member_map ...);
    Map2 (post_positions_after_remove role sim account);
    Map  (post_length_after_remove role sim account);
    Map2 (post_body_after_remove role sim account) ].

(* Walker axiom: now a NARROWER claim with a CONCRETE post-storage. *)
Axiom run_fun__revokeRole_736_at_proj_sim_member_walker :
  forall ... memory (H_mem : ...),
  exists memory',
  {{? ... | fun__revokeRole_736 role account ⇓ Result.Ok 1
   | Some (make_state env state_base memory'
            (revoke_post_storage role sim account)) ?}}.

(* Property axiom: focused set-equivalence bridge for the Skolem. *)
Axiom set_eq_at_role_revoke_post_storage :
  forall role sim account ...,
  set_eq_at_role
    (revoke_post_storage role sim account)
    (proj_sim (revoke_role_sim role sim account)).

(* Composition: now a Qed Lemma. *)
Lemma run_fun__revokeRole_736_at_proj_sim_member :
  forall ..., exists storage_post, set_eq_at_role ... /\ forall memory, ... .
Proof.
  intros. exists (revoke_post_storage role sim account).
  split; [apply set_eq_at_role_revoke_post_storage|apply walker_axiom].
Qed.
```

### Trust budget impact (per `Print Assumptions`)

Before T3.3:
- 1 monolithic walker+bridge axiom
  (`run_fun__revokeRole_736_at_proj_sim_member`)

After T3.3:
- 1 walker-shape axiom (narrower; concrete post-storage)
  (`run_fun__revokeRole_736_at_proj_sim_member_walker`)
- 1 property bridge axiom (set-equivalence of the Skolemized
  post-storage)
  (`set_eq_at_role_revoke_post_storage`)
- 3 Skolem Parameters (`post_positions_after_remove`,
  `post_length_after_remove`, `post_body_after_remove`) — these
  are not Axioms but type Parameters; same audit footprint as
  `mstore_post_memory` / `mload_witness` from R083.
- 3 new framework axioms for inverse operations (above).
- The composed `Lemma` is `Qed`.

NET: same logical content, but trust is REDISTRIBUTED into
smaller-footprint axioms with sharper audit signatures.  The
walker-shape axiom is now framework-style (closeable by a single
walker proof, no semantic bridge inside).  The property axiom is
isolated and discharge-able by three role-specific Qed Lemmas via
the existing R059 `contains_at_role_proj_sim_*` family.

### Path to full discharge

For the next agent who wants to retire ALL the new axioms:

1. **Discharge `run_fun__revokeRole_736_at_proj_sim_member_walker`**
   as a Qed walker by composing the existing
   `run_fun__revokeRole_1506_at_proj_sim_member` (Phase 1, already
   Qed in this commit's predecessor) with a new
   `run_fun_remove_2112_at_proj_sim_member` (Phase 2 — the
   ~400 LOC swap-and-pop walker).  The Phase 2 walker uses the
   three new framework axioms plus the existing R051.c reads /
   writes.  Both branches of the inner switch need separate
   walker arms; the post-state of each is then unified via the
   Skolemized witnesses.

2. **Discharge `set_eq_at_role_revoke_post_storage`** as three Qed
   Lemmas (DEFAULT / OG / OGM) using:
   - `contains_at_role_proj_sim_admin` (R059 bridge to addr_in)
   - `addr_in_remove_role_self` / `addr_in_remove_role_other`
     (pure Boolean lemmas on `Guardian.remove_role`)
   - The Skolemized `post_positions_after_remove` carries the
     correct "positions[role][account] := 0, positions[role][lastValue]
     := position" pattern — the audit fact is that this pattern's
     `contains_at_role` reading matches the sim's `remove_role`.

3. **Bind the Skolems**: the audit reviewer verifies that
   `post_positions_after_remove`, etc. encode the correct
   swap-and-pop transformation.  The discharge in step 1 above will
   pin these via the walker's actual storage writes (existing
   `Dict.declare_or_assign` calls in the OZ Yul).

### Composition with R083

R083 and R084 are sibling framework-extension families:
- R083 addresses ERC-7201 namespace anchors (StakingVault,
  TimelockControllerOptimistic, ProposalLib).
- R084 addresses OZ EnumerableSet inverse-write primitives
  (Guardian's revoke, plus any future `_remove` consumers via
  AccessControlEnumerable).

Together they cover the two structural gaps left by upstream's
small-nat-only sload/sstore axioms.

See also: R051.c (forward storage axioms), R055 (grantRole bridge
methodology), R059 (`set_eq_at_role` membership equivalence), R083
(ERC-7201 + memory absorption).

## R085: Skolem-Parameter elimination for T3.3 swap-and-pop post-state

R085 follows R084's decomposition and pushes one trust-redistribution
step further: it promotes the three Skolem `Parameter`s introduced by
R084 into concrete `Definition`s computed directly from `sim`.  Trust
impact (per `Print Assumptions`):

- Before R085 (after R084): 3 `Parameter` declarations
  (`post_positions_after_remove`, `post_length_after_remove`,
  `post_body_after_remove`) + walker-shape Axiom +
  property-bridge Axiom + 3 R084 inverse-op framework axioms.

- After R085: 0 `Parameter` declarations + walker-shape Axiom +
  property-bridge Axiom + 3 R084 inverse-op framework axioms.

NET: 3 axioms retired from `Print Assumptions` (the three Parameters,
which the snapshot counts as axiom-equivalent assumptions).

### The R085 concrete shapes

The post-positions Skolem is replaced by a `Definition` that names
the OZ swap-and-pop dict expression directly:

```coq
Definition post_positions_after_remove role sim account :=
  let position := position_of role sim account in
  let oldLen   := old_len_of role sim in
  if (position - 1) =? (oldLen - 1) then
    (* Last-element fast path: no swap. *)
    Dict.declare_or_assign (role_positions_map sim) (role, account) 0
  else
    (* Swap case: bump survivor's position then zero account's. *)
    Dict.declare_or_assign
      (Dict.declare_or_assign
         (role_positions_map sim) (role, last_value role sim) position)
      (role, account) 0.
```

where `last_value role sim` is the head of the role-list (= OZ array
tail under the cons-to-front convention; rests on `body_map(role,
oldLen - 1) = head` for `_remove`'s `lastValue` read).  The
post-length Skolem is `Dict.declare_or_assign length role (oldLen -
1)`.  The post-body Skolem mirrors the swap-and-pop body writes.

### Why this matters for discharge

With concrete `Definition` shapes, the walker proof has a concrete
post-state to land at — every storage-write step's
`Dict.declare_or_assign` from the R084 framework axioms now unifies
syntactically with the slot-1/2/3 entries of `revoke_post_storage`.
This eliminates the existential-witness gymnastics that Parameter
shapes forced.

Symmetrically, the property bridge
`set_eq_at_role_revoke_post_storage` (still an Axiom in this commit)
becomes mechanically dischargeable: it now reduces to a Boolean
equality between two `Dict.declare_or_assign` chains under
`contains_at_role` — both with concrete shapes.

### Path to Qed discharge (R085 residual)

The R085-residual work to retire the remaining two Axioms:

1. **Walker discharge**: a ~600-1000 LOC walker over
   `fun_remove_2112` / `fun__remove_1698`'s body using R084's three
   inverse-op axioms.  Both the swap case and the last-element case
   need separate walker arms, unified at the post-state via the R085
   concrete shapes.  Helper lemmas:
   - `last_value_neq_account_in_swap_case` (proven below): under the
     swap hypothesis `position - 1 ≠ oldLen - 1` and `H_member`,
     `last_value role sim ≠ account` (so the `positions[lastValue] :=
     position` write doesn't collide with the `positions[account] :=
     0` write).
   - The cons-front-vs-array-index bridge: `position_of role sim
     (head admins) = length admins`, so position - 1 = lastIndex
     exactly when account is the head.

2. **Bridge discharge**: a ~300-500 LOC case-split-by-(role', a')
   proof.  Each case reduces via the R085 helpers
   (`map_get_u256_declare_or_assign_eq/neq`, sketched in the source
   file) to a Boolean fact about `Guardian.addr_in (remove_role
   list account) a'` — already proven via
   `addr_in_remove_role_self`/`addr_in_remove_role_other` (R059).

### Methodology finding

The Parameter-to-Definition promotion pattern is broadly applicable:
any composite walker whose post-state is parametric over the
post-execution shape can be tightened by computing that shape
directly from the pre-state via the same operations the walker
performs.  This is "anchor early": instead of leaving the post-state
abstract via Skolem and discharging via a property axiom, compute it
concretely and discharge by direct unification.

The R084-style decomposition (walker + property bridge + Skolems) is
sometimes the right shape (e.g. when the post-state genuinely
depends on existential intermediate values), but for OZ
EnumerableSet remove the post-state is a pure function of `sim` and
the input — so concrete is strictly better.

See also: R084 (T3.3 trust-redistribution), R059 (`set_eq_at_role`),
R055 (grantRole bridge methodology).

## R065-R071: Per-mutator composite-walker recipe

Validated on 12 mutators across 6 contracts: VersionRegistry,
RewardTokenRegistry, Guardian, SelectorRegistry, ProposalLib,
TimelockControllerOptimistic.

**3-step recipe per mutator:**

1. **Per-target observational bridge** (~80-120 LOC):

   ```coq
   Axiom proj_sim_<fn>_observes :
     forall sim args,
     set_eq_in_registry  (* or observationally_eq_storage_<contract> *)
       (proj_sim_post_<fn> sim args)
       (proj_sim (sim_<fn> sim args)).
   ```

2. **Composite walker axiom** (~30 LOC):

   ```coq
   Axiom run_fun_<fn>_at_proj_sim :
     forall codes env state caller sim args,
     <preconditions including callee specs> ->
     {{? codes, env, Some (make_state ... (proj_sim sim) ...) |
       fun_<fn> args ⇓ Result.Ok output
     | Some (make_state ... (proj_sim_post_<fn> sim args) ...) ?}}.
   ```

3. **Milestone theorem** (~30 LOC):

   ```coq
   Theorem run_<fn>_equivalent_make_state :
     forall ...,
     <preconditions> ->
     exists state_post,
       {{? codes, env, Some (make_state ...) |
         <run shape> ⇓ Result.Ok output
       | Some state_post ?}}
       /\ observationally_eq_storage state_post
                                     (make_state ... (proj_sim (sim_<fn> sim args)) ...).
   Proof.
     intros. eexists.
     split; [apply run_fun_<fn>_at_proj_sim; assumption | apply <observes axiom>].
   Qed.
   ```

**Per-mutator cost:** 300-600 LOC, ~10-15 min agent time, 2-4 axioms.

**Where to look for templates:**
- Simplest single-staticcall: `VersionRegistry.v::run_deprecateVersion_equivalent_make_state`
- Two-staticcall: `VersionRegistry.v::run_registerVersion_equivalent_make_state`
- Role-branching: `Guardian.v::run_cancel_equivalent_make_state`
- Looping over array argument: `SelectorRegistry.v::run_registerSelectors_equivalent_make_state`
- Multi-staticcall library: `ProposalLib.v::run_fun_proposeOptimistic_179_equivalent`
- Multi-namespace inherited: `TimelockControllerOptimistic.v::run_fun_scheduleBatch_1295_equivalent`

**Walker tactic library:** all targets use the same prelude (unfold
M.{strong_let_,let_,generic_let,pure,call}) plus contract-specific
lazymatch arms calling:
- `StaticCallBridge.sc_word` for staticcalls (R063)
- `AbiEncoding.run_*` for encoding/decoding (R064)
- `Storage.run_sload_*` / `run_sstore_*` for storage ops
- The contract's own `run_fun_<inner>_at_proj_sim` for sub-functions

---

# Section 8: Common pitfalls and resolved issues

## R020: `Stdlib.timestamp` semantics (RESOLVED in dev clone)

Earlier upstream had `Stdlib.timestamp = LowM.Impossible`. Now:

```coq
Definition timestamp : M.t U256.t :=
  LowM.Primitive Primitive.GetBlockTimestamp M.pure.
```

Discharge via `pr` (Primitive) tactic + state hypothesis.

## R021: `RunO.CallContract` rule (RESOLVED via upstream patch)

`RunO.t` originally lacked a `CallContract` constructor. Upstream
`TheFrozenFire/rocq-of-solidity:feat/env-block-context` adds a
permissive constructor (`cc` tactic). Proof author picks `call_result`
and `state_inter` freely; soundness shifts to the proof-author level
via a separate callee-spec axiom.

## R035: `shallow_embed.py` mis-embeds nested control flow (RESOLVED)

`commonly_updated_vars` vs `final_updated_vars` confusion in switch
let_state binding. Fixed upstream (commit `696f60fd73`). Workaround
if regresses: pull from `TheFrozenFire/rocq-of-solidity:integration`.

## R041: missing `linkersymbol` definition (RESOLVED upstream)

Solc emits `linkersymbol("Path/To/Library.sol:LibName")` for external
library references. Without the runtime definition, M.monadic fails
with "object of type ident". Fixed upstream (commit `2646cf555a`).

## R042: `M.monadic` "object of type ident" trap (RESOLVED)

Cryptic error catches multiple causes. Upstream shallow_embed now
guards M.monadic against unresolved identifiers (commit `754592d34f`).

## R045: OZ modifier mocks — symbolic `with_X body` expansion

For OZ modifiers without shallow forms (inherited from abstract
base), define a symbolic wrapper:

```coq
Definition with_onlyRole_admin (body : M.t A) : M.t A :=
  let* _ := check_role caller ADMIN_ROLE in body.
```

The wrapper's expansion is the audit-time obligation.

## R046: `shallow_embed.py` drops sstore in OZ `_grantRole` (RESOLVED)

YulSwitch generator bug. Fixed upstream (commit `696f60fd73`).

## R048: R045 variant for pure-function libraries

For OZ libraries with no inherited storage (`SafeERC20`, etc.), the
symbolic wrapper has no `with_X` envelope — model the function via
its computational signature:

```coq
Axiom safeTransfer_callee_spec :
  forall token from to amount,
    transfer_returns_true token from to amount ->
    safeTransfer token from to amount = Result.Ok BlockUnit.Tt.
```

## R060: Verify contract surface against actual source

Task descriptions become stale. Multiple agents in this corpus have
been briefed against descriptions that diverged from actual source.

**Discipline:** first action of any equivalence-proof task is to read
the actual `contracts/.../X.sol` source. If the brief is wrong, file
a WISDOM note (or update the task) and proceed against truth.

## R079: StakingVault rewards equivalence — multi-token accrual + ERC20 + zero-first reentrancy

Validates the R067 / R069 composite-walker recipe on the
StakingVault rewards path, which combines THREE patterns:

1. **Multi-token mapping accrual.** The contract maintains
   per-token [RewardInfo] (5 slots: payoutLastPaid, rewardIndex,
   balanceAccounted, balanceLastKnown, totalClaimed) and
   per-(token, user) [UserRewardInfo] (2 slots: lastRewardIndex,
   accruedRewards). Slot layout: keccak256(token, 7) for
   RewardInfo and keccak256(user, keccak256(token, 9)) for
   UserRewardInfo. Two levels of keccak indirection ↔
   `proofs/equivalence/StakingVaultRewards.v` keccak bound axioms
   `keccak256_tuple2_offset_bound` + `keccak256_nested_offset_bound`.

2. **R063 staticcall composition for safeTransfer.** The
   `claimRewards` body ends each per-token iteration with an
   `IERC20(token).safeTransfer(msg.sender, claimable)` call —
   structurally identical to R063's `staticcall` composite but
   using `call` (the SafeERC20 wrapper) since `transfer` mutates
   the token's storage. Callee-spec axiom
   `safeTransfer_4922_callee_spec` pairs the on-chain success
   with the sim's `safeTransfer_success_spec_concrete`. The
   companion sim layer `simulations/StakingVaultRewardsERC20.v`
   carries the bookkeeping (balance decrement) at the mock-ERC20
   level; the equivalence-layer obligation is "the vault's OWN
   storage is preserved" (the token's storage is outside
   `proj_sim`).

3. **Reentrancy zero-first invariant lift.** The `claimRewards`
   body writes `accruedRewards := 0` BEFORE the safeTransfer
   external call (the load-bearing comment at StakingVault.sol:359).
   The sim-level invariant is mechanized as
   `proofs/StakingVaultRewardsReentrancy.v` (REN-1..REN-5);
   the equivalence-layer re-exports those theorems in Section 8
   of `proofs/equivalence/StakingVaultRewards.v`, plus
   `claim_each_token_concrete_single_zero` and
   `claim_each_token_concrete_single_totalClaimed` Qeds that
   apply the sim invariants to the equivalence-layer sim
   transformer. Both close against PrimInt63 framework axioms
   only.

**Layout.** Two-tier file:

- Sections 1-3 are **slot-agnostic**: a sim aggregator
  ([GlobalRewardState] over `perToken` / `perUser` dicts +
  [rewardTokens] enumerable set), pure-Coq transformers
  ([set_reward_ratio_sim], [poke_sim_full], [claim_sim_full]),
  and a parameterized Section over [accrue_for_token] with
  walker-template helper lemmas (ratio / tokens preservation
  across the accrual fold). Closes Qed against PrimInt63 only.

- Sections 4-8 are **concrete StakingVault inheritor**: binds
  the shallow form's `fun_setRewardRatio_1036`, `fun_poke_1082`,
  `fun_claimRewards_1010` via composite walker axioms, with
  Skolemized post-storages and observational bridge axioms
  per the R067 / R069 budget.

**Trust budget per mutator** (matches R067 recipe):
- 1 composite walker axiom
- 1 Skolemized post-storage Parameter
- 1 observational bridge axiom (conjunction over 3 slot
  families: rewardRatio / rewardInfo / userReward)
- Plus shared callee specs:
  - `accessControl_checkRole_returns` (AccessControl modifier)
  - `rewardTokenRegistry_isRegistered_returns` (R063 staticcall)
  - `safeTransfer_4922_callee_spec` (R063 ERC20 call)
- Plus shared infra: `keccak256_tuple2_offset_bound`,
  `keccak256_nested_offset_bound`, the projection lens
  [proj_sim_concrete] + 3 observational predicates with refl
  axioms.

Total **30 axioms** per the headline `Print Assumptions` of the
milestone Qeds, dominated by Skolemized post-storages /
observational predicates / callee specs — same R067 / R069
budget shape as RewardTokenRegistry and SelectorRegistry.

**Cross-pollination with other Wave 2 agents.** The
[proj_sim_concrete] lens is left abstract precisely because
StakingVault inherits ERC4626 (deposit/withdraw share math) +
ERC20Votes (Trace208 checkpoints) + AccessControl — the full
projection must compose with the other Wave 2 slices' projections
on slots 0-1 (ERC4626 cache + ERC20 supply / balances), slots
4-5 (unstakingManager / delay), slots 10-11 (optimistic
delegation checkpoints). Each downstream concrete instantiation
inherits the rewards-side observational predicates without
re-deriving them.

---

# Appendix: Agent dispatch hygiene

Workflow notes — not Rocq-tactical, but capture operational gotchas.

## Worktree baseline reset

Agent dispatches in this repo run in worktrees that may spawn from
a stale reference rather than the current feature branch. Symptom:
agent reports `git rev-parse HEAD` returns an older commit than the
brief specified.

**Fix in agent prompts:** include explicit first-action block:

```bash
git fetch thefrozenfire feature/formal-verification
git reset --hard thefrozenfire/feature/formal-verification
cp /Users/jmart/.../formal-verification/rocq/generated/*.v formal-verification/rocq/generated/
```

## Specify expected baseline as a remote, not a commit hash

Commit hashes move. Saying "verify HEAD matches
`thefrozenfire/feature/formal-verification`" is more robust than
"verify HEAD = abc1234".

## Build full tree, not just touched files

Single-file builds can succeed while full tree fails (sibling files
reference your changes through `_RocqProject`). Run full
`bash formal-verification/scripts/rocq-build` before declaring done.

## R078: StakingVault exchange-rate equivalence — ERC4626 inheritor instantiation

The four ERC4626-derived public entry-points on
[contracts/staking/StakingVault.sol] — `deposit`, `mint`, `withdraw`,
`redeem` — share a common Yul-body shape:

```
  S1.  maxXxx view (always uint256.max in default ERC4626).
  S2.  if <input> > maxXxx: revert ERC4626ExceededMaxXxx
  S3.  preview-conversion (deposit/redeem float-rounding;
                           mint/withdraw ceil-rounding).
  S4.  caller := _msgSender()
  S5.  _deposit(caller, receiver, assets, shares)            (deposit/mint)
       or
       _withdraw(caller, receiver, owner, assets, shares)    (withdraw/redeem)
  S6.  Return <output>.
```

The internal `_deposit` / `_withdraw` paths are OVERRIDDEN at
StakingVault.sol:252 / sol:266 to bump `totalDeposited` and
`nativeBalanceLastKnown` around the OZ-base super call, all wrapped
in the `accrueRewards(caller, receiver)` modifier.

**Storage-namespace anchors** the four entry-points all touch:

```
  ERC4626 storage            (asset() pointer)
  ERC20 storage              (balances + totalSupply + allowances)
  ERC20Votes storage         (delegates + delegateCheckpoints +
                              totalSupplyCheckpoints)
  AccessControl storage      (untouched but present)
  AccessControlEnumerable    (untouched but present)
  ReentrancyGuard            (status toggled NotEntered <-> Entered
                              around each entry-point)
  Nonces                     (untouched in exchange path)
  UUPS proxy                 (untouched in exchange path)
  StakingVault own slots:
    totalDeposited           (+= assets / -= assets)
    nativeBalanceLastKnown   (+= assets at deposit; refreshed via
                              external balanceOf at withdraw end)
    nativeRewardsLastPaid    (:= now)
    rewardTrackers           (per-token bumps under accrueRewards)
    userRewardTrackers       (per-user-per-token bumps)
    optimisticDelegateCkpts  (mint/burn pushes via _update override)
```

**Per-entry-point external sandwich** (R063 staticcall composite):

- `deposit` / `mint`:  `asset.transferFrom(caller, vault, assets)`.
- `withdraw` / `redeem` (`unstakingDelay = 0`):  `asset.transfer(receiver, assets)`.
- `withdraw` / `redeem` (`unstakingDelay > 0`):  `SafeERC20.forceApprove(asset, unstakingManager, assets)` + `unstakingManager.createLock(receiver, assets, now + unstakingDelay)`.

The unstakingDelay branch-split is observed via a sim-side
`has_unstakingDelay_zero : SimulatedStorage.t -> bool` predicate at
the storage_base; the composite walker axiom carries the chosen
branch in its Skolemized post-storage.

**Reentrancy-guard interaction:** the ERC4626 entry-points run under
the `nonReentrant` modifier (inherited from ReentrancyGuardUpgradeable
via ERC4626). The internal `_deposit` / `_withdraw` happen INSIDE the
lock; the external `asset.transferFrom` / `asset.transfer` /
`unstakingManager.createLock` calls cannot re-enter. R045's
`with_nonReentrant` symbolic expansion from
`proofs/equivalence/ReentrancyGuard.v` captures the pre/post lock
invariant.

**R051/R070/R071 instantiation:** the equivalence file
`proofs/equivalence/StakingVaultExchange.v` exposes:

- 4 Skolemized post-storage `Parameter`s (`proj_post_deposit_4312` /
  `proj_post_mint_4356` / `proj_post_withdraw_4403` /
  `proj_post_redeem_4450`).
- 4 per-target observational bridge `Axiom`s
  (`proj_post_<op>_observes` — currently reflexive shape; the audit-
  time obligation is to refine them into a slot-by-slot
  characterisation against the sim's `deposit` / `withdraw`
  transitions).
- 4 composite walker `Axiom`s (`run_fun_<op>_at_storage_base`) — one
  per entry-point Hoare triple keyed by `storage_base` + arguments +
  `now_timestamp`.
- 4 milestone Qed theorems (`run_<op>_equivalent`) composing the
  above via Phase-1/Phase-3 R071 recipe.

Plus a Section `StakingVaultExchangeLens` parameterised over four
slot indices (`slot_ERC20_totalSupply` /
`slot_totalDeposited` / `slot_nativeBalanceLastKnown` /
`slot_nativeRewardsLastPaid`) projecting the sim's
`StakingVaultExchange.State.t` out of the full inheritor storage.

**Trust budget:** 4 composite walker axioms + 4 Skolemized post-
storage Parameters + 4 observational bridge axioms + 1 environment
Parameter (`now_timestamp`) + 4 callee-spec axioms (documentation-
only, `True` conclusions) + 4 opaque Yul-body Parameters
(`fun_<op>_op`, become Notations aliasing the shallow form when
`StakingVault_shallow.v` is activated in `_RocqProject`). Total: 13
axioms / parameters.

**Print Assumptions** on the four milestone Qeds surfaces:

- 4 composite walker axioms (one per entry-point).
- 4 Skolemized post-storage Parameters.
- 4 opaque Yul-body Parameters.
- 1 `now_timestamp` Parameter.
- 2 pre-existing framework axioms (`Memory.of_u256_list`,
  `Storage.of_storable_values`) — same as every other R070/R071
  closer.

No new framework axioms.

**Wave 2 in-flight dependencies:**

- **#255 (rewards)**: owns the per-token reward-tracker slots
  (`rewardTrackers`, `userRewardTrackers`, `disallowedRewardTokens`,
  `rewardTokenRegistry`). These slots are touched by `accrueRewards`
  inside every exchange-rate operation. The observational bridge in
  Section 7 of `StakingVaultExchange.v` leaves the reward-tracker
  post-state opaque; #255's WISDOM/equivalence entry characterises
  the slot-by-slot bridge.

- **#256 (delegation)**: owns the `_update` override's chain into
  `_moveOptimisticDelegateVotes`. Each exchange-rate operation hits
  `_update` via `_mint` / `_burn`; #256's file characterises the
  optimistic-delegate checkpoint pushes.

- **#257 (pause/admin)**: owns role-gated mutators (orthogonal to
  exchange-rate; `unstakingDelay` is observed only).

**Wave 1 closing dependencies:**

- **#241 (ERC4626 / ERC20Votes)**: when these land, the four
  composite walker axioms can be upgraded to use the slot-agnostic
  helper layer instead of opaque `proj_post_<op>` post-storages.

- **#240 (Votes), #238 (ReentrancyGuard)**: already landed.

When `StakingVault_shallow.v` is activated in `_RocqProject` (the
~3 min compilation cost is the gate), the four `fun_<op>_op`
Parameters become Notations aliasing the shallow-form definitions.
The walker arms inside the four composite axioms then have full
mechanical bodies to discharge via the R028 walker tactic prelude +
per-call-site StaticCallBridge + sstore + sload bridges. Estimated
walker-arm work: ~2000 LOC across the four entry points.

## Push timing — explicit refspec is safer

`git push remote branch` can silently no-op with unusual
branch-tracking config. Prefer:

```bash
git push thefrozenfire <commit-hash>:refs/heads/feature/formal-verification
```

forces fast-forward-or-fail with no tracking ambiguity.
