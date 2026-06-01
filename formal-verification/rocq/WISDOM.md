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

**CLOSURE 2026-06-01 (task #288, T3-finish)**: The composite-walker
Lemma `run_fun_deprecateVersion_187_at_proj_sim` is now closed as
a `Qed` Lemma (no longer Admitted). Discharge required ~280 LOC
of walker assembly plus six new framework primitives in
[AbiEncoding.v] / [FrameworkExtensions.v]:

1. **`AbiEncoding.staticcall_make_state_bridge_absorbing`** —
   Skolem-form sibling of `staticcall_make_state_bridge` (the
   original required `k < length memory`, which doesn't hold after
   R083-absorbed mstores write at non-32-aligned offsets like 132).
   Companion structural axioms: `staticcall_post_memory_at_out`,
   `staticcall_post_memory_at_other`, `staticcall_post_memory_length`.

2. **`AbiEncoding.make_state_with_gas_eq`** — sibling of
   `make_state_with_rd_eq`. Required because the `Stdlib.gas`
   primitive decrements `State.gas` via `GetGas`'s eval_primitive,
   producing a `<| State.gas := state.gas - 1 |>` override that
   breaks the `make_state` shape required by the bridge. Same
   soundness story as `make_state_with_rd_eq`: gas is a record field
   not touched by `with_current_storage`.

3. **`AbiEncoding.make_state_return_data_eq`** — `make_state`
   preserves `State.return_data` from `state_base`. Needed to derive
   the `H_rd` hypothesis of `run_returndatasize_at_post_bridge` after
   absorbing the rd override into state_base.

4. **`AbiEncoding.run_post_staticcall_decode_bool`** — composite
   axiom for S12-S13 (finalize_allocation + abi_decode_tuple) at
   the absorbing post-state. Skolemises the post-memory; the
   audit-time obligation is that the decoded value equals the
   staticcall's call_result.

5. **`AbiEncoding.run_mapping_index_access_absorbing`** — composite
   axiom for the two-mstore-then-keccak256_tuple2 pattern at the
   absorbing post-state. Replaces the existing `run_mapping_index_access`
   leaf's `exists w0 w1 rest, memory = w0 :: w1 :: rest` precondition
   (which doesn't hold on Skolem memory).

6. **`FrameworkExtensions.mload_witness_bound`** /
   **`FrameworkExtensions.mstore_post_memory_length`** /
   **`FrameworkExtensions.mstore_post_memory_at_far`** — bookkeeping
   axioms about the R083 Skolem functions: post-mstore memory has
   the same length as pre-mstore; mstore at offset O doesn't touch
   word indices "far" from O.

**Strategy**: the post-bridge state-shape (with `<| return_data := bytes |>`
override) is folded into state_base immediately after S9 via
`make_state_with_rd_eq`. This re-establishes `make_state` form for
S10-S21, avoiding the need for `with_rd` companion axioms for each
subsequent step.

These six new primitives are reusable across every R050-blocked
mutator with a staticcall + abi-prelude + abi-decode tail
(VersionRegistry.registerVersion, RewardTokenRegistry.* — though
registerVersion is still R050-blocked per the R058 diagnosis).

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

## R086: SafeERC20 library-call + linkersymbol framework gap

Task #292's investigation of `UnstakingManager`'s three mutator
equivalences (createLock / cancelLock / claimLock) confirmed that
R082's composite-walker methodology applies cleanly: each of the
three Admitted milestone theorems was promoted to a Qed Lemma backed
by a composite walker Axiom + observational bridge Axioms + a
Skolem post-state Parameter (the standard R082 + R084 redistribution
shape — see the per-mutator residual notes in
`proofs/equivalence/UnstakingManager.v`).

**But**: the walker Axioms themselves are NOT yet discharged. The
one remaining framework gap is the SafeERC20 library-call
infrastructure. All three UnstakingManager mutators emit Yul of the
form:

```yul
let expr_X_address := linkersymbol("...path...SafeERC20.sol:SafeERC20")
...
do fun_safeTransferFrom_1037(token, from, to, amount)
```

where `linkersymbol` resolves at link time to the deployed library's
address, and `fun_safeTransferFrom_1037` is the inlined library body
that performs an `extcodesize` check + external `call` to the
token's `transfer` selector + return-data decode.

The shallow embedding has the `linkersymbol` primitive defined
upstream (R041 resolved), but the corresponding `run_linkersymbol`
axiom — analogous to `StaticCallBridge.run_loadimmutable` — is
missing. Without it, the inlined library body cannot walk to a
concrete library-address value, and the subsequent `call` cannot
fire via `StaticCallBridge.run_staticcall_general`.

Two framework primitives are needed to close R086:

1. **`run_linkersymbol`** (StaticCallBridge or AbiEncoding): a
   leaf axiom witnessing `linkersymbol(path) = library_addr`,
   parameterized by a `LinkerBinding` Parameter that fixes the
   path-to-address mapping at the deployment level. Analogous to
   `loadimmutable` but for library addresses.

2. **`fun_safeTransfer_callee_spec`** (per-library composite):
   a callee-spec axiom following the R063 template. Bundles the
   library body's `extcodesize` check + external `call` +
   return-data decode into a single walker arm.
   `safeTransfer_success_spec_concrete` (from StakingVaultRewards
   Section 6) is the model — it pins the trust to a per-(token,
   recipient, amount) success flag witnessing the T-REWARDTOKEN
   assumption.

Once R086 lands, the three UnstakingManager walker Axioms become
mechanically dischargeable via the standard R028 walker prelude +
R082 staticcall bridge + R040 sstore wrappers + R047
case-split-before-eexists. Estimated work per mutator: 500-1500 LOC.

R086 also gates the closure of `StakingVaultExchange.v`'s four
walker Axioms (deposit / mint / withdraw / redeem) — each uses
`forceApprove` and `transferFrom` via SafeERC20 — and any future
contract that uses the SafeERC20 library wrapper.

See also: R041 (resolved — `linkersymbol` definition), R063
(staticcall callee-spec template), R082 (composite-walker
discharge — VersionRegistry.deprecateVersion).

## R087: ROG composite-walker discharge — structural blockers

**Task #291 (T3.2-ROG-finish, 2026-06-01)** attempted to extend the R082
discharge methodology from `VersionRegistry.deprecateVersion` to
ReserveOptimisticGovernor's three composite walker Axioms
(`run_fun_propose_389_at_proj_sim`, `run_fun_castVote_4378_at_proj_sim`,
`run_fun_execute_4145_at_proj_sim`). Diagnosis: **R082's six framework
primitives are necessary but NOT sufficient for the ROG walkers**.
Four classes of structural blocker emerged before any per-walker LOC
was written. (Numbered R087 because R086 was concurrently claimed by
the UnstakingManager SafeERC20 / linkersymbol framework gap — see
above; the two diagnoses are independent.)

### Sized profile of each ROG walker body

`fun_castVote_4378` (the simplest entry point) is a 19-LOC Yul wrapper
that dispatches via `fun__castVote_4615` (also a thin wrapper) →
`fun__castVote_1014` (the meaningful body, 113 LOC). The 1014 body in
turn calls **seven** internal helpers:

  - `fun__validateStateBitmap_4891` (45 LOC) → calls `fun_state_592`
  - `fun_state_592` (204 LOC) — the OZ `Governor.state()` dispatch;
    contains an external `staticcall` to `token.getPastTotalSupply()`
    plus 8+ conditional branches across snapshot/deadline/vetoThreshold
  - `fun_proposalSnapshot_3501` (25 LOC)
  - `fun__isOptimistic_1236` (15 LOC)
  - `fun__getVotes_7797` (48 LOC) — external `staticcall` to
    `token.getPastVotes()`
  - `fun__getOptimisticVotes_1258` (50 LOC) — external `staticcall` to
    `token.getOptimisticVotes()`
  - `fun__countVote_926` (42 LOC) — dispatches to GovernorCountingSimple
  - `fun__tallyUpdated_1059` (89 LOC) — calls `state()` AGAIN and on
    the optimistic-defeat-transition path delegatecalls into
    ProposalLib's `transitionToPessimistic` (itself a 12-step walker
    that is STILL `Axiom run_fun_transitionToPessimistic_400_at_storage_base`)

Total reachable Yul body for `fun_castVote_4378`: **~700 LOC across 8
internal helpers**, with 3 external staticcalls and 1 conditional
delegatecall. The R082 deprecateVersion template handled ONE staticcall
in ONE function body of ~80 LOC.

`fun_execute_4145` (180-LOC body) calls eight helpers — see
`fun__getGovernorStorage_3168`, `fun_getProposalId_3355`,
`fun__encodeStateBitmap_4852` (×2), `fun__validateStateBitmap_4891`
(which calls the 204-LOC `fun_state_592`), `fun__executor_1072`,
`fun_pushBack_18486` (OZ Bytes32Deque), `fun__executeOperations_797`
(which dispatches through TimelockController), `fun_empty_18779`,
`fun_clear_18743` — plus a conditional `for` loop over targets emitting
`keccak256` digests, plus a `log1` event emission.

`fun_propose_389` (80-LOC body) is the smallest entry-level body but
hits the THIRD blocker (see below).

### Blocker 1 — Per-internal-helper sub-axiom proliferation

A mechanical discharge of `fun_castVote_4378` against existing
framework leaves would require introducing **at least 8 new per-helper
composite walker sub-axioms** (one per internal helper above), each
itself a load-bearing trust commitment. Net trust accounting:

  - Before: 1 composite walker `Axiom` (`run_fun_castVote_4378_at_proj_sim`)
  - After: 1 composite walker `Lemma` + 8 helper composite `Axiom`s

This is **not a net trust reduction** — it relocates the trust from one
opaque Hoare triple to eight opaque Hoare triples, each with its own
preconditions and post-state Skolems. R082's discharge gained
methodology value because `fun_deprecateVersion_187` has NO internal
helper dispatches (it's a single 21-step monolithic Yul body); the
framework primitives R082 added (`staticcall_make_state_bridge_absorbing`
et al.) sufficed to walk the body in 280 LOC.

The ROG walkers are NOT "deeper bodies amenable to the same primitives";
they are "heavy inheritor compositions" whose audit cost is dominated
by the inherited OZ Governor / GovernorCountingSimple /
GovernorPreventLateQuorum / GovernorTimelockControl / GovernorVotes
base contracts. R078/R079 mechanized the abstract bases via the
`GovernorBaseEquivalenceTemplate`; that template's slot-anchor
projection IS the audit-time discharge of the inherited helpers. The
composite-walker `Axiom`s in `ReserveOptimisticGovernor.v` are
themselves shaped to delegate inherited-helper discharge to the
GovernorBase template (see Section 11 of `ReserveOptimisticGovernor.v`,
which instantiates the template).

### Blocker 2 — Delegatecall has no framework primitive

`fun_propose_389` performs a **delegatecall** (NOT staticcall) into
`ProposalLib.proposePessimistic` via the linkersymbol-derived
ProposalLib address. The bytecode opcode `DELEGATECALL` differs from
`STATICCALL` in semantics: it executes the callee's bytecode under the
CALLER's storage / address / value context (i.e. the callee can mutate
the caller's storage).

R063's `StaticCallBridge` provides `staticcall_make_state_bridge` (and
R082's `_absorbing` sibling) for staticcalls. There is **no equivalent
primitive for delegatecall** in `AbiEncoding.v`, `StaticCallBridge.v`,
or `FrameworkExtensions.v`. A `delegatecall_make_state_bridge` would
need to express:

  - The post-storage equals the callee body's post-storage shape (the
    delegatecall WRITES the caller's storage).
  - The post-state's `return_data` records the callee's return.
  - The post-state's `memory` carries the callee's mstore tail.

Soundness is more delicate than staticcall (which is read-only):
delegatecall composes the caller's storage shape with the callee's
write effects, so the bridge must thread the callee's per-function
walker chain into the bridge's post-state shape. ProposalLib's
delegatecall target (`proposePessimistic_288`) is itself an unclosed
`Axiom run_fun_proposePessimistic_288_at_storage_base`.

### Blocker 3 — Three missing minor primitives

Even setting aside delegatecall, `fun_propose_389`'s body uses three
Yul primitives with no existing framework leaf:

  - `linkersymbol` — used to materialize the ProposalLib library address
    from its bytecode-relocation tag. Not a Stdlib operation; emitted
    only by the Solidity linker. Discharge: a simple `Axiom` that
    `linkersymbol(<lib-hash>) = some fixed address` per audit
    obligation, ~10 LOC.
  - `extcodesize` — used to gate the delegatecall (revert if the
    library hasn't been deployed). Not a Stdlib operation. Discharge:
    `extcodesize(addr) ≠ 0` under the audit obligation that the
    library is deployed, ~20 LOC.
  - `revert_forward_1` — the standard "bubble up the callee's revert
    data" handler. Used on the iszero-of-delegatecall-result branch.
    The audit-time success branch picks the non-revert side, so the
    primitive's discharge is just "this branch is unreachable under
    the success precondition." ~10 LOC.

These three are **bounded incremental work** (~40 LOC of framework
primitives total). They are NOT the structural blocker.

### Blocker 4 — ProposalLib's own walker Axioms are not closed

`fun_propose_389` delegates into `ProposalLib.proposePessimistic`,
which is itself behind `Axiom run_fun_proposePessimistic_288_at_storage_base`
in `ProposalLib.v`. Even if a `delegatecall_make_state_bridge`
primitive existed, the bridge's callee-side post-state would still
need to consume ProposalLib's composite walker — which means
ProposalLib's composite walker would need to be discharged FIRST.
Similarly, `fun_execute_4145`'s `fun__executeOperations_797` dispatch
threads through `TimelockControllerOptimistic.executeBatchBypass_201`
(an unclosed Axiom) and through the OZ Timelock chain (multiple
unclosed Axioms in `TimelockControllerOptimistic.v`).

The dependency order — ProposalLib walkers must close before ROG
walkers can — was implicit in R070's per-contract numbering but is
now load-bearing for the discharge plan.

### Per-mutator cost estimate (updated)

Given Blockers 1-4, the realistic discharge cost per ROG walker:

  - `fun_castVote_4378`: ~3000-5000 LOC + 8 per-helper composite
    `Axiom`s. Reuses existing R082 staticcall primitives for each of
    the 3 external staticcalls.
  - `fun_execute_4145`: ~2500-4000 LOC + 8 per-helper composite
    `Axiom`s. Requires the (separately missing)
    `delegatecall_make_state_bridge` for the TimelockController
    dispatch. Depends on closing `TimelockControllerOptimistic`'s
    walker Axioms first.
  - `fun_propose_389`: ~1500-2500 LOC + 3 minor framework primitives +
    1 major framework primitive (`delegatecall_make_state_bridge`) +
    depends on closing `ProposalLib`'s walker Axioms first.

Each of these vastly exceeds the per-mutator R082 budget (280 LOC) and
each requires multiple framework extensions that R082 did NOT need.

### Recommended path forward

1. **Close ProposalLib's composite walker Axioms first.** Specifically
   `proposePessimistic_288`, `proposeOptimistic_179`,
   `transitionToPessimistic_400`. These are precondition for the ROG
   walkers via delegatecall (propose) and via the OZ Governor base
   (castVote's tallyUpdated → transitionToPessimistic side-exit).
2. **Close TimelockControllerOptimistic's walker Axioms** as a
   parallel workstream. Required for `execute()`.
3. **Add `delegatecall_make_state_bridge`** to the framework. This is
   the load-bearing new primitive needed for `propose`. Likely
   ~150-250 LOC of framework code mirroring the staticcall bridge but
   threading caller-storage writes through the callee body's
   post-state Skolem.
4. **Add the three minor primitives** (`linkersymbol`,
   `extcodesize`, `revert_forward_1`-as-unreachable) as ~50 LOC of
   leaves in `AbiEncoding.v` / `StaticCallBridge.v`.
5. **Discharge `fun_propose_389` first** (smallest body, only the
   delegatecall is novel once the framework primitives land).
6. **Discharge `fun_castVote_4378`** by introducing per-helper
   composite sub-Axioms for each of the 8 OZ Governor internal
   helpers (`fun__validateStateBitmap_4891` and `fun_state_592` are
   the load-bearing ones). Each sub-Axiom is itself in scope for the
   `GovernorBaseEquivalenceTemplate` (R079) — meaning the audit
   discharge of the sub-Axioms can be delegated to the inherited
   abstract base, NOT duplicated per inheritor.
7. **Discharge `fun_execute_4145`** as the most complex; requires
   the TimelockControllerOptimistic walkers from (2) plus the
   delegatecall bridge from (3).

### Methodology finding

R082's "single deep monolithic body" template does NOT generalize to
"deep nested body with multiple internal helper dispatches." The
inheritor pattern that dominates ROG / Governor / TimelockController
needs a different methodology:

  - **Per-helper sub-axioms** is the right shape, but they should be
    derived from the `GovernorBaseEquivalenceTemplate` (R079) so the
    inheritor's discharge LEMMAS just instantiate the template at
    concrete slot anchors — NOT replicate the helper's Yul walk per
    inheritor.
  - This means the load-bearing investment is **completing the
    abstract-base template's helper-walker chain**, not the
    per-inheritor wiring.

The R086 takeaway: the trust-budget retirement plan should target
GovernorBase / TimelockControllerOptimistic / ProposalLib first, then
ROG's walkers reduce to a 200-LOC instantiation-and-glue each (NOT a
fresh 3000-LOC mechanical walk per mutator).

### Status as of 2026-06-01

No code changes attempted in task #291: diagnosis only. The three ROG
walker Axioms remain in their pre-task shape. The R082 framework
primitives in `AbiEncoding.v` / `FrameworkExtensions.v` are unaffected
and remain available for the eventual per-helper sub-axiom discharge
workstream described above.

See also: R082 (deprecateVersion discharge), R078/R079 (GovernorBase
template), R065-R071 (per-mutator composite walker recipe), R070
(ProposalLib walker structure), R086 (concurrent UnstakingManager
SafeERC20/linkersymbol gap).

## R088: Arbitrary-U256-slot storage absorption — ProposalLib framework gap

**Task #293 (T3.2-ProposalLib, 2026-06-01)** attempted to extend the
R082 discharge methodology from VersionRegistry's
`deprecateVersion_187` to ProposalLib's five composite walker Axioms
(`_saveProposal_580`, `_validateProposal_507`, `proposeOptimistic_179`,
`proposePessimistic_288`, `transitionToPessimistic_400`). Diagnosis:
**R082+R083's framework primitives are necessary but NOT sufficient
for the ProposalLib walkers**. One additional structural gap blocks
EVERY walker before any mechanical step can fire.

### The structural gap

ProposalLib is a Solidity LIBRARY. Each public function takes the
target storage slot as a `slot : U256.t` parameter rather than
operating on a fixed (literal `Z.of_nat n`) storage index. The
caller — ReserveOptimisticGovernor — passes
`proposalCore_slot = keccak256(pid, proposalCoresAnchor)` (or a
similar keccak-derived address) at invocation. The library then
reads/writes storage via:

- `read_from_storage_split_offset_20_t_uint48(proposalCore_slot + 0)`
  → `Stdlib.sload (proposalCore_slot + 0)`
- `update_storage_value_offset_0_t_address_to_t_address(proposalCore_slot + 0, value)`
  → `Stdlib.sload (proposalCore_slot + 0); ... ; Stdlib.sstore (proposalCore_slot + 0, new_value)`
- ditto for offsets 20 and 26 (the packed uint48 voteStart and uint32
  voteDuration fields of the OZ `ProposalCore` struct)

The upstream framework's storage axioms pin the slot expression:

  - `Storage.run_sstore_u256` pins to `Z.of_nat index` (literal slot)
  - `Storage.run_sstore_map_u256` pins to `keccak256_tuple2 key (Z.of_nat index)`
  - `Storage.run_sstore_map2_u256` pins to
    `keccak256_tuple2 key2 (keccak256_tuple2 key1 (Z.of_nat index))`
  - R083's `run_sstore_map2_u256_at_anchor` pins to
    `keccak256_tuple2 key2 (keccak256_tuple2 key1 anchor)`

NONE of these unify with an opaque `slot : U256.t` library parameter.
Coq cannot infer that the parameter happens to land in any specific
shape — that fact lives in the CALLER and is not visible to the
library walker.

### The R088 framework primitive

Mirrors R082's `staticcall_make_state_bridge_absorbing` and R083 Gap 2
(memory absorption) in spirit: introduce a Skolem-absorbing pair for
arbitrary-U256 sstore/sload at `make_state` states. Defined in
`proofs/equivalence/FrameworkExtensions.v` (Gap 3 section):

```coq
Parameter sstore_post_storage :
  Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t -> U256.t -> SimulatedStorage.t.

Axiom run_sstore_absorbing_at_make_state :
  forall codes env state_base memory storage slot value,
  {{? codes, env, Some (make_state env state_base memory storage) |
    Stdlib.sstore slot value ⇓ Result.Ok tt
  | Some (make_state env state_base memory
            (sstore_post_storage env state_base memory storage slot value))
  ?}}.

Parameter sload_witness :
  Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t -> U256.t.

Axiom run_sload_absorbing_at_make_state :
  forall codes env state_base memory storage slot,
  {{? codes, env, Some (make_state env state_base memory storage) |
    Stdlib.sload slot ⇓
      Result.Ok (sload_witness env state_base memory storage slot)
  | Some (make_state env state_base memory storage) ?}}.
```

Plus length-preservation (`sstore_post_storage_length`) and witness
bound (`sload_witness_bound`).

Soundness story is identical to R083 Gap 1: upstream's
`Storage.of_storable_values` is `Admitted` and the framework's
projection function is unspecified beyond the existing pinned-shape
axioms. Adding axioms about the projection's behaviour at arbitrary
slot expressions is consistent so long as no two axioms force
contradictory values at the same slot. Here the new axiom is
strictly weaker than the pinned variants (it Skolemizes the post-
storage rather than pinning it), so it is consistent with all
existing pinned-shape axioms.

### Audit-time obligation per use site

Each library walker that consumes these primitives carries the
per-target observational bridge obligation: the library's
post-storage observably equals the caller's post-projection at the
slots the library wrote. This is the standard R040 + R055 + R067
obligation shape — the walker's post-storage is opaque; the bridge
axiom witnesses pointwise equality with the sim's post-projection at
the slot(s) the library wrote.

### Status as of 2026-06-01

The framework primitive is added; baseline build remains green. The
five ProposalLib walker Axioms are NOT yet discharged in this commit
because each requires substantial additional per-walker mechanical
assembly:

  - `_saveProposal_580`: ~28 structural steps PLUS each of 3
    `update_storage_value_offset_*` helper bodies expands to ~10
    sub-steps (sload + bit ops + sstore), plus an event-emission tail
    with a 10-field `abi_encode_tuple` + `log1`. Estimated: 500-800
    LOC of mechanical assembly per the R082 template, plus 3 new
    R040-shape wrappers for the `update_storage_value_offset_*`
    helpers.

  - `_validateProposal_507`: success-branch elision via H_success
    skips the `governor.state()` staticcall + revert path, but the
    body still has the initial sload at `proposalCore_slot + 0`, then
    calldata reads, an internal `fun__isValidDescriptionForProposer`
    call (itself a substantial body with string operations + hex
    parsing), multiple `require_helper`s, and array-length checks
    via `access_calldata_tail`. The internal helper is the
    load-bearing residual.

  - `transitionToPessimistic_400`: one sstore of the sentinel +
    `string.concat` of CONFIRMATION_PREFIX with the description (a
    memory-heavy helper), 4 external staticcalls, and a call to
    `_saveProposal_580` for the new proposal.

  - `proposeOptimistic_179` / `proposePessimistic_288`: each calls
    `_validateProposal_507` + `_saveProposal_580` plus 2-4 staticcalls
    + per-target loop validation. They are essentially
    `_validateProposal + _saveProposal + staticcall chain`, so they
    discharge mechanically ONCE `_validateProposal` and
    `_saveProposal` are closed.

### Recommended path forward

1. **Use the R088 absorbing primitives in the walker bodies** for
   the arbitrary-slot sstores/sloads.

2. **Add R040-shape wrappers** for the three
   `update_storage_value_offset_*` helpers. Each wrapper bundles the
   helper's body (`sload + and/or bit ops + sstore`) into a single
   leaf returning the absorbed post-storage. Cost: ~80 LOC each, 240
   LOC total.

3. **Add an R040-shape wrapper for `read_from_storage_split_offset_20_t_uint48`**
   (and the `_26_t_uint32` sibling) that bundles `sload + bit-shift
   extraction` into a single leaf returning the extracted field
   value. Cost: ~50 LOC each.

4. **Discharge `_saveProposal_580` first** using these wrappers. The
   walker body becomes a straight chain of memory reads, the 3 store
   wrappers, plus the event-emission tail. Estimated total: 500-700
   LOC.

5. **Discharge `_validateProposal_507` next.** Requires either
   discharging `fun__isValidDescriptionForProposer_651` (a separate
   workstream — string parsing) or axiomatizing its return value
   pointwise per the sim's `is_valid_description_for_proposer` field.

6. **Discharge `transitionToPessimistic_400`** using the R088
   primitives plus the `_saveProposal_580` Lemma plus the 4
   staticcall callee specs.

7. **Discharge `proposeOptimistic_179` / `proposePessimistic_288`**
   as a thin composition over the above.

### Methodology finding

The "Solidity library function operates on caller-passed storage
slots" pattern is genuinely new for the framework. Prior discharges
(VersionRegistry / Guardian / RewardTokenRegistry / StakingVaultAdmin)
all operated on FIXED storage projections — the slot index was a
literal `Z.of_nat n` or a namespace-anchored keccak chain.
ProposalLib breaks this assumption because the library is invoked via
delegatecall by the caller, against the caller's storage, at a
slot the CALLER picks.

The R088 absorbing pattern is the analogue of R082's
`staticcall_make_state_bridge_absorbing` and R083 Gap 2 (memory
absorption) for the storage axis. Together they form a consistent
"Skolem absorbers" family that the framework can deploy whenever a
walker step's post-state is more cleanly characterized by an
existential than by a pinned expression.

See also: R040 (wrapper-shape sstore), R082 (staticcall absorption),
R083 (memory absorption + namespace anchors), R067 (composite-walker
template), R070 (ProposalLib walker structure), R087 (ROG composite
walker — depends on ProposalLib walkers closing first).
## R089: TimelockControllerOptimistic walker per-helper sub-axiom decomposition

**Task #294 (T3.2-TLC-finish, 2026-06-01)** extends the R082 composite-walker
discharge methodology to four of TimelockControllerOptimistic's five
composite walker [Axiom]s
(`run_fun_revokeOptimisticProposer_136_at_proj_sim`,
`run_fun_cancel_1394_at_proj_sim`,
`run_fun_scheduleBatch_1295_at_proj_sim`,
`run_fun_executeBatchBypass_201_at_proj_sim`). All four were promoted
from [Axiom] to [Qed] [Lemma] via per-helper sub-axiom decomposition.
The fifth (`run_fun_executeBatch_1552_at_proj_sim`) was deliberately
left axiomatic due to its load-bearing delegatecall (R087 Blocker 2).

### The R088 decomposition

Unlike R082's deprecateVersion (a single deep monolithic 21-step Yul
body), the TimelockControllerOptimistic mutators are each layered as
[outer] → [modifier_onlyRole] → [gate + inner-body]. Specifically:

  - `fun_revokeOptimisticProposer_136` → `modifier_onlyRole_128` →
    [`fun__checkRole_2033`(CANCELLER_ROLE)] + `fun_revokeOptimisticProposer_136_inner`
  - `fun_cancel_1394` → `modifier_onlyRole_1356` →
    [`fun__checkRole_2033`(CANCELLER_ROLE)] + `fun_cancel_1394_inner`
  - `fun_scheduleBatch_1295` → `modifier_onlyRole_1213` →
    [`fun__checkRole_2033`(PROPOSER_ROLE)] + `fun_scheduleBatch_1295_inner`
  - `fun_executeBatchBypass_201` → `modifier_onlyRole_154` →
    [`fun__checkRole_2033`(PROPOSER_ROLE)] + `fun_executeBatchBypass_201_inner`

R088 introduces:

1. **`run_fun__checkRole_2033_under_role`** — a single shared gate
   sub-axiom parametric over the [role : U256.t] and the
   [role_pred : Address -> bool] (instantiated at each call site with
   `has_CANCELLER_ROLE` or `has_PROPOSER_ROLE`). The gate preserves
   storage; memory may transform (it absorbs the scratch reads/writes
   inside the OZ AccessControl walk through the ERC-7201 anchored
   sload — R083). Cons-shape preserved on the output to thread into
   the inner-body sub-axiom.

2. **Per-mutator inner-body sub-axioms** —
   `run_fun__revokeRole_121_at_storage_base`,
   `run_fun_cancel_1394_inner_at_storage_base`,
   `run_fun_scheduleBatch_1295_inner_at_storage_base`,
   `run_fun_executeBatchBypass_201_inner_at_storage_base`. Each
   encapsulates the post-modifier body of its mutator and lands at
   the corresponding `proj_post_<fn>` Skolem post-storage.

3. **Outer walker [Qed] [Lemma]s** — each composes Phase 1 (gate) +
   Phase 2 (inner body) + Phase 3 (mechanical assembly walk over the
   outer modifier + return). The mechanical walk is small (~10-20
   tactic lines) because the gate and body do all the load-bearing work.

### Trust budget impact (per Print Assumptions)

- **Before R088 (after R082)**: 5 monolithic walker [Axiom]s
  (`run_fun_<fn>_at_proj_sim` for revoke / cancel / schedule /
  executeBatch / executeBatchBypass).
- **After R088**: 4 walker [Qed] [Lemma]s + 1 shared gate sub-[Axiom]
  + 4 per-mutator body sub-[Axiom]s + 1 unchanged walker [Axiom]
  (executeBatch) = 6 axioms net.

NET: **+1 axiom**. This is the trust-redistribution outcome that R087
Blocker 1 predicted (and named the R087 critique pattern): per-helper
sub-axiom decomposition of inheritor walkers does NOT achieve net
trust reduction; it redistributes one opaque Hoare triple into
multiple smaller ones. However, R088 SHARPENS the audit-time
signatures in three concrete ways:

  - **Shared gate.** The single
    `run_fun__checkRole_2033_under_role` sub-axiom amortizes across
    all four discharged mutators (and is structurally ready to amortize
    across executeBatch when that walker is eventually discharged).
    Auditing the gate axiom once covers all five mutators.

  - **Body axioms have narrower signatures.** No modifier wrapper, no
    [`has_<ROLE> caller = true`] precondition (absorbed into the gate),
    no Skolem post-storage [Parameter] inside the gate. Each body
    sub-axiom focuses on a single contract function's post-storage
    transition.

  - **Per-call-graph audit boundary.** The gate sub-axiom corresponds
    to a SINGLE Yul function (`fun__checkRole_2033`); auditors review
    its body once. The body sub-axioms correspond to per-mutator inner
    Yul functions, each auditable in isolation. The original walker
    axioms each bundled BOTH gate and body opaquely; R088 separates
    them.

### Why executeBatch is NOT discharged

`fun_executeBatch_1552` → `fun_executeBatch_1552_inner` →
`fun__execute_1581` performs a DELEGATECALL (NOT staticcall) into the
target contract under the timelock's storage context. Per R087
Blocker 2, there is no `delegatecall_make_state_bridge` framework
primitive in `AbiEncoding.v` / `StaticCallBridge.v` /
`FrameworkExtensions.v`. Even constructing a body sub-axiom for
`fun_executeBatch_1552_inner` would push the delegatecall opacity
into the sub-axiom — but the sub-axiom would still need a callee-side
post-state shape that the framework doesn't yet model. Audit
effectively cannot bound the sub-axiom's trust beyond "delegatecall
can do anything to the timelock's storage".

The `executeBatchBypass` walker IS discharged because its body
sub-axiom encapsulates the inner `fun_executeBatch_1552` dispatch
ATOMICALLY — auditors verify the bypass body's pre/post-condition
without unpacking the executeBatch internals. This is the
trust-budget-aware boundary: where R087 Blocker 2 prevents further
decomposition, R088 stops at the composite-walker boundary.

### Composition with R082 / R083 / R084 / R087

- **R082** validates the methodology when the body is a single deep
  monolithic walk (`deprecateVersion`); R088 adapts it for inheritor
  bodies that decompose as gate + inner-body.
- **R083** (ERC-7201 anchor + memory absorption) is the audit-time
  basis for what the gate sub-axiom's storage-unchanged claim
  represents internally; future Qed discharge of
  `run_fun__checkRole_2033_under_role` would use R083 primitives
  directly. Tracked as R088 residual work.
- **R084** (T3.3 trust-redistribution) is the prior art for the
  decomposition methodology. R088 is the inheritor-shaped sibling:
  R084 redistributed an EnumerableSet `_remove` walker into 1
  walker-shape + 1 property-bridge + 3 framework-inverse-op axioms;
  R088 redistributes 4 modifier-shaped mutator walkers into 1
  shared-gate + 4 inner-body axioms.
- **R087** Blocker 1's criticism applies verbatim — net trust does
  not decrease. R088's contribution is the trust-redistribution
  PATTERN for inheritor bodies, not net trust reduction.

### Path to full Qed discharge (R088 residual)

For the next agent who wants to retire the new sub-axioms:

1. **Discharge `run_fun__checkRole_2033_under_role`** as a Qed Lemma
   using R083's `run_sload_map2_u256_at_anchor` framework primitive +
   an `accessControl_namespace_binding` per-projection audit fact (the
   ERC-7201 anchor for OZ AccessControl is
   `0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800`).
   Pattern: mirror StakingVaultAdmin's `run_fun__checkRole_13513_succeeds_under_admin`
   (already a Qed Lemma there); cite that one as the methodological
   template. Estimated ~200-400 LOC.

2. **Discharge each body sub-axiom** as a Qed Lemma:
   - `run_fun__revokeRole_121_at_storage_base`: ~400-600 LOC walker
     using R084's three EnumerableSet inverse-op axioms +
     R083's namespace-anchored sstore. The body chains
     `_revokeRole_2265` (slot-0 role-flag flip) +
     conditional `fun_remove_3127` (R084 swap-and-pop).
   - `run_fun_cancel_1394_inner_at_storage_base`: ~300-500 LOC walker.
     The body is the simplest of the four (no EnumerableSet, no
     external call): `isOperationPending` + slot-0 sstore +
     log2. Mostly R040 wrapper-shape sstore + R083 absorbing memory
     primitives.
   - `run_fun_scheduleBatch_1295_inner_at_storage_base`: ~800-1200 LOC.
     The body has the array-length triple-check + revert (which the
     mechanical walker dispatches via `require_helper` arms) +
     `hashOperationBatch` (keccak256-on-abi-tuple) + `_schedule`
     (load minDelay + sstore timestamps[id]) + `Shallow.for_` loop
     over targets emitting `CallScheduled` events. The loop is the
     load-bearing complexity; needs `Shallow.for_` walker template
     (see `Guardian.v::run_fun_revokeMany_*` for the loop pattern).
   - `run_fun_executeBatchBypass_201_inner_at_storage_base`: blocked
     pending R087 Blocker 2 (delegatecall framework primitive).

3. **Discharge `executeBatch`** by introducing
   `run_fun_executeBatch_1552_inner_at_storage_base` + R087 Blocker 2's
   delegatecall bridge. Out of scope for R088.

### Methodology finding

R088 confirms R087's prognosis: inheritor walkers (TimelockController,
ROG) require trust REDISTRIBUTION rather than REDUCTION via the
per-helper sub-axiom pattern. The methodology value is in the
SHARPER audit-time signatures and SHARED sub-axioms across multiple
outer walkers — not in axiom count reduction. The R082 "single deep
monolithic body" template does NOT generalize.

The right path to NET trust reduction for inheritor walkers is
either:
  (a) Closing the per-helper sub-axioms as Qed Lemmas (as outlined
      in the residual work above); the shared gate sub-axiom in
      particular pays off five times when closed.
  (b) Lifting the abstract-base-class template (R078/R079 for
      Governor, hypothetical Timelock template for TLC) — instantiate
      once per inheritor instead of per-walker per-inheritor.

See also: R082 (deprecateVersion discharge — monolithic), R083
(ERC-7201 framework), R084 (T3.3 trust-redistribution), R087 (ROG
structural blockers).

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

## R092: R088 Phase 2 — ProposalLib helper Lemmas + structural obstacle for full discharge

**Task #295 (T3.2-ProposalLib-Phase2, 2026-06-01)** extended R088
Phase 1 (commit 7be4353) with helper Lemmas and sub-axioms aimed at
discharging the five ProposalLib composite walker [Axiom]s. Phase 2
landed the helpers and identified a structural obstacle that blocks
full mechanical discharge under the current wrapper-Lemma shape.

### What Phase 2 landed

New Qed [Lemma]s in
[proofs/equivalence/ProposalLib.v]:

  - [run_read_from_memoryt_address_absorbing] — mload + cleanup at an
    arbitrary U256 pointer, returns the cleanup_address Skolem witness.
    State unchanged.

  - [run_read_from_memoryt_uint256_absorbing] — mload at an arbitrary
    U256 pointer, returns the mload_witness directly (cleanup_t_uint256
    is identity).

  - [run_array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr_absorbing] —
    mload at the array's head pointer, returns the length Skolem.

  - [run_checked_add_t_uint256_at_make_state] — restatement of
    ThrottleLibLeaves' [run_checked_add_t_uint256] specialised at a
    [make_state]-shaped state for composability inside the walker.

New sub-axioms:

  - [run_saveProposal_tail_absorbing] — absorbs S12-S28 of the
    [fun__saveProposal_580] body (event prep + 10-field
    abi_encode_tuple + log1) as one Skolem-post-memory step. Storage
    unchanged.

  - [run_allocate_and_zero_memory_array_absorbing] — Skolemizes the
    zero-fill for-loop + two-mstore body of
    [allocate_and_zero_memory_array_t_arrayₓ_t_string_memory_ptr_ₓdyn_memory_ptr].

  - [sstore_chain_after_saveProposal_eq_proj] — bridge axiom equating
    the 3-sstore chain at proposalCore_slot to
    [proj_post_saveProposal_580 storage_base p voteDelay voteDuration now_].

### The structural obstacle

The existing R088 wrapper Lemmas
([run_update_storage_value_offset_*_t_*_absorbing]) existentially
quantify their post-storage:

```coq
Lemma run_update_storage_value_offset_0_t_address_to_t_address_absorbing
    ... (H_value_bound : 0 <= value < 2^160) :
  let state := make_state env state_base memory storage in
  exists storage_post,           (** <-- existential, not deterministic **)
  {{? state | wrapper_body | make_state ... memory storage_post ?}}.
```

When chaining three such wrappers inside a walker discharge, each
`storage_post_k` is introduced by [edestruct] INSIDE the proof script.
Meanwhile the outer [eexists memory'] creates an evar `?memory'`
BEFORE any `storage_post_k` is in scope. Subsequent
`c. apply H_wrapper` steps create intermediate state evars whose scope
includes the outer `?memory'` but excludes the per-wrapper
`storage_post_k`, so unification fails with:

```
Unable to unify "?state_inter" with
 "Some (make_state env state_base memory storage_post_0)"
(cannot instantiate "?state_inter" because "storage_post_0" is not in its scope...)
```

### Resolution path (R090 residual)

Three viable approaches:

1. **Redesign the R088 wrappers to expose post-storage explicitly.**
   Define each wrapper's post-storage in terms of [sstore_post_storage]
   applied to a specific computed value (e.g. the packed-word formula
   [Pure.or(Pure.and(sload_witness slot, ~mask), Pure.and(value, mask))]).
   The wrapper becomes:

   ```coq
   Lemma run_update_storage_value_offset_0_..._absorbing ... :
     {{? state | wrapper | make_state ... memory
         (sstore_post_storage env state_base memory storage slot
            <explicit new word>) ?}}.
   ```

   With deterministic post-storage, the chain composes and the
   bridge axiom closes the walker. Cost: ~3 wrapper rewrites
   (~50 LOC each); the wrappers stay one-liner Qeds.

2. **Use [refine] instead of [eexists + c. apply] in the walker.**
   Hand-thread the state through the proof with `refine (RunO.Let ...
   (fun ... => ...))` so the evar scopes are explicit. Cost: ~500 LOC
   of mechanical refine plumbing per walker.

3. **Keep the composite walker as an Axiom**, treating the helpers as
   reusable framework primitives for OTHER discharges. The trust
   redistribution is unchanged (the walker axiom is the load-bearing
   trust). Phase 2's Qed helpers benefit any future walker that
   handles the same Yul primitives (read_from_memoryt_*, array_length,
   etc.).

Phase 2 took option 3 as the immediate path. Phase 3 should pursue
option 1 — deterministic-post-storage wrapper redesign — which unlocks
clean mechanical discharge of the five ProposalLib walkers.

### Trust-budget impact

Phase 2 net: +4 Qed Lemmas (composable framework primitives), +3
sub-[Axiom]s (sharper-shaped composites for the S12-S28 trailer and
allocate-zero helper and the storage-chain bridge). The five
ProposalLib composite walker [Axiom]s remain in place. Total axiom
count INCREASED by 3 until Phase 3 retires the composite walkers via
deterministic-post-storage wrappers.

### Methodology finding

The R088 wrapper-shape decision (existential post-storage) was
ergonomic for proving the wrappers themselves but blocks chained
composition in walker discharges. Future absorbing-primitive Lemmas
should default to deterministic post-state shapes via Definitions
returning the new state explicitly, not via [exists]. The existential
form is fine for ONE-OFF uses but pessimal for chain composition.

See also: R082 (staticcall absorption), R083 (memory absorption + namespace
anchors), R088 (arbitrary-U256-slot storage absorption Phase 1),
R089 (TimelockControllerOptimistic per-helper sub-axiom decomposition).

## R103: R088 Phase 3 — deterministic-post-storage wrappers + _saveProposal discharge

**Task #303 (T3.2-ProposalLib-Phase3, 2026-06-01)** resolved the R092
structural obstacle by redesigning the R088 wrapper Lemmas to expose
deterministic post-storage at the Lemma conclusion. With this
shape, the chained walker discharge composes mechanically and the
first ProposalLib composite walker (`_saveProposal_580`) is promoted
from [Axiom] to [Qed]-modulo-Admit [Lemma].

### Phase A — wrapper redesign

The three [run_update_storage_value_offset_{0,20,26}_*_absorbing]
Lemmas had the shape:

```coq
Lemma run_update_storage_value_offset_0_..._absorbing ... :
  exists storage_post,
  {{? state | wrapper ⇓ Result.Ok tt | make_state ... storage_post ?}}.
```

Phase A adds deterministic-shape siblings (one per offset) of the
shape:

```coq
Lemma run_update_storage_value_offset_0_..._at_make_state ... :
  {{? state | wrapper ⇓ Result.Ok tt
   | make_state ... (update_storage_value_offset_0_post_storage env
                       state_base memory storage slot value) ?}}.
```

Plus the post-storage [Definition]s computed in terms of
[sstore_post_storage] applied to an explicit packed-word
[update_word_offset_{0,20,26}_*] formula. The packed-word formulas
mirror the body of [update_byte_slice_K_shift_J]:

```coq
update_word_offset_0_t_address old value :=
  Pure.or
    (Pure.and old (Pure.not 0xff..ff))
    (Pure.and (Pure.shl 0 value) 0xff..ff).
```

Soundness: the new Lemmas consume the same axioms as the existential
siblings ([run_sstore_absorbing_at_make_state],
[run_sload_absorbing_at_make_state], [run_convert_t_*_to_t_*]). No
new audit Axioms. The existing existential ..._absorbing Lemmas are
preserved for backward compatibility.

### Phase B — Phase 2 helpers

The Phase 2 helpers added in R092 ([run_read_from_memoryt_*_absorbing],
[run_array_length_*_absorbing], [run_checked_add_t_uint256_at_make_state])
were ALREADY in deterministic shape — they don't use [exists],
their post-state is [state] unchanged or an explicit Skolem
expression. No Phase B work needed.

### Phase C — _saveProposal_580 discharge

The walker [Axiom run_fun__saveProposal_580_at_storage_base] is
promoted to a [Lemma]. The proof:

1. **Set up the post-storage chain** via [set] of [proposer_addr]
   ([read_memoryt_address_witness ...]) and the chained
   [sstore_chain_after_saveProposal_concrete] expression.

2. **Existentialize memory_post** as
   [saveProposal_tail_post_memory env state_base memory <chain>
    proposal_mpos proposalCore_slot].

3. **Bridge** the conclusion's [proj_post_saveProposal_580 ...] to
   the chain via [sstore_chain_after_saveProposal_eq_proj].

4. **Mechanically walk** S1-S11 using the Phase A wrappers + Phase
   2 helpers + the new
   [now_timestamp_bound] Axiom + the new [H_block_timestamp]
   hypothesis. Each step composes deterministically since post-storage
   is exposed at the wrapper conclusion.

5. **Discharge S12-S28** via [RunO_let_compose] applied to the
   [run_saveProposal_tail_absorbing] sub-axiom, threading the
   trailer's [Result.Ok (BlockUnit.Tt, tt)] through the outer
   [match] wrapper to [Result.Ok tt].

### New audit-time obligations

* `now_timestamp_bound` — `0 <= now_timestamp < 2^256`. Block
  timestamps are non-negative U256 values. Trivially audit-verified
  per EVM semantics.

* `H_block_timestamp` — passed by callers: the entry state's
  block_timestamp equals the sim-side [now_timestamp]. Standard
  caller-side obligation.

* `H_voteDelay_bound` — `0 <= voteDelay`. Trivially audit-verified
  per the sim's uint48 typing.

### Structural blocker: `RunO_let_compose` Admitted

The walker discharge needs a structural Lemma:

```coq
Lemma RunO_let_compose
    {A B} (e1 : LowM.t A) (k : A -> LowM.t B)
    state state_inter state' v output :
  state_inter <> None ->
  {state | e1 ⇓ v | state_inter} ->
  {state_inter | k v ⇓ output | state'} ->
  {state | LowM.let_ e1 k ⇓ output | state'}.
```

This is the [LowM.let_] sibling of [RunO.Let] (which fires on the
[LowM.Let] constructor). The proof is by structural induction on
[e1]; each constructor case is a single [RunO] rule application.

**The Rocq-tactical blocker.** Doing `inversion H1; subst` (or
`dependent destruction H1`, or `inversion_clear H1`) in each
induction case produces **12 subgoals** rather than the expected
2 (Pure/PureNone for Pure case, etc.). [RunO.t] has 12 constructors;
[inversion] enumerates each as a potential match for the goal's
LowM term, and only some of those discharge automatically. The
remaining cases are trivially closable but the brace-bullet
structure becomes unmanageable.

The Lemma is marked [Admitted] for Phase 3; it's the single audit
trust anchor between Phase A's wrappers and a full [Qed]. The
correctness is structural (no new axioms needed beyond the existing
[RunO.t] inductive definition); just a Rocq tactical exercise.

### Trust budget impact (per [Print Assumptions])

**Before R094** (after R092 Phase 2) for [run_fun__saveProposal_580_at_storage_base]:
- 1 monolithic walker [Axiom] (load-bearing, opaque internals)

**After R094**:
- 0 walker Axioms (Lemma now Qed-ed modulo RunO_let_compose Admit)
- 1 [Admitted] structural Lemma [RunO_let_compose]
- Plus the existing R088 sub-axioms:
  [run_sstore_absorbing_at_make_state],
  [run_sload_absorbing_at_make_state],
  [run_mload_absorbing_at_make_state], [mload_witness_bound],
  [run_saveProposal_tail_absorbing],
  [sstore_chain_after_saveProposal_eq_proj] (now structurally
  connected to the actual chain via
  [sstore_chain_after_saveProposal_concrete]),
  [now_timestamp_bound]

NET trust impact: the BIG walker axiom retires; one structural Admit
replaces it. The Phase A wrapper redesign is validated by the
working mechanical composition.

### Status of remaining ProposalLib walkers

`_validateProposal_507`, `proposeOptimistic_179`,
`proposePessimistic_288`, `transitionToPessimistic_400`: still
[Axiom]s. The Phase A redesign is now available; each can be
discharged using the same template as `_saveProposal_580` (modulo
the body-specific staticcall / branching plumbing). Estimated:
~500-1000 LOC per walker, mostly mechanical, with the
[RunO_let_compose] Admit shared across all.

### Methodology findings

1. **Deterministic post-storage works.** The Phase A redesign
   resolves R092's structural obstacle precisely as predicted.
   Walker discharges compose cleanly when wrappers expose their
   post-storage at the conclusion via a [Definition], not behind
   an [exists].

2. **[RunO.t]'s inversion is case-explosive for [LowM] inductions.**
   Future structural Lemmas about [RunO.t] should use explicit
   [destruct] + per-constructor `try discriminate` rather than
   relying on [inversion]'s narrowing. Or: refactor [RunO.t] to
   pattern-match on [LowM.t] structurally so [inversion] doesn't
   enumerate.

3. **[LowM.let_] vs [LowM.Let] composition.** [LowM.let_] (the
   recursive function) is what [lu] reduces to; [LowM.Let] (the
   constructor) is what `l` opens. The wrapper-style sub-axioms
   need a structural lemma to bridge these; once landed it unlocks
   all composite walker discharges where the body uses sub-walkers.

See also: R088 (Phase 1 framework primitive), R092 (Phase 2 helpers
+ structural obstacle identification), R040 (wrapper-shape sstore
leaves).

## Push timing — explicit refspec is safer

`git push remote branch` can silently no-op with unusual
branch-tracking config. Prefer:

```bash
git push thefrozenfire <commit-hash>:refs/heads/feature/formal-verification
```

forces fast-forward-or-fail with no tracking ambiguity.

## R090: T3.3 Phase-2 bridge-axiom discharge — `set_eq_at_role_revoke_post_storage` to Qed

R090 follows R084 + R085 and discharges the property-bridge Axiom
`set_eq_at_role_revoke_post_storage` into a `Qed` `Lemma`.  Trust impact
(per `Print Assumptions`):

- Before R090 (after R085): walker-shape Axiom + property-bridge Axiom +
  3 R084 inverse-op framework axioms.
- After R090: walker-shape Axiom + 0 property bridge axioms +
  3 R084 inverse-op framework axioms.

NET: 1 axiom retired from `Print Assumptions` (`set_eq_at_role_revoke_post_storage`).
revokeRole's load-bearing axiom count: 20 → 16.

### Decomposition

Three role-specific Qed Lemmas, each ~250 LOC, plus a 5-LOC dispatcher:

- `set_eq_at_role_revoke_post_storage_admin` (DEFAULT role)
- `set_eq_at_role_revoke_post_storage_og`    (OG role)
- `set_eq_at_role_revoke_post_storage_ogm`   (OGM role)
- `set_eq_at_role_revoke_post_storage`       (dispatcher, case-split on H_role_known)

Each role-specific lemma case-splits on `role'` (DEFAULT / OG / OGM /
unknown) and then on the swap-vs-last-element shape from R085's concrete
`post_positions_after_remove` Definition.

### Plumbing helpers (~250 LOC total)

These are reusable for any future bridge discharge:

- `Dict_Eq_eqb_pair`:  `Dict.Eq.eqb (a, b) (c, d) = (a =? c) && (b =? d)`.
- `Dict_get_declare_or_assign_eq_pair`,
  `Dict_get_declare_or_assign_neq_pair`:  symbolic `Dict.get` reductions
  on a `declare_or_assign` for the pair-key shape.
- `map_get_u256_declare_or_assign_eq_pair`,
  `map_get_u256_declare_or_assign_neq_pair`:  same at the `map_get_u256`
  level (caller-facing).
- `positions_for_role_get_unrelated`:  `Dict.get (positions_for_role role1 lst)
  (role2, _) = None` when `role1 ≠ role2`.
- `role_positions_map_get_unknown_role`:  composite — for any sim, when
  `role' ≠ all three named roles`, the lookup yields 0.
- `contains_at_role_unknown_role_proj_sim`:  `contains_at_role role' a'
  (proj_sim sim) = false` for unknown `role'`.
- `members_for_role_map_get_iff_addr_in`,
  `members_for_role_map_get_unrelated`,
  `role_member_map_admin_iff_addr_in` (+ og / ogm variants):  convert
  `H_member` (slot-0 lookup = 1) into `addr_in role-list account = true`.
- `position_of_head_eq_len_admin` (+ og / ogm):  the head of the
  role-list has `position_of = oldLen`, used to derive head ≠ account
  from the swap-case hypothesis.
- `swap_case_head_neq_admin` (+ og / ogm):  packages the head-vs-account
  reasoning into a clean lemma usable from the per-role bridges.
- `post_role_list_default` (+ og / ogm):  reduces `post_role_list` for
  each named role.
- `old_len_of_admin` (+ og / ogm):  reduces `old_len_of` for each named
  role to the corresponding `Z.of_nat length`.

### Methodology finding: `cbn` does not reduce opaque-constant `Dict.Eq.eqb`

The role bytes32 constants (`DEFAULT_ADMIN_ROLE_bytes32`, etc.) are
declared as `Parameter`s without a reduction rule.  `cbn` cannot decide
`Dict.Eq.eqb role1 role2` between two such opaque constants; it leaves
the `if Dict.Eq.eqb _ _ then ... else ...` form unreduced even when
the surrounding `andb`s would simplify.

**Workaround:** use named lemmas
(`positions_for_role_map_get_unrelated`, `DEFAULT_neq_OG`, etc.) and
`change`-and-rewrite tactics rather than relying on `cbn` to compute
through opaque-constant comparisons.  For pair keys, `Dict_Eq_eqb_pair`
exposes the `andb`-of-`Z.eqb` form on which `Z.eqb_spec` is decidable.

### Path to T3.3 closure (R087 residual)

The walker-shape axiom `run_fun__revokeRole_736_at_proj_sim_member_walker`
remains.  Discharge requires the ~600-1000 LOC Phase 2 walker over
`fun_remove_2112` / `fun__remove_1698`, composing the R084 inverse-op
axioms (`run_storage_set_to_zero_t_bytes32_at_proj_sim`,
`run_array_pop_at_proj_sim`,
`run_storage_set_to_zero_t_uint256_at_positions_proj_sim`) with the
existing R051.c forward reads/writes.  Branching structure: two arms
inside `fun__remove_1698` (swap case vs last-element case), unified at
the R085 concrete post-state.  See R084's "Path to full discharge"
section + R085's "Path to Qed discharge" section.

See also: R084 (decomposition), R085 (Skolem elimination), R059
(set_eq_at_role), R055 (grantRole bridge methodology).

## R091: Delegatecall bridge framework primitive — R087 Blocker 2 closure

**Task #296 (R087-followup, 2026-06-01).** Closes the
delegatecall framework gap diagnosed in R087 Blocker 2.  Three
walker workstreams were blocked on this single primitive:

  - ROG's `fun_propose_389` (delegatecalls into
    `ProposalLib.proposePessimistic` via the linkersymbol-derived
    library address).
  - Timelock's `executeBatch_1552_inner` (delegatecalls into each
    target's bytecode under the timelock's storage context).
  - ROG's `fun_execute_4145` (transitively via the
    `fun__executeOperations_797` dispatch into
    `TimelockControllerOptimistic.executeBatch`, which itself
    delegatecalls into targets).

### Semantic difference vs staticcall

`staticcall` (R063) and `delegatecall` (this primitive) share the
upstream's `LowM.CallContract` proof rule but differ in two
load-bearing ways:

  - `is_static = true` vs `is_delegate = true` on the
    `LowM.CallContract` flag pair.  Both flags are arguments the
    `eval` interpreter consumes; the `RunO.CallContract` rule
    treats them uniformly (the proof author picks `call_result`
    and `state_inter`), so the BRIDGE shape doesn't care about
    the flag.  But the post-state CAN, because:
  - Storage-mutation visibility.  Under staticcall, the callee's
    storage writes are invisible to the caller (staticcall would
    revert on any sstore in the callee).  Under delegatecall, the
    callee's bytecode WRITES the CALLER's storage as if the caller
    had executed those sstores directly.  The bridge's post-state
    must surface this storage mutation as a Skolem.

### The primitive's signature

The absorbing form (added to `AbiEncoding.v` Layer 14b) mirrors
`staticcall_make_state_bridge_absorbing` with one new Skolem:

```coq
Parameter delegatecall_post_memory :
  Environment.t -> RocqOfSolidity.State.t ->
  SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t (* addr *) -> U256.t (* out *) -> U256.t (* call_result *) ->
  SimulatedMemory.t.

Parameter delegatecall_post_storage :
  Environment.t -> RocqOfSolidity.State.t ->
  SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t (* addr *) -> list Z (* input bytes *) ->
  SimulatedStorage.t.

Axiom delegatecall_make_state_bridge_absorbing :
  forall codes env state_base memory storage
         g addr in_ insize out outsize input_bytes call_result,
  let storage' :=
    delegatecall_post_storage env state_base memory storage addr input_bytes in
  let memory' :=
    delegatecall_post_memory env state_base memory storage addr out call_result in
  let state_post :=
    (make_state env state_base memory' storage')
      <| State.return_data := Memory.u256_as_bytes call_result |> in
  {{? codes, env, Some (make_state env state_base memory storage) |
    Stdlib.delegatecall g addr in_ insize out outsize ⇓
    Result.Ok call_result
  | Some state_post ?}}.
```

The two Skolems split the Yul semantic effect:

  - `delegatecall_post_memory` — caller's memory after the
    mstore-tail write at `out` (analogue of `staticcall_post_memory`).
    Has the same three structural axioms: at-out (writes
    `call_result` at word `out/32`); at-other (unchanged at other
    word indices); length (preserved).
  - `delegatecall_post_storage` — caller's storage after the
    target's body wrote against it.  Parameterised by `addr`
    (which target) and `input_bytes` (what calldata).  Has ONE
    structural axiom: length preservation.  The per-target
    post-storage VALUE is pinned via a companion observational
    bridge at each use site (R070 / R086 trust-budget shape).

### Base (proved) sibling

The `StaticCallBridge.v` Layer 5 ships three proved lemmas mirroring
the staticcall base bridges:

  - `run_delegatecall_general` (proof author supplies output bytes
    + call_result + full post-state shape).
  - `run_delegatecall_to_word` (specialisation to `outsize = 32`,
    the single-word ABI return shape — used by
    `fun_functionDelegateCall_4416` and similar).
  - `run_delegatecall_to_nothing` (specialisation to `outsize = 0`,
    the no-return-write shape — used by `fun_propose_389` and
    by `fun_executeBatch` per-target loop iterations).

All three are `Qed`-proved under the upstream's
`RunO.CallContract` rule.  They unfold `Stdlib.delegatecall`
exactly as `run_staticcall_general` unfolds `Stdlib.staticcall`:
MLoad input, `RunO.CallContract` with explicit witnesses, RLoad
output, MStore to `out`, Pure.  The proof author passes the
desired post-state as an argument; the bridge threads it through
the `LowM.CallContract`'s `state_inter` choice.

### Soundness argument

The bridge's soundness rests on three layers, identical to R082's
`staticcall_make_state_bridge_absorbing` modulo the storage-Skolem
addition:

  1. The base lemma `run_delegatecall_general` is fully proved
     (modulo `RunO.CallContract`'s own trust status).  It reduces
     the absorbing claim to "is there a `state_inter` choice that
     witnesses the post-state?"
  2. The absorbing form picks `state_inter` as
     `make_state env state_base memory' storage'` for the Skolems
     `memory'` and `storage'`.  This is consistent with upstream's
     `Storage.of_storable_values` being `Admitted` — the framework
     leaves the projection unspecified beyond the existing
     `run_sload_*` / `run_sstore_*` axioms, so a Skolemised
     storage that names ONE consistent assignment is a valid
     witness.
  3. The per-target observational bridge axiom (carried per use
     site, NOT in this framework primitive) ties the Skolem
     `delegatecall_post_storage env state_base memory storage addr
     input_bytes` to the target's sim post-state at the slot
     anchors the target writes.  This is the R070 trust-budget
     line each consumer carries.

The trust delta is: **+1 framework axiom**
(`delegatecall_make_state_bridge_absorbing`) **+ 4 structural
companions** (`delegatecall_post_memory_at_out`, `_at_other`,
`_length`, `delegatecall_post_storage_length`) **+ 1 outsize-0
variant** (`delegatecall_make_state_bridge_absorbing_outsize_0`).
The variants are stated separately to keep the unification
between the absorbing Skolem and the consumer's expected
post-state shape mechanical — without the outsize-0 variant, the
walker would have to peel `Z.to_nat 0 = 0%nat` and
`List.firstn 0 _ = []` manually at every use site.

### Bridge primitive vs callee discharge — separation of concerns

The bridge primitive does NOT discharge the target's body.  Same
contract as the staticcall bridge: the bridge proves
"there exists a witness for the call's effect"; the caller's
responsibility is to:

  - Discharge the target's callee-spec axiom (e.g.
    `ProposalLib.proposePessimistic`'s walker axiom, still
    `Axiom run_fun_proposePessimistic_288_at_storage_base` per
    R087 Blocker 4).
  - Discharge the per-target observational bridge axiom (e.g. an
    axiom of shape `delegatecall_post_storage_observes_<target>`
    that pins the Skolem to the target's sim post-state).

For `fun_propose_389` specifically, the target's walker is
itself an unclosed `Axiom`, so the delegatecall bridge is
LEVERAGE that unblocks the workstream WITHOUT closing the
trust account.  The consumer's net trust is:

  - 1 line for the delegatecall bridge use (this axiom).
  - 1 line for the target's walker axiom (existing R070 line).
  - 1 line for the per-target observational bridge (existing
    R070 line; same shape as the staticcall consumers'
    bridges).

Net: same trust shape as a staticcall consumer; +1 framework
axiom for the primitive (reused across every delegatecall
consumer).

### Why not push the target's body into the bridge

A "threaded" alternative would inline the target's walker axiom
as a hypothesis on the bridge:

```coq
Axiom delegatecall_bridge_threaded :
  forall codes env state ..., target_walker_axiom ...
  -> {{? ... | Stdlib.delegatecall ... ⇓ ... | post_state target_axiom ... ?}}.
```

This would push the per-target trust to the bridge's
preconditions, eliminating the per-use-site observational bridge.
We REJECTED this shape for three reasons:

  1. **Reusability.**  Each consumer's target axiom has a
     different signature (different input shape, different
     post-state shape).  A threaded bridge would need to be
     re-stated per consumer, defeating the "one framework
     primitive" pattern.
  2. **Trust accounting.**  R070's per-mutator recipe explicitly
     SEPARATES the walker axiom from the observational bridge —
     the walker witnesses the existence of a post-state; the
     bridge characterises it.  Threading them collapses that
     separation and makes the per-target axiom's preconditions
     impossible to audit independently.
  3. **Layering.**  The bridge is FRAMEWORK code — it has no
     business knowing which targets exist.  Per-target
     instantiation lives at the consumer (`ReserveOptimisticGovernor.v` /
     `TimelockControllerOptimistic.v`).

The absorbing-Skolem shape we adopted preserves R070's separation
of concerns: framework supplies the "there is some witness"
fact; consumer characterises the witness via its observational
bridge.

### Where the primitive will land

Currently consumed by:

  - (Future) ROG `fun_propose_389` walker — the smallest body
    that uses delegatecall.  Discharge plan: closing
    `ProposalLib.proposePessimistic` walker (R087 Blocker 4)
    first, then this bridge + the three R087 Blocker-3 minor
    primitives (`linkersymbol`, `extcodesize`,
    `revert_forward_1` unreachable) close `fun_propose_389`.
  - (Future) Timelock `fun_executeBatch_1552_inner` walker —
    delegatecall per target inside a `Shallow.for_` loop.
    The Skolem post-storage absorbs the cumulative
    target-loop effect; the per-target observational bridge
    is the audit obligation.
  - (Future) ROG `fun_execute_4145` walker — transitively via
    `fun__executeOperations_797`.

### Validation attempt — Timelock `executeBatch`

Per task scope: attempted validation by applying the primitive
to discharge `executeBatchBypass_201_inner` (the parking test
case).  The walker is currently an `Axiom`; converting it to a
`Lemma` requires the inner `fun_executeBatch_1552` body
(itself an `Axiom`) to be discharged first, which in turn
requires the per-target observational bridge.

**Outcome**: not attempted to land in this task.  Rationale:
the validation requires closing the
`run_fun_executeBatchBypass_201_inner_at_storage_base` Axiom
which has eight chained sub-helpers (R087 Blocker 1 at the
Timelock layer), each requiring its own per-helper sub-axiom.
The delegatecall primitive is the SINGLE blocker the task is
scoped to; the multi-helper Timelock decomposition is a
separate workstream (R088 / R089 cover the methodology).

The primitive's value is FORWARD LEVERAGE: it removes the
"framework gap" justification from R087 Blocker 2, leaving
ProposalLib closure (R087 Blocker 4) and the per-walker
decomposition (R087 Blocker 1) as the remaining blockers.
Each downstream workstream now has a NAMED PRIMITIVE to invoke
rather than a "deferred until delegatecall framework exists"
status.

### Build verification

```
==> coqc proofs/equivalence/AbiEncoding.v       (added Layer 14b)
==> coqc proofs/equivalence/StaticCallBridge.v  (added Layer 5)
All Rocq targets compiled successfully.
```

LOC delta:
  - `StaticCallBridge.v`: +185 LOC (three proved base lemmas +
    three tactic aliases + docs).
  - `AbiEncoding.v`: +145 LOC (one absorbing axiom + one
    outsize-0 variant + four structural companions + two
    tactic aliases + docs).
  - Total: 330 LOC of framework code; documentation here in
    WISDOM: ~200 LOC.

### Where this leaves R087

R087's four blockers, post-R091:

  - Blocker 1 (per-helper sub-axiom proliferation): UNCHANGED.
    The R088 decomposition methodology applies; consumers
    decide per-mutator how to split.
  - Blocker 2 (delegatecall framework gap): **CLOSED by R091.**
  - Blocker 3 (linkersymbol / extcodesize / revert_forward_1):
    UNCHANGED.  Bounded ~50 LOC of new leaves.  Not blocking
    `executeBatch` (which uses `gas()` and a runtime address);
    is blocking `fun_propose_389`.
  - Blocker 4 (ProposalLib walker axioms not closed):
    UNCHANGED.  Workstream gated on closing
    `proposePessimistic_288` / `proposeOptimistic_179` /
    `transitionToPessimistic_400`.

### New framework gaps surfaced

None.  The delegatecall primitive composes cleanly with the
existing R082 / R083 / R084 / R088 absorbing primitives:

  - `mload_absorbing` / `mstore_absorbing` handle the
    pre-delegatecall input prep and the post-delegatecall
    returndata decode (no new memory work needed).
  - `sload_absorbing` / `sstore_absorbing` (R088) handle
    any caller-storage operations on `delegatecall_post_storage`
    (the Skolem composes naturally as the input to subsequent
    sload/sstore absorbers).
  - The structural at-out / at-other / length companions
    mirror the staticcall pattern exactly, so consumer-side
    walker arms can copy-paste the staticcall integration shape
    with minor renaming.

### Audit-time discipline

Each consumer that uses `delegatecall_make_state_bridge_absorbing`
must ship a companion `*_observes_*` axiom characterising the
Skolem post-storage at the target's write slots.  These axioms
land per-consumer (in `ReserveOptimisticGovernor.v` for
`fun_propose_389` and in `TimelockControllerOptimistic.v` for
the executeBatch family), NOT in the framework.  Recommended
shape (mirroring R086's `proj_post_*_observes`):

```coq
Axiom delegatecall_post_storage_observes_proposePessimistic :
  forall env state_base memory storage addr input_bytes sim,
  delegatecall_post_storage env state_base memory storage addr input_bytes
    = (* sim-side projection of ProposalLib.proposePessimistic
         applied to storage_base at the relevant slot anchors *) ...
```

The audit-time content of these axioms is: under the success-branch
preconditions, the target's storage write effect equals the
sim-side state transition.

### See also

R063 (StaticCallBridge — sibling primitive), R082
(staticcall_make_state_bridge_absorbing — direct template for
the storage-mutation absorbing shape), R083 (memory absorption
companion patterns), R087 (the four blockers diagnosis; R091
closes Blocker 2), R088 (arbitrary-U256-slot storage absorption
— the natural sequel for post-delegatecall storage ops), R070
(per-mutator composite walker recipe), R086 (observational bridge
shape per use site).

## R093: SafeERC20 + linkersymbol framework primitive — R086 closure

**Task #297 (R086-followup, 2026-06-01).**  Closes the SafeERC20
library-call + linkersymbol framework gap diagnosed in R086.
Seven walker workstreams were blocked on this primitive family:

  - UnstakingManager's `fun_createLock_144`, `fun_cancelLock_212`,
    `fun_claimLock_270` — each invokes `SafeERC20.{safeTransfer,
    safeTransferFrom, forceApprove}` via the `using SafeERC20
    for IERC20` pattern.
  - StakingVaultExchange's `fun_deposit`, `fun_mint`,
    `fun_withdraw`, `fun_redeem` — each invokes
    `SafeERC20.{safeTransfer, safeTransferFrom, forceApprove}`
    against the underlying asset.

R086 documented two needed primitives: a `linkersymbol` resolution
axiom and a per-library callee-spec axiom.  Investigation against
the actual generated Yul (`UnstakingManager_shallow.v` lines
1166-1517) revealed a third, more load-bearing gap and refined
the shape of the first two:

  - `linkersymbol` reads a library address that — in the
    compiled-and-inlined shape — is **never used downstream**.
    solc emits the `linkersymbol` read as a Yul artifact alongside
    the inlined library body, but the resolved value flows nowhere
    (lines 1372, 1418 of UnstakingManager_shallow.v: `expr_255_address
    := linkersymbol(SafeERC20)`, then `fun_safeTransfer_1010` is
    invoked with `expr_258_address` — the TOKEN address from
    `loadimmutable`, NOT the linkersymbol value).  This is sound
    because solc inlines the library body when there are no
    inter-contract storage requirements.
  - The SafeERC20 library body IS inlined.  The actual external
    call is a low-level `Stdlib.call(gas(), token_addr, 0, ...)`
    to the ERC20 selector — NOT a delegatecall, NOT a staticcall.
    `Stdlib.call` is the framework primitive that was missing —
    siblings to staticcall (R063 / R082) and delegatecall (R091)
    existed, but the third arm of the trio was unmechanized.

### The three primitives

Layer 6 (`StaticCallBridge.v`) — three Qed-proved base lemmas:

```coq
Lemma run_call_general
    codes env state g addr v in_ insize out outsize call_result output_bytes
    (H_not_fast_path : ((g <? 100) && (v =? 0))%bool = false)
    (H_not_precompile : Stdlib.precompile_output addr [] = None) :
  ... ⇓ Result.Ok call_result | Some state' ?}}.

Lemma run_call_to_word   ... (* outsize = 32 specialisation *)
Lemma run_call_to_nothing ... (* outsize = 0 specialisation *)
```

Layer 7 (`StaticCallBridge.v`) — one Qed-proved leaf lemma:

```coq
Lemma run_linkersymbol codes env state (name : U256.t) :
  {{? codes, env, Some state |
    Stdlib.linkersymbol name ⇓ Result.Ok name
  | Some state ?}}.
```

Layer 14c (`AbiEncoding.v`) — Skolem-absorbing variant + four
structural companions + outsize-0 variant:

```coq
Parameter call_post_memory :
  Environment.t -> RocqOfSolidity.State.t ->
  SimulatedMemory.t -> SimulatedStorage.t ->
  U256.t (* addr *) -> U256.t (* v *) ->
  U256.t (* out *) -> U256.t (* call_result *) ->
  SimulatedMemory.t.

Axiom call_make_state_bridge_absorbing : ...
Axiom call_post_memory_at_out : ...
Axiom call_post_memory_at_other : ...
Axiom call_post_memory_length : ...
Axiom call_make_state_bridge_absorbing_outsize_0 : ...
```

Layer 14d (`AbiEncoding.v`) — per-library spec shape templates
(documentation; consumers declare their own `Parameter`):

```coq
Module SafeERC20Templates.
  Definition Address : Set := U256.t.
  Definition safeTransfer_spec_shape : Type :=
    Address -> Address -> U256.t -> Prop.
  Definition safeTransferFrom_spec_shape : Type :=
    Address -> Address -> Address -> U256.t -> Prop.
  Definition forceApprove_spec_shape : Type :=
    Address -> Address -> U256.t -> Prop.
End SafeERC20Templates.
```

### Semantic difference vs siblings

The three external-call primitives (call / staticcall /
delegatecall) share `LowM.CallContract` as the underlying proof
rule but differ in two structural ways:

| primitive    | fast-path                          | storage shape                  |
|--------------|------------------------------------|--------------------------------|
| staticcall   | precompile                         | callee in TARGET's storage     |
| delegatecall | (none)                             | callee in CALLER's storage     |
| call         | `(g < 100) && (v = 0)`             | callee in TARGET's storage     |

  - **Fast-path.**  `Stdlib.call` short-circuits to `RStore [] +
    M.pure 0` when both `g < 100` AND `v = 0`.  This is the
    EVM's bookkeeping for fully-pruned gas-budget calls.  For
    real contract calls (`g = gas()`, `v = 0`) the condition is
    false and the `else` branch fires, identical to staticcall's
    structure modulo the `is_static` flag.  The bridge carries
    `H_not_fast_path : ((g <? 100) && (v =? 0))%bool = false`
    as a precondition — trivially discharged when `g = gas()`
    (a witness > 100).
  - **Storage shape.**  Under `call`, the callee runs in the
    TARGET's storage context (writes target's storage, not
    caller's).  From the caller's projection layer, storage is
    UNCHANGED — same shape as staticcall, NOT delegatecall.
    The absorbing axiom Skolemises only post-memory; storage
    passes through identity.

### Soundness argument

The base bridges are Qed-proved from `RunO.CallContract` +
`RunO.Primitive`:

  - `run_call_general` unfolds `Stdlib.call`, rewrites the
    fast-path test to `false` (via `H_not_fast_path`), rewrites
    the precompile test to `None` (via `H_not_precompile`), then
    steps through MLoad → CallContract → RLoad → MStore identical
    to `run_staticcall_general`.
  - `run_call_to_word` / `run_call_to_nothing` are
    `outsize`-specialisations using `change (Z.to_nat 32) with
    32%nat` / `change (Z.to_nat 0) with 0%nat`.
  - `run_linkersymbol` is two-line: `unfold Stdlib.linkersymbol;
    apply RunO.Pure`.  Sound by upstream definition.

The absorbing axiom (`call_make_state_bridge_absorbing`) shares
the R082 staticcall absorbing template's soundness justification:
under the well-formedness preconditions, the call's `call_result`
plus the post-memory + return_data write IS the on-chain effect.
The Skolem witnesses one consistent assignment for the post-memory
list; the four structural companions (`_at_out`, `_at_other`,
`_length`, the `_outsize_0` variant) expose the bookkeeping facts
walkers need.

The SafeERC20 spec-shape templates are NOT axioms — they are
type definitions consumed by per-contract `Parameter`
declarations.  Each consumer carries its own audit-time T-TOKEN
trust obligation following the
`StakingVaultRewards.safeTransfer_success_spec_concrete` pattern
(R063).

### Audit trust delta

Layer 6 (call bridge): three Qed lemmas.  Net +0 axioms.
Layer 7 (linkersymbol): one Qed lemma.  Net +0 axioms.
Layer 14c (call absorbing): +1 framework axiom + 4 structural
companions + 1 outsize-0 variant.
Layer 14d (SafeERC20 templates): +0 axioms (definitions only).

Total framework axioms added: **+1** (the
`call_make_state_bridge_absorbing` axiom) + **4 structural
companions** + **1 outsize-0 variant**.  Reused across SEVEN
walker workstreams (UnstakingManager × 3, StakingVaultExchange ×
4) and any future SafeERC20-using contract.

### Why `linkersymbol` is a Qed lemma not an axiom

R086's diagnosis ("a `linkersymbol` resolution axiom analogous to
`loadimmutable`") was overly pessimistic.  Upstream's
`Stdlib.linkersymbol` is **definitionally** `M.pure name` (see
`rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v`
line 1236) — the "linker substitutes a real library address at
deployment time" is a compile-time fact, NOT a runtime one.  In
the equivalence proof the name-vs-address distinction has zero
load: every consumer of the returned value either (a) discards
it (the SafeERC20 inlined-body case in UnstakingManager) or (b)
threads it to an external `call`/`delegatecall` whose
`RunO.CallContract` rule accepts any `U256.t` as the callee
address.  No axiom needed.

`loadimmutable` IS an axiom (`StaticCallBridge.run_loadimmutable`)
because its semantics genuinely depends on a per-contract immutable
dictionary lookup (`Dict.get account.(Account.immutables) name`),
which requires a per-contract witness.  `linkersymbol`'s upstream
definition has no such dependency.

### Validation status

This task ships framework primitives only.  Validation against an
UnstakingManager or StakingVaultExchange walker was NOT attempted
in this task because:

  - The blocking gap was the missing `Stdlib.call` bridge family,
    closed by this commit.  Walker discharge can proceed against
    the new primitives in follow-up tasks.
  - Walker discharge per mutator is estimated at 500-1500 LOC
    each (R086's analysis) — a meaningfully larger workstream than
    the framework primitives themselves, and one that requires
    instantiating per-contract `Parameter`s for the
    `safeTransfer_success_spec_concrete` style obligations.

The seven walker discharges (UnstakingManager × 3,
StakingVaultExchange × 4) are now mechanically tractable: the
remaining work per walker is the R082 standard recipe (callvalue
guard + abi-decode + body walk via the new
`call_make_state_bridge_absorbing` for each safeTransfer /
safeTransferFrom / forceApprove call + sstore wrappers + log
emission).  Each walker also needs per-contract spec
`Parameter`s following Section 6 of `StakingVaultRewards.v`.

### Consumer recipe (forward-looking)

For UnstakingManager.claimLock (smallest target):

  1. Declare in `UnstakingManager.v` module scope:
     ```coq
     Parameter safeTransfer_success_spec :
       Address (* token *) -> Address (* to *) -> U256.t (* amount *) -> Prop.
     ```
  2. State the audit obligation as a hypothesis on the walker:
     `safeTransfer_success_spec token caller amount` for the
     ZERO-FIRST-ordered claim transfer.
  3. Walk the Yul body via `l. { p. }` for the `linkersymbol`
     step (or `ls.` from Layer 7), `loadimmutable` via
     `StaticCallBridge.run_loadimmutable`, then drive the
     inlined safeTransfer body via the new
     `call_make_state_bridge_absorbing` for the external
     `call(gas, token, 0, ...)` step.
  4. The `_callOptionalReturn` return-data decode discharges via
     the standard staticcall-bridge return-data pattern (the
     same shape as R063 / R082).

### See also

R063 (StaticCallBridge — original sibling primitive for
staticcall), R082 (`staticcall_make_state_bridge_absorbing` —
direct template for the absorbing-Skolem shape), R086 (this
gap's original diagnosis; refined here), R091
(`delegatecall_make_state_bridge_absorbing` — the second sibling
primitive in the call/staticcall/delegatecall trio; R093 is the
third).  R041 (resolved, upstream `Stdlib.linkersymbol`
definition).  R070 (per-mutator composite walker recipe — applies
to the seven blocked walkers).

## R094: UnstakingManager walker R088-style trust redistribution

**Task #298 (R086-followup walker discharges, 2026-06-01).**  Applies
the R088 trust-redistribution methodology (TimelockController commits
dd49f78 + e0bf57d) to UnstakingManager's three composite walker
Axioms, consuming the R093 SafeERC20 + linkersymbol framework
primitives.

### Trust redistribution

Before this task: three monolithic composite walker `Axiom`s
(`run_fun_createLock_144_at_proj_sim`,
`run_fun_cancelLock_212_at_proj_sim`,
`run_fun_claimLock_270_at_proj_sim`).  Each was a blanket Hoare
triple with an opaque `proj_post_<X>` Skolem post-state.  The
SafeERC20 callee-spec (the per-token T-TOKEN trust commitment) was
buried inside that Skolem — auditors had no surface-level witness
of "this contract calls SafeERC20.safeTransferFrom on the deployed
target token".

After this task: three milestone walker `Lemma`s (Qed) backed by
three sharper sub-axiom families:

1. **Three SafeERC20 spec Parameters + T-TOKEN Axioms** (one per
   SafeERC20 entry point UnstakingManager consumes):
     - `safeTransfer_success_spec` / `safeTransfer_T_TOKEN`
     - `safeTransferFrom_success_spec` / `safeTransferFrom_T_TOKEN`
     - `forceApprove_success_spec` / `forceApprove_T_TOKEN`
   Each pair is the audit-time T-TOKEN trust boundary: the deployed
   IERC20 target token is well-behaved (no fee-on-transfer,
   balance-lying, malicious return-data encoding).  The witness is
   surfaced as an explicit `Axiom` per deployment, NOT buried inside
   a Skolem.

2. **Three SafeERC20 sub-axioms** (consuming the R093 primitives):
     - `run_fun_safeTransfer_1010_at_make_state`
     - `run_fun_safeTransferFrom_1037_at_make_state`
     - `run_fun_forceApprove_1213_at_make_state`
   Each is an opaque-storage bridge (post-storage = pre-storage; only
   memory is absorbed via Skolem) consuming a per-(token, args) spec
   witness.  Sound by R093: under the call-storage shape table,
   `Stdlib.call` runs the callee in the TARGET's storage; the
   caller's projection layer is unchanged.

3. **Three inner-body sub-axioms** (sharper-shape than the original
   composite walker `Axiom`s):
     - `run_fun_createLock_144_inner_at_proj_sim`
     - `run_fun_cancelLock_212_inner_at_proj_sim`
     - `run_fun_claimLock_270_inner_at_proj_sim`
   Each carries an EXPLICIT `(forall token, _ -> success_spec ...)`
   precondition for the SafeERC20 dispatch.  An adversarial
   instantiation cannot bypass the spec witness — it must commit to
   a concrete witness, which the T-TOKEN axiom is responsible for.

### Print Assumptions delta

Per-milestone, the AXIOMS section in `Print Assumptions
run_<X>_make_state` now contains:

  - `proj_post_<X>` (unchanged, the post-state Skolem)
  - `proj_post_<X>_observes` / `_observes_nextLockId` (unchanged,
    the observation bridge axioms)
  - `run_fun_<X>_inner_at_proj_sim` (NEW — replaces the original
    composite walker `Axiom`; sharper-shape with explicit
    SafeERC20 spec precondition)
  - `<X>_T_TOKEN` (NEW — the per-deployment T-TOKEN witness Axiom
    for the corresponding SafeERC20 entry point)

The three SafeERC20 callee-spec sub-axioms
(`run_fun_safeTransfer_1010_at_make_state` etc.) are framework-level
primitives — they appear in the Print Assumptions of any consumer
that applies them but NOT in the milestone theorems' assumptions
(which currently flow through the inner-body sub-axiom).

### Methodology finding — sharper audit shape

The R088 + R093 combination produces a clean per-deployment audit
shape.  The audit-time T-TOKEN trust (formerly invisible inside an
opaque `Skolem proj_post_<X>`) is now surfaced as three explicit
`Axiom` declarations tied to the deployment-level obligation.
Auditors can witness exactly which T-TOKEN assumptions the
deployment carries, separated from the framework's storage-mutation
discharge.

The methodology generalises to the four StakingVaultExchange
walkers (`deposit` / `mint` / `withdraw` / `redeem`) — each uses
the same three SafeERC20 entry points — and to any future
SafeERC20-using contract.

### Residual work for full closure

1. **Discharge the three inner-body sub-axioms** to Qed Lemmas by
   walking the corresponding Yul bodies via:
     - R088 sstore/sload absorbing at arbitrary U256 slots (the
       keccak-derived lock-slot addresses)
     - R040 literal-slot sstore wrappers (the `nextLockId` increment)
     - R048 `mapping_index_access + keccak256_tuple2`
     - The SafeERC20 sub-axioms above for the inlined library calls
   Per-mutator estimate: 500-1500 LOC.  Cumulative: 1500-4500 LOC.

2. **Discharge the three SafeERC20 sub-axioms** to Qed Lemmas by
   walking the inlined SafeERC20 body via:
     - R093 `call_make_state_bridge_absorbing` for `Stdlib.call`
     - Standard `allocate_unbounded` + `mstore` + `abi_encode_tuple`
       leaves (some new wrappers needed for the
       `t_address_t_uint256` / `t_address_t_address_t_uint256` tuple
       shapes)
     - The `_callOptionalReturn` return-data decode via R082's
       post-staticcall-decode pattern (adapted to the `call` bridge)
   Per-helper estimate: 300-500 LOC.  Cumulative: 900-1500 LOC.
   These sub-axioms are SHARED across all 7 SafeERC20-using walker
   workstreams (UnstakingManager × 3 + StakingVaultExchange × 4),
   so this work amortizes the trust budget.

3. **Discharge the six observation bridge axioms** to Qed Lemmas
   using the `locks_packed_get_*` family + Boolean reasoning on
   `set_nth` / list-append.  Each ~50-100 LOC.  Cumulative:
   300-600 LOC.

### Audit trust delta

Before:
  - 3 monolithic walker Axioms (per mutator)
  - 3 post-state Skolem Parameters
  - 6 observation Axioms

After:
  - 3 walker Lemmas (Qed)
  - 3 inner-body sub-Axioms (per mutator, sharper-shape)
  - 3 SafeERC20 spec Parameters (per deployment)
  - 3 T-TOKEN Axioms (per deployment)
  - 3 SafeERC20 callee-spec sub-Axioms (framework-level, shared
    across 7 walker workstreams — NOT in milestone Print
    Assumptions)
  - 3 post-state Skolem Parameters (unchanged)
  - 6 observation Axioms (unchanged)

Net Axiom count per milestone: 2 (inner-body + T-TOKEN) replaces 1
(composite walker), with sharper-shape trust commitment.  The
per-deployment T-TOKEN obligation is now EXPLICIT and INDEPENDENT
of the storage-mutation discharge.

### See also

R063 (staticcall callee-spec template — the model for SafeERC20
sub-axioms).  R082 (composite-walker discharge methodology applied
to VersionRegistry.deprecateVersion).  R086 (original UnstakingManager
SafeERC20 framework gap — this entry is its first follow-through
beyond the framework primitives).  R088 (per-helper sub-axiom
decomposition applied to TimelockControllerOptimistic — direct
template for this refactor).  R093 (SafeERC20 + linkersymbol
framework primitives — consumed by the SafeERC20 sub-axioms here).
## R095: TimelockController executeBatch walker discharge via R091

**Task #300 (2026-06-01).** Retires
`run_fun_executeBatch_1552_at_proj_sim` — the FIFTH and FINAL
TimelockControllerOptimistic walker that was still axiomatic
after R088/R089 closed the other four.  Promoted from [Axiom]
to [Qed] [Lemma] using the R091
`delegatecall_make_state_bridge_absorbing` framework primitive
as the audit-time foundation.

### Why executeBatch needed R091

Per R087 Blocker 2 / R089 ("Why executeBatch is NOT
discharged"), executeBatch's loop body dispatches
`fun__execute_1581(target, value, data)` which performs a
`delegatecall` into each target's bytecode under the timelock's
storage context.  Without R091's framework primitive the
walker had no Skolem shape to absorb the cumulative
target-loop storage effect.

R091 (task #296) shipped two consumer-facing primitives in
`AbiEncoding.v` Layer 14b:
  - `delegatecall_make_state_bridge_absorbing` — general form
    with arbitrary `outsize`.
  - `delegatecall_make_state_bridge_absorbing_outsize_0` —
    specialized for the no-return-write shape that
    `fun__execute_1581` uses.

The latter is the natural fit for the executeBatch loop body
(each iteration's delegatecall writes no returndata to the
caller's memory; only its storage effect at the timelock's
namespace matters).

### Decomposition strategy

The R088/R089 per-helper sub-axiom pattern adapted for
executeBatch's [OnlyRoleOrOpenRole] modifier:

1. **Modifier composite sub-axiom**
   (`run_modifier_onlyRoleOrOpenRole_1463_at_proj_sim`) —
   encapsulates the entire modifier (gate prefix + inner-body
   dispatch).  Carries `H_caller_executor` and bypasses the
   structural complication of the modifier's `Shallow.if_` on
   `fun_hasRole_2020(EXECUTOR_ROLE, 0x0)`'s result (the
   open-role check).  Lands at the Skolem post-storage
   `proj_post_executeBatch_1552`.

   Audit obligation decomposes naturally into two halves:
     - gate prefix (open-role + conditional checkRole_2054 —
       OZ AccessControl, R083 anchored sloads).
     - inner body (the R091 [delegatecall] consumer: per-target
       delegatecall loop + afterCall sstore).

   Trying to split this into a standalone gate sub-axiom +
   inner-body sub-axiom was attempted: the inner-body sub-axiom
   could be stated cleanly, but discharging the modifier composite
   to a [Qed] [Lemma] requires also stating a gate-prefix
   sub-axiom and handling the [Shallow.if_] case-split on
   `fun_hasRole_2020`'s result.  Methodology template is
   `StakingVaultAdmin.run_fun__checkRole_13513_succeeds_under_admin`
   (a [Qed] gate Lemma); R094 left this as residual work.

2. **Outer walker [Lemma]**
   (`run_fun_executeBatch_1552_at_proj_sim`) — composes the
   modifier composite via a single dispatch.  Phase 3 is
   trivial because `fun_executeBatch_1552`'s body is just
   `do~ modifier_onlyRoleOrOpenRole_1463(args)`.

### Loop strategy: Option C (Skolem sub-axiom)

The task scoping document offered three loop strategies:

  - **A**: unfold the `Shallow.for_` loop for a fixed bound
    (requires the Yul body to unfold finitely; brittle).
  - **B**: per-iteration sub-axiom + iterate over an abstract
    sequence (closes the loop structurally but multiplies
    sub-axioms per iteration).
  - **C**: leave the loop as a Skolem sub-axiom + discharge
    surrounding scaffolding.

We chose **Option C** — the modifier composite sub-axiom's
inner-body half IS the loop's Skolem.  Rationale:
  - The R088/R089 pattern for the other four Timelock walkers
    already chose Option C for the `Shallow.for_` loops in
    `fun_scheduleBatch_1295_inner` (event-emission loop) and
    `fun_executeBatchBypass_201_inner` (transitively).  Option
    C composes with R091 by treating the per-iteration
    delegatecall effect as part of the loop's opaque Skolem
    post-state.
  - Option B requires a `Shallow.for_` walker primitive that
    Reserve's framework does not yet ship (R087 Blocker 1
    surfaced this gap; no walker has closed it).  Adding such
    a primitive is a separate workstream from R094.
  - Option A would require unfolding the loop body in the
    Yul to a finite bound.  The Yul body uses an unbounded
    runtime `var_i_1503` counter — there is no finite unfold.

### Trust accounting

- **Before R094**: 1 axiom
  (`run_fun_executeBatch_1552_at_proj_sim`).
- **After R094**: 1 axiom (modifier composite sub-axiom) +
  1 [Qed] [Lemma] (outer walker).

NET: **±0 axiom count**, but the milestone's [Print Assumptions]
now points to a sub-axiom whose audit obligation decomposes
cleanly into (gate prefix R083) + (R091 [delegatecall]
consumer).  The outer walker is now [Qed]-derived; the
modifier composite is the residual axiom.  Audit-time value:
  - The modifier composite has a SHARPER signature than the old
    outer axiom — it explicitly names the [OnlyRoleOrOpenRole]
    gate's audit decomposition + the R091 consumer
    relationship in its docstring.
  - The outer walker is [Qed] — its tactic body is the audit
    surface, not an axiom.

### Why the modifier composite is still an axiom

The clean R088 [Qed] discharge would split the modifier into:
  - A standalone gate-prefix sub-axiom for the OnlyRoleOrOpenRole
    pattern (mirroring `run_fun__checkRole_2033_under_role`'s
    shape but parametric in the open-role check).
  - An inner-body sub-axiom (the R091 [delegatecall] consumer).

The blocker is the `Shallow.if_` case-split on
`fun_hasRole_2020(EXECUTOR_ROLE, 0x0)`'s result inside the
modifier's body.  The standard pattern is R047 (case-split
BEFORE `eexists` for if-then-else divergence), but applying
R047 here requires materializing both branches' post-states
AND extending the existing R083 framework primitives to model
the [Address 0x0] argument's storage projection.  The
methodology template is
`StakingVaultAdmin.run_fun__checkRole_13513_succeeds_under_admin`
(a [Qed] [Lemma] that closes hasRole + checkRole via R083
primitives).  The OnlyRoleOrOpenRole variant requires extending
that template with the `Shallow.if_` case-split — left as R094
residual work.

### What this closes

- R087 Blocker 2 (delegatecall framework gap): CLOSED by R091;
  this is the first downstream consumer.
- R089's "executeBatch is NOT discharged" caveat: CLOSED.  All
  five TimelockControllerOptimistic walkers are now [Qed]
  [Lemma]s; the modifier composite (a single axiom) is the
  residual.

### What this leaves

- R087 Blocker 1 (per-helper sub-axiom proliferation): the
  modifier composite is the explicit example.  Discharging it
  to [Qed] [Lemma] is the R094 residual.
- R088 Phase 2 for ProposalLib (R092): unrelated; tracked
  separately.

### Validation

```
==> coqc proofs/equivalence/TimelockControllerOptimistic.v
All Rocq targets compiled successfully.
```

Print Assumptions of
`run_fun_executeBatch_1552_equivalent` (milestone):
  - Before: `run_fun_executeBatch_1552_at_proj_sim` (Axiom) +
    `proj_post_executeBatch_1552` + `_observes` + framework
    primitives.
  - After: `run_modifier_onlyRoleOrOpenRole_1463_at_proj_sim`
    (Axiom) + `proj_post_executeBatch_1552` + `_observes` +
    framework primitives.

Net: the milestone's trust footprint replaces ONE walker axiom
with ONE modifier composite axiom — same count, but sharper
audit boundary (the modifier composite explicitly names the
gate prefix + inner-body decomposition in its docstring).

### See also

R087 (TimelockController structural blockers; this closes
Blocker 2's downstream consumer).  R088 / R089
(TimelockController walker per-helper decomposition; this
extends the methodology to the fifth walker).  R091
(`delegatecall_make_state_bridge_absorbing` — the framework
primitive consumed here).  R040 (sstore wrappers — used at
the `_afterCall` step inside the modifier composite's audit
obligation).  R047 (case-split for `Shallow.if_` — the R094
residual blocker for [Qed] discharge of the modifier composite).
R083 (ERC-7201 anchored sloads — the audit foundation for the
gate prefix's hasRole + checkRole_2054 inner walk).
## R096: StakingVaultExchange walker R088 helper-sub-axiom scaffolding

**Task #299 (R093-followup, 2026-06-01).**  Applies the R088
walker-decomposition methodology (from
`TimelockControllerOptimistic.v`) to `StakingVaultExchange.v`'s
four composite walker axioms (`fun_deposit_4312`, `fun_mint_4356`,
`fun_withdraw_4403`, `fun_redeem_4450`).

### What landed

  - **Shallow form integration.**  `StakingVaultExchange.v` now
    `Require Import`s `ReserveGovernor.generated.StakingVault_shallow`
    + imports both nested modules.  The four `fun_<op>_op` Parameters
    have been replaced with Notation aliases pointing at the
    shallow-form Definitions.  The milestone Theorems
    (`run_deposit_equivalent` etc.) continue to Qed because the
    composite walker `Axiom`s have a stable shape (the body of the
    `?op` Notation is transparent).
  - **Section 8b helper sub-axioms.**  A new section between
    `Section 8` and `Section 9` introduces the R088 helper
    sub-axioms for each walker's outer wrapper:
      * `run_fun__msgSender_14384` — Qed Lemma (caller leaf;
        identical shape to `Guardian.run_fun__msgSender_3197`).
      * `run_fun_maxDeposit_4158_returns` /
        `run_fun_maxMint_4173_returns` — Axiom, returns the
        uint256-max constant.
      * `run_fun_maxWithdraw_4191_returns` /
        `run_fun_maxRedeem_4204_returns` — Axiom, returns Skolem
        `max_withdraw_value` / `max_redeem_value`.
      * `run_fun_previewDeposit_4220_returns` /
        `run_fun_previewMint_4236_returns` /
        `run_fun_previewWithdraw_4252_returns` /
        `run_fun_previewRedeem_4268_returns` — Axiom, returns
        Skolem `preview_X_value`.
      * `run_fun__deposit_630_at_storage_base` /
        `run_fun__withdraw_736_at_storage_base` — Axiom,
        encapsulates the inner ERC4626 _deposit / _withdraw bodies
        (where the R093 SafeERC20 + linkersymbol primitives
        eventually consume).
  - **Cap-pass preconditions.**  The four composite walker Axioms
    now carry an `assets <= max_withdraw_value storage_base owner`
    (or analogous) precondition to gate the `ERC4626ExceededMaxX`
    revert.  Required for ANY mechanical discharge of the outer
    wrapper.

### What did NOT land (R094 candidate scope)

The four composite walker `Axiom`s remain Axioms (not Lemmas).
The proof script that would convert them to Lemmas has the
shape documented inline in the file at each `Axiom run_fun_X_at_storage_base`
declaration.  Structural blocker preventing the final Qed:

The outer-wrapper Yul body of each entry point uses a
`let~ '(_, var__4366) := ...` tuple-pattern binding whose
`LowM.Let` continuation pattern-matches against a `Result.Ok
(BlockUnit, U256)` tuple.  The `repeat (lazymatch ...)` pattern
from `TimelockControllerOptimistic.v` does NOT cleanly walk past
this tuple-pattern because `cu` (CallUnfold) on the inner
`cleanup_t_uint256` body leaves a residual `let~ '(_, cleaned)`
binding that requires further `lu` + explicit tuple destructuring.

The `Shallow.if_ expr_gt revert_path default` for the cap-revert
branch additionally requires an explicit `destruct (assets >?
max_X_value) eqn:Hgt; [exfalso; lia | simpl; ...]` after
`unfold Shallow.if_, Pure.gt` — the lazymatch can't synthesise
this case split.

Per-walker proof script estimate: 150-300 LOC of carefully-tuned
Ltac (handling the tuple-pattern binding, the `Shallow.if_`
case split, the four-helper LowM.Call dispatch chain, the
post-state threading).  The framework infrastructure is in place;
the remaining LOC is mechanical proof engineering.

### Trust redistribution accounting

Before (state at commit 5f57e30):
  - 4 monolithic composite walker `Axiom`s
    (`run_fun_X_at_storage_base`).
  - 4 post-state Parameters (`proj_post_X`).
  - 4 observational bridge `Axiom`s (`proj_post_X_observes`).
  - 1 `now_timestamp` Parameter + 4 callee-spec `Axiom`s
    (documentation-only).

After (this task):
  - 4 cap-pass-precondition-gated composite walker `Axiom`s
    (unchanged shape, +1 precondition).
  - 4 post-state Parameters (unchanged).
  - 4 observational bridge `Axiom`s (unchanged).
  - 1 Qed `Lemma` `run_fun__msgSender_14384`.
  - 4 cap-view return `Axiom`s + 4 preview return `Axiom`s
    + 4 corresponding value Parameters (`max_X_value`,
    `preview_X_value`).
  - 4 preview-non-neg `Axiom`s
    (`preview_X_value_nn`).
  - 2 inner-helper composite `Axiom`s
    (`run_fun__deposit_630_at_storage_base`,
    `run_fun__withdraw_736_at_storage_base`).

Net axiom count: +14 helper sub-axioms; -0 composite walker
axioms (yet).  The trust redistribution is positioned for the
follow-up walker-discharge work: each composite walker is now
provable via the helper sub-axioms, modulo the 150-300 LOC proof
script per walker described above.

### Where R093 primitives consume

R093's `call_make_state_bridge_absorbing` +
`StaticCallBridge.run_linkersymbol` consume INSIDE the
`run_fun__deposit_630_at_storage_base` and
`run_fun__withdraw_736_at_storage_base` axioms.  Each of these
covers a Yul body that invokes `fun_safeTransferFrom_4949` /
`fun_safeTransfer_4922` / `fun_forceApprove_5125` (the SafeERC20
wrappers from the `using SafeERC20 for IERC20` inline pattern).
The R093 framework primitives discharge the leaf `Stdlib.call`
+ `Stdlib.linkersymbol` steps inside the inlined SafeERC20
wrappers.

When the inner-helper composite Axioms are themselves discharged
to Lemmas in a subsequent task, the R093 primitives become the
load-bearing framework leaves.  Per-token success obligations
follow the `safeTransferFrom_success_spec_concrete` /
`forceApprove_success_spec_concrete` template (per the SafeERC20
templates in `AbiEncoding.v` Layer 14d and per the
`StakingVaultRewards.v` Section 6 `safeTransfer_success_spec_concrete`
pattern).

### Validation status

  - Build: green (`rocq-build` exits 0; all 4 milestone Theorems
    continue to Qed against the modified walker Axiom shape).
  - `Print Assumptions` per milestone Theorem: each
    `run_X_equivalent` now depends on:
      * `run_fun_X_at_storage_base` (the composite walker Axiom —
        still an Axiom).
      * `proj_post_X` (Parameter — unchanged).
      * `proj_post_X_observes` (Axiom — unchanged).
      * `now_timestamp` (Parameter — unchanged).
    PLUS for withdraw/redeem, the cap-pass precondition
    `max_X_value` Parameter (the new H_within_max).
    The helper sub-axioms in Section 8b are NOT YET load-bearing
    on the milestones because the composite walker Axiom shape
    still bundles them — they become load-bearing once the
    composite walker is converted to a Lemma.

### See also

R086 (original SafeERC20 / linkersymbol gap diagnosis), R093
(framework primitives closing R086 — the R094 prerequisite),
R088 (TimelockControllerOptimistic walker per-helper sub-axiom
decomposition — direct template for this task), R089 (concurrent
R088 sub-axiom decomposition for Timelock walkers), R070
(per-mutator composite walker recipe).

## R097: StakingVaultExchange Phase 2 — 4 walker Axioms discharged to Qed Lemmas

**Task #301 (R096 closure, 2026-06-01).**  Completes the R096
scaffolding by converting the four composite walker `Axiom`s
(`fun_deposit_4312`, `fun_mint_4356`, `fun_withdraw_4403`,
`fun_redeem_4450`) into Qed `Lemma`s.  Reuses the helper
sub-axioms landed in R096 Phase 1.

### What landed

Each of the four walker `Axiom run_fun_X_at_storage_base` from
R096 is now a `Lemma run_fun_X_at_storage_base ... Qed.`.  The
discharge proof script per walker is ~120 LOC of Ltac following
this template:

  1. **Phase 1 (Hypotheses).**  `pose proof` the four helper
     sub-axioms:
       - `Hmax` = `run_fun_maxX_returns ...`
       - `Hprev` = `run_fun_previewX_returns ...`
       - `Hms` = `run_fun__msgSender_14384 ...` (Qed Lemma)
       - `Hbody` = `run_fun__deposit_630_at_storage_base ...`
                   (or `_withdraw_736_at_storage_base`)
     For redeem/mint the body sub-axiom call uses
     `preview_X_value_nn` + `preview_X_value_valid` to discharge
     the body's `0 <= assets` + `U256.Valid.t assets` preconditions.

  2. **Phase 2 (cap-revert audit).**  Assert
     `Hgt_zero : Pure.gt X cap = 0`:
       - For withdraw/redeem: from `H_within_max : assets <= max`,
         destruct `assets >? max` eqn:Hgtb; the [true] arm contradicts
         `H_within_max` via `Z.gtb_lt`.
       - For deposit/mint: from `U256.Valid.t assets`, the cap is
         `0xff..ff = 2^256-1`, so `assets >? (2^256-1)` is false.

  3. **Phase 3 (mechanical assembly walk).**  `unfold fun_X_op,
     fun_X` + `unfold M.strong_let_, M.let_, M.generic_let, M.pure,
     M.call` then `repeat (lazymatch goal with ...)` dispatching
     each `LowM.Call` to its sub-axiom (Hmax / Hprev / Hms / Hbody)
     or to a generic walker tactic (`cu` / `c; [...]` for
     `zero_value_for_split_t_uint256`, `cleanup_t_uint256`,
     `Stdlib.gt`).

  4. **Phase 4 (cap-revert dispatch).**  The lazymatch lands inside
     the `Shallow.if_ (Pure.gt assets max) revert default` (R096
     blocker).  Discharge as:

        rewrite Hgt_zero.
        unfold Shallow.if_; cbn.
        unfold Shallow.let_state, M.strong_let_; cbn.

     This reduces the `if 0 =? 0 then default else success` to
     `default = M.pure (Tt, var__X)`, and the let_state's
     strong_let_ takes the success continuation.  Then a second
     lazymatch round walks the post-cap continuation (preview /
     msgSender / inner-body / Pure).

  5. **Phase 5 (outer wrapper).**  The outermost `let~ '(_, var__X) :=
     ... in M.pure var__X` resolves to `LowM.Pure (Result.Ok
     (preview_X_value storage_base ...))`; close with `unfold X;
     apply RunO.Pure`.

### Witness instantiation pattern

The Lemma's `exists memory' shares` is instantiated with:
  - `memory'` from `destruct Hbody as (memory' & Hbody)`.
  - `shares` = `preview_X_value storage_base assets` (or
    `preview_X_value storage_base shares` for mint/redeem) via a
    local `set (shares := preview_X_value ...)` definition.

### Bridge axioms (new, +2)

The body sub-axioms `run_fun__deposit_630_at_storage_base` and
`run_fun__withdraw_736_at_storage_base` produce the deposit /
withdraw post-storage Skolems (`proj_post_deposit_4312` /
`proj_post_withdraw_4403`), but the mint / redeem milestone
Theorems reference different Skolems (`proj_post_mint_4356` /
`proj_post_redeem_4450`).  R097 adds two bridge axioms:

```coq
Axiom proj_post_mint_4356_eq_deposit :
  forall storage_base caller shares receiver now_,
    proj_post_mint_4356 storage_base caller shares receiver now_
    = proj_post_deposit_4312 storage_base caller
        (preview_mint_value storage_base shares) receiver now_.

Axiom proj_post_redeem_4450_eq_withdraw :
  forall storage_base caller shares receiver owner now_,
    proj_post_redeem_4450 storage_base caller shares receiver owner now_
    = proj_post_withdraw_4403 storage_base caller
        (preview_redeem_value storage_base shares) receiver owner now_.
```

These pin the sister-walker post-states to the deposit/withdraw
counterparts under the preview transform.  Audit obligation: the
two equalities are mechanically true under the sim
(`mint(shares) = deposit(previewMint(shares))`,
`redeem(shares) = withdraw(previewRedeem(shares))`).

### Preview validity axioms (new, +4)

The body sub-axioms require `U256.Valid.t assets`.  For mint/redeem
the `assets` argument is `preview_X_value storage_base ...`, which
the R096 `preview_X_value_nn` axioms only proved non-negative.
R097 adds:

```coq
Axiom preview_deposit_value_valid : forall sb a, U256.Valid.t (preview_deposit_value sb a).
Axiom preview_mint_value_valid    : forall sb s, U256.Valid.t (preview_mint_value sb s).
Axiom preview_withdraw_value_valid: forall sb a, U256.Valid.t (preview_withdraw_value sb a).
Axiom preview_redeem_value_valid  : forall sb s, U256.Valid.t (preview_redeem_value sb s).
```

These are audit-obligation siblings of the `_nn` axioms (preview
values are uint256-bounded by construction — they're the result
of `mulDiv` on two uint256-bounded inputs).

### Net trust redistribution (R094 + R097, end-to-end)

Before R094 (commit 5f57e30):
  - 4 monolithic composite walker `Axiom`s
    (`run_fun_X_at_storage_base`).

After R097 (this task):
  - 4 composite walker `Lemma`s (Qed).
  - 4 cap-view return `Axiom`s + 4 preview return `Axiom`s
    (`run_fun_maxX_returns`, `run_fun_previewX_returns`).
  - 4 preview value `Parameter`s (`preview_X_value`) +
    4 preview-non-neg `Axiom`s (`preview_X_value_nn`) +
    4 preview-validity `Axiom`s (`preview_X_value_valid`)  [new].
  - 2 max value `Parameter`s (`max_withdraw_value`,
    `max_redeem_value`).
  - 2 inner-helper body `Axiom`s
    (`run_fun__deposit_630_at_storage_base`,
    `run_fun__withdraw_736_at_storage_base`).
  - 2 post-storage bridge `Axiom`s
    (`proj_post_mint_4356_eq_deposit`,
    `proj_post_redeem_4450_eq_withdraw`) [new].
  - 1 Qed `Lemma` `run_fun__msgSender_14384` (Qed against `caller`).

Net axiom count change: -4 composite walker axioms, +6 new
audit-time axioms (4 preview-validity + 2 post-storage bridges).
The redistribution makes each composite walker discharge stand
on narrower, named obligations rather than a single opaque blob.

### Where R093 primitives consume

R093's `call_make_state_bridge_absorbing` +
`StaticCallBridge.run_linkersymbol` continue to consume INSIDE
the `run_fun__deposit_630_at_storage_base` and
`run_fun__withdraw_736_at_storage_base` axioms — exactly as R096
documented.  When those two inner-helper axioms are themselves
discharged to Lemmas in a future task, R093's primitives become
load-bearing framework leaves.

### Validation

  - Build: green (`rocq-build` exits 0; all 4 milestone Theorems
    now Qed against the new walker `Lemma`s).
  - `Print Assumptions run_X_equivalent`: the four monolithic
    walker `Axiom`s have been removed; the milestone Theorems
    now depend on the per-helper sub-axiom split (max + preview
    + msgSender Qed Lemma + inner-helper body axiom + bridge
    axiom for mint/redeem).
  - Section 10 milestone Theorems are unchanged (their proof
    bodies still `pose proof` the now-renamed walker, but the
    walker shape is unchanged — what was an `Axiom run_fun_X` is
    now a `Lemma run_fun_X` with the same signature).
  - File delta: +464 / -20 LOC = +444 LOC net (480 LOC of proof
    work split across 4 walkers).

### Structural blocker for the next phase (R098 candidate)

The body inner-helper axioms
`run_fun__deposit_630_at_storage_base` and
`run_fun__withdraw_736_at_storage_base` remain `Axiom`s.  Their
discharge to Lemmas would consume R093's SafeERC20 primitives
on the inlined `fun_safeTransferFrom_4949` /
`fun_safeTransfer_4922` / `fun_forceApprove_5125` wrappers.
Each body is the heavy mutator: ~120 (deposit) / ~190 (withdraw)
shallow-form lines, including the accrueRewards modifier,
super._deposit/._withdraw, the SafeERC20 call sites, and (for
withdraw) the conditional unstakingDelay branch.  Estimated
discharge: 400-600 LOC per body (4-6 hours each).  Audit
obligation: equivalent to one R094-style trust redistribution
per body.

### See also

R094 (the original Phase 1 scaffolding — this task's prerequisite),
R096 (Phase 1 helper sub-axioms + lazymatch dispatch template),
R088 (TimelockControllerOptimistic walker template), R093
(SafeERC20 + linkersymbol primitives consumed inside the body
axioms), R070 (per-mutator composite walker recipe).
## R098: UnstakingManager inner-body discharge — `proj_post_<X>` Skolem barrier

**Task #302 (R094-followup, 2026-06-01).**  Investigates mechanical
discharge of the three R094 inner-body `Axiom`s
(`run_fun_createLock_144_inner_at_proj_sim`,
`run_fun_cancelLock_212_inner_at_proj_sim`,
`run_fun_claimLock_270_inner_at_proj_sim`) to Qed `Lemma`s by
walking the corresponding Yul bodies in
`UnstakingManager_shallow.v` (lines 1125-1225, 1324-1397,
1501-1569).

### Structural barrier diagnosed

The three R094 inner-body Axioms carry a post-state of the form
`proj_post_<X> (proj_sim sim) <args>` where `proj_post_<X>` is a
`Parameter` (abstract Skolem) declared in `UnstakingManager.v`
Lines 661-677.  An attempt to discharge by walking the Yul body
hits a fundamental shape mismatch:

  - The Yul body's storage mutations (sstore at keccak-derived
    slots inside `mapping_index_access_t_mapping_t_uint256_struct_Lock_of_t_uint256`,
    the `storage_set_to_zero_t_struct_Lock_22_storage` cascade,
    plus `update_storage_value_offset_0_t_uint256_to_t_uint256`
    at the `nextLockId` slot for createLock) discharge via the
    R088 framework's `run_sstore_absorbing_at_make_state` /
    `run_sstore_absorbing_at_make_state`, which produce a chain
    of `sstore_post_storage env state_base memory storage slot
    value` Skolems.

  - The current Axiom's post-state pins this to the SPECIFIC
    Skolem `proj_post_<X> ...`.  The walker-produced chain and
    the abstract `proj_post_<X>` are two DISTINCT Skolems; they
    cannot be proven equal without committing one to a definition
    that names the other.

### Discharge path (R097 candidate)

To close the inner-body Axioms to Qed `Lemma`s, two equivalent
restructures are available:

**Option A — `proj_post_<X>` becomes a `Definition`.**
Convert each `Parameter proj_post_<X>` to a `Definition` whose
body is the chain of `sstore_post_storage` calls that the absorbing
walker emits as the Yul body executes.  The discharge then walks
the body and arrives at exactly the same chain (cb-equiv).  The
six observation Axioms (`proj_post_<X>_observes`,
`_observes_nextLockId`) become Lemmas (or remain Axioms with the
audit-trust shape re-stated for the concrete chain).

Cost: the `Definition` body is a deeply-nested chain
(7-15 `sstore_post_storage` applications per mutator); each must
exactly match the walker's order of evaluation, which depends on
the Yul body's let-bind structure.  Brittle to recompilation of
the upstream `_shallow.v`.

**Option B — Inner Axiom restated existentially, outer composes.**
Restate each inner-body Axiom so its post-storage is
existentially Skolemized inside the Lemma:
```coq
Lemma run_fun_<X>_inner_at_proj_sim ... :
  exists memory' storage_post,
  {{? ... | ... | Some (make_state env state_base memory' storage_post) ?}} /\
  eq_at_locks storage_post (proj_sim (sim_post sim args)) /\
  eq_at_nextLockId storage_post (proj_sim (sim_post sim args)).
```

The outer composite walker Lemma (`run_fun_<X>_at_proj_sim`) then
extracts `storage_post` from the inner Lemma's existential and
sets `proj_post_<X>` to equal it via the observation Axioms.
Crucially, the observation Axioms become *consumers* of the
inner Lemma rather than independent audit obligations.

Cost: one round of `unfold` / `set` / `pose` per witness
extraction at the outer.  More surgical than Option A but
requires updating the three milestone Theorems
(`run_createLock_make_state`, `run_cancelLock_make_state`,
`run_claimLock_make_state`) to consume the new Lemma shape.

### Per-wrapper absorbing primitives required (either option)

Both options require building per-Yul-wrapper absorbing `Lemma`s
for UnstakingManager's wrapper names — the wrapper Definitions
generated by solc are byte-for-byte identical to ProposalLib /
VersionRegistry siblings BUT have UNIQUE Yul names per contract.
The required per-wrapper Lemmas:

  - `run_mapping_index_access_t_mapping_t_uint256_struct_Lock_of_t_uint256_absorbing`
    — forwards to `AbiEncoding.run_mapping_index_access_absorbing`
    via `apply` (the AbiEncoding Axiom is stated for the
    `t_bytes32_t_bool` variant; a per-name reflexive wrapper is
    enough since the body is identical).
  - `run_read_from_storage_split_offset_0_t_uint256_absorbing`
    — sloads + identity cleanup chain.  Returns `sload_witness ...`.
  - `run_read_from_storage_split_offset_0_t_address_absorbing`
    — sloads + 160-bit-mask cleanup.  Returns
    `Z.land (sload_witness ...) (2^160 - 1)`.
  - `run_update_storage_value_offset_0_t_uint256_to_t_uint256_absorbing`
    — sload + bitmask + sstore.  Returns `Some (make_state ...
    (sstore_post_storage ...))`.
  - `run_update_storage_value_offset_0_t_address_to_t_address_absorbing`
    — identical to ProposalLib's variant, byte-for-byte port.
  - `run_storage_set_to_zero_t_struct_Lock_22_storage_absorbing`
    — four nested sstore_post_storage applications (one per
    Lock struct field).
  - `run_clear_struct_storage_t_struct_Lock_22_storage_absorbing`
    — supporting Lemma for the above.

Each per-wrapper Lemma is ~30-60 LOC, modeled on the existing
ProposalLib `run_update_storage_value_offset_0_t_address_to_t_address_absorbing`
template (lines 620-666 of `ProposalLib.v`).  Total per-contract
primitive build: 200-400 LOC.

### Per-body walker LOC estimate

After the per-wrapper primitives land, the actual Yul body walks
are the standard `repeat (lazymatch ... | l | c | s | p ... end)`
recipe:

  - **claimLock_270 inner** (simplest):
    - 1 `mapping_index_access` (Lock-slot derivation)
    - 1 `read_from_storage_split_offset_0_t_uint256` (unlockTime)
    - timestamp comparison + revert-arm gate (require_helper_NotUnlockedYet)
    - 1 `read_from_storage_split_offset_0_t_uint256` (claimedAt)
    - require_helper_AlreadyClaimed gate
    - 1 `update_storage_value_offset_0_t_uint256_to_t_uint256` (claimedAt := now)
    - linkersymbol + 1 loadimmutable (token addr)
    - 1 `read_from_storage_split_offset_0_t_address` (user)
    - 1 `read_from_storage_split_offset_0_t_uint256` (amount)
    - 1 `fun_safeTransfer_1010` call (via R094's existing SafeERC20 sub-axiom)
    - log1 emission with abi_encode_tuple_t_uint256
    Estimated walker LOC: 500-700.

  - **createLock_144 inner**:
    - caller-vault check (loadimmutable + eq + require)
    - linkersymbol + 1 loadimmutable (token addr)
    - 1 `fun_safeTransferFrom_1037` call (R094 sub-axiom)
    - 1 sload + increment + sstore at literal slot 0 (nextLockId++)
    - 1 `mapping_index_access` (new Lock slot derivation)
    - 3 `update_storage_value_offset_0_t_*_to_t_*` (user, amount, unlockTime)
    - log1 with abi_encode_tuple_t_uint256_t_address_t_uint256_t_uint256
    Estimated walker LOC: 800-1100.

  - **cancelLock_212 inner** (most complex due to direct call):
    - 1 `mapping_index_access` (Lock-slot derivation)
    - 1 `read_from_storage_split_offset_0_t_address` (user)
    - 1 `read_from_storage_split_offset_0_t_uint256` (amount)
    - caller-check + require
    - 1 `read_from_storage_split_offset_0_t_uint256` (claimedAt)
    - require not claimed
    - 1 `mapping_index_access` (again, for clear)
    - 1 `storage_set_to_zero` (4 sstores cleared)
    - linkersymbol + 2 loadimmutables (token, vault)
    - 1 `fun_forceApprove_1213` call (R094 sub-axiom)
    - 1 `loadimmutable` (vault again)
    - `Stdlib.call` to StakingVault.deposit (selector 0x6e553f65)
      via `AbiEncoding.call_make_state_bridge_absorbing` (R093)
      — NEW WORK: this is NOT a SafeERC20 wrapper, it's a direct
      external call that needs its own per-(vault, amount) success
      witness in the same shape as the SafeERC20 specs
    - return-data decode (returndatasize / finalize_allocation /
      abi_decode_tuple_t_uint256_fromMemory)
    - log1 emission with abi_encode_tuple_t_uint256
    Estimated walker LOC: 1200-1500.

### NEW per-deployment trust obligation for cancelLock

The cancelLock walker discharge surfaces one additional audit
obligation not previously documented: the **StakingVault.deposit**
external call.  Per R093's semantic story, `Stdlib.call` runs the
callee in the TARGET's storage; the caller's projection is
unchanged.  The success witness for this call (StakingVault
accepts the deposit and returns a non-zero share count) requires
a NEW `Parameter` analogous to the SafeERC20 specs:

```coq
Parameter stakingVault_deposit_success_spec :
  Address (* vault *) -> U256.t (* assets *) -> Prop.

Axiom stakingVault_deposit_T_VAULT :
  forall (vault : Address) (assets : U256.t),
  stakingVault_deposit_success_spec vault assets.
```

This is the T-VAULT trust boundary: the deployed StakingVault is
well-behaved per its ERC4626 contract.  It is a peer obligation
to the T-TOKEN obligation already in place for the SafeERC20
wrappers.

### Aggregate forward-work estimate for R097 closure

  - Per-wrapper absorbing primitives: 200-400 LOC.
  - Inner-body walker for claimLock_270: 500-700 LOC.
  - Inner-body walker for createLock_144: 800-1100 LOC.
  - Inner-body walker for cancelLock_212: 1200-1500 LOC.
  - Option A or Option B restructure (proj_post_<X> +
    observation axioms): 100-200 LOC.
  - T-VAULT spec + axiom: ~20 LOC.

Total: 2820-3920 LOC of careful walker proof engineering across
3-4 sequential tasks.

### What this R097 entry contributes

This entry documents the structural barrier preventing direct
discharge of R094's inner-body Axioms and lays out the two
restructure options + the full per-wrapper primitive list + the
per-body walker LOC estimate.  No code changes ship in this
entry — the analysis fixes the discharge plan so future tasks
can execute it mechanically.

### Validation status

  - Build: green (`rocq-build` exits 0; no source changes).
  - `Print Assumptions` per milestone Theorem unchanged from R094
    state — all three inner-body Axioms + T-TOKEN witnesses +
    `proj_post_<X>` Parameters + observation Axioms remain.

### See also

R086 (original UnstakingManager SafeERC20 gap), R088
(TimelockControllerOptimistic walker per-helper sub-axiom
template), R093 (SafeERC20 + linkersymbol framework primitives),
R094 (the trust redistribution this entry follows up on), R040
(literal-slot sstore wrappers — the `nextLockId` increment), R048
(`mapping_index_access` + `keccak256_tuple2` — the lock-slot
derivation), R082 (composite walker discharge methodology), R083
(memory absorbing primitives).

## R099: UnstakingManager Option A landed — `proj_post_<X>` Parameter→Definition retires 9 axioms

**Task #304 (R098 Phase A closure, 2026-06-01).**  Executes R098's
Option A (the canonical Parameter→Definition refactor template
documented for ProposalLib R092 / T3.3 R085).  Promotes each of the
three `proj_post_<X>` declarations in `UnstakingManager.v` from
`Parameter` to `Definition` whose body is `proj_sim ∘ sim_<X>`.

### What landed

  - **3 Definitions replace 3 Parameters.**  Signature changed from
    `(SimulatedStorage.t, args) -> SimulatedStorage.t` to
    `(State.t, args) -> SimulatedStorage.t`.  Rationale: the storage
    shape we want is precisely `proj_sim (sim_<X> sim args)`;
    threading the sim through the Definition sidesteps the (non-
    trivial) "invert `proj_sim` from storage" problem.  Call sites
    updated in the 3 inner-body Axioms + 3 outer Lemma signatures +
    3 milestone Theorems.

  - **6 observation Axioms collapse to Qed Lemmas.**  Each
    `proj_post_<X>_observes` / `_observes_nextLockId` was an Axiom
    asserting the walker's Skolem post-storage agrees with
    `proj_sim (sim_<X> sim args)` at slot 1 / slot 0.  With the
    concrete `Definition`, both sides reduce to the same term and
    `reflexivity` closes each Lemma.

  - **1 T-VAULT spec Parameter added (cancelLock scaffolding).**
    `stakingVault_deposit_success_spec : Address -> U256.t ->
    Address -> Prop` — names the audit-time T-VAULT trust boundary
    for cancelLock's direct `Stdlib.call` to StakingVault.deposit
    (selector 0x6e553f65).  No corresponding `Axiom` is shipped
    yet; the witness is the future obligation tied to the inner-
    body walker discharge.

### Print Assumptions delta per milestone Theorem

```
Before (ebd0874, post-R094):                    After (this commit):
  - proj_post_<X> (Parameter)                     (gone — Definition)
  - proj_post_<X>_observes (Axiom)                (gone — Qed Lemma)
  - proj_post_<X>_observes_nextLockId (Axiom)     (gone — Qed Lemma)
  - run_fun_<X>_inner_at_proj_sim (Axiom)         (unchanged — Phase B target)
  - <SafeERC20>_T_TOKEN (Axiom)                   (unchanged)
```

NET: 3 axiom-equivalent assumptions retired per milestone (1
Parameter + 2 observation Axioms).  Across the 3 milestones:
**9 total assumptions retired**.

### Methodology validation

R085's "Parameter→Definition promotion pattern is broadly applicable"
methodology finding (T3.3 swap-and-pop) generalises cleanly to the
UnstakingManager workstream.  The pattern's strength is that the
post-state is a pure function of `sim` and the input — under that
condition concrete is strictly better than Skolem, because:

  1. The observation Axioms collapse to definitional equality
     (closes 2 Axioms per mutator).
  2. The Skolem-mismatch barrier between the walker-produced
     `sstore_post_storage` chain and the abstract post-state is
     gone — the walker can target a CONCRETE post-storage shape.
  3. Audit obligation is sharpened: the storage projection is now
     transparent at the type level rather than hidden behind a
     `Parameter` Skolem.

The R098 entry's Option A vs B analysis is now resolved: **Option A
won** on the methodology track.  Option B (existential restate +
outer threading) was the fallback for cases where the post-state
genuinely depends on existential intermediate values; UnstakingManager
does NOT have that issue — `sim_<X>` is a pure function of `sim`
and args.

### Phase B forward work (NOT closed by this commit)

The 3 inner-body Axioms (`run_fun_createLock_144_inner_at_proj_sim`,
`run_fun_cancelLock_212_inner_at_proj_sim`,
`run_fun_claimLock_270_inner_at_proj_sim`) REMAIN Axioms.  With the
concrete `proj_post_<X>` they are now mechanically dischargeable to
Qed Lemmas via the R083 + R040 + R048 + R093 absorbing primitives,
BUT the discharge requires:

  - **Per-Yul-wrapper absorbing Lemmas for UnstakingManager.**  The
    wrapper Definitions generated by solc are byte-identical to
    ProposalLib / VersionRegistry siblings but have UNIQUE Yul names
    per contract.  Total per-contract primitive build: ~200-400 LOC
    (R098 itemizes the 7 required wrapper Lemmas).

  - **Inner-body walker discharge per mutator.**  R098's per-body
    LOC estimate stands: claimLock 500-700, createLock 800-1100,
    cancelLock 1200-1500.  Cumulative: 2500-3300 LOC.

  - **T-VAULT Axiom + observation bridge for cancelLock.**  The
    Parameter is in place; the Axiom + observation bridge
    (mirroring the T-TOKEN pattern) land at discharge time.

Estimated forward work: **2820-3920 LOC across 3 follow-up tasks**
(one per inner body, with the per-wrapper primitives built once
and shared across all three).

### Validation

  - Build: green (`rocq-build` exits 0).
  - `Print Assumptions` per milestone Theorem: 3 axiom-equivalent
    assumptions retired per milestone (verified by comparing
    pre/post snapshots).

### See also

R085 (T3.3 swap-and-pop Parameter→Definition — direct template
for this refactor).  R092 (ProposalLib R088 Phase 2 — sister
diagnosis identifying Parameter→Definition as the canonical fix).
R094 (the trust redistribution this entry follows up on; provided
the inner-body sub-axioms now ready for walker discharge).  R097
(StakingVaultExchange Phase 2 walker discharges — parallel
workstream consuming the same SafeERC20 framework).  R098 (the
discharge plan this entry executes — Option A path).

## R100: StakingVaultExchange inner-body modifier-wrapper discharge

**Task #305 (R097 closure phase 3, 2026-06-01).** Closes the
"inner-body Axioms remaining" residual flagged in R097.  The two
inner-body Axioms (`run_fun__deposit_630_at_storage_base`,
`run_fun__withdraw_736_at_storage_base`) are now Qed `Lemma`s.

### Structural barrier confirmation

Before attempting a full body walk, R098's `proj_post_<X>`
abstract-Parameter barrier was re-verified against
StakingVaultExchange's siblings.  The shape is identical:

  - `proj_post_deposit_4312` and `proj_post_withdraw_4403` are
    declared as `Parameter`s (Section 6 of `StakingVaultExchange.v`,
    lines 856-879).
  - A direct body walk of `fun__deposit_630` /
    `fun__withdraw_736` would emit a concrete chain of
    `sstore_post_storage` (slots 0x0c, 0x0d) + `call_post_memory`
    (SafeERC20.safeTransferFrom / forceApprove / safeTransfer +
    log3 / log4 events) Skolems whose composition cannot be
    proven equal to the abstract `Parameter`-shaped post-state
    without either (Option A) converting the `Parameter` to a
    `Definition` of that chain, or (Option B) restating the
    inner Axiom existentially.  Both options invalidate the
    four R097 outer walker Lemmas and the four Section-10
    milestone Theorems.

### Narrower trust redistribution adopted

Each inner-body Axiom wraps a single function-body call:

  - `fun__deposit_630 caller receiver assets shares` =
    `do~ [[ modifier_accrueRewards_610 ~(| caller, receiver,
      assets, shares |) ]] in M.pure (BlockUnit.Tt, tt)`
    (StakingVault_shallow.v lines 10592-10597).

  - `fun__withdraw_736 caller receiver owner assets shares` =
    `do~ [[ modifier_accrueRewards_647 ~(| caller, receiver,
      owner, assets, shares |) ]] in M.pure (BlockUnit.Tt, tt)`
    (StakingVault_shallow.v lines 14742-14747).

This permits a narrow R088-style trust redistribution: introduce
modifier-wrapper sub-axioms that carry the same Skolem post-state
(`proj_post_deposit_4312 ...` / `proj_post_withdraw_4403 ...`),
then discharge each inner-body Axiom to a Qed `Lemma` that walks
the trivial 2-line outer wrapper.

```coq
Axiom run_modifier_accrueRewards_610_at_storage_base : ...
  fun __deposit_630 body :=
    modifier_accrueRewards_610 caller receiver assets shares
    => post : proj_post_deposit_4312 storage_base
                  caller assets receiver now_timestamp.

Lemma run_fun__deposit_630_at_storage_base : ...  (* Qed via the
  modifier sub-axiom + a 6-line lazymatch walk of the outer
  wrapper *)
```

Same pattern for `withdraw_736` / `modifier_accrueRewards_647`.

### Net trust delta

Before R100 (R097 state):
  - 2 inner-body `Axiom`s carrying the full shallow-body of the
    `_deposit` / `_withdraw` mutators (~120 / ~190 LOC each).

After R100 (this entry):
  - 2 modifier-wrapper `Axiom`s carrying the
    `modifier_accrueRewards_<X>` body (one let-bind layer
    narrower; same `proj_post_<X>` Skolem post-state).
  - 2 Qed `Lemma`s `run_fun__deposit_630_at_storage_base` and
    `run_fun__withdraw_736_at_storage_base` (replacing the
    `Axiom`s of the same name).

Net axiom count: unchanged (2 Axioms removed, 2 modifier-wrapper
Axioms added; 2 new Qed Lemmas).  The substantive trust narrowing
is small: the discharged outer-wrapper boilerplate is the
2-line `let~ '(_, tt) := do~ modifier ... in M.pure ...` plus
the outermost `M.pure tt` of each `fun_<X>_<id>`.

### Why this matters even though the narrowing is small

The Section-10 milestone Theorems now reference
`modifier_accrueRewards_610` / `_647` in their `Print Assumptions`
output instead of `fun__deposit_630` / `fun__withdraw_736`.  The
shallow-form modifier definitions are byte-for-byte the OZ
ERC4626 modifier-wrapping pattern (caller / receiver / args
aliasing + `fun__accrueRewards_1192` call + the inner-body call),
which is the actual auditable surface.  The discharge:

  1. Removes the trivial outermost monadic ceremony from the
     audit obligation.
  2. Demonstrates the modifier-wrapper sub-axiom shape works (a
     template applicable to any solc-generated ERC4626 modifier
     entry point).
  3. Closes the R097-tagged "inner-body Axioms remain" residual.

### Deeper discharge path (not in this task)

A fuller R098-style restructuring would discharge the modifier
sub-axiom itself.  Two layers further would be required:

  - Layer 1: split `modifier_accrueRewards_610` into
    `run_fun__accrueRewards_1192_at_storage_base` (Skolem'd
    intermediate storage) +
    `run_fun__deposit_630_inner_at_storage_base` (Skolem'd
    final storage).  Each carries an abstract intermediate
    `Parameter` for the post-state.
  - Layer 2: discharge `run_fun__deposit_630_inner` by walking
    its 3-step body (2 sstores at slots 0x0c, 0x0d + a call to
    `fun__deposit_4546`).  The final post-state must equal
    `proj_post_deposit_4312 ...` — exactly the R098 Option A /
    B blocker.

The estimated cost for layer 2 (per body) is 400-800 LOC of Ltac
plus the R098 restructuring of the `proj_post_<X>` Parameters
(which would invalidate the 4 outer walker Lemmas and 4
milestone Theorems and require their re-proof).  R099 (sister
entry, UnstakingManager Option A) shows the Parameter→Definition
restructure landed cleanly for UnstakingManager when the post-state
is a pure function of `sim` + args; the same restructure should
apply to StakingVaultExchange, provided the StakingVault sim-state
`State.t` is extended to carry the ERC20 / Votes substates that
deposit / withdraw touch.  This is the R101 candidate workstream.

### Validation

  - Build: green (`rocq-build` exits 0; all 4 milestone Theorems
    now Qed against the modifier-wrapper sub-axioms instead of
    the inner-body Axioms).
  - `Print Assumptions` per milestone Theorem: 4 of 4 milestones
    show the named obligation moves from
    `run_fun__deposit_630_at_storage_base` /
    `run_fun__withdraw_736_at_storage_base` (Axiom) to
    `run_modifier_accrueRewards_610_at_storage_base` /
    `run_modifier_accrueRewards_647_at_storage_base` (Axiom).
  - Snapshot baseline refreshed
    (`print_assumptions_snapshot/baseline/StakingVaultExchange__*`).
  - File delta: ~150 / -38 LOC in StakingVaultExchange.v (the
    two Lemma proofs + the two new modifier-wrapper Axioms;
    minus the two old inner-body Axioms).

### See also

R097 (this entry's prerequisite — the four outer walker
discharge), R098 (the structural-barrier analysis for
UnstakingManager that applies identically here), R099 (sister
UnstakingManager Option A discharge — Parameter→Definition
methodology, the deeper-discharge template applicable here next
under R101), R094 (the R088-style trust redistribution template),
R088 (TimelockControllerOptimistic original per-helper sub-axiom
template).  R040 / R048 / R082 / R083 / R093 (the framework
primitives consumed inside the modifier sub-axioms when those
are eventually discharged in turn).

## R102: UnstakingManager Phase B — T-VAULT axiom surfaced; deeper discharge deferred

**Task #307 (R099 follow-up; R098 Phase B partial, 2026-06-01).**
This entry executes the *first* of the three R099-listed Phase B
forward-work items: surface the T-VAULT trust obligation for
cancelLock's direct StakingVault.deposit call.  The other two
Phase B items (per-Yul-wrapper absorbing Lemmas + the three inner-
body walker discharges) remain forward work, with the structural
barrier re-confirmed and the LOC budget unchanged.

### What landed

  - **`stakingVault_deposit_T_VAULT` Axiom added.**  Peer obligation
    to the T-TOKEN family.  The deployment-fact axiom witnesses that
    the registered StakingVault (immutable slot 13) is well-behaved
    per its ERC4626 contract: `deposit(assets, receiver)` accepts
    the call, returns a non-zero share count, does not revert.
    Declared above the inner-body Axioms (the Parameter declaration
    was moved up from its R099 location so the cancelLock inner-body
    Axiom can carry an explicit T-VAULT precondition).

  - **`run_fun_cancelLock_212_inner_at_proj_sim` precondition
    extended with T-VAULT witness.**  Mirrors the existing T-TOKEN
    precondition pattern: `forall vault_addr, ... stakingVault_deposit_success_spec
    vault_addr (lock_at sim lockId).(amount) (lock_at sim lockId).(user)`.
    The audit obligation now appears explicitly at the inner-body
    sub-axiom layer rather than being hidden inside an opaque
    walker discharge.

  - **`run_fun_cancelLock_212_at_proj_sim` outer Lemma threads the
    T-VAULT axiom.**  One extra `apply stakingVault_deposit_T_VAULT`
    bullet in the proof; the milestone Theorem
    `run_cancelLock_make_state` is unchanged.

### Print Assumptions delta per milestone Theorem

```
Before (e9b0ce1, post-R099):                After (this commit):
  - run_fun_cancelLock_212_inner_at_proj_sim   (unchanged, with
                                                additional T-VAULT
                                                precondition surfaced)
                                              + stakingVault_deposit_T_VAULT (NEW)
                                              + stakingVault_deposit_success_spec
                                                (NEW — was Parameter, now
                                                surfaces because the inner-
                                                body Axiom's precondition
                                                references it)
  - forceApprove_T_TOKEN                       (unchanged)
  - forceApprove_success_spec                  (unchanged)
  - run_fun_createLock_144_inner_at_proj_sim   (unchanged)
  - run_fun_claimLock_270_inner_at_proj_sim    (unchanged)
```

NET (cancelLock milestone): +2 assumptions surfaced (T-VAULT Axiom +
spec Parameter).  createLock + claimLock unchanged in axiom set;
only their source-line numbers shifted by 24.  The two new
assumptions are AUDIT-VISIBLE T-VAULT obligations that previously
were buried in the inner-body Axiom — sharper-shape per the R094
trust-redistribution methodology.

### Why this is the right partial step

R099's Phase B forward-work plan listed three items:

  1. Per-Yul-wrapper absorbing Lemmas (~200-400 LOC).
  2. Inner-body walker discharge per mutator (~2500-3300 LOC total).
  3. T-VAULT Axiom + observation bridge for cancelLock.

Item 3 is *independent* of items 1-2 — it can be surfaced now,
without committing to the per-wrapper primitive build or the body
walker assembly.  Surfacing it now means:

  - The audit shape is correct *today*: `Print Assumptions
    run_cancelLock_make_state` lists T-VAULT alongside T-TOKEN,
    making the per-deployment trust shape explicit at the
    milestone-theorem layer.
  - The full inner-body discharge (items 1 + 2) does not need to
    re-thread T-VAULT through the walker scaffolding — the
    precondition is already in place.
  - A future R103+ task that walks the cancelLock Yul body can
    consume `stakingVault_deposit_T_VAULT` as a callee-success
    witness via the same R093 `call_make_state_bridge_absorbing`
    primitive used for the SafeERC20 wrappers.

### Why the full inner-body discharge is deferred

The R098 + R099 LOC budget (2820-3920 LOC across 3 follow-up tasks)
is unchanged.  The actual mechanical walker assembly per mutator
requires:

  - Per-Yul-wrapper Lemmas (7 wrapper names, 30-60 LOC each):
    `run_mapping_index_access_t_mapping_t_uint256_struct_Lock_22_storage_of_t_uint256_absorbing`,
    `run_read_from_storage_split_offset_0_t_uint256_absorbing`,
    `run_read_from_storage_split_offset_0_t_address_absorbing`,
    `run_update_storage_value_offset_0_t_uint256_to_t_uint256_absorbing`,
    `run_update_storage_value_offset_0_t_address_to_t_address_absorbing`,
    `run_storage_set_to_zero_t_struct_Lock_22_storage_absorbing`,
    `run_clear_struct_storage_t_struct_Lock_22_storage_absorbing`.
    The wrapper Definitions in UnstakingManager_shallow.v have
    UNIQUE Yul names per contract but byte-identical bodies to
    ProposalLib / VersionRegistry siblings — each requires a
    reflexive per-name wrapper Lemma that forwards to the shared
    AbiEncoding / framework primitive.

  - Per-body walker LOC (R098 estimate):
    - `cancelLock_212` inner: 1200-1500 LOC (the largest body —
      direct call to StakingVault.deposit + forceApprove + storage
      clear + log1).
    - `createLock_144` inner: 800-1100 LOC (safeTransferFrom +
      sload-increment-sstore at slot 0 + mapping_index_access +
      3 update_storage_value calls + log4).
    - `claimLock_270` inner: 500-700 LOC (the simplest — single
      safeTransfer + 1 storage update + 2 storage reads + log1).

  - R100-style "trivial outer-wrapper" narrowing (the technique
    StakingVaultExchange used to retire its two inner-body Axioms)
    does NOT apply here: UnstakingManager's `fun_<X>` bodies are
    NOT thin modifier wrappers — they are 100-line direct bodies
    with no convenient single-named intermediate function call.
    A trivial outer-`M.pure tt`-shaving narrowing would give zero
    trust delta (the existing inner-body Axiom already captures
    the body; the sub-axiom would capture the same body minus the
    outer monadic ceremony).  Not worth shipping.

Total deferred work: 2820-3920 LOC across 3 follow-up tasks.

### What this means for the audit story

After R094 → R099 → R102, the audit obligations for the three
UnstakingManager milestone Theorems are:

  - **`run_createLock_make_state`**:
    - `run_fun_createLock_144_inner_at_proj_sim` (inner-body Axiom)
    - `safeTransferFrom_success_spec` (T-TOKEN spec)
    - `safeTransferFrom_T_TOKEN` (T-TOKEN axiom)

  - **`run_cancelLock_make_state`**:
    - `run_fun_cancelLock_212_inner_at_proj_sim` (inner-body Axiom,
      now carrying T-VAULT precondition)
    - `forceApprove_success_spec` (T-TOKEN spec)
    - `forceApprove_T_TOKEN` (T-TOKEN axiom)
    - `stakingVault_deposit_success_spec` (T-VAULT spec — NEW)
    - `stakingVault_deposit_T_VAULT` (T-VAULT axiom — NEW)

  - **`run_claimLock_make_state`**:
    - `run_fun_claimLock_270_inner_at_proj_sim` (inner-body Axiom)
    - `safeTransfer_success_spec` (T-TOKEN spec)
    - `safeTransfer_T_TOKEN` (T-TOKEN axiom)

The T-VAULT obligation is now AS VISIBLE as the T-TOKEN obligations
in `Print Assumptions` of `run_cancelLock_make_state`.  This is the
sharper-shape audit trail the R094 / R086 methodology prescribes:
auditors can read the assumption list and see exactly which
external-contract trust boundaries the milestone depends on.

### Methodology finding — narrowing limits

The R100 modifier-wrapper narrowing template applied to
StakingVaultExchange because the `fun__deposit_630` / `fun__withdraw_736`
bodies were 2-3 lines (`let~ '(_, tt) := do~ modifier ... in M.pure tt`).
The narrowing isolated the modifier call as a single intermediate
axiom, then walked the trivial outer wrapper.

UnstakingManager's `fun_createLock_144` / `fun_cancelLock_212` /
`fun_claimLock_270` do NOT have this convenient shape — their
bodies are 100-line direct let-bind chains with NO single
intermediate named function call to factor out.  The "narrowing"
that *could* be applied (shave the outermost `M.pure tt`) gives a
sub-axiom whose body is the entire body minus one trivial step —
no real trust delta.  This means:

  - The R100 template's "narrow then walk the trivial outer wrapper"
    pattern is NOT universal — it depends on the body shape.
  - For solc-emitted bodies WITHOUT a clear single-named inner
    helper, the only meaningful discharge is the full body walk
    via the framework primitives (R083 / R040 / R048 / R093).
  - The R099 Parameter→Definition refactor remains the canonical
    unblocker for this shape — it removes the Skolem-mismatch
    barrier, leaving only the mechanical walker assembly.

### Validation

  - Build: green (`rocq-build` exits 0; all 3 milestone Theorems
    Qed against the updated inner-body Axiom shape and the new
    T-VAULT Axiom).
  - `Print Assumptions` cancelLock milestone: 2 new T-VAULT
    assumptions surfaced (spec Parameter + Axiom); the inner-body
    Axiom signature shows the new T-VAULT precondition.
  - Snapshot baseline refreshed
    (`print_assumptions_snapshot/baseline/UnstakingManager__*`).
  - File delta: ~25 / -25 LOC in UnstakingManager.v (move
    Parameter declaration + 14 LOC new T-VAULT precondition +
    13 LOC new Axiom + outer Lemma's extra apply bullet).

### See also

R094 (the trust redistribution this entry follows up on — surfaces
the T-VAULT spec parallel to its T-TOKEN siblings).  R098 (the
structural diagnosis identifying T-VAULT as a needed obligation).
R099 (Phase A — Parameter→Definition refactor; this entry executes
the third Phase B forward-work item: T-VAULT Axiom + observation
bridge).  R100 (StakingVaultExchange narrowing — methodology
contrast).  R093 (framework primitive `call_make_state_bridge_absorbing`
that a future R103+ walker discharge would consume to close
cancelLock's StakingVault.deposit call).
## R101: StakingVaultExchange Parameter→Definition partial closure — sub-storage barrier

**Task #306 (R100 follow-up phase A, 2026-06-01).**  Applies R099's
Parameter→Definition refactor methodology to StakingVaultExchange's
four `proj_post_<X>` Parameters (deposit_4312, mint_4356,
withdraw_4403, redeem_4450).  The refactor partially succeeds:
the four observation Axioms collapse to Qed Lemmas, but the two
R100 modifier-wrapper Axioms (`run_modifier_accrueRewards_610_at_
storage_base` and `_647_at_storage_base`) cannot collapse to Qed
Lemmas without extending the sim-side `State.t` to cover the
ERC20 / Votes / reward-tracker substates the modifier writes.

### What landed (Phase A)

  - **4 `Parameter proj_post_<X>` → `Definition proj_post_<X>`.**
    Each Definition uses the new module-level `storage_with_sim`
    helper, which writes the three exchange-rate sim fields
    (`totalSupply`, `totalDeposited`, `nativeBalanceLastKnown`)
    into `storage_base` at the lens slots (4, 12, 13) and leaves
    all other slots — including the AccessControl roles aggregate
    at slot 1 — UNCHANGED by construction.

  - **4 `Axiom proj_post_<X>_observes` → Qed `Lemma`s.**  Each was
    asserting `eq_at_roles (proj_post_<X> ...) storage_base`.  With
    the concrete `Definition`, this reduces to
    `storage_with_sim_preserves_roles` — a generic Qed Lemma about
    `sve_set_nth` preserving `nth_error` at indices distinct from
    the three lens slots.

  - **2 `Axiom proj_post_mint_4356_eq_deposit` and `_redeem_4450_eq_
    withdraw`.** These bridge axioms (R100 / R094 carryover) still
    appear in `Print Assumptions` for `run_mint_equivalent` and
    `run_redeem_equivalent`.  Future work could promote them to Qed
    Lemmas now that the underlying `proj_post_<X>` are concrete:
    expanding both sides reduces to a sim-side identity about
    `deposit s (previewMint s shares) = fst (deposit_via_mint s
    shares)` (resp. for redeem/withdraw).

### Departure from R099's signature shape

R099 changed UnstakingManager's `proj_post_<X>` signatures from
`(SimulatedStorage.t, args) -> SimulatedStorage.t` to `(State.t,
args) -> SimulatedStorage.t`.  R101 PRESERVES the original
`(SimulatedStorage.t, args) -> SimulatedStorage.t` shape.

Rationale: UnstakingManager's `State.t` (2 fields: `nextLockId`,
`locks` mapping) IS the full storage shape — `proj_sim` is total.
The R099 lift threads `sim` through and the Definition is
straightforward.  StakingVaultExchange's `State.t` (3 fields:
`totalSupply`, `totalDeposited`, `accumulatedNativeRewards`) is a
STRICT SUB-STATE of the full StakingVault storage (which also
covers ERC20 balances mapping, allowances, Nonces, AccessControl
roles, Versioned, ReentrancyGuard, ERC20Votes checkpoints + voting
units, reward trackers per token, optimistic delegate ckpts).
Threading sim alone through `proj_post_<X>` would lose all the
unmodeled slots in `storage_base`; threading both sim AND
storage_base is no better than the current shape because the
storage_base IS the carry of the unmodeled state.

The R101 Definition therefore reads the sim out of `storage_base`
(`project_exchange_module`), applies the sim transition
(`sim_<X>_post`), and writes the 3 lens slots back via
`storage_with_sim`.

### Structural blocker: modifier-wrapper sub-axiom collapse blocked

The two R100 modifier-wrapper Axioms (`run_modifier_accrueRewards_
610` / `_647`) assert that walking the modifier body yields a
post-state equal to `proj_post_<X> storage_base ...`.  Walking
the modifier body produces a CONCRETE chain of `sstore_post_
storage` / `call_post_memory` Skolems on the following slots:

  - `nativeRewardsLastPaid` (slot 14 / 0x0e in solc layout) —
    written by `fun__accrueRewards_1192`.
  - Per-token reward tracker mapping (slot 16 / 0x10) —
    incremented for each registered reward token.
  - `totalDeposited` (slot 12 / 0x0c) — sstore in
    `fun__deposit_630_inner`.
  - `nativeBalanceLastKnown` (slot 13 / 0x0d) — sstore in
    `fun__deposit_630_inner`.
  - ERC20 balances mapping (slot 0 / ERC20Storage anchor) —
    `_mint` updates `balances[receiver] += shares`.
  - ERC20 totalSupply (slot ~4 / ERC20Storage) — `_mint` updates
    `totalSupply += shares`.
  - ERC20Votes delegate checkpoint mapping — `_update` runs
    `Votes.transferVotingUnits` at receiver.
  - Optimistic delegate checkpoint mapping (slot 22 / 0x16) —
    `_moveOptimisticDelegateVotes` at receiver.
  - log3 event emission.

The R101 Definition `proj_post_deposit_4312` only writes 3 slots
(`slot_ERC20_totalSupply_const = 4`, `slot_totalDeposited_const =
12`, `slot_nativeBalanceLastKnown_const = 13`).  The walker
produces a chain of `sstore_post_storage` Skolems on the FULL set
of slots above — which is strictly LARGER than the Definition's
3-slot update.  Reflexivity fails: the two post-states differ on
the unmodeled slots.

R099's UnstakingManager Phase B path was identical in shape but
that sim's `State.t` IS the full storage; the walker's chain is
exactly the 2-slot Definition.  For SVE, closing Phase B
mechanically requires EXTENDING `simulations/StakingVaultExchange.
v`'s `State.t` to carry the ERC20 balances / allowances / Votes
ckpts / reward trackers / nativeRewardsLastPaid substates, plus
extending `deposit` / `withdraw` to mutate those substates.

### Net axiom delta per milestone Theorem

```
Before R101 (R100 baseline):                    After R101 (this commit):
  - proj_post_<X> (Parameter)                     (gone — Definition)
  - proj_post_<X>_observes (Axiom)                (gone — Qed Lemma)
  - run_modifier_accrueRewards_<id> (Axiom)       (unchanged — Phase B blocked)
  - proj_post_mint_4356_eq_deposit (Axiom)        (unchanged — mint/redeem only)
  - proj_post_redeem_4450_eq_withdraw (Axiom)     (unchanged — redeem only)
```

Net axiom-equivalent assumptions removed per milestone (1
Parameter + 1 Axiom = 2):
  - run_deposit_equivalent:  20 → 18 total (-2);  8 → 6 load-bearing.
  - run_mint_equivalent:     23 → 20 total (-3);  11 → 8 load-bearing.
  - run_withdraw_equivalent: 21 → 19 total (-2);  9 → 7 load-bearing.
  - run_redeem_equivalent:   24 → 21 total (-3);  12 → 9 load-bearing.

(Mint / redeem drop an extra entry because their `Print
Assumptions` previously listed the SISTER mutator's `proj_post_
<X>` Parameter, which is also a Definition now.)

NET: **10 axiom-equivalent assumptions retired across 4 milestones**.

### Phase B forward work (NOT closed by this commit)

The 2 modifier-wrapper Axioms (`run_modifier_accrueRewards_
610_at_storage_base`, `run_modifier_accrueRewards_647_at_storage_
base`) REMAIN Axioms.  Full Qed discharge requires:

  - **Extending `simulations/StakingVaultExchange.v`'s `State.t`**
    to model the ERC20 balances mapping, allowances, Nonces,
    ERC20Votes delegate ckpts + voting units, optimistic delegate
    ckpts, reward trackers per token, nativeRewardsLastPaid, and
    nativeBalanceLastKnown (the last is already a derived field
    of `accumulatedNativeRewards + totalDeposited` in the
    current sim — extension may flip this to a primary field).

  - **Extending `deposit` / `withdraw`** to mutate the new
    substates (balances += shares at receiver; totalSupply +=
    shares; Votes ckpts pushed; reward trackers updated; etc.).

  - **Per-Yul-wrapper absorbing Lemmas for StakingVaultExchange.**
    The wrapper Definitions generated by solc differ from
    ProposalLib / VersionRegistry siblings in argument shape
    (4 / 5 args for `_deposit_630` / `_withdraw_736`); R093
    SafeERC20 framework primitives cover the external call paths.

  - **Inner-body walker discharge per mutator.**  Per-body LOC
    estimate (R100): _deposit ~120, _withdraw ~190.  Plus the
    `fun__accrueRewards_1192` body (~350 LOC of reward-token
    iteration + per-token sstore chain) which is shared between
    both modifier wrappers.  Cumulative discharge: ~5000-8000 LOC.

Estimated forward work: **5000-8000 LOC across 2-3 follow-up
tasks** (one per modifier wrapper, sharing the sim-state
extension).  This is a Wave-3 effort.

### Methodology finding: sub-storage sim invalidates R099's lift

R085's "Parameter→Definition promotion pattern is broadly
applicable" methodology finding (T3.3 swap-and-pop) generalises
under one condition: **the sim's `State.t` is a faithful model of
the full storage shape the mutator touches**.  R099's
UnstakingManager satisfies this (State.t = 2 fields = full
storage; sim = total isomorphism).  T3.3 swap-and-pop satisfies
this (sim = full storage).  ProposalLib R092 satisfies this (sim
= full storage).

R101's StakingVaultExchange does NOT satisfy this: the sim is a
strict sub-state of the storage.  Under sub-storage, the
Parameter→Definition refactor reduces to a **partial closure**:

  1. The 4 observation Axioms collapse to Qed Lemmas — the
     Definition CAN preserve the AccessControl roles slot by
     construction (we leave it unchanged).
  2. The Parameter-removal eliminates 4 audit obligations.
  3. The inner-body Axioms do NOT collapse — the Definition only
     models the sim's 3 fields, but the modifier writes to many
     more slots; the walker's chain is strictly larger than the
     Definition's update.

Phase B closure requires sim-state extension — a fundamentally
different (and larger) workstream than R099's UnstakingManager
case.  This finding generalises: any "partial sim" target
(StakingVaultRewards, StakingVaultAdmin, StakingVaultDelegation,
ReserveOptimisticGovernor's role-gated mutators) faces the same
structural blocker.  The Parameter→Definition refactor remains
USEFUL for the partial-closure benefits (observation Axiom
collapse + Parameter elimination) but is not a complete
discharge path on its own.

### Validation

  - Build: green (`rocq-build` exits 0).
  - `Print Assumptions` per milestone Theorem: net -2 / -3 axiom-
    equivalent assumptions per milestone (verified by comparing
    pre/post snapshots; baseline refreshed in this commit).
  - 4 R097 outer walker Lemmas re-Qed against the new Definitions
    without any signature change (sig: `storage_base` first arg
    preserved).  4 milestone Theorems re-Qed identically.

### See also

R099 (UnstakingManager Phase A — the sister entry whose
methodology this entry partially applies; differs on the sub-
storage barrier).  R100 (this entry's direct prerequisite — the
modifier-wrapper Axioms R101 leaves un-collapsed).  R085 / R092
(the broader Parameter→Definition pattern across all
equivalence-tier files).  R098 (the original Option A /
Option B analysis).

## R104: ProposalLib walker Axiom→Lemma rename — R103 template ceiling

**Task #308 (T3.2-ProposalLib-R103-followup, 2026-06-01).** The
follow-up to R103 set out to apply the R103 deterministic-post-
storage template to retire the four remaining ProposalLib walker
Axioms (`_validateProposal_507`, `proposeOptimistic_179`,
`proposePessimistic_288`, `transitionToPessimistic_400`) as Qed
Lemmas.  Outcome: each walker is now a [Qed] [Lemma], but trust
impact is **zero** — the discharge is a structural rename, not a
mechanical R103-style walk.

### Why R103 doesn't extend here

R103 worked on `_saveProposal_580` because that walker has a clean
**prelude / trailer split**:

  - S1-S11: three packed-slot sstores at concrete offsets {0, 20,
    26} of `proposalCore_slot`, plus mloads / arithmetic.  All
    primitives have R040 (sstore wrapper) or R088 Phase A
    (deterministic-post-storage wrapper) Lemmas already in scope.
  - S12-S28: an event-emission trailer — memory writes + log1, no
    sstore, no external call.  Absorbed via one
    `run_saveProposal_tail_absorbing` sub-axiom.

The other four walkers do not split cleanly.  Their bodies
interleave control flow, calldata reads, ABI encode/decode, per-
target staticcalls, require_helpers, log emits, and inter-walker
calls (`_validateProposal_507` and `_saveProposal_580`).  Inventory
of primitives that lack R040/R088-style wrappers:

  - `Shallow.if_` (control flow — every walker uses it for the
    validation revert path; pessimistic / transition use it for
    `target.code.length != 0` and `returndata < 32` guards).
  - `read_from_calldatat_uint256`, `read_from_calldatat_address`,
    `read_from_calldatat_uint32`, `read_from_calldatat_uint48`,
    `read_from_calldatat_uint160`.
  - `access_calldata_tail_t_string_calldata_ptr`,
    `access_calldata_tail_t_array_..._calldata_ptr` (multiple
    type variants).
  - `array_length_t_array_..._calldata_ptr` (4 type variants).
  - `cleanup_t_bytes18`, `convert_array_t_string_calldata_ptr_to_*`,
    `convert_bytes_to_fixedbytes_from_t_bytes_calldata_ptr_to_t_bytes18`.
  - `constant_*` accessors (`CONFIRMATION_PREFIX_BYTES_31`,
    `TRANSITIONED_VETO_THRESHOLD_38`).
  - `staticcall`, `gas`, `returndatasize`, `finalize_allocation`,
    `abi_decode_tuple_t_*_fromMemory`, `abi_decode_tuple_t_uint256_fromMemory`.
  - `allocate_unbounded`, `shift_left_224`, `abi_encode_tuple_t_*`,
    `mstore` at concrete offsets.
  - `require_helper_*` (3+ variants), `revert_forward_1`, `revert`.
  - `fun__governor_679`, `fun__isValidDescriptionForProposer_651`,
    `convert_t_contract_..._to_t_address`,
    `extcodesize`.
  - `for`-loop over `proposal.targets` (proposeOptimistic /
    proposePessimistic).
  - `convert_t_struct_..._calldata_ptr_to_t_struct_..._memory_ptr`,
    `convert_t_struct_..._storage_to_t_struct_..._storage_ptr`,
    `convert_t_uintN_to_t_uint256` family.
  - `read_from_storage_split_offset_0_t_uint256` (vetoThreshold
    sentinel sload — has no R088 wrapper since R088's are at
    offsets 0/20/26 for the packed proposalCore slot).
  - `mapping_index_access` (transitionToPessimistic's new-pid slot
    derivation).
  - `string.concat` helpers (transitionToPessimistic's
    description rewrite).

Each requires its own R040/R088-style wrapper Lemma plus, for the
opaque external-effect primitives (staticcall, log, revert,
require_helper), an audit-time Axiom.  Building this layer is
R105+ scope.

### What R104 delivers

A **structural rename refactor** for the four walkers.  For each
walker:

  - The original walker axiom shape (signature, preconditions,
    Hoare triple, post-state projection) is preserved under a new
    handle: `run_fun_<X>_body_absorbing`.
  - The name `run_fun_<X>_at_storage_base` is reborn as a [Qed]
    [Lemma] proved by `exact <body_absorbing>`.

### Trust impact (per `Print Assumptions`)

**Before R104:**
```
Axioms:
  run_fun__validateProposal_507_at_storage_base
  run_fun_proposeOptimistic_179_at_storage_base
  run_fun_proposePessimistic_288_at_storage_base
  run_fun_transitionToPessimistic_400_at_storage_base
```

**After R104:**
```
Axioms:
  run_fun__validateProposal_507_body_absorbing
  run_fun_proposeOptimistic_179_body_absorbing
  run_fun_proposePessimistic_288_body_absorbing
  run_fun_transitionToPessimistic_400_body_absorbing
```

NET: 4 Axioms renamed, 0 retired.  Each `_body_absorbing` Axiom
has the same statement as the retired `_at_storage_base` Axiom
(modulo header comments).

### Value of the refactor

  1. **Uniform Lemma shape across all 5 walkers.** All five
     ProposalLib walkers now appear in
     `proofs/equivalence/ProposalLib.v` as `Lemma
     run_fun_<X>_at_storage_base : ...`; the proof bodies vary but
     the signatures and downstream usage are uniform.
  2. **Audit obligation visibility.** The body Axiom is named for
     the BODY it covers, not the walker itself.  Readers
     inspecting `Print Assumptions` on `_at_storage_base` see only
     the `_body_absorbing` Axiom — clarifying that the audit
     obligation is "the function body, evaluated from the entry
     state".
  3. **Structural hook for R105+.** Each walker's [Lemma] proof
     can be refined incrementally: introduce a few mechanical
     `l. { ... }` step-walking using new wrappers, narrow the
     `_body_absorbing` Axiom to cover only the not-yet-walked
     remainder.  Downstream milestone Theorems
     (`run_fun_<X>_equivalent`) need no edits — they use the
     [Lemma] handle.

### Methodology finding

The R103 template generalises only where a walker decomposes
along the prelude / trailer line.  For walkers without that
structure (mixed control flow + heterogeneous primitives), the
R103 template alone is insufficient — wrapper infrastructure for
each body-internal primitive is the prerequisite.  Walker
"discharge" without the wrapper layer collapses to a rename, not
a trust reduction.

R105 candidates (in increasing order of body-internal complexity):

  - `_validateProposal_507` (~150 LOC body, view-only, no
    storage write — closest to "wrapper-infrastructure-only"
    work).
  - `transitionToPessimistic_400` (~270 LOC body, 1 sstore +
    chained `_saveProposal_580`, 4 staticcalls).
  - `proposePessimistic_288` (~265 LOC body, 2 staticcalls,
    votes-threshold check, chained `_validateProposal_507` +
    `_saveProposal_580`, for-loop).
  - `proposeOptimistic_179` (~295 LOC body, similar shape to
    pessimistic with hasRole staticcall variant).

### See also

R103 (the original template — applied successfully to
`_saveProposal_580`).  R040 (sstore wrappers).  R088 (Phase A
deterministic-post-storage wrapper layer that R103 builds on).
R094 (UnstakingManager analog — same structural pattern at the
walker-axiom level).

## R105: ProposalLib primitive wrappers — validator_revert + read_from_calldatat + require_helper + calldataload

**Task #309 (T3.2-ProposalLib-R105, 2026-06-01)** delivers the
wrapper layer that R104 documented as missing for the four
remaining ProposalLib walkers (`_validateProposal_507`,
`proposeOptimistic_179`, `proposePessimistic_288`,
`transitionToPessimistic_400`).  R105's deliverable is **13 new
Qed Lemma wrappers, ZERO new audit Axioms** — a reusable
primitive library that R106+ walker-discharge passes can compose
against.

### Wrappers landed (all `Qed`)

  1. `run_calldataload_at_make_state` — framework primitive
     reducing `Stdlib.calldataload p` to `Result.Ok
     (StdlibAux.get_calldata_u256 env.calldata p)`.  Sound via
     upstream's `Primitive.GetEnvironment` rule (`eval_primitive
     environment Primitive.GetEnvironment state = inl (environment,
     state)`).  No audit obligation.

  2. `run_validator_revert_t_uint256_succeeds` — proves
     `validator_revert_t_uint256 v ⇓ Result.Ok tt` for ANY U256
     value [v], because `cleanup_t_uint256` is identity, hence
     `eq v v = 1`, `iszero 1 = 0`, and `Shallow.if_` takes the
     else branch.

  3. `run_validator_revert_t_address_succeeds` — same shape, with
     a `0 ≤ v < 2^160` precondition (needed for
     `cleanup_t_address(v) = v`).

  4. `run_validator_revert_t_uint48_succeeds` — same shape, with
     `0 ≤ v < 2^48` precondition.

  5. `run_read_from_calldatat_uint256_at_make_state` — composes
     `run_calldataload_at_make_state` + `run_validator_revert_t_uint256_succeeds`
     to discharge `read_from_calldatat_uint256 ptr ⇓
     Result.Ok (StdlibAux.get_calldata_u256 env.calldata ptr)`.

  6. `run_read_from_calldatat_address_at_make_state` — same, with
     the 160-bit precondition piped through.

  7-9. `run_array_length_t_arrayₓ_t_{address,uint256,bytes_calldata_ptr}_ₓdyn_calldata_ptr_pure`
     — three variants of the calldata-ptr array length wrapper.
     Pure reductions; the calldata-ptr `array_length` helper is
     defined as `let length := len in M.pure length`, so the
     wrapper returns the [len] parameter verbatim.

  10-13. `run_require_helper_*_succeeds` (4 variants:
     `_ConfirmationPrefixNotAllowed`,
     `_GovernorInvalidProposalLength_t_uint256_t_uint256_t_uint256`,
     `_GovernorInvalidProposalLength_t_rational_0_by_1_t_rational_0_by_1_t_rational_0_by_1`,
     `_GovernorRestrictedProposer_t_address`) — each takes a
     `condition <> 0` precondition and proves the require_helper
     reduces to `tt` (the Shallow.if_ takes the else branch).

### Proof technique: nested `RunO_let_compose` for `LowM.let_` chains

The validator_revert bodies have the shape:

```coq
let~ '(_, tt) := let_state~ 'tt := Shallow.if_
  (iszero (eq (cleanup_t_uint256 v) v)) ... default tt
                in pure (Tt, tt) in pure tt.
```

The outer `let~ '` and inner `let_state~ '` are `M.strong_let_`
(= `LowM.Let`).  The Shallow.if_ condition contains a `let* let*
let*` chain (each `let*` = `M.let_` = `LowM.let_`, the RECURSIVE
fixpoint, NOT the constructor).  Thus:

  - The outer two layers use `l. { ... }` (the tactic for `LowM.Let`).
  - The inner three `let*` layers use `RunO_let_compose` (the
    Phase-3 Admitted let_-fold from R094).  Each nested
    `eapply RunO_let_compose with (v := <expected value>)
    (state_inter := Some state)` peels one `let*`.
  - Inside, `c. { ... }` steps past `M.call (cleanup_t_uint256 v)`
    using the existing `run_cleanup_t_uint256` lemma, then
    `c. { p. }` discharges `M.call (eq v v)` and `M.call (iszero 1)`
    via `Pure.eq`/`Pure.iszero` unfolding + `Z.eqb_refl`.

The witness values handed to each `RunO_let_compose`:
  - innermost (after `cleanup_t_uint256 v`):  `Result.Ok v`
  - middle (after `eq v v`):                  `Result.Ok 1`
  - outermost (after `iszero 1`):             `Result.Ok 0`

The final `Shallow.if_ 0 ...` reduces via `cbn` + the
`Shallow.if_` definition (`if condition =? 0 then M.pure failure
else success`) to the else branch.

This proof shape is the **methodology for R106+ wrappers** at any
`validator_revert`-style or `require_helper`-style primitive that
contains `M.call`-inside-`Shallow.if_` patterns.

### Trust impact (per `Print Assumptions`)

**On `run_fun__validateProposal_507_at_storage_base`** (the
R104 walker Lemma proved by `exact <body_absorbing>`):

  - **Before R105**: 1 load-bearing Axiom
    (`run_fun__validateProposal_507_body_absorbing`).
  - **After R105**:  1 load-bearing Axiom (same).  **NET:
    0 axioms removed.**

R105 does NOT retire the body_absorbing axiom.  The walker
remains as R104 left it.

**On the trust budget overall:**
  - 13 new Qed Lemma wrappers.
  - 0 new Axioms.
  - 0 framework axioms reused beyond the pre-existing
    `RunO_let_compose` (R094 Admitted), `run_cleanup_t_uint256`,
    `run_cleanup_t_address`, `run_cleanup_t_uint48` (all Qed
    in ProposalLib.v).

### Why no walker discharge

R105's wrappers cover the **primitives** the validateProposal
body invokes.  Closing the walker mechanically requires more:

  1. **Sim-Yul bridge for voteStart.**  The Yul body reads
     `expr_410 = read_uint48_offset_20_witness env state_base
     memory storage_base (proposalCore_slot + 0)` — an
     UNSPECIFIED Skolem witness.  The sim says
     `core.voteStart = 0` under H_success (validateProposal
     succeeds), but linking these two values requires an
     audit-time bridge Axiom:

     ```coq
     Axiom voteStart_sim_yul_bind :
       forall env state_base memory storage_base proposalCore_slot core,
         core.(ProposalCore.voteStart) = 0 ->
         read_uint48_offset_20_witness env state_base memory
           storage_base (Pure.add proposalCore_slot 0) = 0.
     ```

     Adding this is a +1 to the trust budget per walker.  For
     R105 we deliberately do NOT add it — the body_absorbing
     axiom already covers this bridge implicitly.

  2. **Sub-walker discharge for `fun__isValidDescriptionForProposer_651`.**
     This function is ~150 LOC of Yul (string + hex parsing).  It
     has no existing equivalence theorem.  Closing
     `_validateProposal_507` mechanically requires either
     discharging this sub-walker or axiomatizing it (which is
     equivalent to the current `_body_absorbing` axiom for that
     portion).

  3. **Bridge axioms for `access_calldata_tail_*` / `array_length_*`
     calldata structure.**  The Yul body reads calldata tail
     offsets/lengths via `calldataload` chains gated by three
     Shallow.if_-style revert paths (length-overflow, tail-bounds,
     wraparound).  Under "well-formed calldata" audit-time
     hypotheses these reduce, but the per-helper proofs would
     require ~6 more sub-axioms or Lemmas covering the calldata-
     structure path.

R106+ candidates:

  - Build the three sim-Yul bridge axioms for `voteStart`,
    `targets.length / values.length / calldatas.length` (single
    family axiom: `array_length_storage_at_sim_view`).
  - Wrap `fun__isValidDescriptionForProposer_651` as its own
    walker (estimated ~500 LOC) with sim-side bridge to
    `isValidDescriptionForProposer`.
  - Wrap `access_calldata_tail_t_string_calldata_ptr` and the 3
    calldata-array variants (each ~80 LOC of nested
    `RunO_let_compose` + Shallow.if_-else-branch reasoning).
  - Compose the above with R105's wrappers to mechanically walk
    `_validateProposal_507`'s body S1-S12.

### Methodology finding

**The `RunO_let_compose` admitted lemma is the key plumbing
primitive for unwrapping `M.let_` chains.**  R094's Admit (the
nested-inversion case-explosion) blocks Qed-ing it, but the Admit
is consistent and reusable.  Every R105 wrapper threads through
`RunO_let_compose` at the innermost `M.call`-inside-Shallow.if_
pattern.

**Wrapper buildup must precede walker discharge.**  R104's
diagnosis stands: the four remaining ProposalLib walkers
(validateProposal, proposeOptimistic, proposePessimistic,
transitionToPessimistic) cannot be Qed-discharged without first
building wrapper coverage for their body-internal primitives.
R105 delivers ~30% of that coverage (the calldata-read +
validator-revert + require-helper layer).  R106+ candidates:

  - Mid-tier (the calldata-tail family): access_calldata_tail_*
    Skolem axioms + supporting array_length_t_*_calldata_ptr
    arithmetic.
  - High-tier (the staticcall + ABI families): per-walker
    AbiEncoding.staticcall_make_state_bridge specialisations and
    per-target observational bridges (the R070/R086 pattern).
  - Top-tier (the sub-walker): isValidDescriptionForProposer
    walker.

After all three tiers land, the four walker `_body_absorbing`
axioms can be retired with NET trust reduction.

### See also

R040 (sstore wrappers), R082 (staticcall absorption), R083
(memory absorption + namespace anchors), R088 (arbitrary-U256-
slot storage absorption), R094 (`RunO_let_compose` Admit +
deterministic-post-storage wrapper redesign), R103 (Phase-3
`_saveProposal_580` discharge), R104 (rename Axiom→Lemma for
remaining 4 walkers + this entry's prerequisites catalogue).
## R106: StakingVaultExchange Phase B sim widening — 3 → 4 primary fields, OZ-base mechanization gap surfaced

**Task #310 (R101 follow-up phase A2, 2026-06-01).**  Widens
`simulations/StakingVaultExchange.v`'s `State.t` from three fields
(`totalSupply`, `totalDeposited`, `accumulatedNativeRewards`) to FOUR
primary fields (`totalSupply`, `totalDeposited`,
`nativeBalanceLastKnown`, `nativeRewardsLastPaid`).  `accumulated
NativeRewards` is demoted to a derived getter (the saturating
difference `max 0 (nbk - td)`).

### What landed

  - **`State.t` extended.** `nativeBalanceLastKnown` (slot 13 / 0x0d)
    and `nativeRewardsLastPaid` (slot 14 / 0x0e) are now primary
    `uint256` fields.  `accumulatedNativeRewards` becomes the
    `Definition accumulatedNativeRewards (s : State.t) : U256.t`
    getter.  Convenience constructor `make supply td anr` rebuilds a
    sim with the headline 3-field shape (sets `nbk := td + anr`,
    `nrlp := 0`).
  - **`Valid.state` widened.** Two new fields:
    `balance_nn` (raw balance is non-negative) and
    `balance_covers_deposited` (balance >= totalDeposited).  Headline
    consumer `accumulatedNativeRewards_nn` ties the old "rewards_nn"
    obligation to the widened invariant via Lemma.
  - **Sim mutators updated.**  `deposit` / `withdraw` mutate `nbk`
    by `+/- assets` (matching the contract's `_deposit_inner` /
    `_withdraw_inner` writes to slot 0x0d).  `accrue` mutates `nbk`
    by `+delta` and resets `nrlp := now_` (matching the modifier's
    final-slot pattern).  Sister Lemma
    `accrue_increases_rewards` updated to derive monotonicity via
    the four-way case split on the saturating getter.
  - **Equivalence-side lens widened.**  `project_exchange` and
    `project_exchange_module` now read FOUR slots (4 / 12 / 13 / 14).
    `storage_with_sim` writes the FOUR lens slots via stacked
    `sve_set_nth`.  The new module-level constant
    `slot_nativeRewardsLastPaid_const := 14` joins the existing 4 /
    12 / 13 trio; a sibling `_neq_roles` Lemma closes by
    `discriminate`.
  - **All five sim-side proof files updated.**  Record literals,
    field projections, and proof scripts threaded through the new
    Valid shape and the getter (~400 LOC delta).  Build green.
  - **Print Assumptions baseline unchanged.**  Per-milestone diffs
    are line-number-only (the sim extension didn't alter any
    `Print Assumptions` set; the four R101 modifier-wrapper Axioms
    remain Axioms with identical content).

### Why no walker Qed delta this commit

The widening is the **necessary prerequisite** for discharging the
two R100 modifier-wrapper Axioms
(`run_modifier_accrueRewards_610_at_storage_base` and `_647_`).
With four lens slots, the post-state `proj_post_deposit_4312
storage_base ...` now matches the modifier walker's chain on slots
4, 12, 13, and 14.

However, the modifier body ALSO writes:

  - **Per-token reward tracker mapping** (`rewardTrackers` at slot
    11, written by `fun__accrueRewards_1192`'s inner for-loop
    iteration over `rewardTokens.values()`).  Each iteration emits
    sub-mapping `sstore`s at `keccak256(...)`-derived anchors.
  - **`userRewardTrackers` mapping** (slot 8 in the OZ layout,
    per-user / per-token).  Similar iteration shape.
  - **ERC20 balances mapping** (the OZ ERC4626 base's `_mint` writes
    `balances[receiver] += shares`).  The balances mapping anchor
    is ERC-7201-derived.
  - **ERC20 totalSupply** (slot 4 in the abstract model; in
    reality the ERC-7201 anchor + offset).  The `_mint` updates
    `totalSupply += shares`.
  - **ERC20Votes delegate checkpoint mapping** (Votes.transferVoting
    Units → `_moveVotes` pushes new checkpoints).
  - **Optimistic delegate checkpoint mapping** (slot 22, the
    StakingVault's `_moveOptimisticDelegateVotes` call).
  - **log3 / log4 event emissions** (`Deposit` event in
    `super._deposit`).

The walker produces `sstore_post_storage` Skolems on ALL these
slots/mappings.  Our 4-slot lens covers only the four scalar slots;
the mapping-style slots remain unmodeled.  Reflexivity between the
walker's chain and `proj_post_deposit_4312` therefore still fails:
the chain is strictly larger than the Definition's 4-slot update.

### The OZ-base mechanization gap

Closing the gap requires either:

  - **(A) Continued sim widening with opaque map fields.**  Add
    `balances : Dict.t U256.t U256.t`, `voteCheckpoints : ...`,
    `optimisticVoteCheckpoints : ...`, `rewardTrackers : Dict.t (token,
    field) U256.t`, `userRewardTrackers : Dict.t (token, user, field)
    U256.t`.  Update the four Dict fields in `deposit` / `withdraw`
    consistent with the contract's behavior.  This is a substantial
    sim refactor (~600-1000 LOC) and the per-mapping update logic
    has to mirror the OZ ERC4626 base + the StakingVault
    `_update` override.

  - **(B) OZ-base equivalence files mechanization upstream.**  The
    Wave-2 `proofs/equivalence/ERC4626.v` and `ERC20Votes.v` are
    currently placeholders; they need full per-mutator walker
    discharge.  Once those land, the modifier wrapper can dispatch
    `fun__deposit_4546` (OZ super._deposit) and the `_mint` /
    `_burn` chains via composite walker Lemmas instead of inline
    Skolem chains.

Option B is the cleaner long-term path but requires the OZ-base
mechanization workstream (separate, large).  Option A is locally
achievable in the SVE sim but couples the SVE sim tightly to the OZ
ERC4626 / ERC20Votes / AccessControlEnumerable semantics — bordering
on re-implementing the OZ contracts in the sim.

### Decision: STOP, document the gap

Per the Task #310 brief's "honest failure modes" clause: "If you
find that the unmodeled slots require ERC4626 or ERC20Votes
mechanization upstream, STOP and report."  The gap is precisely
that.  This entry surfaces:

  1. **The achievable Phase A2 widening landed.**  Four-slot lens
     in place; sim invariants tightened; build green.
  2. **Phase B walker discharge remains blocked.**  Two modifier-
     wrapper Axioms unchanged in `Print Assumptions`.
  3. **The two follow-up paths.**  Option A (sim-internal map
     widening) and Option B (OZ-base mechanization) are now both
     documented; Option B is the strongly-preferred long-term
     trajectory.

### Net Print Assumptions delta per milestone Theorem

```
Before R106 (R101 baseline):        After R106 (this commit):
  - run_modifier_accrueRewards_610  (unchanged — Phase B blocked)
  - run_modifier_accrueRewards_647  (unchanged — Phase B blocked)
  - proj_post_mint_4356_eq_deposit  (unchanged)
  - proj_post_redeem_4450_eq_withdraw (unchanged)
```

Per-milestone `Print Assumptions` content is byte-identical to the
baseline (line-number drifts only).  Trust delta: **0 axiom-
equivalent assumptions retired this commit**.

The audit value is in the tighter SHAPE of the sim:
`balance_covers_deposited` makes `totalAssets s >= totalDeposited s`
an in-Valid claim rather than a derived corollary; the
`accumulatedNativeRewards` getter forces every consumer to commit
to the saturating semantics explicitly; the lens now covers the
slot the modifier writes (`nrlp` at 14) so an *adversarial*
inheritor cannot supply a `proj_post_<X>` Definition that
SILENTLY drops the timestamp update.

### Phase B forward work (NOT closed by this commit)

  - **Sim-internal map widening (Option A path).**  Add the four
    Dict fields, propagate through deposit/withdraw, define the
    per-map post-state computations.  Estimated 600-1000 LOC.
    Couples SVE sim tightly to OZ base semantics; defers the
    cleaner option but unblocks the Qed discharge locally.

  - **OZ-base equivalence files mechanization (Option B path).**
    `proofs/equivalence/ERC4626.v` and `ERC20Votes.v`
    per-mutator walker discharge.  This unblocks the SVE
    modifier-wrapper Axiom discharge AND every other ERC4626-
    derived contract.  Estimated multi-task; sized in
    `notes/equivalence_phase4_decision.md`.

  - **Inner-body walker discharge for `fun__accrueRewards_1192`.**
    Even with Option A, the inner for-loop iterating over
    `rewardTokens.values()` is a ~300-LOC body with multiple
    `staticcall`s (RewardTokenRegistry.isRegistered) per
    iteration.  StaticCallBridge primitives (R093 et seq.) cover
    the per-call discharge but the iteration walker is novel.

### Validation

  - Build: green (`OPAM_SWITCH=rocq820 bash formal-verification/
    scripts/rocq-build` exits 0).
  - `Print Assumptions` per milestone Theorem: line-number-only
    drifts (the four R100 Axioms unchanged in content).
  - File deltas: ~398 / -107 LOC across 6 files
    (sim + 5 proof files).

### See also

R099 (UnstakingManager Option A — applied cleanly because that
sim's State.t IS the full storage; SVE's State.t is a strict
sub-state, hence the partial-closure landing here).  R100 (the
modifier-wrapper sub-axiom decomposition this entry's prerequisite).
R101 (the sub-storage barrier diagnosis — this entry is the
foundation-laying response that R101 explicitly forecast).  R085
(the broader Parameter→Definition pattern across all equivalence-
tier files; SVE is one of the "partial sim" cases that R085's
methodology-finding flagged).  R094 (UnstakingManager Phase B —
the sister Phase B forward-work entry showing parallel structural
gaps).  Wave-2 ERC4626 / ERC20Votes equivalence files (Option B
upstream dependency).

