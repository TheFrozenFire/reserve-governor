# Rocq proof discipline (Reserve formal-verification)

Patterns and gotchas captured while authoring the proof tree under
`formal-verification/rocq/`. This file is a **reference**, not a
changelog — it's organized by pattern category, with each entry
showing the canonical shape an agent should reach for. R-numbers
are preserved for traceability against git history but are not the
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
- R005: Re-export with `Notation`, not `Theorem`
- R006: `vm_compute; reflexivity` for numerical witnesses
- R007: List-output domains need `Forall` lifting
- R008: Storage-state preservation needs the call-boundary hypothesis
- Named-tactic glossary (`p`/`l`/`lu`/`c`/`cu`/`s`/`pr`/`pe`/`cc`)

### Walker patterns (RunO Hoare triple)
- R024: `l. { c. { apply leaf } ... }` canonical step-through
- R025: `pe` (PureEq) leaves two subgoals
- R026: `let~ '` desugars to `M.strong_let_`
- R027: `eapply RunO.Call` two-subgoal split
- R028: Walker unfold list
- R029: Checked-arithmetic precondition direction
- R036: Upfront-pose for evar-scope problems
- R037: `idtac G; fail` diagnostic
- R038: Slot-discriminated walker arms for storage reads
- R040: Wrapper-shape leaves for sstore
- R044: Two outer-wrapper proof patterns
- R047: Case-split BEFORE `eexists` for if-then-else divergence
- R053: Outer-walker composition layer

### Bit / Z arithmetic
- R019: `Dict.Eq.eqb` on tuple keys (RESOLVED via R022)
- R023: `Z.lor` on if-then-else arguments (RESOLVED — case-split)
- R032/R033: Bridging if-then-else with `RunO.PureEq`
- R034: `Dict.declare_or_assign` chains (RESOLVED via cascade)

### Storage projection and observational equality
- R049: Multi-slot `proj_sim` cons-to-front Map2 encoding
- R052: `StorableValue.MapToArray` honest `mapping(K => T[])` primitive
- R054: `observationally_eq_storage` per-slot pointwise equality
- R059: `set_eq_at_role` membership equivalence (and `set_eq_in_registry`)

### Methodology — composite-walker-axiom recipe
- R051: Composite-axiom shape for milestone Qeds
- R065-R071: Per-mutator composite-walker recipe template
- R072: Abstract-base equivalence — slot-agnostic helpers + lens
- R075: OZ TimelockController equivalence — timestamp-as-state-encoding
- R076: ERC4626 — share-asset arithmetic + inflation defense
- R078: ERC20Votes — multi-base composition (ERC20 + Votes)
- R079: OZ Governor — virtual functions as explicit args
- R080: StakingVault dual-axis delegation + bySig composition
- R081: StakingVault pause/admin + UUPS upgrade authorization

### Framework primitives — the absorbing/bridge family
- R063: `staticcall` as composite of existing primitives
- R064: `AbiEncoding.v` — abi-encoding leaves
- R082: `staticcall_make_state_bridge_absorbing` + `make_state_with_*_eq`
- R083: ERC-7201 anchor lens + memory absorption
- R088: Arbitrary-U256-slot storage absorption (library functions)
- R091: Delegatecall bridge framework primitive
- R093: SafeERC20 + `Stdlib.call` bridge + `linkersymbol`
- R094: T-TOKEN / T-VAULT explicit-witness pattern
- R105: ProposalLib calldata + validator_revert + require_helper wrappers

### Trust redistribution patterns
- R084: Walker-shape Axiom + property-bridge Axiom + Skolem Parameters
- R085: Skolem-`Parameter` → `Definition` promotion ("anchor early")
- R089: Modifier composite + shared gate sub-axiom
- R099: Parameter→Definition refactor (works when sim = full storage)
- R101: Sub-storage barrier — partial closure only when sim is sub-state
- R103: Deterministic-post-storage wrapper template
- R104: Walker Axiom→Lemma rename (when wrapper layer not yet built)
- R106: Sim widening to match modifier writes (preliminary to discharge)
- R107: Shallow.let_state / Shallow.if_ structural absorbers (Yul if-revert shape)
- R108: OZ-base body / wrapper-chain bridge — trust decomposition for inherited overrides
- R109: OZ ERC20 _update body — Yul-helper leaf infrastructure (25 Qed leaves)
- R110: OZ ERC20 _update body — Section bridges + Yul-switch absorber + Axiom→Lemma

### Common pitfalls and resolved issues
- R020/R021/R035/R041/R042/R046/R073/R074: shallow_embed.py + framework bugs (RESOLVED upstream)
- R045/R048: OZ modifier mocks — symbolic wrappers
- R060: Verify contract surface against actual source

### Agent dispatch hygiene
- Worktree baseline reset
- Build full tree, not just touched files
- Push timing — explicit refspec is safer

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
Document the older as deprecated and migrate callers.

## R016: Logical-path naming

The governor repo uses `-R . ReserveGovernor` so files appear as
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

**Fix:** `set b := <expr>` before the destruct so both sites refer
to the same `b`. Or `change` on the hypothesis.

---

# Section 3: Tactical primitives

## Named-tactic glossary

Walker proofs use single-letter tactic aliases. They're defined
upstream in `RocqOfSolidity` and lifted at the top of each proof
file. The mnemonic reading:

| name | invokes                   | use                                          |
|------|---------------------------|----------------------------------------------|
| `p`  | `apply RunO.Pure`         | close a `M.pure x` goal with refl outputs    |
| `pe` | `apply RunO.PureEq`       | close a `M.pure ...` with side equality      |
| `l`  | `apply RunO.Let`          | step past `LowM.Let`                         |
| `lu` | let-unfold                | open the `let~` desugaring                   |
| `c`  | `apply RunO.Call`         | step past `LowM.Call` (split into 2 subgoals)|
| `cu` | call-unfold               | step past `LowM.Call (LowM.Let _ _) _`       |
| `s`  | "step"                    | fallback tactic (lazymatch default)          |
| `pr` | `apply RunO.Primitive`    | step past a primitive (`GetEnv`, `MLoad`, …) |
| `cc` | `apply RunO.CallContract` | step past `LowM.CallContract` (staticcall etc.) |

Walker arms typically open with `lu.` then enter a `repeat (lazymatch
goal with ...)` driven by `l. { c. { apply <leaf>. } ... }` shapes
per arm.

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

`Notation` is a pure alias; `Theorem ... := body` forces re-elaboration
and bloats compile time.

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

Get the direction right or leaf application fails.

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

## R019: `Dict.Eq.eqb` on tuple keys (RESOLVED via R022)

The typeclass projection on `Dict.Eq.ITuple2` is the underlying
cause; see R022 for the `change` workaround.

## R023: `Z.lor` on if-then-else arguments (RESOLVED — case-split)

Goal `Z.lor a (if b then x else y) = if b then Z.lor a x else Z.lor a y`
doesn't reduce automatically. **Fix:** case-split on `b` first;
both sides become concrete `Z.lor`s.

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
then `if false then _ else _` → else branch.

---

# Section 6: Storage projection and observational equality

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

## R052: `StorableValue.MapToArray` honest mapping(K => T[]) primitive

OZ's `EnumerableSet` and any Solidity `mapping(K => T[])` consumer
lay out per-key dynamic-array storage in a shape distinct from the
framework's nested-keccak Map/Map2/MapStruct primitives:

```text
slot[keccak(key, baseSlot)]              = array length
slot[keccak(keccak(key, baseSlot)) + i]  = values[i]
```

Upstream now ships `MapToArray (value : Dict.t U256.t (list U256.t))`
on `StorableValue.t` with four `Admitted` framework lemmas:
`run_sload_maptoarray_length` / `run_sload_maptoarray_elem` /
`run_sstore_maptoarray_length` / `run_sstore_maptoarray_elem`. Plus
four `apply_run_*` Ltacs and an `IsStorable.IMapToArray` typeclass
instance. Trust transfers once to the framework rather than being
re-asserted per-consumer (the previous "Option 1" per-contract
axioms were structurally false — see `Guardian.v` notes for the
remaining elimination work).

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

---

# Section 7: The composite-walker-axiom recipe

## R051: Composite-axiom shape for milestone Qeds

Bundle the function's walker into a single Hoare-triple axiom keyed
on the pre-state, with the post-state via a Skolemized Parameter:

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

## R065-R071: Per-mutator composite-walker recipe (canonical)

Validated on 12+ mutators across six contracts (VersionRegistry,
RewardTokenRegistry, Guardian, SelectorRegistry, ProposalLib,
TimelockControllerOptimistic). **3-step recipe per mutator:**

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

**Per-mutator cost:** 300-600 LOC, 2-4 axioms.

**Walker tactic library:** all targets use the same prelude (R028)
plus contract-specific lazymatch arms calling `StaticCallBridge.sc_word`
for staticcalls (R063), `AbiEncoding.run_*` for encoding/decoding
(R064), `Storage.run_sload_*` / `run_sstore_*` for storage ops, and
the contract's own `run_fun_<inner>_at_proj_sim` for sub-functions.

**Where to look for templates:**
- Simplest single-staticcall: `VersionRegistry.v::run_deprecateVersion_equivalent_make_state`
- Two-staticcall: `VersionRegistry.v::run_registerVersion_equivalent_make_state`
- Role-branching: `Guardian.v::run_cancel_equivalent_make_state`
- Looping over array argument: `SelectorRegistry.v::run_registerSelectors_equivalent_make_state`
- Multi-staticcall library: `ProposalLib.v::run_fun_proposeOptimistic_179_equivalent`
- Multi-namespace inherited: `TimelockControllerOptimistic.v::run_fun_scheduleBatch_1295_equivalent`

## R072: Abstract-base equivalence — slot-agnostic helpers + lens

Some OZ bases are **abstract**: they declare storage slots and methods
but never deploy standalone. Examples consumed in the corpus:
`AccessControl`, `AccessControlEnumerable`, `Nonces`,
`ReentrancyGuard`, `EnumerableSet`, `Votes`, `Checkpoints.Trace208`,
`ERC4626`, `ERC20Votes`, `TimelockControllerBase`, `GovernorBase`.

There's no `<base>_shallow.v` from solc for these — the Yul translation
lands in the inheritor's shallow form, with slot indices fixed by the
inheritor's storage layout.

**Pattern:**

1. The `proofs/equivalence/<Base>.v` file is **slot-agnostic**: it
   states sim-level lemmas about `mocks/<Base>.v` that hold
   independently of where the inheritor lays out the base's slots.
2. The file declares a Section parameterized by the slot indices
   and a projection lens (`project : SimulatedStorage.t -> Base.State.t`).
3. Lens-correctness hypotheses are declared as Section variables;
   inheritors discharge them by `reflexivity` at instantiation.
4. Walker-arm shapes are documented as comments — they can't be
   made concrete without a shallow form to point at.

**Trust:** zero new axioms. The slot-agnostic helpers close as
pure-Coq facts about the mock; the lens hypotheses are discharged
locally at instantiation time.

## R075: OZ TimelockController equivalence — timestamp-as-state-encoding

A specific application of R072 to OZ `TimelockController`. The base
packs the 4-state `OperationState` enum into a single
`mapping(bytes32 => uint256) _timestamps` using sentinel values:

```text
_timestamps[id] = 0              <=> Unset
_timestamps[id] = 1              <=> Done (the _DONE_TIMESTAMP magic)
_timestamps[id] > 1, > now       <=> Waiting
_timestamps[id] > 1, <= now      <=> Ready
```

Every public function reads it via `getOperationState(id)`; every
mutator writes it via a single sstore. Four post-state observation
lemmas (`schedule_post_state_waiting`, `execute_post_state_done`,
`cancel_post_state_unset`, plus `getOperationState_{zero,done,
waiting,ready}` discriminators) discharge the projection arms.

**`isOperation*` family as iff lemmas.** The four boolean predicates
are thin projections on `getOperationState`; expose each as iff so
walkers can rewrite in both directions.

**Open-role pattern (`onlyRoleOrOpenRole`):** dispatches through
`has_role` or `has_role_or_open` (`hasRole(role, msg.sender) ||
hasRole(role, address(0))`). Load-bearing for the `EXECUTOR_ROLE`
gate inside `execute`.

## R076: ERC4626 — share-asset arithmetic + inflation defense

OZ's `ERC4626` is an abstract base extending `ERC20`. It bridges a
**shares** ERC20 with an **assets** ERC20 via `Math.mulDiv` with
explicit rounding direction. The structural challenge:
`totalAssets()` reads the external asset's balance via a `staticcall`
to `IERC20(asset).balanceOf(this)`.

**Methodology (slot-agnostic, Option 2 per R072):**

1. **`_asset` opaque address — state field, not Section parameter.**
   Inheritor discharges by `reflexivity` at instantiation.
2. **`totalAssets()` — Section-parameter `project_asset_balance` +
   R063 discharge.** Inheritor discharges by a single R063 staticcall-
   bridge lemma. Conversion functions become closed-form muldiv
   against the projected asset balance.
3. **`Rounding` enum + `muldiv` primitive.** Sim is Z-valued so muldiv
   is exact. Public functions select rounding to favor the vault.
4. **`_decimalsOffset` virtual — `nat` state field bounded ≤ 77.**

**Headline inflation-attack property:** at `totalSupply = 0`,
`convertToShares s assets = floor(assets * 10^offset / (totalAssets + 1))`
regardless of donation. The `10^offset` multiplier is static —
the attacker's donation can't reduce it.

## R078: ERC20Votes — multi-base composition (ERC20 + Votes)

First OZ abstract base in the corpus to inherit from TWO other
abstract bases. Critical override is `_update(from, to, value)` —
every motion of ERC20 balance MUST mirror in the Votes checkpoint
history.

**Why one Section, not two stacked:** combining ERC20 + Votes into
a single Section lets the lens carry the `_getVotingUnits = balanceOf`
coupling as a Section-level Hypothesis (discharged once at
instantiation time by `reflexivity` on the inheritor's `proj_sim`
constructor). Two stacked Sections would force the consumer to
reason about TWO independent state projections that must satisfy a
cross-state coupling invariant manually.

The composed `_update` operates on disjoint slot indices (ERC20 vs
Votes); single-base walker tactics (R040, R047, R033) apply to
each half independently. Trust budget per call site: same as
single-base (2-4 composite axioms).

## R079: OZ Governor — virtual functions as explicit args

The OZ `Governor` base (~820 lines, ~15 `virtual` functions). Handle
virtuals in three buckets:

(A) **Explicit arguments to mock entry points.** View-only / state-
    extending virtuals (`votingDelay`, `votingPeriod`, `quorum`,
    `_quorumReached`, `_voteSucceeded`, `_getVotes`, `_queueOperations`,
    `_executor`) are passed as `Z` / `bool` / `U256.t` arguments to
    the relevant mock functions.

(B) **Section parameters at the equivalence layer.** Declare
    `votingDelay_fn`, `votingPeriod_fn`, `getVotes_fn`, etc. as
    `Variable`s. Inheritor walker proofs supply concrete witnesses.

(C) **Out of scope.** `_tallyUpdated` (empty default), token-receiver
    surface, EIP-712 / SignatureChecker path — compose orthogonally.

**Tally surface** carried as opaque `VoteTally` record. Concrete
inheritors with richer counting modules extend/project through it.

**Re-entrancy queue (`_governanceCall`):** modeled as `Bytes32Set`
(membership only). FIFO order is observationally irrelevant.

**The `state` 8-state cascade** lifted as `state_unfold` + 7 per-phase
characterizing lemmas + downstream stickiness lemmas
(`execute_leads_to_executed_state`, `cancel_leads_to_canceled_state`).

## R080: StakingVault dual-axis delegation + bySig

StakingVault carries TWO parallel Votes-inheritance bookkeeping
layers — standard ERC20Votes (`_delegatee` + `_delegateCheckpoints` +
total-supply Trace208) AND contract-local optimistic
(`optimisticDelegatees` at slot 0x0a + `optimisticDelegateCheckpoints`
Trace208 at slot 0x0b). Both touched on EVERY `_update`; public
`delegate*` entrypoints each touch ONLY ONE axis.

The "dual-axis independence" property: slot layout ensures the two
ledgers operate on disjoint storage regions, so each entrypoint's
walker decomposes along its single axis.

**Joined SimState carrier:**

```coq
Module SimState.
  Record t : Set := {
    base       : StakingVaultDelegation.State.t;  (* dual latest-side *)
    std_traces : TraceMap;
    opt_traces : TraceMap;
    nonces     : Nonces.Map;
    domain     : ECDSA.Domain.t;
    clock      : U256.t;
  }.
End SimState.
```

**Trace208 push at delegation transitions** chains directly via
`Trace208.latest_after_push`. **EIP-712 + ECDSA + Nonces composition
(BySig)** composes via foundation-tier equivalence proofs (`ECDSA.v`,
`Nonces.v`, `Checkpoints.v`, `Votes.v`).

The `OPTIMISTIC_DELEGATION_TYPEHASH` vs `DELEGATION_TYPEHASH`
distinction binds each BySig variant to a different axis via
`struct_hash_injective` (mocks/ECDSA.v).

The methodology file is `proofs/equivalence/StakingVaultDelegation_methodology.v`
— headline theorems are universally quantified at Section closure
and carry no semantic content until instantiated; see Audit.v
Caveat-5 for the audit-honest framing.

## R081: StakingVault pause/admin + UUPS upgrade authorization

StakingVault.sol has admin mutators across three tiers:

- **Tier-1** direct admin entry-points: `setUnstakingDelay`,
  `setRewardRatio`, `_authorizeUpgrade`.
- **Tier-2** inherited AccessControl: `grantRole` / `revokeRole` /
  `renounceRole`.
- **Tier-3** proxy entry-point: `upgradeToAndCall`.

The R070 abstract-storage_base recipe (Skolemized post-storage
Parameter + composite walker Axiom + reflexive observational bridge
under `storage_equiv := eq`) is the right call because:

1. StakingVault inherits TEN OZ namespaces, each at an ERC-7201
   keccak-derived anchor; concretizing per-slot would require
   re-mechanizing each namespace.
2. The admin theorems characterise WHICH slots are touched but the
   FULL-state post-condition is only meaningful relative to the
   per-domain equivalence files.

**Upgrade-authorization integration (R063 composition):** the
`_authorizeUpgrade` hook is the integration point with VersionRegistry.
Three staticcalls — `version()`, `getLatestVersion()`,
`getImplementationsForVersion()` — gate the upgrade. The audit
reason: (a) impl's version is the registry's latest, (b) not
deprecated, (c) registry's stakingVaultImpl matches the upgrade
target. Dual to VersionRegistry's `registerVersion` mutator.

---

# Section 8: Framework primitives — the absorbing/bridge family

The framework grew an "absorbing primitive" family that Skolemizes
post-states at `make_state`-shaped entry states. Three sibling
primitives in the call/staticcall/delegatecall trio, plus a memory
absorption family, plus an arbitrary-slot storage absorption family.

| primitive    | fast-path                          | storage shape                  |
|--------------|------------------------------------|--------------------------------|
| staticcall   | precompile                         | callee in TARGET's storage     |
| delegatecall | (none)                             | callee in CALLER's storage     |
| call         | `(g < 100) && (v = 0)`             | callee in TARGET's storage     |

## R063: `staticcall` as composite of existing primitives

Yul's `staticcall` decomposes upstream into:
`MLoad input + CallContract a 0 input true false + RLoad output +
MStore out (firstn outsize output) + pure result`.

R063 is bridge lemmas + walker arms. Walker tactic (`sc_word`):

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

Trust axioms (`run_abi_encode_tuple_*`, `run_finalize_allocation_*`,
`run_abi_decode_tuple_*`) are reusable across all R063-blocked
mutators.

## R082: `staticcall_make_state_bridge_absorbing` + `make_state_with_*_eq`

Skolem-form sibling of `staticcall_make_state_bridge` for walkers
where the staticcall fires against an absorbed memory layout (e.g.
after R083 has written at non-32-aligned offsets). Plus four
structural companions: `staticcall_post_memory_at_out`, `_at_other`,
`_length`, and the outsize-0 variant.

Companion `make_state_*_eq` commutators (`make_state_with_rd_eq`,
`make_state_with_gas_eq`, `make_state_return_data_eq`) fold record-
override fields back into the `state_base` argument so existing
`make_state`-shape leaves apply unchanged.

**Pattern.** After a staticcall step produces `<| return_data := bytes |>`,
apply `make_state_with_rd_eq` immediately to re-establish `make_state`
form for subsequent steps. Avoids needing `with_rd` companion axioms
for each subsequent step.

## R083: ERC-7201 anchor lens + memory absorption

### Gap 1 — ERC-7201 namespaced storage lens

OZ AccessControl / AccessControlEnumerable / UUPS / ERC20Permit /
Initializable / ReentrancyGuard all store at keccak-derived ERC-7201
namespace anchors (e.g. AccessControl at
`0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800`).
Upstream's `Storage.run_sload_map2_u256` pins the inner-keccak slot
to `Z.of_nat <small_nat>`, which CANNOT unify with a 256-bit keccak
output.

Slot-anchor-agnostic primitive in
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

Companion `run_sload_struct_field_at_anchor` (for mapping(K=>Struct))
and `run_sstore_map2_u256_at_anchor` follow the same template.

**Per-contract binding** is one Axiom of the form:

```coq
Axiom accessControl_namespace_binding :
  forall sb, IsNamespaceAnchor sb slot_accessControl 0x02dd...
```

This is the audit-time obligation — the abstract projection MUST
pin the designated slot to the keccak-derived anchor.

### Gap 2 — Memory absorption for event-emission tails

Walker tails where the memory result doesn't matter (event emission,
free-memory-pointer reads) but per-index `nth_error` bookkeeping is
brittle. Absorbing variants Skolemize the post-state:

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

Companion `run_mload_absorbing_at_make_state` returns a Skolemized
`mload_witness` value. Plus bookkeeping axioms about length
preservation and "far" word indices being untouched.

**Soundness obligation per use site:** Solidity practice mstores at
32-aligned addresses (free-memory pointer is `0x80 + k*32`; scratch
space at 0 / 0x20). Every Yul mstore in the corpus passes this audit.

## R088: Arbitrary-U256-slot storage absorption (Solidity libraries)

Solidity libraries (e.g. ProposalLib) take the target storage slot
as a `slot : U256.t` parameter — caller passes `keccak256(pid,
anchor)` or similar at invocation. Upstream's storage axioms pin
the slot expression to literal/keccak shapes; none unify with an
opaque library parameter.

Skolem-absorbing pair for arbitrary-U256 sstore/sload at
`make_state` states:

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

Parameter sload_witness : (* ... *) U256.t.
Axiom run_sload_absorbing_at_make_state : (* ... *).
```

Plus length-preservation and witness-bound axioms. Soundness story
identical to R083: upstream's `Storage.of_storable_values` is
`Admitted`; adding axioms about the projection at arbitrary slot
expressions is consistent so long as no two axioms force
contradictory values at the same slot.

**Per-target observational bridge obligation:** the library's
post-storage observably equals the caller's post-projection at the
slots the library wrote. Standard R040 + R055 + R067 shape.

## R091: Delegatecall bridge framework primitive

Delegatecall semantics: callee's bytecode runs under the CALLER's
storage / address / value context — the callee can mutate the
caller's storage. The bridge must surface this storage mutation as
a Skolem.

```coq
Parameter delegatecall_post_memory : (* ... *) SimulatedMemory.t.
Parameter delegatecall_post_storage : (* ... *) SimulatedStorage.t.

Axiom delegatecall_make_state_bridge_absorbing : (* ... *).
```

Plus three structural companions (`_at_out`, `_at_other`, `_length`)
for memory, length-preservation for storage, and an outsize-0
variant. Base sibling lemmas (Qed-proved against `RunO.CallContract`):
`run_delegatecall_general` / `run_delegatecall_to_word` /
`run_delegatecall_to_nothing`.

**Separation of concerns** (audit shape preserved from R070):
- Framework supplies "there is some witness for the call's effect."
- Per-target observational bridge axiom (carried per use site, NOT
  in the framework primitive) ties the Skolem to the target's sim
  post-state at the write slots.

**Why NOT thread the target's axiom through the bridge:**
reusability (per-consumer target axioms have different signatures),
trust accounting (R070 separates walker from observational bridge),
layering (framework has no business knowing which targets exist).

## R093: SafeERC20 + `Stdlib.call` bridge + `linkersymbol`

Closes the third arm of the call/staticcall/delegatecall trio.
`Stdlib.call` has fast-path `(g < 100) && (v = 0)` (EVM's gas-pruned
bookkeeping); for real contract calls (`g = gas()`) the condition is
false and the else branch fires, identical to staticcall modulo the
`is_static` flag.

Three Qed-proved base lemmas in `StaticCallBridge.v`:
`run_call_general` / `run_call_to_word` / `run_call_to_nothing`.
Skolem-absorbing variant `call_make_state_bridge_absorbing` in
`AbiEncoding.v` Layer 14c with four structural companions + outsize-0
variant.

**`linkersymbol` is a Qed lemma, NOT an axiom.** Upstream's
`Stdlib.linkersymbol` is definitionally `M.pure name`. The "linker
substitutes a real library address at deployment" is a compile-time
fact, not a runtime one. Consumers either discard the value (the
SafeERC20 inlined-body case — solc inlines the library body when
there are no inter-contract storage requirements) or thread it to
an external `call`/`delegatecall` whose `RunO.CallContract` rule
accepts any `U256.t` as the callee address.

**Storage shape under `call`:** callee runs in TARGET's storage; the
caller's projection is UNCHANGED. The absorbing axiom Skolemises
only post-memory; storage passes through identity.

## R094: T-TOKEN / T-VAULT explicit-witness pattern

For SafeERC20 (and any opaque external-contract dependency), surface
the deployment-fact trust at the milestone-theorem layer rather
than burying it inside an opaque walker Skolem:

```coq
Parameter safeTransfer_success_spec :
  Address -> Address -> U256.t -> Prop.
Axiom safeTransfer_T_TOKEN :
  forall token to amount, safeTransfer_success_spec token to amount.
```

Per-deployment T-TOKEN is the audit boundary: the deployed IERC20
target is well-behaved (no fee-on-transfer, balance-lying, malicious
return-data encoding). Surfaced explicitly at the inner-body sub-axiom
precondition so an adversarial instantiation cannot bypass the
witness.

Sibling T-VAULT pattern for direct StakingVault.deposit calls
(`stakingVault_deposit_success_spec` + `stakingVault_deposit_T_VAULT`).
Same audit shape; named for the deployed contract being trusted.

## R105: ProposalLib primitive wrappers — calldata + validator_revert + require_helper

Family of small Qed Lemma wrappers built BEFORE any walker discharge,
on the principle "wrapper buildup must precede walker discharge."
The 13 wrappers in `ProposalLib.v`:

- `run_calldataload_at_make_state` — `Stdlib.calldataload p` reduces
  to `Result.Ok (StdlibAux.get_calldata_u256 env.calldata p)` via
  `Primitive.GetEnvironment`.
- `run_validator_revert_t_{uint256,address,uint48}_succeeds` — closes
  to `tt` for any value (cleanup is identity / mask, then `eq v v = 1`,
  `iszero 1 = 0`, Shallow.if_ else branch).
- `run_read_from_calldatat_{uint256,address}_at_make_state` —
  composes calldataload + validator_revert.
- `run_array_length_*_pure` — three variants for calldata-ptr array
  length (defined as `let length := len in M.pure length`).
- `run_require_helper_*_succeeds` — four variants taking
  `condition <> 0` precondition.

**Proof technique:** nested `RunO_let_compose` for `LowM.let_` chains.
The validator_revert bodies have a `let* let* let*` chain (each
`let*` = `M.let_` = `LowM.let_`, the RECURSIVE fixpoint, NOT the
constructor). Outer `let~ '` uses `l. { ... }`; inner `let*` layers
use `RunO_let_compose` (the Phase-3 Admitted let_-fold).

This proof shape is the methodology for any `validator_revert`-style
or `require_helper`-style primitive that contains
`M.call`-inside-`Shallow.if_` patterns.

**Note on `RunO_let_compose` Admit:** the `LowM.let_` sibling of
`RunO.Let`; closed by structural induction on the underlying LowM.t,
each constructor case being a single RunO rule application. The
Rocq-tactical blocker is that `inversion` on `RunO.t` enumerates 12
constructors. Marked `Admitted`; trust impact is one structural
Admit (no new axioms needed beyond the existing `RunO.t` inductive
definition). Future work should use explicit `destruct` +
per-constructor `try discriminate` rather than relying on `inversion`.

---

# Section 9: Trust redistribution patterns

When discharging a composite walker Axiom to a Qed Lemma is not
mechanically tractable, several patterns redistribute the trust
into smaller-footprint axioms with sharper audit signatures. Net
axiom count often doesn't decrease — the methodology value is in
auditable shape.

## R084: Walker-shape Axiom + property-bridge Axiom + Skolem Parameters

For OZ EnumerableSet `_remove` and similar swap-and-pop bodies, the
monolithic walker+bridge axiom decomposes into:

- **Walker-shape Axiom** with concrete post-storage (the chain of
  storage writes the walker emits).
- **Property-bridge Axiom** (`set_eq_at_role_revoke_post_storage`)
  bridging the Skolem post-storage to the sim's post-projection.
- **Skolem Parameters** for the post-storage slots' new contents.
- **Framework inverse-op axioms** (e.g. `run_storage_set_to_zero_*`,
  `run_array_pop_at_proj_sim`) — siblings of the forward sstore
  axioms with same parametric-trust footprint.

The walker-shape axiom is now framework-style (closeable by a single
walker proof, no semantic bridge inside). The property axiom is
isolated and discharge-able by role-specific Qed Lemmas.

## R085: Skolem-`Parameter` → `Definition` promotion ("anchor early")

When a Skolem post-state is a pure function of `sim` and the input,
compute it concretely instead of leaving abstract:

```coq
Definition post_positions_after_remove role sim account :=
  let position := position_of role sim account in
  let oldLen   := old_len_of role sim in
  if (position - 1) =? (oldLen - 1) then
    Dict.declare_or_assign (role_positions_map sim) (role, account) 0
  else
    Dict.declare_or_assign
      (Dict.declare_or_assign
         (role_positions_map sim) (role, last_value role sim) position)
      (role, account) 0.
```

The walker proof now has a concrete post-state to land at — every
storage-write step unifies syntactically. The property bridge
becomes mechanically dischargeable (reduces to a Boolean equality
between two `Dict.declare_or_assign` chains). Retires the
Skolem-Parameter from `Print Assumptions`.

**When this works:** sim's `State.t` is a faithful model of the full
storage shape the mutator touches (sim = total isomorphism). UnstakingManager
satisfies this (R099); T3.3 swap-and-pop satisfies this; ProposalLib
satisfies this. See R101 for the failure mode.

## R089: Modifier composite + shared gate sub-axiom

For inheritor walkers shaped as `outer → modifier_onlyRole → gate +
inner-body` (TimelockControllerOptimistic, ReserveOptimisticGovernor),
decompose into:

1. **Shared gate sub-axiom** parametric over `role` and `role_pred`,
   amortizes across all mutators using the same modifier.
2. **Per-mutator inner-body sub-axiom** at storage_base.
3. **Outer walker Lemma** composes (~10-20 tactic lines).

Trust budget impact (per `Print Assumptions`): NET ±0 axioms — the
methodology value is sharper audit signatures and shared sub-axioms
across multiple outer walkers, not axiom count reduction. Pays off
when the shared gate sub-axiom is closed to a Qed Lemma (covers all
mutators at once).

## R099: Parameter→Definition refactor — when sim = full storage

Promote each `proj_post_<X>` `Parameter` to a `Definition` whose body
is `proj_sim ∘ sim_<X>`. With concrete `Definition`:
- Observation Axioms collapse to Qed Lemmas (reduce to definitional
  equality).
- Skolem-mismatch barrier between walker chain and abstract post-
  state disappears.
- Audit obligation sharpened — the storage projection is transparent
  at the type level.

Applied cleanly to UnstakingManager (whose `State.t` IS the full
storage). 9 axioms retired across 3 milestones.

## R101: Sub-storage barrier — partial closure only

For inheritors where the sim's `State.t` is a strict sub-state of the
full storage (StakingVaultExchange covers only 3-4 of ~20 namespaced
slots), R099 yields only partial closure:

1. Observation Axioms collapse to Qed Lemmas (Definition preserves
   non-modeled slots by construction).
2. Parameter is removed.
3. **Inner-body Axioms do NOT collapse** — the walker's chain writes
   slots outside the Definition's lens (ERC20 balances, Votes ckpts,
   reward trackers, AccessControl roles).

Path forward (multi-task):
- (A) Sim-internal map widening — add Dict fields for unmodeled
  substates and propagate through mutators. Couples sim tightly to
  OZ base semantics.
- (B) OZ-base equivalence files mechanization upstream — when ERC4626
  / ERC20Votes / etc land, modifier wrappers dispatch via composite
  walker Lemmas instead of inline Skolem chains. Cleaner long-term
  path but larger workstream.

## R103: Deterministic-post-storage wrapper template

The R088 wrapper Lemmas originally existentially quantified their
post-storage (`exists storage_post, {{? ... | wrapper | make_state ...
storage_post ?}}`). This blocked chained composition — each
`storage_post_k` introduced by `edestruct` is out of scope for the
outer `eexists memory'` evar (R092 barrier).

**Fix:** add deterministic-shape siblings exposing post-storage at
the conclusion:

```coq
Lemma run_update_storage_value_offset_0_..._at_make_state ... :
  {{? state | wrapper ⇓ Result.Ok tt
   | make_state ... (update_storage_value_offset_0_post_storage env
                       state_base memory storage slot value) ?}}.
```

Plus the post-storage `Definition`s computed in terms of
`sstore_post_storage` applied to an explicit packed-word
(`update_word_offset_{0,20,26}_*`) formula mirroring
`update_byte_slice_K_shift_J`.

Soundness: consumes the same axioms as the existential siblings; no
new audit axioms. Walker discharges then compose mechanically.

**Methodology finding:** future absorbing-primitive Lemmas should
default to deterministic post-state shapes via `Definition`s
returning the new state explicitly, not via `exists`. Existential
form is fine for ONE-OFF uses but pessimal for chain composition.

**Honest catalog — what R103 doesn't handle.** R103 worked on
`_saveProposal_580` (clean prelude/trailer split: 11 packed-slot
sstores at concrete offsets + event-emission trailer absorbed via
one sub-axiom). For walkers without that structure (mixed control
flow + heterogeneous primitives — `_validateProposal_507`,
`proposeOptimistic_179`, `proposePessimistic_288`,
`transitionToPessimistic_400`), the R103 template alone is
insufficient. Wrapper infrastructure for each body-internal
primitive (R105) is the prerequisite.

## R104: Walker Axiom→Lemma rename — when wrappers not yet built

A purely structural refactor: rename `run_fun_<X>_at_storage_base`
Axiom to `_body_absorbing` Axiom, then make `_at_storage_base` a
Qed Lemma proved by `exact <body_absorbing>`. NET 0 axioms retired
— trust impact is zero.

Value:
1. Uniform Lemma shape across all walkers in a file.
2. Audit obligation visibility — `Print Assumptions` shows only the
   `_body_absorbing` Axiom, clarifying that the audit obligation is
   "the function body, evaluated from the entry state."
3. Structural hook for incremental refinement — each walker's
   `Lemma` proof can be tightened mechanically with new wrappers,
   narrowing the `_body_absorbing` Axiom to cover only the
   not-yet-walked remainder.

## R106: Sim widening to match modifier writes

Preliminary step toward closing modifier-wrapper Axioms when the sim's
State.t is a sub-state of full storage (R101). Widen the sim's
primary fields to match the slots the modifier actually writes
(e.g. `nativeBalanceLastKnown`, `nativeRewardsLastPaid` promoted
from derived getters to primary fields), tighten `Valid.t` with the
new invariants (e.g. `balance_covers_deposited`), update sim mutators
to write the new fields.

NET 0 trust delta per milestone Theorem (modifier wrappers remain
Axioms with line-number-only drifts). The audit value is in the
tighter sim shape — `Valid.t` makes derived facts in-Valid claims,
and the lens covers slots the modifier writes so an adversarial
inheritor cannot supply a `proj_post_<X>` that silently drops
side-effects.

Final discharge of modifier wrappers still requires sim-internal map
widening (R101 Option A) or OZ-base mechanization (Option B).

## R107: Shallow.let_state / Shallow.if_ structural absorbers

Yul `if (cond) revert(...)` patterns produce the canonical post-cond-
discharged shape

```
let_state~ 'tt := Shallow.if_ cond <revert_block> tt default~ tt in <continuation>
```

Once we prove `cond = 0`, the `Shallow.if_` reduces by computation to
`M.pure (BlockUnit.Tt, tt)` (its definition: `if condition =? 0 then
pure (Tt, failure) else success`).  The outer `Shallow.let_state` then
desugars to a `LowM.Let` over the BlockUnit dispatch — which produces
~50 lines of nested `match` cases (four BlockUnit constructors × the
nested continuation), none of which `cbn match` reduces alone.

**Absorber** (Qed Lemma in `proofs/equivalence/FrameworkExtensions.v`):

```coq
Lemma run_shallow_let_state_pure_BlockUnit_Tt
    {S1 S2 : Set}
    (state : option State.t) (x : S1)
    (body : S1 -> S2 * Shallow.t S2)
    (output : Result.t (BlockUnit.t * S2))
    (state' : option State.t)
    (H : {{? codes, env, state | snd (body x) ⇓ output | state' ?}}) :
  {{? codes, env, state |
    Shallow.let_state (M.pure (BlockUnit.Tt, x)) body ⇓ output | state' ?}}.
Proof.
  unfold Shallow.let_state, M.strong_let_, M.generic_let, M.pure.
  eapply RunO.Let.
  - apply RunO.Pure.
  - cbn match. exact H.
Qed.
```

Plus the composite sibling `run_shallow_let_state_if_zero` that bakes
in the `Shallow.if_ 0 ...` reduction step (one tactic call instead of
two).

**Why a structural Lemma, not an inlined tactic.** The `cbn match`
tactic doesn't reduce through the `let~` (which is `M.strong_let_ =
generic_let LowM.Let`), and unfolding `Shallow.let_state` produces a
goal with the full BlockUnit dispatch that the walker engine can't
easily unify against.  The absorber bundles the unfold + the
constructor `RunO.Let` + the `Result.Ok` continuation match into one
forward-direction rewrite.

**Soundness.** No new audit-time axioms — both absorbers are Qed
Lemmas proven from `RunO.Let` + `RunO.Pure` + reduction.

**Reuse.** Any Yul `if (cond) revert(...)` walker landing after
`cond` has been proven zero discharges its structural residual with
one `apply run_shallow_let_state_if_zero` (or
`run_shallow_let_state_pure_BlockUnit_Tt` if the let_state body is
already simplified past the `Shallow.if_`).  First consumer:
`run_fun__mint_3368_equivalent` (task #314, NET 0 new audit Axioms
for the headline theorem).  Future consumers: every `_burn` /
`_transfer` / `_approve` / `validator_revert_*` walker shape.

## R108: OZ-base body / wrapper-chain bridge — trust decomposition

When an OZ abstract base function (e.g. ERC20's `_update`) is wrapped
by inheritor-specific overrides (e.g. StakingVault's `accrueRewards`
modifier + ERC20Votes's maxSupply / `transferVotingUnits` +
StakingVault-local `_moveOptimisticDelegateVotes`), the audit-time
obligation has TWO genuinely separable concerns:

1. **The OZ base body**, inlined by solc into the inheritor's shallow
   form, implements the canonical semantics under the standard
   preconditions.  Mechanically discharge-able via R083 anchor lens +
   R107 absorbers, but is bookkeeping-heavy (~300 lines per branch
   for `fun__update_3335`: walk through `mapping_index_access` scratch
   memory + `sload`/`sstore` at namespace anchor + `keccak256` + Yul
   `add(slot, offset)` reductions + event emission).

2. **The wrapper chain** writes to slots OUTSIDE the OZ base lens
   (delegation checkpoints, accrueRewards state, optimistic delegate
   state) and its effect on the OZ base projection (`proj_sim`) is
   observationally identity.

**Body-absorbing-composite (task #314 shape):** ONE axiom per
branch that absorbs both the wrapper chain AND the body.

```coq
Axiom run_fun__update_1459_at_proj_sim_mint :
  forall ..., <preconditions> ->
  exists memory',
  {{? ... | fun__update_1459 0 account value ⇓ Ok tt
   | Some (make_state ... memory' (proj_sim_post_mint sim ...)) ?}}.
```

Audit obligation: the whole wrapper chain produces the OZ-base
post-state.  Conflates body semantics with wrapper-side identity.

**Decomposed-trust (task #315 shape):** TWO narrower axioms per
branch — one for the OZ base body, one for the wrapper-chain bridge.

```coq
(* OZ base body: mechanically discharge-able. *)
Axiom run_fun__update_3335_at_proj_sim_mint :
  forall ..., <preconditions> ->
  exists memory',
  {{? ... | fun__update_3335 0 account value ⇓ Ok tt
   | Some (make_state ... memory' (proj_sim_post_mint sim ...)) ?}}.

(* Wrapper-chain bridge: per-target audit (R070 shape). *)
Axiom run_fun__update_1459_wraps_fun__update_3335 :
  forall ..., <inner walker> -> exists memory', <outer walker>.

(* Composite: now a Qed Lemma. *)
Lemma run_fun__update_1459_at_proj_sim_mint :
  forall ..., <preconditions> ->
  exists memory', <outer walker for fun__update_1459 ...>.
Proof.
  pose proof (run_fun__update_3335_at_proj_sim_mint ...) as Hbody.
  destruct Hbody as [memory_inner Hbody].
  pose proof (run_fun__update_1459_wraps_fun__update_3335 ... Hbody)
    as [memory_outer Houter].
  exists memory_outer. exact Houter.
Qed.
```

**Recipe (per branch):**

1. State `run_fun__<OZbase>_at_proj_sim_<branch>` Axiom — the OZ base
   body's effect on the proj_sim lens, parameterized by the inheritor
   projection.  Preconditions are exactly the OZ-base preconditions
   (e.g. for `_update` mint: `from = 0`, `to != 0`, value bounded,
   `totalSupply + value < 2^256`).

2. State `run_fun__<wrapper>_wraps_fun__<OZbase>` Axiom — generic over
   arguments, says "if the inner OZ base walker produces a post-state,
   the wrapper chain produces an observationally-equal post-state
   (modulo memory perturbations)."  This is the R070 / R080
   per-target observational bridge.

3. Derive `run_fun__<wrapper>_at_proj_sim_<branch>` as a Qed Lemma by
   posing (1) and (2) and exists-introducing the witnesses.

**Why this matters:**

- **Narrows audit obligations.**  Each axiom is independently
  auditable: the OZ base body axiom against the well-known OZ
  reference implementation, the bridge axiom against the inheritor's
  specific override chain.

- **Path to full mechanization.**  The OZ base body axiom is
  mechanically discharge-able via R083 anchor lens primitives +
  R107 absorbers + a per-Yul-op leaf library.  The wrapper bridge
  remains per-target audit obligation (vanilla OZ deployments
  discharge it trivially).

- **Reuse across all `_update` consumers.**  The same OZ base body
  axiom is reused by `_mint`, `_burn`, `_transfer`, and any future
  ERC4626 `_deposit` / `_withdraw` that internally calls `_update`.

**Concrete bookkeeping for the OZ ERC20 `_update` discharge (R108
mechanical-discharge recipe):**

The body of `fun__update_3335` has the shape:

```
  let_state~ 'tt := switch on (from == 0) — mint vs decrement-from
  let_state~ 'tt := switch on (to == 0)   — burn vs increment-to
  let_state~ 'tt := emit Transfer event
```

For the **mint branch** (from = 0):

1. Walk through pure prelude (~12 let-bindings) — `RunO.Let` +
   `RunO.Pure` per step.
2. Reduce `eq(0, 0) = 1` via a dedicated leaf
   `run_eq_address_zero_at_zero`.
3. Apply `Shallow.if_` reduction (δ = 1 → else branch).
4. Walk mint body:
   - `add(anchor, 2)` reduces via a `Pure_add_anchor_offset` lemma
     (bound proof for `anchor + 2 < 2^256`).
   - `sload(anchor + 2)` reduces via
     `run_sload_u256_at_anchor_offset` (R083 framework primitive).
   - `checked_add_t_uint256(totalSupply, value)` reduces under
     `H_no_overflow` to `M.pure (totalSupply + value)`.
   - `sstore(anchor + 2, totalSupply + value)` reduces via
     `run_sstore_u256_at_anchor_offset`.
5. Walk through second-switch prelude (~7 let-bindings).
6. Reduce `eq(account, 0) = 0` via `run_eq_address_zero_check`.
7. Apply `Shallow.if_` reduction (δ = 0 → if branch).
8. Walk not-burn body:
   - `mapping_index_access(anchor, account)` reduces via a
     `MappingIndexAccessAddressU256` Lemma (mirror of Guardian's
     `MappingIndexAccessAddressBool`).
   - `sload(keccak256_tuple2(account, anchor))` reduces via
     `run_sload_map_u256_at_anchor` (R083 framework primitive).
   - `wrapping_add_t_uint256(balance, value)` reduces to
     `M.pure (Pure.add balance value)` (modular).
   - `sstore(...)` reduces via `run_sstore_map_u256_at_anchor`.
9. Walk Transfer event emission: `allocate_unbounded` →
   `abi_encode_tuple_t_uint256__to_t_uint256__fromStack` → `log3`,
   absorbed via R083 memory variants
   (`run_mstore_absorbing_at_make_state` + skolem post-memory).
10. Compose into the final `proj_sim (ERC20.mint sim account value)`
    post-state via the `proj_sim` projection structural lemmas
    (needed: an inheritor-supplied Hypothesis tying
    `update_nth (proj_sim sim) slot (Map (balances_to_dict (set_balance bs acc v)))`
    to `proj_sim (mint sim acc v)`).

For **burn** and **transfer** branches, the recipe is mirror-symmetric:
swap `from == 0` and `to == 0` switches, use `wrapping_sub_t_uint256`
instead of `wrapping_add_t_uint256` where the balance decreases, and
use `checked_sub` (no precondition needed since `lt` check is in the
body itself).

**Soundness footnote.**  The decomposition introduces NO new
soundness obligation: the wrapper bridge axiom is consistent with
the framework's existing `RunO.t` semantics so long as the wrapper
chain is observed to write only non-projected slots — exactly the
audit-claim shape already used for delegatecall bridges (R091) and
arbitrary-slot library writes (R088).

**First consumers:** `run_fun__mint_3368_equivalent` /
`run_fun__burn_3401_equivalent` / `run_fun__transfer_3243_equivalent`
in `proofs/equivalence/ERC20.v` (task #315 closure).

---

## R109: OZ ERC20 _update body — Yul-helper leaf infrastructure

Task #316 was charged with discharging the three `run_fun__update_3335_at_proj_sim_<branch>` axioms from R108
to Qed Lemmas. The body of `fun__update_3335` (≈125 Yul lines per
branch) consumes a fixed set of Yul-helper functions that each
expand to a deterministic let-chain over `Stdlib` primitives:

```
  fun__getERC20Storage_2971              (returns the anchor)
  cleanup_t_uint256                      (identity on U256.t)
  cleanup_from_storage_t_uint256         (identity)
  shift_right_0_unsigned                 (identity: shr 0)
  extract_from_storage_value_offset_0_t_uint256  (chain of the above)
  identity                               (identity)
  convert_t_uint256_to_t_uint256         (cleanup ∘ id ∘ cleanup)
  prepare_store_t_uint256                (identity)
  shift_left_0                           (identity for v < 2^256)
  update_byte_slice_32_shift_0           (identity for new < 2^256)
  wrapping_add_t_uint256                 (= Pure.add)
  wrapping_sub_t_uint256                 (= Pure.sub)
  checked_add_t_uint256                  (= x+y under no-overflow)
  checked_sub_t_uint256                  (= x-y under no-underflow)
  cleanup_t_uint160                      (identity on Address.Valid.t)
  convert_t_uint160_to_t_uint160         (chain of the above)
  convert_t_uint160_to_t_address         (chain of the above)
  convert_t_address_to_t_address         (chain of the above)
  mapping_index_access_t_mapping…address_of_t_address (mstore-mstore-keccak; absorbing-memory variant)
  read_from_storage_split_offset_0_t_uint256        (sload + identity chain; Map-keyed and U256-at-offset variants)
  update_storage_value_offset_0_t_uint256_to_t_uint256 (convert + sload + prepare + ubs + sstore; Map-keyed and U256-at-offset variants)
```

**R109 contribution.** Discharge each of these to a closed (Qed)
Lemma, declared near the top of `Module ERC20Equivalence` (outside
the per-inheritor `Section`). The `mapping_index_access_t_address`
variant is an Axiom (mirror of `AbiEncoding.run_mapping_index_access_absorbing`
for the bytes32-keyed variant; same R083 Gap 2 pattern). All other
leaves are Lemmas with no new audit-time obligations.

The four composite storage helpers
(`run_read_from_storage_split_offset_0_t_uint256_at_*_anchor*`,
`run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_*_anchor*`)
combine the R083 framework primitives with the identity-on-U256 chain
to give direct sload/sstore reasoning at the namespace-anchor lens.
They are the load-bearing pieces for the body discharge.

**Residual for follow-up.** The three body axioms remain in place;
they cannot be discharged within the abstract Section without three
additional `proj_sim` bridging hypotheses:

  1. `proj_sim_pointwise_balance_update` — describes
     `update_nth (proj_sim sim) slot_balances (Map ...)` as `proj_sim sim'`
     for `sim'` constructed by the per-slot balance write.

  2. `proj_sim_pointwise_totalSupply_update` — companion for
     `slot_totalSupply`.

  3. `proj_sim_independent_slots` — distinct list indices commute.

Plus a "switch-non-zero" Shallow absorber: Yul `switch`s lower to
`let δ := c in if δ =? 0 then else_branch else if_branch` (a raw
Coq-level `if-then-else`, not `Shallow.if_`), which the R107 `if_zero`
absorber doesn't pattern-match. The mint branch picks the `else`
arm (δ = 1 from `eq(0, 0) = 1`), so we need an absorber for that
shape. (Burn/transfer pick the `if` arm; same family.)

These bridges + the switch absorber are per-inheritor audit
obligations (discharged by `reflexivity` once `proj_sim` is
concrete). Adding them touches the `Section ERC20BaseEquivalence`
signature, which is out-of-scope for the leaf-infrastructure pass.

**Net trust delta vs task #315.**

- Axioms BEFORE (task #315): 3 body axioms + 1 wrapper bridge =
  4 audit-time obligations per `_update` consumer.
- Axioms AFTER (task #316): SAME 3 body axioms + 1 wrapper bridge,
  PLUS 1 new memory-absorbing axiom
  (`run_mapping_index_access_t_address_at_make_state`) parallel to
  the existing bytes32 variant in AbiEncoding.
- Closed Lemmas added: 25 Qed leaves for body helpers.
- Total trust footprint change: +1 axiom (mirroring an existing
  family member), -0 axioms. **Net trust reduction is deferred to
  the follow-up that lands the Section bridges.**

**Why the body discharge is not closed in #316.** The Section's
abstract `proj_sim : ERC20.State → SimulatedStorage.t` is opaque —
the inheritor (StakingVault) supplies its concrete shape at
instantiation. Without per-slot bridging hypotheses, the body
discharge cannot produce the post-state form
`make_state ... memory' (proj_sim_post_mint sim account value)`
required by the axiom signature. The leaves close the
"every Yul helper has a closed lemma" obligation; the bridges close
the "the projection composes pointwise with the per-slot updates"
obligation. Both are required; only the first is delivered in #316.

**First consumers:** `run_fun__update_3335_at_proj_sim_mint` /
`_burn` / `_transfer` discharges in `proofs/equivalence/ERC20.v`,
when the Section bridges land.

---

## R110: OZ ERC20 _update body — Section bridges + Yul-switch absorber

Task #317 was charged with landing the structural pieces that R109
identified as gating the OZ ERC20 `_update` body Qed closure:
three Section bridging hypotheses for `proj_sim` pointwise
composition + a new Shallow absorber for Yul `switch` shapes.

### Piece 1: Three Section bridging hypotheses (`ERC20BaseEquivalence`)

The abstract `proj_sim : ERC20.State → SimulatedStorage.t` is a
Section Variable.  The `_update` body writes to two slots
(`slot_balances` map + `slot_totalSupply` U256), and the final
post-state must equal `proj_sim sim'` for the appropriate sim
post-state.  Without compositional hypotheses tying the abstract
`proj_sim` to per-slot updates, the body walker can produce the
storage trace but cannot identify it with `proj_sim_post_<branch>`.

Three new `Hypothesis` declarations land in the Section:

1. **`map_get_balances_eq_balanceOf`** — the helper bridge that ties
   `StorableValue.map_get_u256 (balances_to_dict sim.balances) account`
   to `ERC20.balanceOf sim account`.  Audit-time obligation: per
   inheritor's concrete `balances_to_dict` definition, this holds
   structurally on the dict representation.

2. **`proj_sim_pointwise_balance_update`** — the mint composition
   bridge.  Says: composing the two storage writes (totalSupply,
   balances) the Yul body produces equals `proj_sim (ERC20.mint sim
   account value)`.  Handles `value = 0` edge case via dict
   equality (writing back same value at existing key is identity;
   for absent keys, the projection treats the `(key, 0)` entry
   equivalently to absence).

3. **`proj_sim_pointwise_totalSupply_update`** — the burn composition
   bridge.  Says: composing the balances-decrement + totalSupply-
   decrement writes equals `proj_sim sim'` where `ERC20.burn sim
   account value = Success sim'`.

4. **`proj_sim_independent_slots`** — the transfer composition
   bridge.  Says: composing the from-debit and to-credit writes
   (both into the balances slot) equals `proj_sim sim'` where
   `ERC20.do_transfer sim from to value = Success sim'`.  Audit
   obligation: handles the from = to self-transfer no-op case via
   the mock's short-circuit.

(The names are inherited from the brief; the contents are
composition-bridges per branch, not "pointwise atomic update"
shapes.  The R109 brief's shape sketches turned out to require
composing the two slot writes per branch into a single bridge,
because intermediate storage states between the two writes are
not themselves equal to any `proj_sim sim_intermediate`.)

Per-hypothesis trust justification:
- Each hypothesis is parameterized by the abstract `proj_sim`.
- At inheritor instantiation (StakingVault), `proj_sim` is concrete
  and the slot indices are literal nats.  The `update_nth` chain
  reduces computationally.  The remaining content is dict equality
  of `balances_to_dict` over `set_balance` updates, which is a
  pure Gallina lemma.
- Net soundness: same as the prior body axioms — the inheritor
  discharges the hypotheses by `reflexivity`/structural reasoning.

### Piece 2: New Yul-switch absorber (`FrameworkExtensions`)

The Yul `switch` statement lowers in the shallow embedding to:

```coq
let_state~ 'tt :=
  let~ δ := [[ expr ]] in
  if δ =? 0 then else_branch else if_branch
default~ tt in <continuation>
```

The `let~ δ := ... in if δ =? 0 then _ else _` is a raw Coq
`M.strong_let_` over a raw Coq `if`-`then`-`else`.  R107's
`run_shallow_let_state_if_zero` doesn't match this shape because
its inner shape is `Shallow.if_`, not raw Coq `if`.

**Two new absorbers** land in `FrameworkExtensions.v`:

- **`run_let_state_match_pure_zero`** — discharges the case where
  `expr ⇓ Result.Ok 0`: commits to the `else_branch` (since
  `0 =? 0` is `true`).
- **`run_let_state_match_pure_nonzero`** — discharges the case
  where `expr ⇓ Result.Ok δ_val` with `δ_val <> 0`: commits to the
  `if_branch` (since `δ_val =? 0` is `false`).

Both Qed via [eapply RunO.Let] + reduction of the raw `if` against
the precondition.  No new audit-time axioms.

### Piece 3: Axiom→Lemma signature conversion

The three body axioms in `Section ERC20BaseEquivalence`
(`run_fun__update_3335_at_proj_sim_<mint|burn|transfer>`) convert
from `Axiom` to `Lemma <statement>. Admitted.`  Signatures
unchanged; the conversion preserves all consumer code (downstream
walkers compose them identically).

Net trust position vs R109:
- 0 axioms removed from `Print Assumptions` of the headline
  theorems (`run_fun__mint_3368_equivalent` etc.) since the
  Admitted Lemmas surface as axioms over the Section parameters.
- 4 new Section hypotheses added (load-bearing for the headline
  theorems once the body Qed closes; they then replace the body
  axiom names in `Print Assumptions`).
- 2 new Qed Lemmas in `FrameworkExtensions` (the switch
  absorbers) — pure structural, no audit obligation.

### Status: body discharge SCAFFOLD landed; Qed closure deferred

The actual walker proof through `fun__update_3335`'s 125-Yul-line
body remains pending.  Each branch (mint, burn, transfer) requires
~400 LOC of mechanical tactic code:
- 12-30 prelude let-bindings each handled by `eapply RunO.Let +
  apply RunO.Pure + cbn match` (or via call-sites for helper
  invocations).
- One `apply run_eq_address_zero_at_zero` or `run_eq_address_zero_check`.
- One `apply run_let_state_match_pure_<zero|nonzero>` to commit
  to the right switch arm.
- Per write subblock: a sequence of `eapply RunO.Let +
  apply Pure | apply <helper>` chains for each of:
  `sload`, `checked_add`/`wrapping_*`, `sstore`, plus the
  composite helpers `run_read_from_storage_split_offset_0_*_at_*`
  and `run_update_storage_value_offset_0_*_at_*`.
- log3 emission tail: `apply run_allocate_unbounded +
  walk abi_encode_tuple + apply run_mstore_absorbing_at_make_state
  + apply RunO.Pure` (log3 = `M.pure tt`).
- Final composition: `apply proj_sim_pointwise_balance_update`
  (or `_totalSupply` / `_independent_slots` for burn / transfer).

The decision to ship the SCAFFOLD without the body Qed is
pragmatic: the walker tactic code is ~1200 LOC across three
branches, which exceeds a single focused agent run when combined
with the Section bridge design + new absorber.  The infrastructure
delivered makes the body Qed a pure mechanical exercise — no new
lemmas, no new design decisions.

**Recipe for the follow-up Qed closure:**

For each branch, write the walker via this skeleton (mint example):

```coq
intros codes env state_base memory sim account value
       H_account_nz H_account_bound H_value_bound
       H_valid H_no_overflow.
(* Skolemize memory' via the log3 tail's mstore_absorbing. *)
eexists.
unfold fun__update_3335.
unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
cbn match.
eapply RunO.Let.
{ (* getERC20Storage + prelude up to eq(0,0) *)
  c; [apply run_fun__getERC20Storage_2971_returns_anchor|].
  cbn match.
  walk_prelude_pure.
  (* expr_3264: eq(cleanup_t_address 0, cleanup_t_address 0) = 1 *)
  eapply RunO.Let.
  { simpl LowM.let_.
    c; [apply run_cleanup_t_address|]. cbn match.
    c; [apply run_cleanup_t_address|]. cbn match.
    c; [apply run_eq_address_zero_at_zero|].
    apply RunO.Pure. }
  cbn match.
  (* Switch: δ = 1, take else branch (mint). *)
  apply (run_let_state_match_pure_nonzero codes env _ _ _ 1
           ltac:(discriminate) _ _ _ _ _ _
           ltac:(apply RunO.Pure)
           ltac:(...else_branch_walker...)
           ltac:(...post_switch_continuation...)).
  ...
}
cbn match.
apply RunO.Pure.
```

The else_branch_walker walks the TS-write subblock (sload + checked_add
+ sstore at anchor+2 lens), then returns `Result.Ok (Tt, tt)`.  The
post_switch_continuation walks the second prelude → eq(account, 0) → 0,
applies `run_let_state_match_pure_zero` to commit to the balance-credit
arm, walks the balance-credit subblock (keccak + sload + wrapping_add +
sstore at balances map lens), then walks the log3 tail (allocate +
abi_encode + mstore_absorbing + log3-as-pure).  Finally, the post-state
matches via `proj_sim_pointwise_balance_update` applied to the
totalSupply + balances writes.

Burn and transfer follow the symmetric recipe with the appropriate
helpers (wrapping_sub / checked_sub) and the appropriate bridging
hypothesis.

**First consumers:** `run_fun__mint_3368_equivalent` /
`run_fun__burn_3401_equivalent` / `run_fun__transfer_3243_equivalent`
in `proofs/equivalence/ERC20.v` — once body Qed lands, their
`Print Assumptions` will exclude the body Lemma names entirely.

---

# Section 10: Common pitfalls and resolved issues

## R020: `Stdlib.timestamp` semantics (RESOLVED in dev clone)

Now defined as `LowM.Primitive Primitive.GetBlockTimestamp M.pure`.
Discharge via `pr` (Primitive) tactic + state hypothesis.

## R021: `RunO.CallContract` rule (RESOLVED via upstream patch)

Upstream `TheFrozenFire/rocq-of-solidity:feat/env-block-context` adds
a permissive constructor (`cc` tactic). Proof author picks
`call_result` and `state_inter` freely; soundness shifts to the
proof-author level via a separate callee-spec axiom.

## R035: `shallow_embed.py` mis-embeds nested control flow (RESOLVED)

`commonly_updated_vars` vs `final_updated_vars` confusion in switch
let_state binding. Fixed upstream (commit `696f60fd73`).

## R041: missing `linkersymbol` definition (RESOLVED upstream)

Fixed upstream (commit `2646cf555a`).

## R042: `M.monadic` "object of type ident" trap (RESOLVED)

Upstream shallow_embed now guards M.monadic against unresolved
identifiers (commit `754592d34f`).

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

## R073: `shallow_embed.py` emits Rocq keyword `fun` (RESOLVED)

Solc's internal-function-pointer dispatcher
`function dispatch_internal_in_N_out_M(fun, ...)` has a literal `fun`
parameter name. Fixed upstream by broadening `reserved_names` to
include `fun` (suffixed with `_`).

## R074: `shallow_embed.py` zero-inits tuple binders as scalar 0 (RESOLVED)

`YulVariableDeclaration` with no initializer was emitting `"0"`
regardless of binder arity. Fixed upstream by fanning out implicit
zero across the binder arity.

---

# Section 11: Agent dispatch hygiene

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

## Push timing — explicit refspec is safer

`git push remote branch` can silently no-op with unusual
branch-tracking config. Prefer:

```bash
git push thefrozenfire <commit-hash>:refs/heads/feature/formal-verification
```

forces fast-forward-or-fail with no tracking ambiguity.

## Print Assumptions snapshot baselines

`formal-verification/scripts/print-assumptions-snapshot` writes per-
milestone trust snapshots to
`formal-verification/rocq/print_assumptions_snapshot/baseline/`.
Refresh on any commit that changes a milestone Theorem's load-bearing
axiom set. Diff against baseline in CI to catch silent trust regressions.

---

# Consolidated / dropped R-entries

The 2026-06-01 consolidation pass dropped or merged the following
chronological-narrative entries. The R-numbers are reserved against
git history — searching `git log --grep "R0xx"` retrieves the
original landing context.

- **R055**: merged into R059 (set_eq_at_role) — the two were the
  same membership-equivalence pattern at different keys.
- **R067 / R068 / R069 / R070 / R071**: merged into the R065-R071
  composite-walker recipe entry. Each was a per-mutator validation
  ("we ran this on contract X"); the recipe template is the wisdom.
- **R077** (ReserveOptimisticGovernor mutator equivalence): per-task
  narrative, dropped. Pattern carried by R079 (Governor base) +
  R070 (composite-walker recipe). The hybrid optimistic/pessimistic
  wrinkles are documented in `proofs/equivalence/ReserveOptimisticGovernor.v`'s
  own header comments.
- **R078 (StakingVault exchange-rate)** and **R079 (StakingVault
  rewards equivalence — duplicate number)**: per-task narratives,
  dropped. Patterns carried by R076 (ERC4626), R078 (ERC20Votes),
  R080 (delegation), R081 (admin). Two R-entries shared the numbers
  078/079 in the prior file — a clue the entries were diary, not
  reference.
- **R082's CRIT-A composite-walker discharge narrative**: per-task
  closure ("the 18-step mechanical discharge follows..."). Kept the
  framework primitive landing (`staticcall_make_state_bridge_absorbing`
  + `make_state_with_*_eq` companions) as the R082 reference content.
- **R086 (SafeERC20 + linkersymbol framework gap)**: per-task
  diagnostic, dropped. The closure pattern is in R093.
- **R087 (ROG composite-walker discharge — structural blockers)**:
  per-task post-mortem. The four blockers were documented; the
  closures are R091 (Blocker 2), R088 (Blocker 1 redistribution),
  pending walker discharges (Blocker 4). The reference content is
  in the closure entries.
- **R090 (T3.3 Phase-2 bridge-axiom discharge)**: per-task closure.
  Pattern is in R084 + R085.
- **R092 (R088 Phase 2 — ProposalLib helper Lemmas + structural
  obstacle)**: per-task obstacle diagnosis. Closure pattern is in
  R103.
- **R095 (TimelockController executeBatch walker discharge)**:
  per-task closure narrative. The methodology is R089 + R091.
- **R096 (StakingVaultExchange walker scaffolding)** and **R097
  (StakingVaultExchange Phase 2 — walkers to Lemmas)**: per-task
  closure narratives. The methodology is R089 + R094.
- **R098 (UnstakingManager inner-body Skolem barrier)** and **R102
  (UnstakingManager Phase B — T-VAULT surfaced)**: per-task
  narratives. Pattern is in R094 (T-VAULT shape) + R099 (Parameter→
  Definition fix).
- **R100 (StakingVaultExchange inner-body modifier-wrapper
  narrowing)**: per-task narrative. Pattern is R089 trust
  redistribution.

---

# Appendix: When in doubt, where to look

For an agent about to write a new equivalence proof:

1. **Read the .sol source.** R060.
2. **Pick a template walker** from the R065-R071 "where to look" list
   that matches your contract's shape (single staticcall? role-
   branching? for-loop? inherited modifier?).
3. **Identify the abstract bases.** If the contract inherits
   OZ ERC4626 / ERC20Votes / Governor / TimelockController /
   AccessControl, consult R072 + the per-base entry (R075-R081)
   for the slot-agnostic Section pattern.
4. **Decide on Skolem post-state vs `Definition` post-state.** If
   the sim is total over the contract storage, prefer R085 / R099
   (`Definition`). If sub-state, R101 — partial closure is your
   ceiling.
5. **For library or arbitrary-slot writes**, reach for R088
   absorbing primitives.
6. **For staticcall/call/delegatecall**, the framework primitives
   are R063 / R093 / R091.
7. **For the walker tactic body**, R028 prelude + R024 step-through
   + R040 sstore wrappers + R047 case-split. Diagnostic R037 when
   it misfires.

When a walker discharge hits a structural barrier, the trust-
redistribution menu is R084 / R085 / R089 / R094 / R103 / R104.
Pick the one whose audit shape matches what's blocking you.
