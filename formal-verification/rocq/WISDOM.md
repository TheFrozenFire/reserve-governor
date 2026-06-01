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
- R072: Abstract-base-class equivalence — slot-agnostic helpers + lens
- R075: OZ TimelockController equivalence methodology — timestamp-as-state-encoding + AccessControl interaction
- R076: ERC4626 equivalence — share-asset arithmetic + inflation defense
- R078: ERC20Votes equivalence — multi-base composition (ERC20 + Votes)
- R079: OZ Governor abstract base equivalence (virtual functions as explicit args)

### The R050 staticcall recipe
- R063: `staticcall` as composite of existing primitives
- R064: `AbiEncoding.v` module
- R065-R071: Per-mutator composite-walker recipe (validated on 12 mutators across 6 contracts)

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

## Push timing — explicit refspec is safer

`git push remote branch` can silently no-op with unusual
branch-tracking config. Prefer:

```bash
git push thefrozenfire <commit-hash>:refs/heads/feature/formal-verification
```

forces fast-forward-or-fail with no tracking ambiguity.
