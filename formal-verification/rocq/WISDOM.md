# Rocq proof discipline (Reserve formal-verification)

Lessons captured while authoring the proof tree under
`formal-verification/rocq/`. Each entry documents a Rocq/Coq 8.20.1
gotcha that cost real time during this work, captured so the next
contributor hits each at most once. Mirrors the `cas/WISDOM.md`
convention.

## R001: Mark FixLib operations `Opaque` before destructs

The simulation's `powu` definition contains `Z.to_nat (Z.log2 _)`
which Coq tries to reduce eagerly during `inversion` of a hypothesis
that mentions a `powu` term. The reduction explodes the goal-term
size and OOMs the kernel.

**Workaround:** before any `injection`/`destruct` of a hypothesis like
`melt s now bal = (s', amt)`, declare:

```coq
Opaque FixLib.powu FixLib.mulu_toUint FixLib.minus FixLib.divrnd.
```

This is the single most common cause of "the proof was working a
moment ago, why does it OOM now": adding a new lemma that touches
`powu` without first marking it opaque blows up downstream proofs.

## R002: Use `injection ... as ... ; subst <name>` over `inversion ... subst`

`inversion H; subst` does maximal substitution: every variable mentioned
in `H` gets substituted away, which forces Coq to evaluate the
right-hand sides, including any large arithmetic expressions
(`powu`, `mulu_toUint`, `divrnd`).

**Workaround:** prefer `injection H as <eq1> <eq2>; subst <name>`. This
keeps the equations as named hypotheses and lets you choose which
variable to eliminate. For pair equalities, the canonical pattern is:

```coq
injection Hpair as Hs'_eq Hamt_eq.
subst s'.
(* Hamt_eq : amount = <giant arithmetic expression> remains symbolic *)
```

Forward `rewrite Hamt_eq` (not `<-`); Coq 8.20's `injection` produces
equations in the `<expr> = name` direction.

## R003: Do NOT install `Z.to_euclidean_division_equations` zify hook

Some Rocq tutorials suggest:

```coq
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
```

Don't. It enables `lia` to reason about division/mod relationships, but
on these proofs the rewrite rules amplify combinatorially. We measured
single-file compile times jump from <1s to 6+ minutes. Direct
`destruct (n mod d =? 0)` plus `lia` is reliably fast.

## R004: Fully qualify imports across simulations/ and proofs/

Module-name collisions are common when both `Reserve.simulations.X`
and `Reserve.proofs.X` are in scope (e.g. both define `Module X.`).
The Rocq compiler rejects bare `Import X` as ambiguous, and the error
message is unhelpful (`The reference X.foo was not found in the
current environment`).

**Workaround:** fully qualify both imports:

```coq
Require Import Reserve.simulations.Throttle.
Require Import Reserve.proofs.Throttle_validity.
Import Reserve.simulations.Throttle.ThrottleLib.
Import Reserve.proofs.Throttle_validity.ThrottleValidity.
```

The convention used throughout this tree: simulation modules are
named after the contract (e.g. `ThrottleLib`); proof modules append
`Proofs` / `Validity` / `Chain` (e.g. `ThrottleProofs`,
`ThrottleValidity`, `ThrottleChain`). Following the convention avoids
most collisions; fully qualifying handles the rest.

## R005: Re-export with `Notation`, not `Theorem name := body.`

Coq's `Theorem` with `:=` requires an explicit type annotation:

```coq
Theorem audit_foo : forall x, P x.
Proof. ... Qed.

(* Re-export: does NOT compile *)
Theorem audit_foo := MyModule.original_foo.   (* error: missing type *)
```

For lossless re-export of an existing lemma, `Notation` is the canonical
form:

```coq
Notation audit_foo := MyModule.original_foo.
```

`Check audit_foo` then prints the original statement. Used throughout
`Audit.v` to alias load-bearing theorems under audit-friendly names.

## R006: `vm_compute; reflexivity` for numerical witnesses

The `_xcheck.v` and `_witnesses.v` files cross-check exact integer
values from CAS witnesses against the Rocq simulation. The canonical
pattern is:

```coq
Lemma w_canonical_input :
  mul (10^18) (10^18 / 2) RoundingMode.FLOOR = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.
```

`vm_compute` invokes the Rocq bytecode VM (much faster than `simpl`
for arithmetic on big integers), then `reflexivity` closes by
syntactic equality. This is the cheapest possible proof shape; prefer
it over `lia` for any goal that's a closed-form numerical equality.

For inequalities at concrete inputs, the analogous pattern is
`vm_compute; discriminate.` against an `=? false` reduction.

## R007: List-output domains need `Forall` lifting

Domains like `BasketHandler.quoteQuantities` and
`Distributor.distributeAmounts` return lists. Their per-element
correctness lemmas need `List.Forall` lifting to express "every
element satisfies P". The canonical induction pattern:

```coq
Lemma quoteQuantities_pointwise s baskets mode :
  P_inputs s baskets ->
  Forall (fun '(_, q) => P_output q) (quoteQuantities s baskets mode).
Proof.
  induction s.(BasketHandler.Storage.collaterals) as [|c rest IH]; cbn.
  - apply Forall_nil.
  - apply Forall_cons; [| apply IH; ...].
    (* per-element discharge *)
Qed.
```

For pointwise comparisons across two list outputs (e.g. FLOOR vs
CEIL `quoteQuantities`), use `Forall2 Z.le` rather than `Forall (fun
x => P x y)`.

## R008: Storage-state preservation needs the call-boundary hypothesis

When proving `<op>_preserves_input_bounded` for an operation that does
arithmetic on the new state field (e.g. `s'.lastAvailable = available
- amount`), the bound on `s'.lastAvailable` cannot in general be
derived from the bound on `s.lastAvailable` alone; production relies
on the EVM's `_safeWrap` revert path to enforce the next-state bound.

**Convention:** model `_safeWrap` as a hypothesis on the post-state:

```coq
Lemma op_preserves_input_bounded
    (s s' : Storage.t) <args> :
  Valid.t s -> InputBounded.t s ->
  <input bounds> ->
  s'.(<arithmetic-derived-field>) <= UINT256_MAX ->   (* the _safeWrap proxy *)
  op s <args> = Result.Success s' ->
  InputBounded.t s'.
```

The on-chain story: a successful `op` is exactly the path on which
`_safeWrap` does not revert; `_safeWrap` reverts iff the post-state
overflows. Hypothesizing the post-state bound is the cleanest model.

Trying to *derive* the post-state bound intrinsically (without the
hypothesis) typically requires new companion lemmas in
`Fixed_safety.v` (e.g. `mulu_toUint_le_when_payoutRatio_le_FIX_ONE`).
Worth doing once for high-touch operations; over-investing here was
the wave-12 `StRSR_uint256_bounds` budget overrun.

## R009: Don't commit auto-translated harness `.v` files

`solc-rocq` emits one `.v` file per harness contract under
`rocq/<HarnessName>.v`. These files are 0–4K+ lines of
auto-generated Yul-derived Rocq. They are:

- regenerable via the documented Docker pipeline (see
  `../contracts/README.md`)
- not referenced by any active proof; Yul-equivalence is parked
- 10K+ lines of generated content if all included

`.gitignore` does not exclude them by extension (we want to track our
hand-written `.v` files). Convention: do not add them to
`_RocqProject` and do not `git add` them.

## R010: Opaque scope is a Goldilocks problem

R001 says mark FixLib operations `Opaque` before destructs. The full
story is more nuanced when the destruct is on a domain-level function
that *contains* FixLib calls — e.g. `BackingManager.computeSurplusSplit`,
`BackingManager.forwardRevenueIter`. Three regimes:

- **All transparent** → `cbn`/`destruct` unfolds FixLib operations
  inside the goal; the term explodes. Build pins coqc at 100% CPU
  indefinitely. (R001's headline failure mode.)

- **Domain function opaque too** → proofs that `unfold computeSurplusSplit`
  to expose its branches fail with `computeSurplusSplit is opaque`.
  Going too broad breaks lemmas that legitimately need the unfolded
  form.

- **FixLib opaque, domain function transparent, domain function's
  *outer wrapper* opaque** → the sweet spot. The domain function can
  unfold to expose its `if/match` structure; the FixLib operations
  inside it stay symbolic; the outer wrapper (e.g. `forwardRevenueIter`
  vs `forwardRevenueIter_aux`) is opaque so a `destruct` on it doesn't
  trigger evaluation through the entire iteration.

When you're writing proofs that span a domain function + its inner
FixLib content + its outer iteration wrapper, set the Opaque list at
exactly two layers: FixLib primitives, and the iteration wrapper.
Leave the middle layer transparent.

## R011: Coq 8.20 nested intro pattern parser quirk

The pattern `[X [Y Z]]` (right-nested conjunction destructor) trips
the Coq 8.20 parser when the identifiers contain underscores:

```coq
(* fails with "Syntax error: '|' or ']' expected" *)
pose proof (lemma_returning_3_conj args) as [Hr_nn [Ht_nn Hd_nn]].

(* parses cleanly, identical semantics *)
pose proof (lemma_returning_3_conj args) as Hnn.
destruct Hnn as (Hr_nn & Ht_nn & Hd_nn).
```

The conj-pattern shorthand `(X & Y & Z)` is the safe form. Use it for
any nested destructor with underscore-bearing names. This is purely
a lexer issue — the semantics are identical — but it costs an
otherwise inexplicable build failure when you don't know about it.

## R012: Per-file build timeout is mandatory

A tactic explosion (the R001 / R010 patterns) can pin coqc at 100%
CPU indefinitely. Without a per-file timeout, a single bad file
hangs the whole build. The build script wraps each `coqc` invocation
with `timeout` (Linux) or `gtimeout` (macOS, via `brew install
coreutils`). Default budget is 180s; override with `RB_TIMEOUT=<sec>`.

If a build fires the timeout, the diagnostic points at WISDOM.md
R001 — that's almost always the cause. Don't bypass the timeout
without first verifying the file *needs* the longer budget; it's
much more likely you have an Opaque hole.

## R013: Two-version operations are a maintenance trap

When extending a simulation to model production semantics more
faithfully (e.g. Furnace's `setRatio_with_melt` calling `melt` first
to capture old-ratio accrual; Distributor's
`distributeAmounts_with_dao_fee` modeling the DAO fee leg), the
temptation is to add the new version *alongside* the existing simpler
one. This is dangerous: a future proof writer reaching for the
simpler version unwittingly picks a model that production doesn't
exhibit. The proof is technically correct but the claim it supports
is narrower than the reader thinks.

Pick a single canonical version. If both are needed (e.g. for proofs
that don't care about ordering), make the simpler one a derived
specialization (`setRatio s r := snd (setRatio_with_melt s r 0 0)`)
or rename it explicitly (`setRatio_unordered`) so the production
mismatch is in the name itself.

## R014: `simpl` aggressively unfolds `Z.eqb` and breaks subsequent rewrites

In Coq 8.20, `simpl` will eagerly unfold `Z.eqb` into a raw
`match` on `Z.pos`/`Z.neg` constructors. Subsequent surface-level
tactics like `rewrite Z.eqb_refl` or `rewrite Hxeqby` then fail to
match because the term shape no longer carries `Z.eqb` at all.

Workaround: keep `Z.eqb` opaque to `simpl` via either
`cbn -[Z.eqb]` or by reaching for the goal with `change` + `subst`
instead. `cbn` respects the unfolding blacklist where `simpl`
ignores it.

## R015: Nested intro patterns crash the Coq 8.20 parser

In addition to R011 (`[X [Y Z]]` failing on conj-elimination),
nested OR-patterns like `[Heq | []]` and `[Heq | [Heq2 | Hin]]`
also fail to parse. Symptoms: cryptic "syntax error" at the
opening `[` with no useful position info.

Workaround: expand each nesting to an explicit `destruct` chain in
the proof body, or use Coq 8.20's `(X & Y & Z)` conj-pattern
syntax for AND and `[X | Y | Z]` flat OR-pattern syntax where the
shape allows it.

## R016: Logical-path short-name clash when both `simulations.X` and `proofs.X` exist

When a domain `X` has both `simulations/X.v` and `proofs/X.v`, the
`Import` mechanism doesn't pick a winner — the unqualified name
`X` resolves to whichever was imported last (typically not the one
you wanted). Both modules need to be explicitly imported:

```
Require Import ReserveGovernor.simulations.X.
Require Import ReserveGovernor.proofs.X.
Import ReserveGovernor.simulations.X.   (* picks simulations.X.X *)
Import X.                                (* alias for the inner module *)
```

The second `Import X.` aliases the inner module after the qualified
form has already pinned which `X` we mean. Skipping it leaves
unqualified references bound to whichever `Require` ran last.

## R017: `destruct ... eqn:H` does not substitute through `set`-bound lets

A pattern like:

```
set (v := f x).
destruct (v) eqn:Hv.   (* Hv : v = ... ; does NOT rewrite f x *)
```

doesn't unfold `v` in the goal — the `eqn:Hv` records the
post-`set` equation, not the original `f x`. Subsequent `rewrite`
attempts against `f x` then fail.

Workaround: unfold the `set` binding before destructing, or
destruct directly on `f x`:

```
unfold v. destruct (f x) eqn:Hv.   (* rewrites the original *)
```

## R018: Use `cbn -[Z.div Z.mul SCALAR DEC18]` over `lia` for 10^18 arithmetic

`lia` is correct over the rationals but pays a steep symbolic cost
when the goal contains `10^18` literals — typical reward-math
calculations spent 30-60s per goal in early rounds.

`cbn -[Z.div Z.mul SCALAR DEC18]` (or whichever D18 / scaling
constants are in the goal) reduces the structural part while
keeping the heavy operations symbolic. The remaining lia step is
then small and fast. Apply this preemptively in any rewards /
ratio / exchange proof to keep build times tractable.

## R019: `Dict.Eq.eqb` typeclass projection blocks `cbn` / `simpl` reduction

The upstream rocq-of-solidity's `Dict.Eq.eqb` is a typeclass field
(`Class C (A : Set) := eqb : A -> A -> bool`), not a regular
Definition. Neither `simpl` nor `cbn` reduces it to its instance
body, even when the dict is concrete (`Dict.t Address.t V` where
`Address.t = Z` and the instance is `IZ := Z.eqb`).

Symptom: in Dict get-after-set proofs, after `induction dict;
cbn`, the cons-branch goal contains `Dict.Eq.eqb k key` rather
than `Z.eqb k key`. `destruct (k =? key)` and `rewrite Z.eqb_refl`
both fail to find the subterm they expect because the term in the
goal is still the typeclass projection.

Workaround: use `hauto` (`From Hammer Require Import Tactics.`) as
the kitchen-sink tactic. It handles the typeclass dispatch + the
case-split + the induction step in one go:

```coq
Lemma dict_get_declare_or_assign_eq {V : Set}
    (dict : Dict.t Address.t V) (key : Address.t) (value : V) :
  Dict.get (Dict.declare_or_assign dict key value) key = Some value.
Proof.
  unfold Dict.declare_or_assign.
  induction dict as [|[k v] dict IH];
    hauto lq: on use: Z.eqb_refl, Z.eqb_eq, Z.eqb_neq.
Qed.
```

Will apply to every storage-projection proof in
`proofs/equivalence/` since each one needs Dict.get-after-set
lemmas. Prefer `hauto`; fall back to manual unfolds only when
`hauto` exhausts its depth bound.

## R020: `Stdlib.timestamp` (and friends) — RESOLVED in dev clone

**Resolution status**: solved upstream as of the
`~/git/reserve/formal-verification/rocq-of-solidity` dev clone
(commit `10387d00 doc: update`, ahead of the older
`~/git/reserve/_tools/rocq-of-solidity` checkout). Our
`scripts/rocq-build` now defaults `ROCQ_TREE` to the dev clone.

In the dev clone:

```coq
Definition timestamp : M.t U256.t :=
  LowM.Primitive Primitive.GetBlockTimestamp M.pure.

Definition number : M.t U256.t :=
  LowM.Primitive Primitive.GetBlockNumber M.pure.
```

and `eval_primitive` (line 1518–1532) has clauses that read from
`State.block_timestamp` and `State.block_number`. Verified end-to-end
by `proofs/equivalence/Sandbox.v::R020VerificationCheck` — both
`timestamp_returns_block_timestamp` and `number_returns_block_number`
close in three tactic steps.

The original blocker text follows for archival.

---

The rocq-of-solidity upstream defines several `Stdlib.*` primitives
as `LowM.Impossible "<name>"` rather than giving them real
semantics:

- `timestamp`, `number`, `coinbase`, `difficulty`, `prevrandao`,
  `gaslimit`, `blobhash` (block context)
- `balance`, `selfbalance` (account context)
- `chainid`, `origin`, `gasprice` (transaction context)

What works (Environment-driven): `address`, `caller`, `callvalue`,
`calldataload`, `gas` (hardcoded as 1000).

The `RunO.t` Hoare-triple judgment has no inference rule for
`LowM.Impossible` — any proof that reaches one of these calls gets
stuck. Symptom: equivalence proofs for contracts that read
`block.timestamp` or `block.number` cannot close against the
current upstream apparatus.

For governor work this is a substantive blocker — ThrottleLib,
UnstakingManager, Governor, Timelock, StakingVault rewards all read
`block.timestamp`. The clean fix is patching the upstream's
`Stdlib.timestamp` to read from a new `Environment.timestamp`
field; the workaround for any specific proof is to skip the contract
or supply a governor-side `Stdlib`-shim. See
`notes/equivalence_proof_methodology.md` § Phase 1.2 outcome for the
full treatment.

## R021: `RunO.t` has no `CallContract` constructor — RESOLVED via upstream patch

**Resolution status**: solved by upstream patch
`TheFrozenFire/rocq-of-solidity:feat/env-block-context` commit
`51f4e4cff2` ("Add RunO.CallContract proof rule + cc tactic").
The patch adds a permissive `RunO.CallContract` constructor and a
matching single-letter tactic `cc`.

The new rule:

```coq
| CallContract (address : U256.t) (value : U256.t) (input : list Z)
    (is_static : bool) (is_delegate : bool)
    (k : U256.t -> LowM.t A)
    (call_result : U256.t)
    (state state_inter state' : option State.t) :
  {{? codes, environment, state_inter | k call_result ⇓ output | state' ?}} ->
  {{? codes, environment, state |
    LowM.CallContract address value input is_static is_delegate k ⇓ output
  | state' ?}}
```

The rule is intentionally permissive — the proof author picks
`call_result` and `state_inter` freely. **Soundness shifts to the
proof-author level**: the choice must be justified by a separate
callee-spec axiom (matches how Certora handles cross-contract
calls via spec-level interface contracts). The fully-sound
alternative — a meta-theorem connecting `eval` to `RunO` for
CallContract — is substantial work and remains open.

For our governor proofs, the workflow is: each external call site
needs a paired axiom (or sub-lemma) tying the callee's address +
input bytes to a `call_result` value and the storage delta. The
audit-time obligation is reviewing those axioms.

Verified end-to-end by
`proofs/equivalence/Sandbox.v::R021VerificationCheck::callcontract_can_be_discharged`
— closes in `cc. apply RunO.Pure.`

The original blocker text follows for archival.

---

`LowM.t` has a `CallContract` constructor for `staticcall` /
`delegatecall` / `call` to other contracts. But `RunO.t` (the
upstream's proof judgment, defined at
`rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v:1462–1530`)
has no inference rule for `LowM.CallContract`. Available
constructors: `Pure`, `PureNone`, `Primitive`, `PrimitiveNone`,
`CallFunction` (within-contract function calls), `Let`,
`LetUnfold`, `Call`, `CallUnfold`, `LoopOngoing`,
`LoopTerminating`. Cross-contract is absent.

This is broader than R020. R020 blocks contracts that read
`block.timestamp`; R021 blocks contracts that make any external
call (`staticcall`/`delegatecall`/`call`). For the governor
codebase:

| Contract | Time blocker (R020) | CallContract blocker (R021) |
|---|---|---|
| ThrottleLib | YES | no |
| UnstakingManager | YES | YES (IERC20 transfer) |
| Governor | YES | YES |
| Timelock | YES | YES (target.call) |
| StakingVault | YES | YES (IERC20) |
| VersionRegistry | no | YES (isOwner, version()) |
| RewardTokenRegistry | likely no | YES (isOwner) |
| Guardian | no | YES (cancel chain) |

ThrottleLib is the **only** governor contract that's blocked only
on R020 and not on R021. Patching just R020 unblocks it alone;
unblocking the others additionally needs an upstream `CallContract`
proof apparatus (much bigger effort — model the called contract's
semantics in some bounded way, or trust the caller's expectation
via uninterpreted-function-style axioms).

For our workstream this means: either patch upstream both ways
(weeks of work, not days), or park the equivalence-proof tier
entirely. The intermediate option is to close ONLY ThrottleLib
(after R020 patch) as a demonstration target and leave Caveat-5
permanently partial for the rest.

## R022: `Dict.Eq.eqb` on tuple keys anomalies `cbn`/`simpl`/`hauto` — RESOLVED

When mechanizing lemmas about `Dict.t (U256.t * U256.t) U256.t` (used
by the upstream's `StorableValue.MapStruct` variant), the
`Dict.Eq.eqb (a, b) (c, d)` projection dispatches through the
`Dict.Eq.ITuple2` typeclass instance and Coq 8.20.1 anomalies when
the surrounding tactic tries to reduce it.

Concretely, the goal looks like:

```coq
StorableValue.map_get_u256 (some_flat_map sim) (account, 0)
  = ...some_field_accessor account
```

After `unfold StorableValue.map_get_u256, Dict.get`, the head reduces
to `match Dict.Eq.eqb (account, 0) (k, j) with ...` and *any* attempt
to reduce that projection — `simpl`, `cbn`, `cbn -[Dict.Eq.eqb]`,
even `hauto lq: on` — surfaces:

```
Conversion test raised an anomaly:
Anomaly "Uncaught exception Not_found."
```

The anomaly is at the kernel level, not the tactic level. It occurs
even with `at i j`-positional `unfold` and even when restricting the
blacklist to `Dict.Eq.eqb`.

### Resolution (commit 004f75f)

The fix is to combine three independent tricks:

1. **Definitional rewrite lemma**: `Dict_Eq_eqb_ZZ_pair_unfold` in
   `proofs/equivalence/Common.v` exposes the reduction at the lemma
   level via `Proof. reflexivity. Qed.` — the kernel performs the
   typeclass-instance reduction at definition time, so `reflexivity`
   succeeds where `simpl`/`cbn`/`hauto` anomaly.

   ```coq
   Lemma Dict_Eq_eqb_ZZ_pair_unfold (a1 a2 b1 b2 : Z) :
     @Dict.Eq.eqb (Z * Z) Dict.Eq.ITuple2 (a1, b1) (a2, b2)
     = andb (Z.eqb a1 a2) (Z.eqb b1 b2).
   Proof. reflexivity. Qed.
   ```

2. **One-step cons-unfolding**: `map_get_u256_pair_cons` exposes the
   `Dict.get` Fixpoint's cons-step body via `change` (the body is
   definitionally equal to the `if`-form). Combined with #1, this
   lets us peel off one cons-list head without invoking `cbn`.

   ```coq
   Lemma map_get_u256_pair_cons rest a c b d v :
     map_get_u256 (((c, d), v) :: rest) (a, b)
     = if andb (a =? c) (b =? d) then v
       else map_get_u256 rest (a, b).
   Proof.
     unfold StorableValue.map_get_u256.
     change (Dict.get (((c, d), v) :: rest) (a, b))
       with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (a, b) (c, d)
             then Some v else Dict.get rest (a, b)).
     rewrite Dict_Eq_eqb_ZZ_pair_unfold.
     destruct (Z.eqb a c && Z.eqb b d); reflexivity.
   Qed.
   ```

3. **`pose proof` + `replace ... in H` + `exact H`** for goals where
   `rewrite` fails to find a pattern despite obvious unifiability.
   Build the hypothesis, normalize it to match the goal exactly,
   then close by `exact`. This sidesteps `rewrite`'s strict matching
   when the LHS pattern contains subterms that need separate
   simplification.

### Touchpoints in this repo

- `proofs/equivalence/Common.v`: hosts the unblocker lemmas
  (`Dict_Eq_eqb_ZZ_pair_unfold`, `map_get_u256_pair_cons`,
  `Dict_Eq_eqb_Z_unfold`, `map_get_u256_Z_cons`).
- `proofs/equivalence/ThrottleLib.v`: `throttles_packed_currentCharge`,
  `throttles_packed_lastUpdated` — CLOSED.
- `proofs/equivalence/UnstakingManager.v`: `locks_packed_get_user`,
  `locks_packed_get_amount`, `locks_packed_get_unlockTime`,
  `locks_packed_get_claimedAt` — all four CLOSED via a generalized
  `flat_entries` helper plus the per-offset `flat_entries_cons_peel_*`
  lemmas. The accumulator-threading shape of `locks_packed_aux`
  required an additional `locks_packed_eq_flat` bridge.

## R023: Z.lor on if-then-else arguments resists tactical reduction — RESOLVED

After unfolding [Pure.or], [Pure.iszero], [Pure.eq], [Pure.div], a
goal like

```coq
Pure.iszero (Z.lor (if x =? 0 then 1 else 0)
                   (if y =? d then 1 else 0))
```

does not reduce via `cbn` / `simpl` / `vm_compute` to a single
0-or-1 value. The issue: `Z.lor` is defined via positional bit-level
case analysis that does NOT pattern-match on `if-then-else` results
cleanly. Even after case-splitting on `x =? 0` and `y =? d` so both
arguments are concrete 0 or 1, `cbn [Z.lor]` exposes the
`Pos.lor`/`N.ldiff` recursion machinery rather than reducing to 0
or 1 outright.

### Resolution (commit 8dde5b9)

The trick is much simpler than the workaround sketch I wrote
originally. Don't use `eqn:` on the destructs:

```coq
destruct (x =? 0) eqn:Hx0.
- apply Z.eqb_eq in Hx0. subst x.   (* x replaced by 0 in goal *)
  destruct (y =? 0) eqn:Hyb.
  + apply Z.eqb_eq in Hyb. subst y.  (* y replaced by 0 *)
    s. repeat (lu || cu || p).        (* all if-thens fully reduce; named tactics close *)
  + s. repeat (lu || cu || p).
- apply Z.eqb_neq in Hx0.
  assert (Hdiv : (x*y)/x = y).
  rewrite Hdiv, Z.eqb_refl.
  s. repeat (lu || cu || p).
```

The key insight: `destruct ... eqn:H` adds a hypothesis but does
NOT substitute back into `(if cond then ... else ...)`-shapes in
the goal. After `apply Z.eqb_eq in H. subst <var>`, the variable
is replaced everywhere, including inside `(if var =? ... then ...
else ...)`. Then `s. repeat (lu || cu || p)` walks the named-tactic
chain through the fully-reduced expression, and `p` (apply RunO.Pure)
closes goals where the value/state match syntactically.

No `Z_lor_bool_unfold` helper needed — the closure happens because
the substituted concrete values make `Z.lor 0 0`, `Z.lor 0 1`, etc.
fully evaluate. Goal becomes `Result.Ok (0 * 0) ⇓ Result.Ok 0`,
discharged by `p`.

### Touchpoints in this repo

- `proofs/equivalence/ThrottleLib.v`: `run_checked_mul_t_uint256`
  CLOSED via this pattern. Final proof is ~25 lines.

## R024: `l. { c. { apply leaf } ... }` pattern is the canonical step-through

The upstream's erc20 body proof uses a uniform pattern for stepping
through a Yul `do~ [[ ... ]]` block that contains nested `M.call`s:

```coq
l. {                              (* one Yul let-step *)
  c. { apply run_inner_thing. }   (* first M.call *)
  c. { apply_run_mstore. }        (* next M.call uses prior result *)
  CanonizeState.execute.          (* normalize make_state shape *)
  p.                              (* close with Pure for the let RHS *)
}
```

Key insights:

1. `l.` (eapply RunO.Let) breaks the `LowM.Let` head into call-step +
   continuation. One `l.` per Yul let-step (each `let~ ... :=` or
   `do~ [[ ... ]]`).
2. Inside the `l. { ... }` block, sequential `c. { apply leaf. }`
   discharge each nested `M.call` in the RHS in order. The
   continuation of one `c.` feeds the next.
3. `CanonizeState.execute` is mandatory after any mstore — it folds
   the post-state back into [make_state env state mem storage] form
   so subsequent applications match.
4. Conclude the inner block with `p.` (apply RunO.Pure).

A different shape — `lu. cu. apply_run_mstore` — also works for
some simpler bodies but doesn't compose with `CanonizeState.execute`
the same way. When in doubt, copy erc20's pattern.

### Anti-pattern

A bare

```coq
unfold f. lu. l. { c. { apply leaf. } ... } repeat (lu || cu || p).
```

leaves intermediate state-shapes that the next `l.` cannot match
against. Always interleave `CanonizeState.execute` after each
mstore in a let-block.

## R025: `pe` (PureEq) leaves two subgoals

`pe := apply RunO.PureEq` is the goto for closing a `LowM.Pure e1 ⇓ Result.Ok e2`
goal when `e1 = e2` is the obligation. It splits the goal into:

  1. The value equality (`e1 = e2`).
  2. The state-equality (`state_after = state_before`).

So the canonical close is:

```coq
pe.
- f_equal. lia.      (* value equality *)
- reflexivity.       (* state equality *)
```

OR chain with `;` to dispatch both:

```coq
pe; f_equal. lia.    (* hope both subgoals close uniformly *)
```

The chaining form works when both subgoals reduce by the same
tactic. Trying `pe. rewrite ... reflexivity.` without splitting will
hit "Expected a single focused goal but 2 goals are focused."

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `run_cleanup_t_uint160_on_address` uses the two-subgoal split form.
- `run_checked_add_t_uint256` (upstream pattern) uses
  `pe; f_equal. lia.` chaining.

## R026: `let~ '` desugars to M.strong_let_, not LowM.Let directly

The generated shallow form uses `let~ ' (a, b) := e in k` notation
which desugars to `M.strong_let_ e (fun '(a, b) => k)`. The
`M.strong_let_` is

```coq
Definition strong_let_ {A B : Set} : t A -> (A -> t B) -> t B :=
  generic_let (fun A B => @LowM.Let B A).
```

where `generic_let f e1 e2 = f e1 (fun result => match result with
| Ok v => e2 v | Return p s => LowM.Pure (Return p s) | Revert ...
end)`.

So `let~ ' pat := e in k` desugars to

```coq
LowM.Let e (fun result =>
  match result with
  | Ok pat => k
  | Return p s => LowM.Pure (Result.Return p s)
  | Revert p s => LowM.Pure (Result.Revert p s)
  end)
```

This means **immediately after `unfold f`, the goal head is NOT
`LowM.Let` directly** — it's `M.strong_let_` (or `M.let_` / `M.pure`
/ `M.call`). The `l` / `c` / `p` tactics from RunO.* won't match
until you unfold these wrapper definitions.

### Workaround

Add this unfolding step right after `unfold <function>`:

```coq
unfold M.strong_let_, M.generic_let, M.pure, M.call.
```

After this, the underlying `LowM.Let` / `LowM.Pure` / `LowM.Call`
shapes are exposed and `l` / `p` / `c` apply. The continuation
introduced by `generic_let` (the `match result with | Ok ... |
Return ... | Revert ... end` wrap) needs `s` (named tactic for
`fold @LowM.let_; simpl_goal`) to reduce after each call discharge.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`: Phase F closure uses this
  pattern in `run_getProposalsAvailable_public_make_state`.

### Closure template (works for thin wrappers)

```coq
Proof.
  pose proof <inner_theorem> as HE.
  destruct HE as [state' HE].
  eexists state'.
  unfold <wrapper_function>.
  unfold M.strong_let_, M.generic_let, M.pure, M.call.
  repeat
    (lazymatch goal with
     | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
     | |- {{? _, _, _ | LowM.Call <leaf1> _ ⇓ _ | _ ?}} =>
         c; [ apply <leaf1_lemma> | ]
     | ...one arm per leaf...
     | |- {{? _, _, _ | LowM.Call <inner_fn _ _> _ ⇓ _ | _ ?}} =>
         c; [ exact HE | ]
     | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
         apply RunO.Pure
     | |- _ => s
     end).
Qed.
```

Closing a substantive body (Phase E shape, not thin wrapper) needs
additional arms for memory-writing primitives (mstore + keccak +
CanonizeState.execute) and storage reads. Those are documented in
R024 (canonical step-through pattern).

## R027: `eapply RunO.Call` two-subgoal split — pose-once, dispatch separately

When a function-body walker hits a `LowM.Call e LowM.Pure` (the
`M.call e` shape, which is how every shallow `f ~(| args |)` desugars
after R026's unfold), `eapply RunO.Call` produces two subgoals:

1. `e ⇓ ?out_inter | ?st_inter`           — the call premise
2. `LowM.Pure ?out_inter ⇓ ?out | ?st`    — the continuation, which
                                              is just the `M.call`
                                              wrapper's identity pass

The right move is `eapply RunO.Call; [ <call-closer> | apply RunO.Pure ]`.
The continuation subgoal is closed by `RunO.Pure` because Pure's
constructor signature `Pure state : LowM.Pure output ⇓ output | state`
makes it pattern-match-only: it unifies `?out := ?out_inter` and
`?st := ?st_inter` automatically, propagating the call's post-state.

A prior session attempted `eapply RunO.Call; [ apply Hmia | apply Hmia ]`
where `Hmia` was the helper-lemma instance for the call. This fails on
the second subgoal because Hmia's conclusion is about the call (i.e.,
`mapping_index_access ⇓ ...`), not about `LowM.Pure`. The deferred
"state-threading issue" in commit `a6f8007` was just a misidentified
second subgoal — the closure pattern above resolves it cleanly.

### Anti-pattern: pose-inside-the-arm

A failed earlier shape posed the helper lemma *inside* the lazymatch
arm:

```coq
| |- {{? _ | LowM.Call (mapping_index_access _ _) _ ⇓ _ | _ ?}} =>
    pose proof (run_mapping_index_access ...) as Hmia;
    destruct Hmia as [mp Hmia];
    eapply RunO.Call; [ apply Hmia | ]   (* missing 2nd dispatch *)
```

Three issues:
- `pose proof` + `destruct` repeats on every walker iteration
- `mp` (the existential witness) gets re-introduced and shadowed
- single-bracket dispatch leaves the second subgoal open, which the
  `try (repeat ...)` then absorbs silently — looks like progress but
  isn't.

### Correct shape: pose-once outside the walker

Pose the lemma **once** at the top of the proof, destruct the
existential once, then dispatch both subgoals in the lazymatch arm:

```coq
Proof.
  pose proof (run_mapping_index_access codes env state_base
                <slot> <key> <storage> <memory>
                <H_key> <H_mem>) as Hmia.
  destruct Hmia as [mp Hmia].
  ...
  repeat (lazymatch goal with
    ...
    | |- {{? _ | LowM.Call (mapping_index_access_t_... _ _) _ ⇓ _ | _ ?}} =>
        eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
    ...
    end).
```

### Touchpoints

- `proofs/equivalence/ThrottleLib.v` Phase E
  (`run_getProposalsAvailable_equivalent_make_state`) — unblocked the
  walker past the keccak/memory write step, which now threads the
  `keccak256_tuple2 account (Pure.add 0 1)` result through to the
  subsequent storage reads.

The same pattern applies for any non-leaf helper that returns an
existential (memory-mutating helpers, scratch-using helpers,
struct-field accessors).

## R028: Walker unfold list must include M.let_, not just M.strong_let_

When the shallow form has a call with a NESTED call as an argument —
e.g., `checked_mul ~(| x, convert(y) |)` — the inner call gets
sequenced via `M.let_` (lowercase), not `M.strong_let_`. The two are
similar but desugar to different underlying constructors:

- `M.strong_let_ e1 e2 = LowM.Let e1 (fun result => match result …)`
  — matches the walker's `LowM.Let _ _` arm via [l].
- `M.let_ e1 e2 = LowM.let_ e1 (fun result => match result …)`
  — `LowM.let_` (lowercase) is a `Fixpoint` that walks the
  expression, not a constructor; the walker's `LowM.Let` arm
  does NOT match it.

If your unfold list at proof entry is only
`unfold M.strong_let_, M.generic_let, M.pure, M.call.`, nested-call
sites leave `M.let_` in the goal and the walker stalls. Add `M.let_`
to the unfold list:

```coq
unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
```

After this, both top-level `let~` and nested `M.let_` expose their
underlying `LowM.let_ ...` form which then steps under `s` (which
runs `simpl_goal` and reduces the Fixpoint).

### Touchpoints

- `proofs/equivalence/ThrottleLib.v` Phase E. The check for
  `checked_mul ~(| (now - lastUpdated), convert_t_rational_…_to_t_uint256
  ~(| FIX_ONE |) |)` was leaving an unwalked `let* v := … in …` until
  `M.let_` was added to the unfold list.

## R029: Checked-arithmetic preconditions — `>=` vs `<=` direction matters

The upstream's checked-arithmetic leaves take their no-underflow /
no-overflow preconditions as `<=` (or `<`) inequalities:

```coq
Lemma run_checked_sub_t_uint256 codes env state (x y : U256.t)
    (H_x : 0 <= x < 2^256)
    (H_y : 0 <= y < 2^256)
    (H_no_underflow : y <= x) :
  …
```

If your context hypothesis is `now >= lastUpdated` (i.e., `Z.ge`),
`exact H_now_geq` against `lastUpdated <= now` FAILS even though the
two are definitionally equal (`Z.ge x y := y <= x`). Coq's `exact`
requires syntactic-after-conversion identity, and the `Z.ge`
wrapper doesn't unfold during unification.

### Workaround

Use `lia` instead of `exact` for the no-underflow / no-overflow
precondition slot — `lia` understands both directions and discharges
either way:

```coq
c; [ apply ThrottleLibLeaves.run_checked_sub_t_uint256;
     [ exact H_x_validity
     | exact H_y_validity
     | lia ] | ]
```

### Touchpoints

- `proofs/equivalence/ThrottleLib.v` Phase E checked_sub arm. The
  diagnostic trail showed all preconditions reaching their idtac
  markers, but the third (`exact H_now_geq`) silently failed —
  `lia` closes it cleanly.

The same trap likely applies to checked_mul, checked_div,
checked_add arms with `<` / `>=` preconditions sourced from a
context hypothesis written in the opposite direction.

## R030: `cbn; lia` over `10^18` is pathologically slow — use `change` instead

A single `unfold ProposerThrottle.FIX_ONE; cbn; lia` invocation in
`get_throttle_currentCharge_capped` was costing **26.8 seconds** —
basically the entire ThrottleLib.v compile time. Profile via
`coqc -time` flagged it as one tactic.

The cause: `cbn` was being asked to reduce `10^18 = Z.pow 10 18`
to its 19-digit decimal value. Whatever path `cbn` takes for
non-binary bases is dramatically slower than for `2^256` (which
parallel proofs reduce in <0.1s). Possibly the binary-exponentiation
fast path applies cleanly to base 2 but not base 10; possibly the
intermediate Z values are larger; in any case the empirical gap is
20-300x.

### Workaround

Replace `cbn; lia` with targeted `change` substitutions that bypass
the kernel-level reduction:

```coq
(* Slow: 26.8s *)
unfold ProposerThrottle.FIX_ONE; cbn; lia.

(* Fast: 1.4s *)
change ProposerThrottle.FIX_ONE with 1000000000000000000.
change (some_record.(projection)) with 0.   (* if needed *)
lia.
```

`change A with B` is convertibility-checked once, no kernel reduction.
`lia` then sees a numeric literal directly.

### When this applies

- Any `cbn` / `simpl` / `vm_compute` call that touches a non-binary
  large power (10^N, 60^N, etc.).
- Field-validity helpers on default-record projections.
- Goal reductions involving big rational constants.

### How to detect

```sh
coqc -time <file>.v 2>&1 | awk '/secs$/' | sort -gr | head
```

Top entry is the slowest tactic. Anything >1s for an arithmetic
goal is worth investigating — usually a `change`-then-`lia` fix.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `get_throttle_currentCharge_capped`. ~27s → ~1.4s after the swap.

## R031: `destruct (expr) eqn:Hgt` requires the exact same syntactic form in all hypotheses

### The trap

Standard pattern: case-split on a boolean inside a hypothesis.

```coq
Hclamp : ((... charge_raw ... / PROPOSAL_THROTTLE_PERIOD) >? FIX_ONE) = false
```

You want to derive `charge_raw <= FIX_ONE`. Reaching for
`destruct (charge_raw >? FIX_ONE) eqn:Hgt` to case-split — but the
destruct silently abstracts the expression in every hypothesis it
touches, and that abstraction fails with
`Found no subterm matching ... in Hclamp` if the expression in
Hclamp and the destruct expression have any syntactic divergence,
even when they're definitionally equal.

In practice this hits when `PROPOSAL_THROTTLE_PERIOD := 12 * 3600`
gets unfolded inside Hclamp (showing as `(12 * 3600)`) but the
destruct uses the symbol. Or when the goal has `43200` but the
hypothesis still has `(12 * 3600)`.

### Working approaches

1. **Abstract via `set` first.** Set introduces a fresh local
   variable for the boolean expression, then destruct the variable:

   ```coq
   set (b := charge_raw >? FIX_ONE) in *.
   destruct b eqn:Hgt.
   ```

   `set ... in *` folds the expression in both hypothesis and goal,
   so they share one definition. Destruct on the variable name avoids
   the syntactic-match problem entirely.

2. **Apply `Z.eqb_eq` upfront.** If the hypothesis is in
   `(... =? 0) = true` form, `apply Z.eqb_eq in H` flattens it to
   `(...) = 0`. This often makes the structure more amenable to
   the next step.

3. **Use `Z.gtb_spec` for `gtb = false ⇒ ≤`.** `Z.gtb_ge` doesn't
   exist in Coq 8.20's ZArith. The BoolSpec pattern is:

   ```coq
   destruct (Z.gtb_spec a b) as [Hlt|Hle];
     [congruence | exact Hle].
   ```

   `congruence` handles the contradictory branch where
   `(a >? b) = true` clashes with the `Hgt : (a >? b) = false`
   in context.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `run_getProposalsAvailable_equivalent_make_state` Goal 1 (unclamped
  `checked_mul` precondition). Initial attempts with raw `destruct`
  failed; `set ... in *; destruct b eqn:Hgt; apply Z.eqb_eq in
  Hclamp; rewrite Hgt in Hclamp; discriminate` closes the
  contradictory branch.

## R032: Phase E syntactic-vs-algebraic gap on `Z.min FIX_ONE raw` — RESOLVED via `RunO.PureEq`

### The gap (resolved 2026-05-29)

The contract emits `(FIX_ONE, cap * FIX_ONE / FIX_ONE)` in the
clamped branch (when `raw > FIX_ONE`). The theorem expects
`(readCharge, proposalsAvailable)` from the sim, where
`readCharge = Z.min FIX_ONE raw` and
`proposalsAvailable = (cap * Z.min FIX_ONE raw) / FIX_ONE`.

These are algebraically equal when `raw > FIX_ONE` (`Z.min` reduces
to `FIX_ONE`), but `apply RunO.Pure` uses syntactic unification and
won't reduce `Z.min` without an explicit case-split. The unclamped
branch has the inverse problem: `(raw, cap*raw/FIX_ONE)` vs
`(Z.min FIX_ONE raw, ...)` where `raw ≤ FIX_ONE ⇒ Z.min = raw`.

### The fix: `RunO.PureEq` (alias tactic `pe`)

The upstream library exposes a constructor `RunO.PureEq` that
accepts syntactically-different outputs with a side equality proof:

```coq
Lemma PureEq codes environment {A : Set} (output output' : A) state state' :
  output = output' ->
  state = state' ->
  {{? codes, environment, state | LowM.Pure output ⇓ output' | state' ?}}.
```

Where `RunO.Pure` requires `output ≡ output'` syntactically, `PureEq`
just needs them provably equal. This is the right tool for bridging
if-then-else branches whose concrete forms equal a shared abstract
form (like `Z.min FIX_ONE raw`).

### Closure pattern

```coq
(* Goal 4 (clamped): emit is (1e18, cap*1e18/1e18); shared
   metavariable expects (Z.min 1e18 raw, cap*Z.min 1e18 raw/1e18). *)
apply RunO.PureEq.
- (* output equality *)
  assert (E : Z.min 1e18 raw_expr = 1e18) by (apply Z.min_l; <bound>).
  rewrite E. reflexivity.
- (* state equality *)
  reflexivity.
```

The single `rewrite E` substitutes `Z.min 1e18 raw_expr` with `1e18`
in ALL positions of the goal at once (because they're all the SAME
subexpression — Coq's rewrite finds and substitutes uniformly).
After that, the two sides become syntactically equal, and
`reflexivity` closes.

### Partial-closure pattern that works (Goal 2.B unclamped)

The unclamped branch closes with `Z.min_r` because there's a single
`raw` expression to substitute, and the substitution propagates
naturally:

```coq
(* Goal 2.B final emit: LowM.Pure (Result.Ok (BlockUnit.Tt,
   (raw, cap*raw/FIX_ONE))). raw <= FIX_ONE from Hclamp = true. *)
replace raw with (Z.min FIX_ONE raw)
  by (apply Z.min_r; exact Hle_raw).
apply RunO.Pure.
```

The result: shared metavariable picks up `(Z.min FIX_ONE raw,
cap*Z.min FIX_ONE raw/FIX_ONE)` — Goal 2 closes cleanly.

### Why the symmetric Goal 4 closure fails

The clamped branch has `(FIX_ONE, cap*FIX_ONE/FIX_ONE)`. The literal
`FIX_ONE` appears in three positions: charge value, multiplier in
`cap*FIX_ONE`, and divisor in `/FIX_ONE`. We want positions 1 and 2
to become `Z.min FIX_ONE raw` but position 3 to stay as `FIX_ONE`.

Naive `replace FIX_ONE with (Z.min FIX_ONE raw)` substitutes all
three. Targeted `rewrite H_eq at 1` / `rewrite at 1` doesn't work
because each rewrite changes occurrence indices, and Coq's
unification engine accumulates *nested* `Z.min` wrappers as it tries
to match the goal's `FIX_ONE` against the already-set metavariable
form.

After several `rewrite at 1`, the expected form ends up with
`Z.min (Z.min (Z.min FIX_ONE raw) ...) ...` — algebraically the
same as `Z.min FIX_ONE raw` (idempotence), but syntactically
different so `apply RunO.Pure` still fails.

### Final Goal 4 closure (commit 78af2aa)

The shared-metavariable problem is bridged by `RunO.PureEq` with a
side equality proof that uses `Z.min_l` (clamped branch) or
`Z.min_r` (unclamped branch). Key trick for the clamped branch:
introduce the equality as a named hypothesis `E`, normalize any
literal computation (e.g. `replace (12 * 3600) with 43200`) inside
the side proof, then do a single `rewrite E` in the main goal:

```coq
apply RunO.PureEq.
+ assert (E : Z.min 1000000000000000000 (<raw_expr>) = 1000000000000000000)
    by (apply Z.min_l; exact Hge_raw).
  replace (12 * 3600) with 43200 in E by reflexivity.
  rewrite E. reflexivity.
+ reflexivity.
```

A single `rewrite E` finds every occurrence of the LHS uniformly and
substitutes, so the three FIX_ONE positions become three (Z.min ...)
positions atomically — no accumulating nested wrappers as the
"rewrite at N" approach would have produced.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `run_getProposalsAvailable_equivalent_make_state` closes with Qed.
  Goal 2.B uses Z.min_r; Goal 4 uses the RunO.PureEq + Z.min_l +
  rewrite-E pattern; Goal 5 closes by `cbn match; unfold
  proposalsAvailable, readCharge; apply RunO.Pure` once Goal 2's
  bridge has fixed the metavariable.

## R033: Bridging if-then-else metavariable sharing with `RunO.PureEq` — the recipe

### When to reach for this

A theorem's body has an if-then-else (or any `match` with multiple
result arms) whose branches emit *concretely different* output
tuples, but the abstract `output` metavariable bound at the top of
the proof (`eexists state'`-style) is shared across all branches. As
soon as branch 1 closes with `apply RunO.Pure`, the metavariable
unifies with branch 1's concrete shape, and branch 2 then fails
because its shape doesn't match — even though both shapes equal a
shared *abstract* form (e.g. `Z.min FIX_ONE raw`).

This pattern shows up whenever a Solidity `if (cond) { return X }
else { return Y }` corresponds to a sim that returns
`Z.min/Z.max/clamp/abs(...)`. The Yul side emits both literal forms;
the sim side stays abstract.

### The two-leg recipe

For each branch, do one of the two following:

**Leg A — unclamped / inverse: `replace` introduces the abstract form.**

```coq
(* The branch emits raw; abstract form is `Z.min FIX_ONE raw` and
   we have `raw <= FIX_ONE` in scope. *)
replace raw with (Z.min FIX_ONE raw) by (apply Z.min_r; exact Hle).
apply RunO.Pure.
```

The single `replace` substitutes uniformly across the goal, so all
positions of `raw` become `Z.min FIX_ONE raw` at once. Branch 1
closes with `RunO.Pure`. The metavariable picks up the abstract
form.

**Leg B — clamped / direct: `RunO.PureEq` accepts the mismatch.**

```coq
(* The branch emits literal `FIX_ONE`; abstract form is
   `Z.min FIX_ONE raw` and we have `raw > FIX_ONE` ⇒ `FIX_ONE <= raw`. *)
apply RunO.PureEq.
+ assert (E : Z.min FIX_ONE <raw_expr> = FIX_ONE)
    by (apply Z.min_l; <exact-the-bound>).
  rewrite E. reflexivity.
+ reflexivity.
```

`RunO.PureEq` accepts an `output ≠ output'` mismatch with a side
equality proof. The `assert E` introduces the algebraic fact; the
single `rewrite E` substitutes uniformly so all positions of the
abstract `Z.min` form collapse to the literal at once.

### Why a single rewrite over `rewrite at N`

`rewrite E at 1` shifts occurrence indices after each invocation,
and Coq's unification engine accumulates *nested* `Z.min` wrappers
trying to match. A single unscoped `rewrite E` collapses every
matching subterm to the literal in one step — no indexing trap.

### Literal normalization inside the side proof

If the side equality contains expressions like `12 * 3600` that need
to match a literal `43200` in the goal, normalize them inside the
assertion before `rewrite E`:

```coq
assert (E : ... = FIX_ONE) by (apply Z.min_l; exact Hge_raw).
replace (12 * 3600) with 43200 in E by reflexivity.
rewrite E. reflexivity.
```

### Tactic alias

`pe` is the upstream alias for `apply RunO.PureEq`. The recipe in
its compact form:

```coq
pe.
- assert (E : <abstract> = <concrete>) by (apply Z.min_{l,r}; <bound>).
  rewrite E. reflexivity.
- reflexivity.
```

### Touchpoints / future use

The Phase 1.3 mutator (`run_consumeProposalCharge_make_state`) will
hit the same shape on its bound-clamp: the sim returns `Z.min
FIX_ONE (currentCharge + delta)` while Yul emits literal `FIX_ONE`
on overflow and the raw expression otherwise. Same recipe applies.

Other places to expect this pattern:
- Any `proposalsAvailable / readCharge` rederivation in
  ProposerThrottle equivalence proofs.
- Reward-cap clamps in StakingVault.
- Block-timestamp `min(deadline, now)` patterns in Timelock.

### Anti-patterns

- `rewrite ... at 1; rewrite ... at 2; ...` — indices shift, nested
  wrappers accumulate.
- `apply RunO.Pure` then trying `f_equal` on tuple components — the
  whole problem is the unification at apply-time, not after.
- Refactoring to put the destruct at an outer level — works in
  theory but bloats the proof; the recipe above is local and
  composable.

## R034: `Dict.declare_or_assign` chains resist structural-equality proofs

### The shape

For Phase 1.3 (`consumeProposalCharge` equivalence), the post-state's
packed map is two stacked `Dict.declare_or_assign` calls — one for
each sstore. The natural equivalence target is

```coq
Dict.declare_or_assign
  (Dict.declare_or_assign (throttles_packed sim) (account, 0) charge)
  (account, 1) lastUpdated
= throttles_packed (set_throttle sim account new_throttle)
```

The two sides ARE structurally equal up to permutation in all cases
(account already in sim's throttles, account fresh), but reaching
that equality through `rewrite + Z.eqb_refl + simpl` chains hits
multiple traps.

### What goes wrong

1. **Rewrite picks the inner declare_or_assign first**, not the outer.
   The pattern `Dict.declare_or_assign (((c,d),v)::rest) (a,b) new_v`
   matches the INNER call's first arg (a literal cons), not the
   OUTER call's first arg (a function application).

2. **After `rewrite Z.eqb_refl; simpl`, the goal shape mutates** in
   ways that make the SECOND rewrite fail to find a matching
   subterm. `simpl` reduces the if's conditional but also
   over-eagerly normalizes adjacent expressions, breaking the
   `((c,d),v)::rest` shape needed for the pattern.

3. **The third nested declare_or_assign needs another pair_cons_step
   rewrite**, not a Z_cons_step. The two helpers have different
   shapes; mixing them in the proof script silently fails when the
   right tool isn't reached.

### The structural-vs-observational trade-off

Observational equality (`forall key, map_get_u256 LHS key =
map_get_u256 RHS key`) closes cleanly by induction over sim's
throttles dict, with the `map_get_u256_pair_cons` helper handling
each step. The proof is roughly 15-20 lines.

Structural equality requires showing the underlying Dict lists are
identical sequences. That requires:
- Carefully threading `Dict.declare_or_assign_function` reductions
  through the typeclass-dispatch `Dict.Eq.eqb`.
- Avoiding `simpl` which over-reduces.
- Matching specifically when the inner cons is hit twice (offsets 0
  and 1) versus skipped twice.

### Why we need structural

The equivalence theorem asserts
`{{? ... | yul_body ⇓ Result.Ok tt | Some post_state ?}}` where
`post_state` is computed from the sim. The State.t embeds the
MapStruct as a literal Dict (a list). For the theorem to typecheck,
the two states need to be structurally equal — not just
observationally equivalent maps. Coq's state-equality is up to
syntactic equality of the underlying Dict.

### Workarounds

Three options, ordered by feasibility:

1. **Restate the equivalence theorem with observational equality on
   the storage map.** Introduce a helper relation
   `state_extensionally_equal env state1 state2` that compares
   storage entries pointwise. Loses the clean `state' = ...`
   form but the proof closes immediately.

2. **Mechanize the structural equality by hand**, step by step, with
   `change` instead of `simpl` to avoid over-reduction. Estimated
   1-2 hours of focused work.

3. **Add `Dict.declare_or_assign_commute` and related rewrite lemmas
   upstream**, then use them to normalize both sides into a
   canonical form before equality check. Upstream change required.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `throttles_packed_set_throttle_two_sstores` is Admitted under this
  banner; the lemma statement is correct. The helpers
  `declare_or_assign_pair_cons_step` and
  `declare_or_assign_Z_cons_step` are proven and reusable.
- Future contracts with struct-valued mappings (UnstakingManager.locks,
  StakingVault rewards, Governor proposals) will hit the same shape.
  This entry should be revisited when one of those equivalence
  theorems is attempted.
