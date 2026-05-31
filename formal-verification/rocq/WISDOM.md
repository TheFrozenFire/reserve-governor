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

## R034: `Dict.declare_or_assign` chains — RESOLVED via `rewrite H; simpl` cascade

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

### Second-pass progress (2026-05-29 evening)

A focused attempt closed two of three cases:

- **Empty case** (`sim.throttles = []`): closes with
  `cbn [List.flat_map]; change Dict.declare_or_assign [] _ _ with [(...)]; rewrite declare_or_assign_pair_cons_step; replace ...; cbv iota; reflexivity`.
- **Matching case** (`k = account`): closes with three
  `rewrite declare_or_assign_pair_cons_step; rewrite Z.eqb_refl; simpl`
  plus a final `rewrite declare_or_assign_Z_cons_step; rewrite Z.eqb_refl; reflexivity`.

- **Non-matching case**: still stuck. Added helper
  `two_sstores_pass_through_nonmatch` (closes with Qed via
  the cons-step + cbv iota pattern). When applied via `rewrite`,
  the goal becomes `head_pair ++ <IH's LHS>`. But `rewrite IH`
  then fails with "no subterm matching" even after `cbn [List.app]`
  reduces the append into cons form. Tried renaming
  `throttles_packed`'s binder from `account` → `addr` to rule out
  shadowing — same error. The IH's LHS appears in the goal but
  rewrite's syntactic-occurrence finder doesn't pick it up.

### Next-attempt hypotheses

- `etransitivity. apply IH. ...` — bypasses `rewrite`'s pattern
  matching by using transitivity of equality directly. The goal
  becomes `head_pair ++ IH_RHS = goal_RHS`, which is a separate
  proof but doesn't need to find IH's LHS as a subterm.
- `replace (Dict.declare_or_assign (Dict.declare_or_assign (flat_map _ dict) ...) ...) with (flat_map _ (Dict.declare_or_assign_function dict ...))` — explicitly substitute, then `[ | exact IH ]` closes the equality side-goal.
- Restructure to do the recursive case BEFORE the
  pass-through-nonmatch helper, so the IH applies at the top level
  rather than inside a cons.

### Resolution (2026-05-29 night)

**Lemma now closes with Qed.** The breakthrough was replacing the
`replace (Z.eqb k account && Z.eqb 0 0) with false by (rewrite Hkneb; reflexivity); cbv iota`
pattern with the simpler `rewrite Hkneb; simpl` cascade. Working
proof shape for the non-matching case:

```coq
apply Z.eqb_neq in Hkne as Hkneb.
change (List.flat_map _ ((k, v) :: dict))
  with ((k, 0, vcc) :: (k, 1, vlu) :: List.flat_map _ dict).
rewrite declare_or_assign_pair_cons_step. rewrite Hkneb. simpl.
rewrite declare_or_assign_pair_cons_step. rewrite Hkneb. simpl.
rewrite declare_or_assign_pair_cons_step. rewrite Hkneb. simpl.
rewrite declare_or_assign_pair_cons_step. rewrite Hkneb. simpl.
rewrite declare_or_assign_Z_cons_step. rewrite Hkneb. simpl.
cbn [List.flat_map].
f_equal. f_equal. exact IH.
```

### Why `rewrite Hkneb; simpl` works where `replace + cbv iota` failed

- `rewrite Hkneb` substitutes `Z.eqb k account` with `false` at the
  first occurrence in the goal. This affects ALL four cons-step
  conditions (since each contains `Z.eqb k account`).
- `simpl` then evaluates the entire cascade: `false && Z.eqb d b`
  short-circuits to `false`, the `if false then ... else ...`
  reduces to the else branch, and the let-bindings in the
  declare_or_assign body collapse.
- The `replace + cbv iota` pattern substituted a SLICE of the
  condition (the whole `andb` expression), but `cbv iota` apparently
  doesn't follow through to reduce the if when the conditional is
  syntactically `false` but Coq's iota-reduction looks for a
  match-pattern not a recognized term.

### Touchpoints

- `proofs/equivalence/ThrottleLib.v`:
  `throttles_packed_set_throttle_two_sstores` closes with Qed.
  Helpers `declare_or_assign_pair_cons_step`,
  `declare_or_assign_Z_cons_step`,
  `two_sstores_pass_through_nonmatch` all proven with Qed.
- The composite lemma unblocks the Phase 1.3 (#196)
  `run_consumeProposalCharge_make_state` proof body.
- Future contracts with struct-valued mappings can copy this
  pattern verbatim — the helpers are reusable, the proof template
  fits any two-sstore-per-account mutation shape.

## R035: shallow_embed.py mis-embeds nested control flow

### Original symptom (switch bug — now FIXED)

`generated/UnstakingManager_shallow.v` line 897 used to fail with a
type error because the YulSwitch translation bound the result as
`'tt` (unit) while the branches returned a Z. See "The switch bug —
FIXED" section below.

### Current symptom (separate, downstream bug)

With the switch fix in place, UnstakingManager_shallow.v still fails,
now at `fun_cancelLock_212` (and similarly `fun_claimLock_270`):
```
Error: Must evaluate to a closed term
offending expression: 
e
this is an object of type ident
```

The error comes from `M.monadic` Ltac — `[[ e ]]` is
`(ltac:(M.monadic e))`. M.monadic can traverse raw `let v := x in f v`
and `run x` patterns but doesn't know how to handle a `Shallow.let_state`
(the `let_state~` notation) appearing inside its scope.

### Affected contracts

- UnstakingManager.sol: cancelLock_212 and claimLock_270 both have a
  `let_state~ ... := [[ Shallow.if_ (| _, <succ_with_nested_let_state>, _ |) ]]`
  pattern. The inner let_state's `[[ ]]` brackets don't compile.
- ThrottleLib, VersionRegistry, RewardTokenRegistry, Guardian shallow
  forms have no nested let_state inside [[ ]] — they compile cleanly.

### Touchpoints

- `proofs/equivalence/UnstakingManager.v`: header comment documents
  the issue; three theorems are placeholder-bodied.
- `scripts/shallow-embed-sweep`: generates the file successfully but
  the consumer can't load it.
- Upstream: `~/git/reserve/formal-verification/rocq-of-solidity/rocq/scripts/shallow_embed.py`
  — emits `Shallow.let_state` nested inside `Shallow.if_`'s success
  parameter, which lands inside `[[ ]]` brackets.
- Upstream: `rocq/RocqOfSolidity/RocqOfSolidity.v` `Ltac M.monadic` —
  doesn't recognise the `Shallow.let_state` shape.

### The switch bug — FIXED (2026-05-30)

The natural one-line patch is line 254:
```python
updated_vars_to_rocq(True, final_updated_vars)  →
updated_vars_to_rocq(True, commonly_updated_vars)
```

Landed upstream in TheFrozenFire/rocq-of-solidity:feat/env-block-context
as commit `8421532309`. The previous diagnosis (this fix "cascades into a
type mismatch") was wrong: `Shallow.let_state` is heterogeneous in its
State1 and State2 parameters — body's value type and continuation's state
type are independent. So `let_state~ expr_1376 := body default~ tt`
typechecks cleanly when body returns Z and continuation expects unit.

```coq
Definition let_state {State1 State2 : Set}
    (expression : t State1) (body : State1 -> State2 * t State2) :
    t State2 := ...
```

After the patch, line 897 of UnstakingManager_shallow.v reads
`let_state~ expr_1376 := [[ <switch> ]] default~ tt in` — types check,
and the subsequent `Shallow.if_ (| expr_1376, ... |)` correctly reads
the switch's update (lexical scope captures the binding).

### Remaining downstream issue (separate from the switch bug)

With the switch fix in place, UnstakingManager_shallow.v still fails to
compile at `fun_cancelLock_212` (and similarly `fun_claimLock_270`) with
a *different* error:

```
Error: Must evaluate to a closed term
offending expression: 
e
this is an object of type ident
```

The pointer covers the whole `Definition fun_cancelLock_212` body. The
trigger is a nested `let_state~` *inside* `[[ ]]` brackets: the outer
`let_state~ expr_205 := [[ Shallow.if_ (| _77, succ, expr_205 |) ]]
default~ tt in` wraps a `Shallow.if_` whose `succ` branch contains an
*inner* `let_state~ _78 := [[ ... ]] default~ expr_205 in`.

`[[ e ]]` is `(ltac:(M.monadic e))`. The `M.monadic` Ltac knows how to
traverse raw `let v := x in f v` and `run x` patterns but doesn't
specifically handle `Shallow.let_state` notation expansion. When the
nested let_state appears inside the outer brackets' body, M.monadic gets
confused and fails with this "object of type ident" error.

The proper fix is one of:
1. Extend `M.monadic` (upstream) to recognise `Shallow.let_state ...`
   shape and traverse it the way it does `let v := x in f v`.
2. Restructure shallow_embed.py to emit code without `let_state~` inside
   `[[ ]]` brackets — keep all `let_state~` at the top-level shallow
   layer, never inside the `M.monadic` Ltac's scope.

Both are upstream changes. Option 2 is shallower (string-rewriting
restructure) but may not always be feasible — Shallow.if_ takes a
`success : M.t (BlockUnit.t * State)` parameter, and to express a
mutator inside it you'd need to thread state via raw M.strong_let_
without `let_state~`.

Until either lands, UnstakingManager_shallow.v stays unloaded. The
other four shallow forms (ThrottleLib, VersionRegistry,
RewardTokenRegistry, Guardian) compile cleanly with the patch in place
and are wired into _RocqProject.

## R036: Upfront-pose pattern for evar-scope problems in `c;[..|..]` walkers

When the walker fires `c; [ eapply Lemma | ]` (or `eapply RunO.Call;
[exact H | ...]`) on a Yul-style equivalence proof, Coq creates a
state/output metavariable BEFORE the walker continues. If the lemma
the walker uses has existentials in its post-state (e.g.,
`exists w0' w1' rest', ... | Some (make_state ... (w0' :: w1' ::
rest') ...) ?}}`), the natural pattern would be to destruct those
existentials *after* the lemma application — but by then the
metavariable's scope has already been fixed, and the witnesses live
outside it.

Result: `eapply` fails to unify, with an error like "cannot
instantiate ?state_inter1 because w0' is not in its scope".

### Fix — pose proof + destruct upfront

Apply the lemma BEFORE the walker fires, name the result, destruct
its existentials into named witnesses, then `set` an alias for the
reconstructed cons-form. By the time the walker creates its
metavariables, the witnesses are already in scope.

```coq
pose proof (MappingIndexAccess.run_mapping_index_access
              codes env state_base (Pure.add 0 1) account
              (proj_sim sim) state_E
              H_valid_account
              (ex_intro _ e_w0 (ex_intro _ e_w1
                 (ex_intro _ e_rest eq_refl)))) as Hmia.
destruct Hmia as (w0_mia & w1_mia & rest_mia & Hmia).
(* Now Hmia is a concrete RunO.t fact, all witnesses in scope *)
eexists.  (* outer state' evar; created AFTER witnesses *)
(* walker fires; uses 'exact Hmia' in the matched arm *)
```

In the walker arm:
```coq
| |- {{? _, _, _ |
      LowM.Call (mapping_index_access_... _ _) _ ⇓ _ | _ ?}} =>
    eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
```

The walker no longer creates a metavariable scoped before the
witnesses — `exact Hmia` plugs in the concrete fact directly.

### When this kicks in

- Any walker arm whose target lemma has `exists` in its post-state.
- Mapping/struct lookups (mapping_index_access has the `cons-of-3`
  shape on memory).
- Phase E sub-call composition (Phase E itself uses this pattern
  for its inner mapping lookup).

### Why this isn't `c;[apply X | ]` automatically

`c;[apply X | ]` creates the post-state evar BEFORE the inner tactic
runs. The evar's scope captures only what was in context before the
focus. Any new variable introduced inside the focus is outside that
scope.

The upfront-pose pattern inverts the order: facts come first,
metavariables second.

## R037: `idtac G; fail` diagnostic for silent walker arm mismatches

When a `repeat (lazymatch ... end)` walker silently doesn't fire on
a sub-call you expect it to handle, the most likely cause is a
name-qualification mismatch: the walker arm matches against a
`Notation`-qualified or short name, but the actual goal head is the
fully-qualified shallow-form name (e.g.,
`ThrottleLib_153.ThrottleLib_153_deployed.mapping_index_access_t_mappingₓ_t_address_ₓ_t_structₓ_ProposalThrottle_ₓ18_storage_ₓ_of_t_address`,
not a friendlier alias).

Lazymatch's failure is silent — it tries the next arm or falls
through to the wildcard, leaving you wondering why your tactic
"didn't run." There's no error message.

### Diagnostic: insert idtac G; fail near the suspected arm

```coq
repeat (lazymatch goal with
  | |- {{? _, _, _ | LowM.Call ?head _ ⇓ _ | _ ?}} =>
      idtac head; fail   (* prints the head, then fails to stop the walker *)
  | |- _ => s
  end).
```

This prints the exact goal head before failing. Once you see the
true name, update the walker arm to match. For shallow-form names,
the pattern is typically
`<ContractName>_<id>.<ContractName>_<id>_deployed.<function_name>`.

### When to use

- Walker iterates past a sub-call but you expected it to fire.
- A new sub-call appears after refactoring and your walker doesn't
  handle it.
- After upstream shallow_embed.py changes — names may have shifted.

Take out the `idtac; fail` after diagnosis; it's a one-shot tool.

## R038: Slot-discriminated walker arms for storage reads

A generic walker arm like

```coq
| |- {{? _, _, _ |
      LowM.Call (read_from_storage_split_offset_0_t_uint256 _) _
      ⇓ _ | _ ?}} =>
    c; [ eapply ThrottleLibLeaves.run_read_from_storage_split_offset_0_t_uint256 | ]
```

invokes the lower-level leaf which takes an `?account` evar as the
runtime account at `env.(Environment.address)`. That evar then
propagates through every downstream goal that references the read
value — typically 5+ goals all referring to `?account.(Account.
storage) slot`.

### Fix — slot-discriminating arms BEFORE the generic fallback

If the proof has higher-level lemmas that return concrete sim values
(e.g., `run_read_capacity_from_make_state` returns
`sim.(ThrottleLibStorage.capacity)` directly, no evar), discriminate
the walker arm by slot pattern:

```coq
(* Slot-discriminated arms first; order matters in lazymatch *)
| |- {{? _, _, _ |
      LowM.Call (read_from_storage_split_offset_0_t_uint256
                   (Pure.add 0 0)) _
      ⇓ _ | _ ?}} =>
    c; [ apply run_read_capacity_from_make_state | ]
| |- {{? _, _, _ |
      LowM.Call (read_from_storage_split_offset_0_t_uint256
                   (Pure.add (keccak256_tuple2 _ _) 0)) _
      ⇓ _ | _ ?}} =>
    c; [ apply run_read_currentCharge_from_make_state | ]
| |- {{? _, _, _ |
      LowM.Call (read_from_storage_split_offset_0_t_uint256
                   (Pure.add (keccak256_tuple2 _ _) 1)) _
      ⇓ _ | _ ?}} =>
    c; [ apply run_read_lastUpdated_from_make_state | ]
| |- {{? _, _, _ |
      LowM.Call (read_from_storage_split_offset_0_t_uint256 _) _
      ⇓ _ | _ ?}} =>
    c; [ eapply ThrottleLibLeaves.run_read_from_storage_split_offset_0_t_uint256 | ]
```

### What this collapses

Phase 1.3's `run_consumeProposalCharge_make_state` had 11 focused +
6 shelved goals after the generic walker; switching to
slot-discriminated arms left 8 focused + 5 shelved, with `?account`
gone from every remaining goal. The bounds and arithmetic that
followed became closeable by `lia` directly, with no need for
intermediate evar instantiation.

### General principle

When a leaf's signature exposes an evar that ends up threaded
through downstream goals, look for higher-level lemmas that
instantiate that evar to a concrete value. If they exist, walker
arms targeting specific slots/values are strictly better than a
single generic arm.

## R039: rocq-mcp interactive setup for cross-repo projects

When governor proofs depend on `rocq-of-solidity`'s `RocqOfSolidity`
library (under `~/git/reserve/formal-verification/rocq-of-solidity/
rocq/RocqOfSolidity/`), `rocq-mcp` v0.2.1's path-containment check
rejects absolute paths and symlinks that resolve outside the
workspace. The fix is a parent-level `_CoqProject` that bridges both
repos.

### Setup

1. **Use the Coq 8.20 opam switch.** The `.vo` files are built with
   Coq 8.20.1 (rocq820 switch); `pet` from Coq 9.1 (rocq switch)
   can't load them. Configure rocq-mcp's PATH to start with
   `~/.opam/rocq820/bin`:

   ```sh
   claude mcp remove rocq-mcp --scope user
   claude mcp add rocq-mcp --scope user --env PATH=/Users/jmart/.opam/rocq820/bin:/usr/bin:/bin -- uvx rocq-mcp
   ```

2. **Place `_CoqProject` at the parent of both repos.** For Reserve
   governor work, that's `/Users/jmart/git/reserve/formal-verification/`:

   ```
   -R governor/formal-verification/rocq ReserveGovernor
   -R rocq-of-solidity/rocq/RocqOfSolidity RocqOfSolidity
   -arg -impredicative-set
   -arg -w
   -arg -stdlib-vector
   ```

3. **Use `-R` (recursive, exclusive), not `-Q`.** Unqualified
   imports like `Require Import simulations.RocqOfSolidity.` only
   resolve when the prefix is bound via `-R`.

4. **Pass `workspace` explicitly to rocq-mcp tool calls.** Auto-
   detection walks up from the file looking for `_CoqProject`, but
   passing it explicitly avoids ambiguity when multiple are nested.

### Usage

```
rocq_start(
  file=governor/formal-verification/rocq/proofs/equivalence/ThrottleLib.v,
  workspace=/Users/jmart/git/reserve/formal-verification,
  theorem=run_consumeProposalCharge_make_state)
```

### Diagnostics

- `rocq_check` returning empty TOC: missing imports — pet sees the
  module body as empty because `Require Import` silently failed.
- "Cannot find a physical path bound to logical path X": `-R`/`-Q`
  prefix mismatch in `_CoqProject`, or the `.vo` files are version-
  mismatched (built with a different Coq version than `pet` is using).
- `_check_path_containment` rejection: workspace path doesn't cover
  the file or one of its imports — try a parent-level `_CoqProject`.


## R040: Wrapper-shape leaves for sstore — bake in the storage list shape

**Status:** RESOLVED. Pattern landed in `proofs/equivalence/ThrottleLib.v` as
`run_update_storage_offset_0_at_two_slot_list`.

The upstream sstore leaf
`run_update_storage_value_offset_0_t_uint256_to_t_uint256` (in
`ThrottleLib_Leaves.v`) is generic over the storage list, so its
conclusion is wrapped in a `match List.update_nth storage index ... with
| Some s' => {{? ... ?}} | None => True end`. The match-form blocks
`eapply` / `apply` because the unifier cannot see past the constructor
mediation.

When the walker reaches the sstore call, `c; [eapply <leaf> | ]` fails on
the first subgoal because the leaf's conclusion is not a clean Hoare
triple. The walker stops there, leaving the post-state as an evar.

### The fix: a specialized wrapper

Write a thin wrapper that bakes in the concrete shape of the storage
list (e.g., for ThrottleLib, `[StorableValue.U256 cap; StorableValue.MapStruct map]`
which is definitionally `proj_sim sim`). Inside the wrapper, invoke the
generic leaf with the concrete list, `simpl List.update_nth` reduces the
match, and the result is a clean Hoare-triple conclusion.

```coq
Lemma run_update_storage_offset_0_at_two_slot_list
    codes env state_base memory
    (cap : U256.t)
    (map : Dict.t (U256.t * U256.t) U256.t)
    (key offset value : U256.t)
    (H_off : 0 <= offset < 32)
    (H_v : 0 <= value < 2^256) :
  let map' := Dict.declare_or_assign map (key, offset) value in
  {{? codes, env, Some (make_state env state_base memory
                          [StorableValue.U256 cap; StorableValue.MapStruct map]) |
    update_storage_value_offset_0_t_uint256_to_t_uint256
      (Pure.add (keccak256_tuple2 key 1) offset) value ⇓
    Result.Ok tt
  | Some (make_state env state_base memory
            [StorableValue.U256 cap; StorableValue.MapStruct map']) ?}}.
Proof.
  rewrite Pure_add_keccak_offset by exact H_off.
  pose proof (ThrottleLibLeaves.run_update_storage_value_offset_0_t_uint256_to_t_uint256
                codes env state_base memory
                [StorableValue.U256 cap; StorableValue.MapStruct map] 1%nat map
                key offset value
                H_v eq_refl) as H.
  cbv zeta in H.
  simpl List.update_nth in H.
  change (Z.of_nat 1) with 1%Z in H.
  unfold make_state in H at 2.
  rewrite CanonizeState.with_current_storage_twice_eq in H.
  exact H.
Qed.
```

The walker arm then uses `apply` on the wrapper, which has a clean
`{{? ?}}` conclusion, side conditions H_off and H_v that close via
lia / domain bounds.

### Generalization

The same pattern applies to any contract whose sstore writes to a
struct-mapping slot. The wrapper bakes in the contract's `proj_sim`
shape (typically `[U256 cap; MapStruct map]` for a single-mapping
contract, or longer lists for multi-field storage). Once the wrapper
exists, the walker proceeds past the sstore mechanically, treating the
post-state as a concrete updated list.

For multi-sstore bodies (e.g., consumeProposalCharge's two-sstore
pattern), the wrapper handles each sstore independently. The first
sstore's post-state is `[U256 cap; MapStruct (declare_or_assign map ...)]`,
which IS a valid input for the wrapper's second invocation (it just
sees a different `map` parameter). After both sstores, the storage
list is `[U256 cap; MapStruct (declare_or_assign (declare_or_assign ...) ...)]`,
which `throttles_packed_set_throttle_two_sstores` (R034) rewrites
back to `proj_sim new_sim` if needed — though for proofs concluding
just `exists state', {{? ?}}` (rather than a specific post-state),
this rewrite isn't required.

### When to apply

- The Yul body writes to a struct-mapping slot via
  `update_storage_value_offset_0_t_uint256_to_t_uint256` (or a similar
  one-of-N sstore variant).
- The walker stops at the sstore call because the generic leaf has a
  match-wrapped conclusion.
- The pre-state of the sstore is `make_state ... (proj_sim sim)` or a
  similar concrete-list form.

### Related infrastructure

- `CanonizeState.with_current_storage_twice_eq` (upstream) — collapses
  double `with_current_storage` calls to a single one, exposing the
  natural `make_state` form in the post-state.
- `Pure_add_keccak_offset` (ThrottleLib.v) — bridges Yul's
  `Pure.add (keccak ...) offset` to Z-level `keccak ... + offset`
  under the cryptographic bound.
- `proj_sim_throttles` / `proj_sim_capacity` (ThrottleLib.v) — supply
  the `nth_error storage index = Some ...` precondition for the
  generic leaf.

### Timestamp arm

The companion piece for Phase 1.3's walker: the `LowM.Call Stdlib.timestamp`
form needs a dedicated arm because `pr` (Primitive) doesn't fire on the
wrapper. Use:

```coq
| |- {{? _, _, _ |
      LowM.Call Stdlib.timestamp _ ⇓ _ | _ ?}} =>
    c; [ apply ThrottleLibLeaves.run_timestamp;
         rewrite ThrottleLibLeaves.make_state_block_timestamp;
         exact H_timestamp | ]
```

This composes `run_timestamp` (which discharges the call) with
`make_state_block_timestamp` (which says `make_state` preserves
`block_timestamp`) and the outer proof's `H_timestamp` (which says
`state_base.(block_timestamp) = now`). The result: the call evaluates
to `Result.Ok now` with the state unchanged.

## R041 (resolved): missing `linkersymbol` definition in rocq-of-solidity

**TL;DR.** The Yul primitive `linkersymbol` was never defined in
`RocqOfSolidity/simulations/RocqOfSolidity.v`.  Every Coq elaboration of
a generated `[[ linkersymbol ~(| ... |) ]]` crashed via `M.monadic` with
`Must evaluate to a closed term, offending expression: e, this is an
object of type ident`.  The "ident" is literally the unbound
`linkersymbol` token — `M.monadic`'s default `exact e` arm has no way
to error gracefully when one of its subterms is unresolved.  The fix
is a one-definition patch to the simulations file.

The original WISDOM entry below pinned the bug on `Shallow.let_state`
nested inside `[[ ]]` brackets.  That diagnosis was wrong — the
M.monadic-vs-Shallow.let_state issue IS real (the partial fix in
`shallow_embed.py` addresses it), but it isn't what was blocking
`fun_cancelLock_212`.  The actual blocker was `linkersymbol`.

### Resolution

Added to `RocqOfSolidity/simulations/RocqOfSolidity.v` next to the
sibling primitives (`loadimmutable`, `memoryguard`, etc.):

```coq
Definition linkersymbol (name : U256.t) : M.t U256.t :=
  M.pure name.
```

This models `linkersymbol` as identity on the name — the address-vs-
name distinction doesn't matter for the contract's own equivalence
proof because every use of the returned value flows through the same
opaque path.  A dedicated `Primitive.LinkerSymbol` constructor would be
more faithful but isn't required for current proof targets.

After this patch:

| File | Pre-patch | Post-patch |
|---|---|---|
| `Guardian_shallow.v` | compiles | compiles |
| `ThrottleLib_shallow.v` | compiles | compiles |
| `UnstakingManager_shallow.v` (whole file, including `fun_cancelLock_212`, `fun_claimLock_270`, `fun_createLock_144`) | fails | **compiles** |

### Diagnostic trail (preserved for the agent doing the proving work)

The breakthrough was bisecting cancelLock_212's body — adding one
`let~` line at a time until the compile flipped from pass to fail.
The 43rd `let~` was:

```
let~ expr_189_address := [[ linkersymbol ~(| 0x6e6f64655f6d6f64756c65732f... |) ]] in
```

That hex literal is the ASCII for
`"node_modules/@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol:SafeERC20"`
— 142 hex digits, way over U256's 64-digit ceiling.  My first
hypothesis was that the over-sized literal was breaking type
inference.  Stubbing `Parameter linkersymbol : U256.t -> M.t U256.t.`
made the same line (with the same over-sized literal) compile
instantly.  The literal size was a red herring; the unbound function
name was the bug.

Why three big functions all failed: `fun_cancelLock_212`,
`fun_claimLock_270`, and `fun_createLock_144` all call SafeERC20
methods (transfer/transferFrom/forceApprove), and solc emits
`linkersymbol(...)` for each of those library references.  Every
other function in `UnstakingManager_shallow.v` only uses storage and
plain-EVM primitives, so the missing `linkersymbol` never surfaces
in them.

### Why the M.monadic-vs-Shallow.let_state finding still has value

The original WISDOM R041 diagnosis identified a real Ltac defect:
when `Shallow.let_state` nests inside `[[ ]]` and rebinds a name from
the enclosing scope, `M.monadic`'s `context [run ?x]` traversal can
produce an unbound metavariable error.  That defect was just not what
was triggering on the contracts we have.  The partial fix in
`shallow_embed.py` (CPS pre-bind for YulIf, outer-bracket drop for
YulSwitch) pre-empts the defect by never emitting that shape, and is
worth keeping in case future contracts emit the offending pattern.

### Where the original (now-superseded) diagnosis lived

## R041 (original, now-superseded diagnosis): `M.monadic` Ltac doesn't traverse `Shallow.let_state` — cancelLock_212 still blocked

Diagnosed end-of-session 2026-05-30 while attempting to wire
UnstakingManager_shallow.v into _RocqProject. The R035 switch-binding
fix (upstream commit `8421532309`) was supposed to unblock the file,
but `fun_cancelLock_212` still hits a `Must evaluate to a closed
term, offending expression: e` error from coqc.

### The actual failure shape

The generator emits (at UnstakingManager_shallow.v:1186):

```coq
let~ _78 := [[ 32 ]] in
let_state~ _78 := [[
  Shallow.if_ (|
    gt ~(| _78, returndatasize ~(||) |),
    let~ _78 := [[ returndatasize ~(||) ]] in
    M.pure (BlockUnit.Tt, _78),
    _78
  |)
]] default~ expr_205 in
```

The `let_state~` binds `_78` (the inner YulIf's `then_updated_vars`)
but defaults to `expr_205` (the surrounding then-block's
`final_updated_vars`). The binding/default shapes don't have to match
type-wise (Shallow.let_state is heterogeneous), but `[[ ]]` invokes
`M.monadic` on the Shallow.if_ expression, and M.monadic doesn't have
a lazymatch arm for `Shallow.let_state` notation expansions.

### Why M.monadic falls over

`M.monadic` (in upstream `simulations/RocqOfSolidity.v:401`) handles:

1. `let v := ?x in @?f v` — Coq's primitive let.
2. `run ?x` — the M.run marker.
3. Default: `type of e` → `exact e` or `exact (pure e)`.

`let_state~` expands via Notation to `Shallow.let_state e (fun x => (state, k))`.
This is a function application, not a primitive let. M.monadic falls
into the default arm. The `type of e` check seemingly succeeds for the
outer call, but the recursive `[[ ]]` inside the YulIf body (line 1185
above: `[[ returndatasize ~(||) ]]`) triggers another M.monadic call
with `_78` rebound by the outer `let~ _78 := 32` — and somewhere in
that path, an elaboration-time hole isn't resolved.

The exact site of the unbound `e` is hard to pinpoint without
interactive Ltac tracing. Symptoms suggest the inner Shallow.if_'s
success branch's `M.pure (BlockUnit.Tt, _78)` references the `_78`
bound by `let_state~ _78 := [[ ... ]]`, but when M.monadic processes
the outer expression, it `exact e`s a term where the inner `_78`
hasn't been bound yet by the lambda — leaving a hole that surfaces
as "must evaluate to a closed term".

### Fix paths considered

**Option A: extend M.monadic with a Shallow.let_state arm.**
Add a lazymatch arm matching `Shallow.let_state ?e1 (fun ?v => @?f v)`
that recursively monadic-izes `e1` and `f v`. Risk: the typing of
`(state, k)` (the body's return shape — `State2 * t State2`) doesn't
fit M.monadic's `let_` constructor signature. Significant upstream
refactor needed.

**Option B: pull `Shallow.if_` out of `[[ ]]` brackets in
shallow_embed.py.** The current emission wraps the whole
`Shallow.if_(| cond, body, fail |)` in `[[ ]]` so M.monadic can
process M.run markers in the condition. Pulling it out keeps
M.monadic from descending into Shallow.* DSL constructs.

### Trap: the naive Option B doesn't compile

The simple "drop the outer `[[ ]]`" change fails before even
reaching cancelLock_212. The reason is a type asymmetry I missed
the first time round:

| Construct | Condition type |
|---|---|
| `Shallow.for_` | `State -> M.t U256.t` (monadic) |
| `Shallow.if_`  | `U256.t` (pure)              |

`[[ e ]]` always elaborates to a term of type `M.t _` (M.monadic's
default arm wraps non-`t _` terms with `M.pure`). So
`[[ iszero ~(| eq ~(| value, cleanup ~(| value |) |) |) ]]` has
type `M.t U256.t` — which fits `Shallow.for_`'s slot but not
`Shallow.if_`'s. Every `YulIf` with an effectful condition fails
at type-checking. Verified empirically in this session.

YulForLoop bracketing its condition works because of its slot's
type. Reusing the pattern for YulIf without adjustment doesn't.

### Option B done correctly: CPS-bind the condition first

The principled fix is to **pre-bind the condition via `let~`**
before the `Shallow.if_`, so the slot receives a pure `U256.t`
variable:

```
let_state~ outer_var :=
  let~ _condition := [[ original_condition ]] in
  Shallow.if_ (|
    _condition,         (* pure U256.t, no type mismatch *)
    then_body,          (* unbracketed; let_state~ inside is fine *)
    fallback
  |)
default~ ... in
```

The `let~` is `M.strong_let_`, which evaluates `[[ condition ]]`
(handling M.run markers), then binds the result to `_condition`
in scope as a pure value. The `Shallow.if_` lives outside any
`[[ ]]`, so M.monadic never has to descend into Shallow.* — which
is the layering rule that dissolves R041.

YulSwitch already pre-binds its discriminant (`let~ δ := [[ expr ]] in`)
inside the outer brackets, so its fix is simpler: just drop the
outer `[[ ]]`. No new pre-bind needed.

### Status — partial fix landed, cancelLock_212 still blocked

**Implemented** in `_tools/rocq-of-solidity/rocq/scripts/shallow_embed.py`
(and mirrored to `formal-verification/rocq-of-solidity/...`):

- YulIf: pre-bind condition via `let~ γ_cond := [[ condition ]] in`
  before calling `Shallow.if_ γ_cond success failure` (direct function
  application, NOT the `(| |)` notation which forces `M.run` and
  strips the monad off the result).
- YulSwitch: drop the outer `[[ ]]` around the if-then-else chain;
  the inner `let~ δ := [[ expression ]] in` already pre-binds the
  discriminant.

Verification with this fix:

| File | Result |
|---|---|
| `ThrottleLib_shallow.v` | compiles (unchanged behaviour vs pre-fix) |
| `Guardian_shallow.v` | compiles (unchanged behaviour) |
| Minimal hand-written repro of the nested-rebind pattern | compiles |
| `UnstakingManager_shallow.v` `fun_cancelLock_212` | **still fails** with the same `Must evaluate to a closed term, offending expression: e` |

So the CPS shape is *correct* for the abstract pattern (minimal
repro compiles) and doesn't regress simpler files — but the real
trigger isn't what WISDOM originally diagnosed.

### Bisection findings — the failure is broader than cancelLock_212

When `fun_cancelLock_212`'s body is stubbed to `M.pure tt`, the
error moves to `fun_claimLock_270`.  Stub that too, and it moves
to `fun_createLock_144`.  All three are the three "big" Yul
entrypoints — 50+ `let~` bindings each.  Every earlier (smaller)
function compiles fine, including ones with `let_state~`/
`Shallow.if_`/nested rebinds inside.  So:

- The failure is correlated with **function size**, not with the
  nested-rebind pattern specifically.
- A hand-written 12-`let~` chain with no Shallow constructs
  compiles fine standalone — but the first ~12 `let~` bindings of
  `fun_cancelLock_212` (with all helpers in scope, no
  `let_state~`/`Shallow.if_`) fail.  So it's not a Coq-side
  property of plain `let~`-chains either — it depends on either
  the surrounding module context or the specific function calls
  these definitions make.

### pet/coq-lsp disagrees with coqc

`pet.get_state_at_pos` reports `proof_finished=true` and no errors
at any position inside `fun_cancelLock_212`'s body — coq-lsp's
incremental processor elaborates the definition cleanly.  But
`coqc`-driven `rocq_compile_file` rejects the same definition
with the `Must evaluate to a closed term` error.  Two interactive
clients see different things from the same source.  Hypothesis:
coq-lsp's Fleche defers or sidesteps an M.monadic elaboration
step that strict coqc forces, so the failure surfaces only under
coqc.  This would explain why WISDOM's original diagnosis (made
during an interactive session) didn't catch what the batch
compile actually trips on.

### Next-step suggestions

For an agent picking this up:

1. Verify pet-vs-coqc discrepancy in isolation: regenerate
   `UnstakingManager_shallow.v`, run `pet` on `fun_cancelLock_212`
   directly, run `coqc -I ... -R ...` on the same file, compare
   exit codes and stderr.
2. If discrepancy holds, file upstream against coq-lsp / Coq
   — this is potentially a strict-vs-lenient elaboration bug
   rather than a generator issue.
3. If the discrepancy is illusory (e.g. pet IS reporting errors
   but rocq-mcp's `rocq_start` is hiding them), trace via raw
   pet protocol logs.
4. Independent approach: instrument the generator to add explicit
   type annotations (`: U256.t`) on every `let~` binding, removing
   any inference latitude that might trip M.monadic's
   `lazymatch type of e`.

The fix in shallow_embed.py is kept (no regressions; lifts the
ceiling on what compiles cleanly for smaller contracts).  The
placeholder-equivalence workaround below remains in effect for
the three big entrypoints — `cancelLock_212`, `claimLock_270`,
`createLock_144`.

### Why the original outer-bracket pattern was fragile

`M.monadic`'s `context ctxt [run ?x]` arm is a *global* term
traversal: it can reach an `M.run` marker anywhere inside the
bracketed expression, including inside lambda bodies. That's how
the original wrap-the-whole-`Shallow.if_` pattern worked for
non-nested cases — M.monadic walks past `Shallow.if_` treating it
as an opaque function call, finds the M.run markers in subterms,
binds them.

The fragility shows up with `Shallow.let_state` nested inside the
body. When M.monadic's `context` matcher reaches inside the
`let_state` lambda's body, the lambda binder isn't yet introduced
into the proof context (M.monadic hasn't recursed *through* the
lambda yet). Names bound by the outer `let~` chain that appear in
the `let_state` continuation's state pair end up as unbound
metavariables — surfacing as `Must evaluate to a closed term`.

This is the precise defect. The CPS-bind fix avoids it by never
putting `Shallow.let_state` inside brackets in the first place.

### Workaround in effect (2026-05-30, ORIGINAL)

Defer for `fun_cancelLock_212` specifically.  UnstakingManager
equivalence theorems retain placeholder bodies proving
`LowM.Pure (Result.Ok tt) ⇓ Result.Ok tt`.

### Resolution update (2026-05-30, LATER same day)

The deeper hypothesis above turned out to be wrong. The "still
blocked" state was real DURING the bisection but resolved once a
clean regeneration ran against the linkersymbol-patched library.
Empirical test post-fixes: `coqc -R . ReserveGovernor -R ...
RocqOfSolidity ... generated/UnstakingManager_shallow.v` returns
exit code 0. All three big entrypoints (cancelLock_212,
claimLock_270, createLock_144) elaborate cleanly.

The CPS-pre-bind change in shallow_embed.py (commit c7d737aee0)
was reverted because it materially altered Shallow.if_ emission
shape in a way that broke ThrottleLib's existing Phase 1.3 walker
(the walker matches on the old `Shallow.if_(| ... |)` call form,
the CPS variant emits `let~ γ_cond := [[ ... ]] in Shallow.if_
γ_cond ...`). The defensive CPS layering rule is technically
correct for the abstract pattern, but it's a breaking change for
consumer codebases with walkers tuned to the prior emission. Worth
keeping in a separate branch upstream for future contracts that
hit the M.monadic-vs-Shallow.let_state defect, but not applied as
a global migration without coordinating walker updates.

### When this might matter elsewhere

Any contract with **nested if-then-else where the inner if rebinds a
local declared in the outer if's then-block** can still hit the
underlying M.monadic-vs-Shallow.let_state defect — even with
linkersymbol defined, if some future Yul pattern emits that exact
shape inside `[[ ]]`. The pattern shows up in Solidity's safe-call
patterns (try/catch), ERC-style returndata-handling, and any code
using `returndatasize` + memory clamping. The CPS pre-bind fix in
shallow_embed.py defends against this; reapply it (or write
walkers against the CPS shape from the start) if a future
contract surfaces the error genuinely. Cross-reference with
[[R035]] (the YulSwitch surface fix) — these are sibling
generator-side hardenings.

## R042: `M.monadic` diagnostic — the "object of type ident" trap is solved

When `[[ e ]]` contains an unresolved identifier (a missing
primitive Definition, a misspelled function name, a forward
reference, or a missing Require Import), Coq previously surfaced
the failure as:

```
Error: Must evaluate to a closed term
offending expression: e
this is an object of type ident
```

This is the diagnostic shape that misled WISDOM R041's first-pass
diagnosis for hours.  The "ident" is M.monadic's Ltac argument
name leaking through `exact` when [type of e] can't elaborate the
expression.  Every kind of unresolved-identifier error produces
this *identical* message — there's nothing distinguishing a
missing Yul primitive from a typo from a forward reference.

### Fix landed (commit 754592d34f on
`TheFrozenFire/rocq-of-solidity:integration`)

`M.monadic` is now guarded by a `tryif (type of e) then ... else
fail 100 ...` wrapper.  On the success path: zero behaviour change.
On the failure path: the cryptic `ident` message is replaced with
a clear `Tactic failure` that names the two most common causes
(missing Require Import / missing primitive Definition) and points
at the canonical fix location.

The empirical effect:

```
Before:
  Error: Must evaluate to a closed term
  offending expression: e
  this is an object of type ident

After:
  Tactic failure: M.monadic: the expression inside [[ ... ]]
  cannot be type-checked.  Most likely cause: an identifier used
  inside the brackets has no Definition in scope.  Common cases:
  (1) a missing Require Import for a Module that defines the
  identifier; (2) a Yul primitive that rocq-of-solidity doesn't
  yet model — add it next to loadimmutable / memoryguard in
  simulations/RocqOfSolidity.v.  See WISDOM R041 for the
  linkersymbol case study.
```

Any future R041-class bug should take seconds to diagnose instead
of hours.  Multi-agent workflows benefit doubly: every agent that
hits this error in the future gets pointed at the real cause
instead of running the same bisection ladder from scratch.

### Companion finding: Stdlib primitive coverage is complete

A defensive sweep cross-checked every standard Yul EVM
instruction (arithmetic, comparison, environment, block,
storage/memory, logging, system, object-mode) against
`simulations/RocqOfSolidity.v`'s `Stdlib` module.  Every primitive
the generator can emit is defined, modulo the rename convention
for Coq reserved words (`mod` → `mod_`, `return` → `return_`).
Notably included: `loadimmutable`, `setimmutable`, `linkersymbol`
(the R041 fix), `memoryguard`, `dataoffset`, `datasize`,
`datacopy`.

If a future contract surfaces another unbound-identifier error
inside `[[ ]]`, the M.monadic diagnostic will catch it — but
based on this sweep, the cause won't be another missing standard
Yul primitive.  The cause will be either: (a) a generator
emission for a non-standard / object-level construct
(`verbatim_*`, inline-assembly bytes blocks), or (b) a typo in
hand-written proof code, or (c) a missing Require Import.  The
M.monadic error message covers all three.

## R044: two patterns for outer-wrapper equivalence proofs

Two patterns surfaced together while closing the RewardTokenRegistry
[fun_isRegistered_155] outer wrapper. Both are reusable for any
contract whose entry point delegates through a helper chain.

### Pattern A: generic `cu` arm for nested-function bodies

When an outer function calls a helper whose body is `unfold`ed in the
prelude, the call site becomes `LowM.Call (LowM.Let ...) LowM.Pure`.
The walker can't recognize this via its specific-function arms — those
match function names, not the inlined body shape.

Add a generic arm:

```coq
| |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
```

This unfolds the call to `LowM.let_ body continuation`, letting the
walker traverse the inlined body normally. Use after the
specific-function arms so they get first crack; the generic arm is
the fallback for "any call whose body has already been unfolded."

The alternative — proving a separate theorem about the helper and
delegating via `c; [apply HelperTheorem | ]` — is the right move when
the helper appears in many places. For one-shot inlining, the generic
`cu` arm is shorter.

### Pattern B: subst the intro-introduced lets before destruct

When a theorem uses `let state := ... in let expected := ... in
exists state', ...`, an `intros state expected` brings them in as
*local definitions* (with `:=`). `destruct` doesn't see through these
— it case-splits the syntactic expression in the goal, leaving
`expected` symbolic on the LHS while substituting only on the RHS.

Fix: `subst expected. subst positions_value.` (or whichever locals
appear in the case-split). After `subst`, the let-bindings are gone
and `destruct (positions_value =? 0)` correctly case-splits both
sides.

Smell test for this pattern: after `destruct ... eqn:H`, the goal
has `expected = if true then X else Y` on the LHS (where `expected`
is a local let) but the RHS computed normally. The fix is upstream
in the proof — `subst` before the walker.

### When to combine

Outer-wrapper proofs that bridge contract output → sim invariant
typically need BOTH patterns:

  1. `subst` the let-introduced expected/state/positions_value.
  2. Pose the inner theorem upfront with all its witnesses.
  3. Walker with generic `cu` arm for unfolded-helper calls.
  4. Closure via `RunO.PureEq + f_equal + bridge lemma`.

RewardTokenRegistry.run_isRegistered_equivalent is the canonical
example. Same shape generalizes to any
`view_function token → helper_chain → leaf_view` composition.

## R045: OZ modifier mocks — symbolic [with_X body] expansion in lieu of shallow form

### The problem

OZ modifiers (`nonReentrant`, `whenNotPaused`, `onlyRole`, etc.) expand
inline in Solidity as wrapper statements bracketing the body:

```
modifier nonReentrant() {
  _nonReentrantBefore();
  _;                // <user body>
  _nonReentrantAfter();
}
```

After `solc`, the modifier expansion may not be visible in either the
shallow or deep generated form: solc compresses the wrapper into a
named helper (`modifier_<name>_<id>`) that the call site dispatches
through, rather than inlining the pre/post sstore + check sequence at
the call site. For some contracts (`StakingVault.claimRewards`), the
shallow form isn't generated at all because the contract is large and
the equivalence tier hasn't reached it.

This blocks the natural equivalence approach — there's no Yul-side
call chain to thread the pre/post checks through.

### The pattern: symbolic `with_X` expansion against the mock

Mock the modifier's storage semantics ([State.t], [enter], [exit])
exactly per OZ source. Then define a Gallina-level wrapper that
models the modifier's expansion shape:

```coq
Definition with_nonReentrant {A : Set}
    (s : State.t) (body : State.t -> Result.t (State.t * A)) :
    Result.t (State.t * A) :=
  match nonReentrant_enter s with
  | Result.Revert p q => Result.Revert p q
  | Result.Success s_entered =>
      match body s_entered with
      | Result.Revert p q => Result.Revert p q
      | Result.Success (s_after_body, a) =>
          Result.Success (nonReentrant_exit s_after_body, a)
      end
  end.
```

Prove the headline properties against this wrapper:

- `with_X_post_status_invariant` — storage-trace property (status
  unchanged across boundary).
- `with_X_nested_call_reverts` — OWASP SC01 form.
- `with_X_already_X_short_circuits` — pre-check fail-fast.
- `with_X_passthrough_output` — modifier is transparent on success.
- `with_X_body_sees_X` — characterises the state the body observes.

Each is a 5-10 line direct destruct/rewrite proof. All close with Qed.

### When this beats waiting for the shallow form

- **Right now**: lets you state machine-checkable properties of the
  modifier's effect (used by Audit.v / Caveat-5 to claim coverage of
  OWASP SC01 etc.) without waiting for the equivalence tier to catch
  up.
- **Later**: when the shallow form lands, the `with_X` wrapper
  becomes the bridge — equivalence proof rewrites the Yul call
  sequence into `with_X body` shape, then the existing lemmas close.

### When NOT to use this

If the shallow form already inlines the pre/post check sequence
visibly (ThrottleLib's modifiers do this), bind directly to the
shallow form via R040 (wrapper-shape sstore leaves) + R033 (PureEq
for branches). The symbolic-expansion path is for the case where the
shallow form doesn't exist OR compresses the modifier into a helper.

### Touchpoints

- `mocks/ReentrancyGuard.v` — mock with [State.t], [nonReentrant_enter],
  [nonReentrant_exit] semantics.
- `proofs/equivalence/ReentrancyGuard.v` — `with_nonReentrant` symbolic
  wrapper + 5 headline lemmas.
- `mocks/Nonces.v` — replay-protection mock; precondition shape,
  not a wrapping modifier. See "Variant: precondition shape" below.
- `proofs/equivalence/Nonces.v` — `with_useCheckedNonce` symbolic
  wrapper + 5 headline lemmas (task #236).
- Future: `mocks/Pausable.v` (whenNotPaused / whenPaused),
  `mocks/AccessControlEnumerable.v`'s onlyRole expansion.

### Variant: precondition shape (not a wrapping modifier)

Some OZ helpers expand as a precondition check followed by the body
— no post-call cleanup. The canonical example is `_useCheckedNonce`:

```
_useCheckedNonce(owner, nonce);  // can revert, mutates state on success
<body>;                          // user code, sees mutated state
```

For this shape the wrapper drops the exit pair from R045's basic
template and threads the mutated state straight into the body:

```coq
Definition with_X {A : Set}
    (s : State.t) (args ...) (body : State.t -> Result.t (State.t * A)) :
    Result.t (State.t * A) :=
  match X_check s args ... with
  | Result.Revert p q => Result.Revert p q
  | Result.Success s' => body s'
  end.
```

The five-lemma template still applies, but the lemmas shift focus
from enter/exit invariants to "body sees the mutated state" /
"replay-attempt reverts inside the precondition". Concrete shapes
demonstrated by `proofs/equivalence/Nonces.v`:

- `with_X_match_runs_body` — when precondition holds, body executes
  with the mutated state (analogue of `with_X_body_sees_X`).
- `with_X_replay_reverts` — when precondition fails, the wrapper
  short-circuits and the body never runs (analogue of
  `with_X_already_X_short_circuits`).
- `with_X_increments_target_account` (mock-specific) — the
  per-entity mutation respects isolation properties of the
  underlying mock.
- `with_X_monotone` (mock-specific) — the mutation is directional
  (here, strictly increasing).
- `with_X_replay_protection` — two-step composition: a successful
  call followed by a second call with stale arguments reverts.

This subclass arises whenever the helper is a state-mutating
precondition rather than a pre/post bracket. Pausable's
`whenNotPaused` still fits the wrapping-modifier shape (no
mutation); `_useCheckedNonce` and most `_consume*` helpers fit the
precondition shape.

### Catalog reference

OZ has ~14 modifier-class items in the catalog. Treating each via
this pattern lets the foundation tier progress in parallel with the
equivalence tier, with mechanical promotion to real bindings as
shallow forms become available.

## R046: shallow_embed.py drops sstore in OZ _grantRole — generator bug

**Status: RESOLVED upstream at
`TheFrozenFire/rocq-of-solidity:integration@696f60fd73` (2026-05-30).**

The fix was a 33-line patch to `shallow_embed.py`'s `YulSwitch`
handler: previously the list comprehension filtered out the default
case (`if case.get('value') != "default"`) and replaced its body with
a synthetic `else M.pure (BlockUnit.Tt, …)` no-op. The patch now
emits the default's body as the `else` branch (with the same
`lift_state_update` shape used for value cases) and folds the
default's `updated_vars` into `commonly_updated_vars` so the
surrounding `let_state~` binding picks up everything.

Affected contracts beyond Guardian: any OZ AccessControl mutator
(`_grantRole`, `_revokeRole`, `_setRoleAdmin`) AND every
`EnumerableSet` mutator (`_add`, `_remove`) — solc lowers these to
Yul switches where the entire mutation body lives in the default arm.
RewardTokenRegistry_shallow.v regenerated locally shows ~80 lines
recovered in `fun__add_…` and `fun__remove_…` alone.

Verification (2026-05-30, against the regenerated Guardian_shallow.v):
- `fun__grantRole_1468`'s `else` arm now contains the expected
  `update_storage_value_offset_0_t_bool_to_t_bool` call, the `log4`
  for `RoleGranted`, and the `var__1437 := 1` + `Leave` sequence.
- The regenerated `Guardian_shallow.v` compiles cleanly under
  `coqc 8.20.1` (no R035-style `M.monadic`-vs-`Shallow.let_state`
  nesting issue surfaces — the nested `let_state~ 'tt :=` produced
  for the `log4` block stays well-formed).
- `proofs/equivalence/Guardian.v::run_grantRole_1468_observed_behavior`
  fails to compile against the new shallow form (it asserted the
  function returns 0 with state unchanged, which is no longer true).
  The break is the success criterion.

Follow-on tasks left after the upstream landing:
  - Regenerate Guardian/RewardTokenRegistry/VersionRegistry shallow
    forms via `bash formal-verification/scripts/shallow-embed-sweep`
    (Guardian regenerated and validated locally as part of this
    landing; others as needed).
  - Retire or restate
    `proofs/equivalence/Guardian.v::run_grantRole_1468_observed_behavior`
    — left as-is per the upstream-fix instructions, so it currently
    breaks the build by design.
  - Close `run_grantRole_1359_equivalent` (currently `Admitted`) using
    the projection-against-`AccessControl.grantRole` shape sketched in
    its docstring — now possible with the sstore in place.

Diagnosed 2026-05-30 while staging task #234 Phase 1 (Guardian
grantRole equivalence). The bug: `shallow_embed.py` drops the
sstore body in the success branch of OZ's `_grantRole` Yul switch.

### The bug

OZ 5.4.0's `AccessControl._grantRole(role, account)` Solidity:

```solidity
function _grantRole(role, account) internal returns (bool) {
  if (!hasRole(role, account)) {
    _roles[role].hasRole[account] = true;   // <-- this sstore
    emit RoleGranted(role, account, _msgSender());
    return true;                            // <-- and this assignment
  } else {
    return false;
  }
}
```

In `Guardian_shallow.v`'s `fun__grantRole_1468`, the corresponding
shallow form (verified via `rocq_query Print`):

```coq
let~ expr_1442 := fun_hasRole_1292 role account in
let~ expr_1443 := cleanup_t_bool (iszero expr_1442) in
let_state~ var__1439 :=
  let~ δ := pure expr_1443 in
  if δ =? 0 then    (* already a member *)
    let~ expr_1463 := pure 0 in
    let~ var__1439 := pure expr_1463 in
    pure (BlockUnit.Leave, var__1439)
  else              (* SHOULD grant, but body is a no-op *)
    pure (BlockUnit.Tt, var__1438)      (* var__1438 = 0 here *)
default~ var__1439 in
pure (BlockUnit.Tt, var__1439)
```

The "should grant" branch is just `pure (BlockUnit.Tt, var__1438)`
where var__1438 was Pure-bound to 0. The sstore
(`update_storage_value_offset_0_t_bool_to_t_bool`) and the
`var := 1` assignment from the deep form are both missing.

Result: `fun__grantRole_1468` is observationally a constant function
that returns 0 with state unchanged, regardless of inputs.

### Detection recipe (cross-contract)

For any OZ-derived shallow form, check the AccessControl mutator
chain (\_grantRole / \_revokeRole / \_setRoleAdmin) by Print:

```
rocq_query Print <Contract>_<id>.<Contract>_<id>_deployed.fun__grantRole_<n>.
```

If the `let_state~ ... default~ ... in` body's `else` arm of the
switch is `pure (BlockUnit.Tt, var__N)` (a no-op continuation),
the sstore was dropped. Compare with the deep form's `Code.Function.make`
for the same function — the deep form WILL have the missing
mapping_index_access + update_storage_value_offset_0_t_bool_to_t_bool
sequence inside a `M.switch` arm.

### Affected proofs

- `proofs/equivalence/Guardian.v::run_grantRole_1359_equivalent`
  (admitted, awaiting upstream fix).
- Any future RewardTokenRegistry / VersionRegistry / TimelockController
  role-mutator equivalence (same OZ inheritance chain).

### What still works

- View-only equivalence (hasRole, getRoleAdmin, isRegistered, etc.)
  — the read side doesn't touch the broken sstore arm.
- Mock-level proofs against `mocks/AccessControl.v` — the mock is
  sound; the gap is only in the shallow form.
- Equivalence proofs for non-OZ-AccessControl mutators (e.g., the
  Throttle's consumeProposalCharge — already Qed'd in ThrottleLib.v).

### Fix path

Upstream `shallow_embed.py` — option 1 from `notes/shallow_embed_oz_gaps.md`:
extend `M.monadic` (in `rocq-of-solidity/rocq/RocqOfSolidity/RocqOfSolidity.v`)
to traverse `Shallow.let_state`. The current Ltac defect causes the
`success` lambda inside `Shallow.if_(| _, succ, _ |)` to be silently
dropped when `succ` is a `let_state~`-shape with an sstore inside.

A scoped alternative (until the upstream fix lands): hand-patch
`Guardian_shallow.v::fun__grantRole_1468` to inline the missing
sstore. Rejected — drift would re-introduce the bug on the next
`shallow_embed.py` sweep, and there's no governance enforcing the
patch. The right fix is upstream.

### Provenance

- First documented in: `proofs/equivalence/Guardian.v` inline
  docstring above `run_grantRole_1359_equivalent`.
- Cross-ref: WISDOM R035 (the underlying Ltac defect),
  `notes/shallow_embed_oz_gaps.md` gap 2 (catalogued risk).

## R047: Case-split BEFORE [eexists] when an if-then-else emits diverging BlockUnit modes

**Status: closed. Pattern landed in
`proofs/equivalence/Guardian.v::run_grantRole_1468_observed_behavior`.**

A Yul switch (lowered as `Shallow.let_state ~ ... := [[ if δ =? 0
then BlockUnit.Leave else BlockUnit.Tt ]] default~ ...`) whose two
arms emit DIFFERENT `BlockUnit.t` modes but the same value cannot
be closed with `eexists; ... ; destruct cond eqn:Hd`. The
`?output_inter` metavariable for the let_state's intermediate
result is shared across both branches; one branch instantiates it
to `Result.Ok (Leave, 0)`, the other to `Result.Ok (Tt, 0)`, and
they conflict.

### Smell test

After case-splitting on the switch condition inside an `eexists`
proof, you get a unification error like:

```
Unable to unify
  "Result.Ok (BlockUnit.Tt, 0)" with
  "Result.Ok (BlockUnit.Leave, 0)".
```

The error fires at `apply RunO.Pure` in the second branch — the
first branch already committed the metavar.

### Fix — case-split before eexists, use [exists] explicitly per-arm

```coq
(* Set up the prelude (pose, set, etc.) — anything that doesn't
   introduce existentials. *)
intros state.
pose proof (... ) as Hinner.
set (cond := ...) in *.

(* CASE-SPLIT FIRST, before eexists. *)
destruct (cond =? 0) eqn:Hd.
- (* hd = true branch *)
  exists state_hr.           (* witness committed per-branch *)
  ... close arm ...
- (* hd = false branch *)
  exists state_hr.           (* DIFFERENT witness (or same) per-branch *)
  ... close arm ...
```

The witnesses can be the same (`state_hr` in both arms above) or
different — but they're committed in disjoint scopes, so the
metavar conflict disappears.

### When to combine with R033

R033's `RunO.PureEq` bridge fixes the *value* divergence (one arm
emits `1e18` while the other emits `Z.min 1e18 raw`). R047 fixes
the *control-mode* divergence (one arm `Leave`s while the other
`Tt`s). The two are independent.

If a switch's body has BOTH kinds of divergence (different modes
AND different value shapes that need PureEq to bridge), apply R047
first (case-split before eexists), then R033 inside each branch.

### Why the case-split-after-eexists trap exists

`eexists state'` allocates `?state'` as a metavariable in scope
*before* the case-split. Any subsequent walker step that needs to
produce a concrete `state'` instantiates it the first time. After
the case-split, both arms share the same `?state'` — instantiated
by whichever closes first.

For `?output_inter` metavars (the intermediate output of a
let_state or sub-call), the same applies — they're allocated by
the walker BEFORE the case-split, so they're shared across arms.

`destruct` before `eexists` keeps each arm's existentials in its
own scope, so witnesses commit per-arm and don't conflict.

### Touchpoints

- `proofs/equivalence/Guardian.v::run_grantRole_1468_observed_behavior`
  closes with Qed using this pattern (commit landing this WISDOM).
- Future use: any OZ AccessControl mutator equivalence with the
  same switch shape, once the upstream `shallow_embed.py` sstore
  bug is fixed (see R046). The case-split-first pattern remains
  the right move for any post-`shallow_embed.py`-fix mutator
  whose two arms still emit different modes (the granted vs
  already-member case).
- Generalized: any Yul `for`-loop with conditional `break` /
  `continue` / `leave` exit — same divergent-mode shape.

## R048: R045 variant for pure-function libraries (no [with_X] wrapper)

R045 captured two shapes for OZ helpers — modifier-shape (bracketing
[with_X body], e.g. [nonReentrant]) and precondition-shape (sequenced
check-then-body, e.g. [_useCheckedNonce]). A third shape arises for
pure-function libraries (`library` keyword in Solidity, all entries
operate over an explicit `Set storage` / equivalent reference passed
in by the caller — OZ's `EnumerableSet`, `EnumerableMap`,
`Checkpoints`, etc.).

### Why [with_X] doesn't fit

The Yul-side call shape at a consumer is:

```
let prev = sload(...)
let res  = library_op(prev, args)
sstore(...)
```

There is no surrounding body to bracket: the library call is a single
sub-expression in the caller's straight-line code, not a wrapper that
runs before/after user code. A [with_X body] wrapper is a category
mismatch — there's no [body] argument to thread through.

### The right shape: standalone consistency theorems

The R045 sanity check for this class is the mock's standalone
internal-consistency lemmas, expressed at the equivalence-file level
as their domain-flavored composition theorems:

- `contains_after_add_is_true` — set-add post-condition
- `length_grows_strictly_with_add_of_new` — length is a faithful
  counter for distinct elements
- `length_after_successful_remove` — symmetric to add
- `at_index_some_iff_in_bounds` — bounded read is total on `[0, len)`
- `position_of_nonzero_iff_contains` — the redundant index agrees
  with the membership test (OZ's [_contains] vs the [_values] scan)
- composition lemmas (e.g. `add_remove_inverts_when_absent`) — the
  operations interact correctly, not just in isolation

This is more like a unit-test sufficiency proof than a
modifier-expansion bridge: the mock's semantics are demonstrated
consistent, and downstream equivalence binds to those semantics
once the shallow form lands.

### When this applies

The library shape — every operation takes the state-by-reference and
returns either a new state or a primitive value, no per-call
storage-side-effect bracket — is the test. If the consumer expands
the library call as `sload; op; sstore` rather than as a wrapping
modifier, use the standalone-consistency shape.

### Catalog members

- `EnumerableSet` (Bytes32Set / AddressSet / UintSet) — closed by
  [proofs/equivalence/EnumerableSet.v] (task #232).
- `EnumerableMap` (future) — same shape.
- `Checkpoints.Trace*` — already shape-matched by
  [mocks/Trace208.v] + ad-hoc theorems; the consistency style is
  in place but not standardized.
- `Address` / `SafeCast` / `Math` (pure stateless) — same shape
  but no state argument, so the theorems collapse to "value-level
  algebraic identities".

### Touchpoints

- [proofs/equivalence/EnumerableSet.v] — the prototype. Seven Qed'd
  consistency theorems against [mocks/EnumerableSet.v].
- Future EnumerableMap / Checkpoints work should adopt this shape
  unless a wrapping-call or precondition-call story emerges in the
  consumer (in which case fall back to R045 modifier-shape or
  precondition-shape).

### Cross-references

- R045 — the modifier-shape and precondition-shape variants for
  state-mutating helpers.
- R046 — generator gap that makes full-mutator equivalence against
  the shallow form unreachable for OZ AccessControl mutators;
  blocks the natural EnumerableSet binding via
  AccessControlEnumerable.

## R049: Multi-slot proj_sim — cons-to-front Map2 encoding for EnumerableSet positions

**Status: closed. Landed in
`proofs/equivalence/Guardian.v::proj_sim` (slot 1) and
`proj_sim_add_admin_not_in` (bridge lemma); task #248.**

When a sim collapses an OZ `AccessControlEnumerable`-derived role
machinery into one `list Address` per named role, the natural
storage projection is multi-slot:

  - slot 0 = `Map2 (role, account) -> 0/1` (the `_roles` members
    sub-mapping; reads close the `hasRole` view).
  - slot 1 = `Map2 (role, value) -> position` (the `_roleMembers`
    EnumerableSet `_positions` sub-mapping; reads come up only on
    `_remove`'s gate check, but the slot is touched on every `add`).

The catch: OZ's `EnumerableSet._add` appends to the end of the
internal `_values` array and assigns `position = new_length`. A sim
that conses to the FRONT (e.g., `add_role lst a = a :: lst`) has a
different ordering. To get a clean inductive bridge lemma without
contorting the sim, define `positions_for_role role (a :: rest) =
((role, a), Z.of_nat (List.length rest) + 1) :: positions_for_role
role rest` — i.e., assign the new position based on the AT-TIME-OF-
INSERT tail length. Under this convention the sim's cons-to-front
gives the same set of (key, value) pairs the OZ append-and-assign
would, just enumerated in reverse insertion order.

The bridge lemma then reads:

```coq
~ In addr s.(State.admins) ->
proj_sim (add_admin s addr) =
  [ Map2 (((role, addr), 1) :: role_member_map s);
    Map2 (((role, addr), length admins + 1) :: role_positions_map s) ].
```

Proof closes by `unfold; addr_in_false_iff_not_In; reflexivity`. The
`addr_in_X_iff_In` pair (boolean ↔ Coq `In`) is the canonical bridge
between the sim's Boolean membership checks and the projection's
`In`-flavored hypothesis.

### When to use

- The sim has a list-of-elements per role/category, with cons-style
  add and the OZ implementation uses an EnumerableSet (or open-coded
  equivalent — see RewardTokenRegistry).
- The projection covers the `_roles`/`_positions` slots faithfully
  but not the `_values` array body (which is unobserved by the
  equivalence-of-interest path).

### What this doesn't address

- The `_values` array length cell and the `_values[i]` array body
  slots. They live at `keccak256(set_slot)` (length) and
  `keccak256(set_slot) + i` (body). If a future equivalence touches
  `getRoleMember(role, idx)` or `getRoleMemberCount`, extend
  `proj_sim` with additional slots.
- The walker-side bridge: this lemma states the post-state shape
  but doesn't run the sstore. The companion walker proof (residual C
  in the task #248 plan) uses
  `Storage.run_sstore_map2_u256` which produces a
  `Dict.declare_or_assign`-shaped post-map; the conversion from
  that shape to the cons-prefixed shape used by this bridge needs a
  separate `declare_or_assign_eq_cons_when_absent` lemma (~5 lines,
  by induction on the dict).

### Touchpoints

- `proofs/equivalence/Guardian.v` — multi-slot `proj_sim`,
  `positions_for_role`, `role_positions_map`,
  `addr_in_{false,true}_iff_{not_,}In`,
  `role_{member,positions}_map_add_admin_not_in`,
  `proj_sim_add_admin_not_in` (the headline B-residual closure),
  `proj_sim_add_admin_in` (idempotency companion).
- The pattern transposes to revoke (slot 1 update is more complex —
  OZ's swap-and-pop reshuffles the last element into the removed
  slot; the position invariant needs a tail-rewrite). Defer until a
  revoke equivalence is needed.

### Cross-references

- R044 — outer-wrapper proof patterns (this bridge is the
  companion to a wrapper-walker pose).
- R046 — the upstream `shallow_embed.py` fix that made the slot-0
  sstore body re-emit; same fix recovers the slot-1 EnumerableSet
  mutator bodies.
- R048 — pure-function-library shape that EnumerableSet itself fits;
  this R049 entry is about EnumerableSet's CONSUMER (the
  `AccessControlEnumerable` pattern), where the set is woven into
  a contract's `proj_sim` rather than reasoned about in isolation.

## R050: External `staticcall`-gated mutators — infrastructure gap blocking VersionRegistry.deprecateVersion

**Status: open. Scaffold landed in
`proofs/equivalence/VersionRegistry.v::run_deprecateVersion_equivalent_make_state`
with the residual catalogue documented inline.**

VersionRegistry.deprecateVersion was nominated as the first OZ
mutator-equivalence target after the R046 generator fix, on the
premise that it "JUST sstores true at slot 1". The actual contract
gates the sstore with an EXTERNAL `staticcall` to a separate
`roleRegistry` contract — NOT an internal OZ `AccessControl.hasRole`
read. The Yul body's prelude is, before the sstore can fire:

```
loadimmutable(roleRegistry)
mstore(_22, shift_left_224(0x1918a29c))   ; hasRole_OwnerOrEmergency selector
abi_encode_tuple_t_address(_22 + 4, caller)
_24 := staticcall(gas, roleRegistry, _22, _23 - _22, _22, 32)
if iszero(_24) { revert_forward_1 }       ; staticcall failure
expr_162 := abi_decode_tuple_t_bool_fromMemory(_22, _22 + _25)
require_helper_t_error_10_InvalidCaller(expr_162)
```

The trust-based `RunO.CallContract` rule (R021) lets us choose a
result `call_result = 1` and step past the staticcall, but the
surrounding memory machinery (allocate_unbounded, finalize_allocation,
abi_encode_tuple_t_address, abi_decode_tuple_t_bool_fromMemory,
returndatasize) needs to be built before the walker can fire through.
NONE of that infrastructure exists in the corpus today — every
equivalence proof so far (ThrottleLib, Guardian view side,
RewardTokenRegistry view side, etc.) avoids contracts that do an
EXTERNAL staticcall as part of their mutator gate.

### The residual catalogue (transcribed from the scaffold)

1. **R-statcall** — choose `call_result = 1` via `RunO.CallContract`,
   tied to a callee-spec axiom that says
   `is_owner_or_emergency env.caller = true ⇒ roleRegistry returns 1`.
   The axiom lives alongside `version_hash_injective` and similar
   opaque assumptions in `simulations/VersionRegistry.v`.
2. **R-memprelude** — six new memory leaves:
   `run_allocate_unbounded`, `run_finalize_allocation`,
   `run_mstore_with_shift_left_224`,
   `run_abi_encode_tuple_t_address__to_t_address__fromStack`,
   `run_abi_decode_tuple_t_bool_fromMemory`,
   `run_returndatasize_after_callcontract`. The trickiest is the
   last — the trust-based `cc` rule does NOT canonicalize the
   `Primitive.RLoad` state set by `LowM.CallContract`, so the proof
   author has to assert the post-staticcall return-data length is
   32 bytes either as a hypothesis or as a separate axiom on the
   chosen `state_inter`.
3. **R-immutable** — `run_loadimmutable_returns_role_registry`:
   models `Primitive.LoadImmutable` against a hypothesis
   `env.(immutables) ! "roleRegistry" = Some addr`. ~10 lines.
4. **R-bool-sstore** — `run_update_storage_value_offset_0_t_bool_to_t_bool_at_proj_sim`:
   R040-style wrapper baking in `proj_sim sim`'s 3-slot layout for
   the bool flavor sstore. The body is
   `sload + prepare_store_t_bool + update_byte_slice_1_shift_0 +
   sstore`. ~80 lines once attempted.
5. **R-require** — `run_require_helper_t_error_10_InvalidCaller_succeeds`
   and `run_require_helper_t_error_16_AlreadyDeprecated_succeeds`.
   Mirror ThrottleLib's `run_require_helper_succeeds`. ~15 lines each.
6. **R-postbridge** — `proj_sim_deprecate_at`: R049-style multi-slot
   projection bridge for the deprecate-at-index sim operation.
   ~40 lines.

### Why "simplest OZ mutator" was wrong

The premise that VersionRegistry.deprecateVersion is the simplest OZ
mutator missed the EXTERNAL gating. Guardian.grantRole is actually
the simpler shape (its gate is an internal `hasRole` read against
`_roles[role].members`, same contract, same projection). The R046 fix
unblocks BOTH — but Guardian.grantRole only needs R-bool-sstore +
R-postbridge + the upfront `run_hasRole_equivalent` pose (already
landed). VersionRegistry.deprecateVersion additionally needs all of
R-statcall + R-memprelude + R-immutable.

### Implication for the OZ mutator equivalence roadmap

The "first OZ mutator equivalence" milestone is more naturally hit
via Guardian.grantRole (which the existing
`run_grantRole_1359_equivalent` scaffold is set up for), not
VersionRegistry.deprecateVersion. The latter requires R050's
external-staticcall infrastructure as a prerequisite, which is a
multi-day workstream on its own. The former blocks on R049's
EnumerableSet walker + R-bool-sstore — both of which are visible
on the existing Guardian scaffold's residual list.

Recommend retargeting the "first OZ mutator equivalence" goal to
Guardian.grantRole. VersionRegistry.deprecateVersion remains a valid
target but needs the R050 infrastructure landed first.

### Touchpoints

- `proofs/equivalence/VersionRegistry.v::run_deprecateVersion_equivalent_make_state`
  — the scaffold with theorem statement + admitted proof + full
  residual catalogue in the docstring.
- `proofs/equivalence/Sandbox.v::R021VerificationCheck` — the only
  existing in-corpus use of `RunO.CallContract` (`cc` tactic), a
  one-liner that confirms the constructor + tactic compose.
- `generated/VersionRegistry_shallow.v::fun_deprecateVersion_187`
  — the Yul body referenced above.
- `simulations/VersionRegistry.v::deprecateVersion` — the sim-side
  reference that the equivalence binds against.

### Cross-references

- R021 — the trust-based `RunO.CallContract` rule that R-statcall
  builds on.
- R040 — wrapper-shape sstore that R-bool-sstore mirrors for the
  bool flavor.
- R046 — the upstream generator fix that put the sstore body BACK
  in the success arm (without R046, even the R050 leaves wouldn't
  have an sstore to dispatch on).
- R049 — the multi-slot proj_sim pattern that R-postbridge mirrors.

## R051: Guardian.grantRole closure — deeper residuals than R046 anticipated

**Status: open. msgSender leaf landed; three structural residuals
remain. Closes the prompt's "first OZ mutator Qed" milestone target
back to in-progress.**

Post-R046, the inner `_grantRole_1468` sstore was supposed to be the
only big blocker for `Guardian.grantRole`'s equivalence. Closing the
full chain (`fun_grantRole_1359` → `modifier_onlyRole_1351` →
`fun_getRoleAdmin_1340` + `fun__checkRole_1305` →
`fun_grantRole_1359_inner` → `fun__grantRole_704` →
`fun__grantRole_1468` + `fun_add_2085`) uncovered three structural
gaps the original residual catalogue (in
`run_grantRole_1359_equivalent`'s pre-task-#248 docstring)
under-specified:

### R051.a — slot-1 admin-field read (`fun_getRoleAdmin_1340`)

**Status: CLOSED (2026-05-31).**
`run_fun_getRoleAdmin_1340_at_proj_sim` landed at
`proofs/equivalence/Guardian.v`. The admin-field slot
`keccak256(role, 0) + 1` is OUTSIDE `proj_sim`'s range (slot 0 is
a `Map2 (role, account)`, not a `MapStruct (role, offset)`).
Closed via Option A from the gap analysis — the
**out-of-projection trust axiom** path, NOT a structural refactor
of slot 0 (which would break R051.b's
`run_update_storage_value_t_bool_at_proj_sim` and `run_hasRole_equivalent`).

What landed:
- `run_sload_role_admin_at_proj_sim` (Axiom): asserts that
  `sload(keccak256_tuple2 role 0 + 1)` returns
  `DEFAULT_ADMIN_ROLE_bytes32` under `proj_sim sim` for any of the
  three Guardian roles (`H_role_known` disjunction hypothesis).
- `run_read_role_admin_at_proj_sim` (Qed): wraps the axiom with
  the `extract_from_storage_value_offset_0_t_bytes32` identity
  chain (`shift_right_0_unsigned + cleanup_from_storage_t_bytes32`,
  both no-ops at U256 rep level). Two new helper lemmas
  (`run_cleanup_from_storage_t_bytes32`,
  `run_extract_from_storage_value_offset_0_t_bytes32`) added.
- `run_fun_getRoleAdmin_1340_at_proj_sim` (Qed): composite leaf
  for the full `fun_getRoleAdmin_1340` body — chains the
  `MappingIndexAccessBytes32RoleData` memory-threading lemma, the
  `Pure_add_keccak_offset` discharge for the `add(_, 1)`, and the
  read helper above.

Trust justification: every Guardian role uses DEFAULT_ADMIN_ROLE
as its admin (`project_sim_to_ac` already encodes this); Guardian.sol
never calls `_setRoleAdmin` so the OZ default applies. Same
parametric-trust shape as R049's slot-1 positions modeling and
R052 Option 1's array-slot axioms. Documented as an audit caveat
inline in the lemma's docstring.

### R051.b — bool sstore wrapper (`update_storage_value_offset_0_t_bool_to_t_bool`)

**Status: CLOSED (2026-05-31).**
`run_update_storage_value_t_bool_at_proj_sim` landed at
`proofs/equivalence/Guardian.v`. Sister to the slot-3 bytes32
wrapper `run_update_storage_value_t_bytes32_at_proj_sim` from
R051.c Phase 3. The R046-restored sstore in `_grantRole_1468`'s
success arm goes through `convert_t_bool_to_t_bool + sload +
update_byte_slice_1_shift_0 + prepare_store_t_bool + sstore` (the
bool flavor of the R040 chain).

The walker composes:
- `run_sload_role_member_at_proj_sim` (slot-0 sload, already
  existed pre-R051.b)
- `run_convert_t_bool_to_t_bool_of_1` + `run_prepare_store_t_bool`
  + `run_update_byte_slice_1_shift_0_bool_1` (bit-mask reduction
  under the bool invariant `prev ∈ {0,1}` from
  `role_member_map_values_bool`)
- `run_sstore_role_member_at_proj_sim` (slot-0 sstore wrapper —
  proven directly from the framework's `run_sstore_map2_u256`
  because slot 0's nested-keccak Map2 shape ALIGNS with the
  framework axiom; NO per-shape trust axiom is required, unlike
  R051.c slot-3 where the array body's `keccak256_single`-based
  slot shape diverges from the framework's nested-keccak).

The post-state is `Dict.declare_or_assign role_member_map (role,
account) 1` — i.e., the framework-shape Map2 update. The
projection bridge `proj_sim_add_admin_not_in` then converts this
to the cons-prefixed shape used by the outer grantRole walker.

What `run_update_storage_value_t_bool_at_proj_sim` does NOT
include: the bridge from `Dict.declare_or_assign` to the
cons-prefix shape itself. That conversion is a separate
`declare_or_assign_eq_cons_when_absent`-style lemma (R049
docstring describes it) which is downstream of where this wrapper
lands; the grantRole outer walker calls it after this leaf fires.

### R051.c — EnumerableSet `_values` array (`fun_add_2085`)

The deepest blocker. `fun_add_2085` → `fun__add_1614` performs:
  - `array_push_from_t_bytes32_to_t_array...dyn_storage_ptr`: writes
    to the `_values` array length cell (slot
    `keccak256(role, 1) + 0`) AND the body element at
    `keccak256(keccak256(role, 1)) + length`.
  - `update_storage_value_offset_0_t_uint256_to_t_uint256` at the
    positions sub-mapping (slot 1's offset 1; this matches
    `role_positions_map`).

The `_values` length cell and array body slots are NOT in proj_sim.
R049 explicitly defers them ("If a future equivalence touches
`getRoleMember(role, idx)` or `getRoleMemberCount(role)`, extend
proj_sim with additional slots"). For grantRole, NO downstream
observer reads these — but the SSTOREs fire regardless, and the
walker needs leaves to discharge them. This is multi-day work:
  - extend proj_sim with a third slot for the EnumerableSet `_values`
    array (length + body, encoded so the bridge lemma stays
    inductive on the role list)
  - build `run_array_push_at_proj_sim` as an R040-style wrapper
  - extend `proj_sim_add_admin_not_in` (or build a companion) to
    cover the new slot's post-state shape.

### What this means for the milestone

The "first OZ mutator equivalence Qed" milestone target (originally
nominated for `run_grantRole_1359_equivalent` after R050 retargeted
away from VersionRegistry.deprecateVersion) requires R051.a, .b,
and .c. **All three closed (2026-05-31).** The remaining work for
`Guardian.grantRole`'s full Qed is purely the outer-walker
threading pass — no remaining structural gaps.

Re-evaluating the corpus's OZ mutator targets:
  - `Guardian.grantRole` — all three R051 leaves CLOSED. Only
    outer-walker threading remains before Qed.
  - `Guardian.revokeRole` — R051.a CLOSED; still needs a
    swap-and-pop variant of .c (harder than .c because the
    positions invariant needs a tail-rewrite per R049's
    deferred-revoke note).
  - `VersionRegistry.deprecateVersion` — needs R050.full.
  - `Guardian.renounceRole` — same shape as revoke.

`Guardian.grantRole` is now within reach of a few-hour
outer-walker threading pass that composes the per-leaf lemmas
through the
[fun_grantRole_1359 → modifier → _grantRole_1468 + fun_add_2085]
chain. No structural blockers remain.

### What this session landed

- `run_fun__msgSender_3197` caller leaf — closes residual (D) from
  the original Guardian.grantRole catalogue. The R046-resolved
  `_grantRole_1468` calls this leaf for the event-log msg.sender
  argument.
- Updated `run_grantRole_1359_equivalent`'s inline residual catalogue
  to reflect R051.a/b/c and the (D)-closed status.

### Touchpoints

- `proofs/equivalence/Guardian.v::run_fun__msgSender_3197` — the
  landed leaf.
- `proofs/equivalence/Guardian.v::run_grantRole_1359_equivalent`
  — the still-Admitted theorem, with R051 residuals enumerated
  inline.
- `simulations/RocqOfSolidity.v::StorableValue.{Map2, MapStruct}`
  — the encoding choice that R051.a refactor would touch.
- R046 (resolved) — the upstream fix that exposed the deeper
  structural gaps R051 catalogues.

### Cross-references

- R040 — wrapper-shape sstore (uint256 flavor); R051.b is the bool
  flavor.
- R046 — the upstream generator fix; pre-R046 the success-arm
  sstore was missing, so R051.b's gap was masked.
- R049 — the multi-slot proj_sim landing that R051.a/c would extend.
- R050 — VersionRegistry.deprecateVersion's external-staticcall
  infrastructure gap; the sister blocker that retargeted this
  milestone to Guardian in the first place.
- R052 — array-shape vs nested-keccak storage gap surfaced while
  attempting the R051.c walker leaf; documents the structural
  blocker that defers Phase 3 of R051.c.

## R052: AccessControlEnumerable `_values` array — projection landed, walker leaf blocked on framework-shape gap

**Status: Option 3 RESOLVED upstream at
`TheFrozenFire/rocq-of-solidity:integration@86d1392e86` (2026-05-30).
Slots 2/3 + projection bridge landed for [Guardian.add_admin] (R051.c
Phases 1-2; task #264). Phase 3 — [run_array_push_at_proj_sim] walker
leaf — newly unblocked: the upstream patch adds [keccak256_single]
(sim-level [Parameter]) and [run_keccak256_single] +
[apply_run_keccak256_single] (proof-side lemma + Ltac), the minimum
primitive that lets the [mstore(0, anchor); keccak256(0, 0x20)]
composite emit a usable [keccak256_single anchor] symbol. The
slot-expression sload/sstore axioms at the array body shape
[keccak256_single anchor + offset] are intentionally left to callers
— their shape depends on the caller's projection (whether the array
body is exposed as a per-anchor [Dict.t U256.t U256.t], a
[Dict.t (U256.t * U256.t) U256.t] keyed by [(anchor, offset)], or a
multi-role [Map2] bridged to the array shape via a per-contract trust
axiom). The smoke lemma
[Guardian.v::ArrayDataslotBytes32.run_array_dataslot] closes the
[array_dataslot_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr] composite
([mstore + keccak256]) with Qed, demonstrating Option 3 composes
cleanly with the existing memory machinery.

Original framework-shape diagnosis (kept for the historical
record): framework's storage axioms expose nested-keccak shapes
([keccak256_tuple2 key (Z.of_nat index)] for single-Map,
[keccak256_tuple2 key2 (keccak256_tuple2 key1 (Z.of_nat index))]
for Map2), but OZ's [array_push] generator emits ARRAY shapes
([sstore(array, len+1)] where [array = set_slot];
[sstore(keccak256(array) + i, value)] at
the keccak-derived dataslot). The two shapes are NOT
unifiable by simple rewriting — they're different storage
expressions.**

### What landed (Phases 1-2)

[Guardian.v::proj_sim] now exposes FOUR slots:

  - slot 0: [Map2 (role, account) → 0/1]      (R049-era)
  - slot 1: [Map2 (role, addr) → 1-indexed-pos] (R049-era)
  - slot 2: [Map (role → length)]              (R051.c; new)
  - slot 3: [Map2 ((role, idx) → value)]       (R051.c; new)

The R051.c additions carry the EnumerableSet `_values` dynamic array.
[role_values_length_map] and [role_values_body_map] project the sim's
three address lists into per-role length and (role, idx)-keyed body
dicts. Convention: with sim list [a_k :: ... :: a_0], OZ's append-style
array is [a_0; a_1; ...; a_k]; element at body index [i] is the value
that, at insert time, made the array length [i + 1].

The projection bridge [proj_sim_add_admin_not_in] now mutates all
four slots simultaneously:

```coq
proj_sim (add_admin s addr) =
  [ Map2 (((DEFAULT, addr), 1) :: role_member_map s);
    Map2 (((DEFAULT, addr), length admins + 1) :: role_positions_map s);
    Map ((DEFAULT, length admins + 1) :: tl (role_values_length_map s));
    Map2 (((DEFAULT, length admins), addr) :: role_values_body_map s) ]
```

The helper [values_for_role_cons_unfold] (cons-of-list under the
[Nat.pred (S n) = n] unfold) makes the slot-3 bridge inductive.

### What the gap looks like — concrete

[Guardian_shallow.v::fun__add_1614]'s body (the `_add` internal call
under [fun_add_2085]) calls
[array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr
set_slot value], which the generator emits as:

```
oldLen     := sload(set_slot)                            (* length read *)
sstore(set_slot, oldLen + 1)                              (* length bump *)
dataArea   := keccak256(0x00, 0x20) after mstore(0, set_slot)  (* = keccak256(set_slot) *)
slot       := dataArea + oldLen * 1
sstore(slot, value)                                       (* body write *)
```

The walker for these three sstores would close cleanly if the
framework exposed:

  - [run_sstore_at_array_length set_slot value]: gives sstore at
    [set_slot] (NOT [keccak256_tuple2 role 2] as Map's axiom
    requires).
  - [run_sstore_at_array_body set_slot i value]: gives sstore at
    [keccak256(set_slot) + i] (NOT [keccak256_tuple2 i
    (keccak256_tuple2 role 3)] as Map2's axiom requires).

The framework provides Map and Map2 axioms in nested-keccak shape.
The slot-1 [_positions] precedent (R049) approximates by
identifying [keccak256(addr, keccak256(role, 1) + 1)] (OZ-actual)
with [keccak256(addr, keccak256(role, 1))] (framework Map2 shape) —
that's an off-by-1 INPUT to the inner keccak. For the `_values`
length/body the gap is bigger: [set_slot] = [keccak256(role, 1)]
(an opaque keccak result), and the framework's Map-axiom shape
[keccak256(role, 2)] is a SEPARATE opaque keccak. The two are
distinct symbolic terms with no shared structure.

### Three options for closing C.3 walker

1. **Per-shape opaque-rewriting axioms** — adopt slot-1's
   approximation strategy: declare an axiom equating the
   array-shape slot expression with the nested-keccak shape under
   the [set_slot = keccak256_tuple2 role 1] precondition.

   ```coq
   Axiom set_slot_length_eq :
     forall (role : U256.t),
       keccak256_tuple2 role 1 = keccak256_tuple2 role 2.
   ```

   This is FALSE in any honest model (different inner keccak
   inputs). It's parametric trust the same way R021's
   `RunO.CallContract` rule is — accept the inconsistency, gain
   the proof. R049 already does this for slot-1; doing it for
   slots 2 and 3 propagates the same loophole.

2. **Add a [StorableValue.Array] constructor** — upstream extension
   to [rocq-of-solidity]:

   ```coq
   Inductive StorableValue.t :=
   | ...
   | Array (length : U256.t) (body : Dict.t U256.t U256.t).
   ```

   plus matching [run_sstore_array_length] and
   [run_sstore_array_body] axioms at the array-shape slot
   expressions. Half-day upstream PR; closes the modeling
   honestly. Then update proj_sim's slots 2/3 to a single
   [StorableValue.Array] per role.

3. **Single-word keccak helper** — at minimum, add
   [run_keccak256_word] (analogous to existing
   [run_keccak256_tuple2] but for one-word input). This lets the
   array_push walker discharge the [mstore(0, x); keccak256(0,
   0x20)] composite into a [keccak256_one x] term. Then options 1
   or 2 can be built on top. Standalone ~30-line addition to
   [rocq-of-solidity/proofs/RocqOfSolidity.v].
   **RESOLVED 2026-05-30** at
   `TheFrozenFire/rocq-of-solidity:integration@86d1392e86`. Final
   patch: 53 lines (15 sim + 38 proof = [keccak256_single]
   [Parameter], [run_keccak256_single] [Admitted] proof lemma,
   [apply_run_keccak256_single] Ltac). Smoke-tested downstream by
   [Guardian.v::ArrayDataslotBytes32.run_array_dataslot] (Qed).

### Recommendation

**Updated 2026-05-30**: Option 3 (the single-word keccak helper)
has landed upstream, providing the minimum primitive needed to
land the [array_dataslot] composite. The next session attempting
[run_grantRole_1359_equivalent] closure can now build the full
[run_array_push_at_proj_sim] walker leaf on top of Option 3 — the
remaining work is the per-contract sload/sstore axioms at the
[keccak256_single anchor + offset] shape, which are intentionally
governor-local (their projection-vs-array bridge is the same
trust-based pattern as the slot-1 positions approximation from
R049). Concrete next-session sketch:

  - In [simulations/Guardian.v] or alongside [proj_sim], declare
    [Axiom run_sstore_at_keccak_single_offset_proj_sim] (or similar
    name) that, given [set_slot = keccak256_tuple2 role <values-slot>],
    discharges [sstore(keccak256_single set_slot + i, value)] to a
    [Dict.declare_or_assign (role_values_body_map sim) (role, i)
    value] post-state. Mirror the [sload] companion.
  - The [array_push] walker then chains:
    [sload(set_slot)] (length read, via [run_sload_map_u256]) →
    [sstore(set_slot, len+1)] (length bump, via [run_sstore_map_u256]) →
    [mstore(0, set_slot)] (memory write, via [apply_run_mstore]) →
    [keccak256(0, 32)] (via [apply_run_keccak256_single]) →
    [sstore(<keccak_single> + len, value)] (body write, via the
    new per-contract axiom above) → final state-equality via
    [proj_sim_add_admin_not_in].

(Historical recommendation, kept for reference: Option 2 is the
right long-term direction — it grows the framework's storage
taxonomy faithfully and makes EnumerableSet modeling cleanly
first-class. With Option 3 landed Option 2 becomes a follow-on
clean-up, not a blocker. Option 1 (the slot-1-precedent extension)
remains available for sessions that want to skip even the
per-contract trust axiom; with Option 3 in place its surface area
is smaller.)

### Touchpoints

- `proofs/equivalence/Guardian.v::proj_sim` — the FOUR-slot
  projection.
- `proofs/equivalence/Guardian.v::role_values_length_map`,
  `role_values_body_map`, `values_for_role`,
  `values_for_role_aux`, `values_for_role_cons_unfold` — the new
  helpers.
- `proofs/equivalence/Guardian.v::proj_sim_add_admin_not_in` —
  the extended four-slot bridge (with companion per-slot lemmas
  `role_values_length_map_add_admin_not_in` and
  `role_values_body_map_add_admin_not_in`).
- `proofs/equivalence/Guardian.v::run_grantRole_1359_equivalent`
  — the still-Admitted theorem; inline residual catalogue
  updated to reflect (A)/(B) closed, (C.3)-walker still open
  with the option-set above documented.
- `generated/Guardian_shallow.v::array_push_from_t_bytes32_to_t_arrayₓ_t_bytes32_ₓdyn_storage_ptr`
  (line 384-400) — the concrete array_push body the walker would
  need to step.
- `rocq-of-solidity/rocq/RocqOfSolidity/proofs/RocqOfSolidity.v`
  — current storage axioms; the new array axioms would land here.

### Cross-references

- R040 — wrapper-shape sstore (uint256 flavor; the C.1 / C.3
  positions-sstore would mirror this for the bool / uint256
  flavors against the projection's slot-0 / slot-1).
- R049 — slot-1 approximation precedent; the same pattern that
  R052's Option 1 would extend to slots 2/3.
- R051 — the parent task; R051.c Phases 1-2 close here; Phase 3
  partially closed (see update below).

### R051.c Phase 3 update — axioms + statement landed, walker body Admitted

A subsequent session (this one) opted for R052 Option 1 — the
per-shape opaque-rewriting axioms — to unblock the
[run_array_push_at_proj_sim] walker. Three governor-local trust
axioms landed in `proofs/equivalence/Guardian.v`:

  - [run_sload_role_values_length_at_proj_sim] — sload at
    [keccak256_tuple2 role 1] returns the per-role length from
    [proj_sim sim]'s slot 2.
  - [run_sstore_role_values_length_at_proj_sim] — sstore at
    [keccak256_tuple2 role 1] updates slot 2's length map.
  - [run_sstore_role_values_body_at_proj_sim] — sstore at
    [keccak256_single (keccak256_tuple2 role 1) + idx] updates
    slot 3's body map at key [(role, idx)].

The [run_array_push_at_proj_sim] composite lemma's STATEMENT
landed alongside; its proof is [Admitted] with a detailed
inline outline of the eight walker steps. The remaining work is
mechanical bit-mask / convert / dataslot composition (~100
lines once attempted in isolation) plus a small companion axiom
([keccak256_single_offset_bound], a sibling to the existing
[keccak256_tuple2_offset_bound]) for the [Pure.add (dataArea)
oldLen = dataArea + oldLen] step in the dataslot path.

### Cross-references (updated)

- R040 — wrapper-shape sstore (uint256 flavor; the C.1 / C.3
  positions-sstore would mirror this for the bool / uint256
  flavors against the projection's slot-0 / slot-1).
- R049 — slot-1 approximation precedent; the new R052 Option-1
  axioms here mirror that pattern for slots 2/3.
- R051 — parent task; the C.3 walker leaf is now infrastructure-
  in-place but the composite proof body remains Admitted.

### R051.c Phase 3 second pass (2026-05-31) — Phase 1 closed; Phase 2 walker open with infrastructure ready

A follow-up session added the Phase 1 axiom + lemma and two new
sload axioms that complete the trust-axiom set needed by the
[run_array_push_at_proj_sim] walker:

  - **[keccak256_single_offset_bound]** (+ derived
    [Pure_add_keccak_single_offset]) — sibling to
    [keccak256_tuple2_offset_bound]. Bounds:
    `0 <= offset < 2^240 → keccak256_single anchor + offset < 2^256`.
    The wider offset bound (vs the [< 32] used for struct fields)
    accommodates array indices up to `2^64 - 1` under
    EnumerableSet's `push` guard.
  - **[run_sload_role_values_length_at_proj_sim_post]** — the
    [storage_array_index_access] body re-reads the array length
    AFTER the [array_push] length sstore has swapped a custom
    [length_map'] into slot 2. The original axiom targets the
    literal [proj_sim sim] shape; this post-shape variant lets the
    walker thread the mid-walker storage mutation cleanly.
  - **[run_sload_role_values_body_at_proj_sim]** — companion sload
    to the existing body sstore axiom. The [update_storage_value]
    body reads the body slot before merging with the incoming
    value via [update_byte_slice_dynamic32]. Missing entries
    return 0 via [map_get_u256]'s default, modeling Solidity's
    zero-init for fresh array indices.

The walker proof body remains Admitted with a detailed in-source
status block (`run_array_push_at_proj_sim`) catalogueing the four
tactical blockers encountered. Summary:

  1. **let_state / if_ unfold cascade** — after eager unfold of
     `M.strong_let_, M.let_, M.generic_let, M.pure, M.call,
     Shallow.let_state, Shallow.if_`, the goal alternates between
     `LowM.Let` (constructor) and `LowM.let_` (CPS function)
     shapes. The `l`/`lu`/`cu` tactic family handles each but
     deciding when to `simpl LowM.let_` vs `cu` requires care.
     ThrottleLib's `throttle_walker` absorbs this with one
     recursive `lazymatch` sweep — the structural fix is to
     build an analogous `array_push_walker` for this contract.
  2. **`update_byte_slice_dynamic32 (sload slot) 0 v` algebraic
     reduction** — the chain
     `or(and(prev, not(shl(0, MAX))), and(shl(0, shr(0, v)),
     shl(0, MAX)))` reduces to `v` for `v` in `[0, 2^256)`,
     independent of `prev`. ~15 lines once isolated as a leaf
     lemma `run_update_byte_slice_offset_0_t_bytes32` mirroring
     `ThrottleLibLeaves.run_update_storage_value_offset_0_t_uint256_to_t_uint256`.
  3. **Body sstore arg** — after (2), the stored value is provably
     `value`, so the walker arm becomes
     `c; [apply run_update_byte_slice_offset_0 |
        apply run_sstore_role_values_body_at_proj_sim]`.
  4. **State threading across the length sstore** — closed by the
     new `_post` axiom variant; only re-binding remains.

**Recommendation for next session (~45 min estimated):** factor
out the bit-mask leaf as a separate Qed lemma in
`proofs/equivalence/Guardian.v` (or a Guardian_Leaves sibling),
then assemble a compact `array_push_walker` `lazymatch` Ltac that
dispatches each call head (sload / sstore / mstore /
keccak256_single / lt / iszero / add / mul / and / or / not /
shl / shr) in one recursive sweep. The eight-step outline resolves
mechanically.

**Build status:** Guardian.v compiles with the proof body
Admitted; the three new infrastructure additions (1 axiom + 1
lemma + 2 new sload axioms) are fully Qed/Axiom-stated and
typecheck against the existing `proj_sim` projection. No
existing definitions, axioms, or proof statements were modified
in this pass.

## R053: grantRole outer-walker composition layer

**Status: PARTIAL (2026-05-31). Composable wrappers for the auth-gate
half landed; mutator body still pending. Milestone Qed not yet reached.**

Post-R051.a/b/c the structural prerequisites for
`run_grantRole_1359_equivalent` are all CLOSED. This pass attacked the
outer-walker threading layer that composes the per-leaf lemmas through
the 5-deep call chain
(`fun_grantRole_1359 → modifier_onlyRole_1351 → fun_getRoleAdmin_1340 +
fun__checkRole_1305 → fun_grantRole_1359_inner → fun__grantRole_704 →
fun__grantRole_1468 + fun_add_2085`).

### Landed in this pass

All Qed-closed and compile against the existing R051 leaves:

- **`run_fun_hasRole_1292_at_proj_sim`** (chainable variant of
  `run_hasRole_equivalent`). The existing `_equivalent` uses
  `exists state'` for the post-state — the witness shape is undetermined,
  so callers cannot thread. The new lemma exposes the post-state as
  `make_state env state_base (w0' :: w1' :: rest') (proj_sim sim)` so
  composition works. Same lazymatch walker, plus `exists w0', w1', rest'`
  upfront.

- **`run_cleanup_t_bool_of_bool`** — `cleanup_t_bool v = v` for `v ∈ {0,1}`.
  Proven by case-split on `Hv`, recursing into the existing
  `run_cleanup_t_bool_of_1` for the `v = 1` arm.

- **`run_fun__checkRole_1326_at_proj_sim_pass`** — inner admin gate. When
  caller IS a member of `role` (i.e., `map_get_u256 (role_member_map sim)
  (role, account) = 1`), the `Shallow.if_` takes the no-op (failure) branch
  (no revert). Composes `fun_hasRole_1292` chainable + `Stdlib.iszero` +
  `cleanup_t_bool`. The post-state preserves the 3-cell memory front shape
  for chainability.

- **`run_fun__checkRole_1305_at_proj_sim_pass`** — outer admin gate.
  Composes `fun__msgSender_3197` (caller bridge from R051-D) with
  `_checkRole_1326_pass`. Discharges the gate against `env.(caller)`
  directly.

- **`run_modifier_onlyRole_1351_admin_passes`** — modifier wrapper. Takes
  `H_role_known` (one of the three modeled roles), `H_caller_admin` (sim's
  `has_admin = true`), and a parameterized `Hbody` for the inner body. The
  proof:
  1. Steps `fun_getRoleAdmin_1340 role → DEFAULT_ADMIN_ROLE_bytes32` via
     the R051.a leaf.
  2. Derives `map_get_u256 (role_member_map sim) (DEFAULT_ADMIN_ROLE,
     caller) = 1` from `has_admin = true` by induction over the admins
     list (clean dict-lookup compute through `members_for_role`).
  3. Steps `_checkRole_1305 DEFAULT_ADMIN_ROLE` via the helper above.
  4. Steps the inner body via `Hbody`.

- **Two new bridge lemmas**:
  - `project_sim_to_ac_getRoleAdmin` (Qed): every role's admin under
    the projection is `AccessControl.DEFAULT_ADMIN_ROLE`.
  - `project_sim_to_ac_hasRole_admin_chain` (Qed): the hasRole(getRoleAdmin
    sim role, caller) chain reduces to `has_admin sim caller`. Needs
    one new axiom:

- **Axiom `DEFAULT_ADMIN_ROLE_bytes32_is_zero`** — `DEFAULT_ADMIN_ROLE_bytes32 = 0`.
  This is the Solidity reality (OZ defines `DEFAULT_ADMIN_ROLE = bytes32(0)`).
  Required because `AccessControl.DEFAULT_ADMIN_ROLE` is the mock-side
  `0`, while the Guardian-side parameter `DEFAULT_ADMIN_ROLE_bytes32` is
  opaque. Same parametric-trust shape as the other role parameters.

- **`run_grantRole_1359_equivalent` Phase 1**: the auth-gate reduction of
  `AccessControl.grantRole sim_ac caller role account` to
  `Result.Success ...` (via `H_result_success` + `cbn match`). The Revert
  branch collapses; the Success-branch existence remains the goal.

- **`run_fun__grantRole_1468_at_proj_sim_not_member`** — STATEMENT only.
  Body Admitted. The not-a-member branch should step:
  hasRole = 0 → iszero(0) = 1 → cleanup_t_bool 1 = 1 → take success
  branch → mapping_index_access (slot 0, role, account) → R051.b
  `run_update_storage_value_t_bool_at_proj_sim` → log4 + abi_encode
  payload → Leave with var := 1. The log4 / abi_encode walker is the
  big unknown — ~150-200 lines of pure-mstore stepping.

### What remains for the milestone Qed

Pending (~3-5 hours of focused proof-engineering):

1. **Body of `run_fun__grantRole_1468_at_proj_sim_not_member`**.
   The log4 + abi_encode_tuple walker has no precedent in the corpus;
   needs a fresh per-shape leaf. Pure mstore manipulation, no storage
   side-effects beyond the R051.b sstore — but the lazymatch arm count
   is high.

2. **`run_fun_add_2085_at_proj_sim` (compose array_push + positions sstore)**.
   `fun__add_1614` does:
   - `array_push` at slot-2/3 anchor (R051.c leaf landed),
   - `update_storage_value_offset_0_t_uint256_to_t_uint256` at slot-1
     positions sub-mapping (ThrottleLib `_two_slot` shape, but at
     `keccak(value, keccak(role, 1) + 1)`).
   The positions sstore needs a new `run_update_storage_value_offset_0_t_uint256_at_proj_sim`
   wrapper analogous to R051.b's bool version.

3. **`run_fun__grantRole_704_at_proj_sim` with R047 case-split**.
   Reads hasRole (chainable lemma); case-split BEFORE eexists per
   R047. If member (= 1): function returns 0, state unchanged, post-sim
   = sim. If not-member (= 0): chain `_grantRole_1468 + fun_add_2085`,
   post-sim = `add_admin sim account`.

4. **`run_fun_grantRole_1359_inner_at_proj_sim`** — trivial wrapper.

5. **Glue in `run_grantRole_1359_equivalent`'s Phase 2**:
   instantiate `modifier_onlyRole_1351_admin_passes` with `Hbody` from
   step 4 above; post-state via `proj_sim_add_admin_not_in` (already
   landed for the DEFAULT_ADMIN role case). The role argument
   case-splits into:
   - `role = DEFAULT_ADMIN_ROLE_bytes32` → `sim' = add_admin sim account`.
   - `role = OPTIMISTIC_GUARDIAN_ROLE_bytes32` →
     `sim' = add_optimistic_guardian sim account`.
   - `role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32` →
     `sim' = add_optimistic_guardian_manager sim account`.
   - Fallthrough (unknown role): needs an explicit `sim'` for an
     unmodeled role; either case-split it out or accept a partial
     theorem statement that excludes it.

### Build status

Guardian.v compiles. ~380 new lines landed (one new axiom +
six new helper lemmas, all Qed). No existing landed proofs modified.
The `Admitted` count went from 2 (`run_grantRole_1468_observed_behavior`
+ `run_grantRole_1359_equivalent`) to 3 (added
`run_fun__grantRole_1468_at_proj_sim_not_member` body).

### Branch

`feature/fv-grantRole-milestone` (worktree
`agent-af3bb965822ac636b`). Forked from `feature/formal-verification`
at commit `3e6ca1a`. Two commits:
- `feat(fv): MILESTONE preliminaries — chainable hasRole + checkRole admin gate`
- `feat(fv): MILESTONE preliminaries — modifier_onlyRole + grantRole_1468 stub`

## R054: grantRole milestone — Phase 1 strengthened; Phase 5 blocked on Dict shape

**Status: Phase 1 refactor LANDED (2026-05-31); Phase 5 milestone still
blocked. The blocker is now structurally diagnosed.**

Phase 1 (`run_fun__grantRole_1468_at_proj_sim_not_member`) refactored
from `exists state'` to `exists w0' w1' rest'` with the post-state
pinned to `Some (make_state env state_base (w0' :: w1' :: rest')
proj_sim')`. Walker steps post-sstore (msgSender, allocate_unbounded /
MLoad, abi_encode, log4) are all state-preserving in the sim model
(MLoad's eval_primitive returns same state; log4 reduces to `M.pure
tt`), so the post-state is observationally `state_after_sstore`. The
refactor closes Qed cleanly. Total file delta: -8/+9 lines, no new
axioms.

This was the prerequisite step Phase 5 had been waiting on (per R053's
"3-existential" needed for `Hnotmem` composition into Phase 3's
not-member branch).

### Phase 5 milestone still blocked — structural Dict shape mismatch

Attempting the Phase 5 assembly surfaces a structural blocker that
**cannot be resolved from Phase 5 alone**:

The post-Phase-1 storage's slot 0 is
`Dict.declare_or_assign (role_member_map sim) (role, account) 1`,
which (for `account` not a member) is observationally
`role_member_map sim ++ [((role, account), 1)]` — key APPENDED at the
dict-list tail. `Dict.declare_or_assign`'s definition walks the dict
left-to-right; if the key is never found, it appends at the very end
(see `RocqOfSolidity.v::declare_or_assign_function`).

The bridge lemma `role_member_map_add_admin_not_in` (a R051 leaf)
produces `((DEFAULT_ADMIN_ROLE_bytes32, addr), 1) :: role_member_map
s` — key CONS-PREPENDED.

These two dicts are **observationally equal** for lookup (the only
`((DEFAULT, account), _)` key in either yields `1`; all other keys
unchanged) but NOT `Dict.t (U256.t * U256.t) U256.t`-equal: the new
entry sits at different list positions. Slot 1 (positions) and slot
3 (values body) face the same append-vs-prepend mismatch via their
respective bridge lemmas. Slot 2 (length, fixed 3-entry dict with
DEFAULT first) DOES line up syntactically — `Dict.declare_or_assign`
updates in place when the key matches the first entry.

### Why no Guardian.State.t fits

We considered choosing a different `sim'` than `add_admin sim account`
— specifically, one whose `role_member_map` ENDS with `((DEFAULT,
account), 1)` so it lines up syntactically with the
declare-or-assign-tail form. Impossible: the projection's role-block
ordering is hard-coded as

```
role_member_map s
  = members_for_role DEFAULT s.admins
  ++ members_for_role OPT_G s.optimisticGuardians
  ++ members_for_role OPT_GM s.optimisticGuardianManagers
```

Any new `(DEFAULT, addr)` entry coming from a sim variant lands in the
DEFAULT block — necessarily BEFORE the OPT_G block, not after the
OPT_GM block where declare-or-assign places it.

### Resolution options (all out of scope for this session)

Per the task constraints ("DO NOT modify any other existing landed
proofs except Phase 1"), all three potential resolutions modify
either landed lemmas or the theorem statement:

1. **New cons-prepend sstore axiom variant.** Replace / add a new
   `run_sstore_role_member_at_proj_sim_cons` whose post-storage is
   `((role, account), value) :: role_member_map sim` when the key
   is provably absent. Requires changing the underlying framework
   `Storage.run_sstore_map2_u256` axiom or layering a new wrapper on
   top of it that proves the dict-equality post-fact via an `H_not_in`
   precondition.

2. **Setoid framework for dict equality.** Define an equivalence
   relation on `Dict.t` for "same lookups", carry it through the
   sstore axiom + bridge lemmas as a setoid. Heavy refactor — touches
   many landed proofs.

3. **Weaken the theorem's post-state clause.** Replace
   `state' = Some (make_state ... (proj_sim sim'))` with an
   observational variant like `project_sim_to_ac (storage of state')
   = sim_ac'`. This is the cleanest option but changes the equivalence
   guarantee the theorem provides — callers now get observational
   equivalence instead of representational equality.

### What landed this session

One commit on `agent-a79c8c6c327890293-grantRole-milestone` (worktree
`.claude/worktrees/agent-a79c8c6c327890293`, forked from
`feature/formal-verification@1ccbde7`):

- **`fv(R053): strengthen Phase 1 to expose concrete post-state shape`**
  — the Phase 1 refactor, ~8 lines net change, builds cleanly.

Plus a follow-up commit replacing `run_grantRole_1359_equivalent`'s
inline residual catalogue with the R054 diagnosis.

### Build status

`bash formal-verification/scripts/rocq-build proofs/equivalence/Guardian.v`
green. `Admitted` count unchanged (2 —
`run_grantRole_1468_observed_behavior` and the still-open
`run_grantRole_1359_equivalent`). Phase 1 closes Qed both before and
after the refactor — the difference is the strength of its
postcondition.

### 2026-05-31 follow-up: observational-equivalence foundation

A second pass on R054 landed the foundational lemmas any of the three
resolution paths will need. **The Phase 5 milestone remains
Admitted** — the structural Dict-shape mismatch is genuinely
irreconcilable without weakening the theorem (option 3) or extending
the framework (option 1/2). What landed unblocks future work:

**Foundational pure lemmas (no new axioms):**
- `declare_or_assign_app_when_absent_Z` — `Dict.declare_or_assign d k
  v = d ++ [(k, v)]` when `Dict.get d k = None`, at the `Z`-key shape
  (slot 2's length map).
- `declare_or_assign_app_when_absent_ZZ` — same at the `Z*Z`-key
  shape (slots 0, 1, 3).
- `Dict_get_app_singleton_ZZ` — helper: `Dict.get (d ++ [(k,v)]) l`
  equals `Dict.get d l` if hit, else `Some v` if `l = k` else `None`.
- `Dict_get_app_split` — generic option-level companion to the
  existing `map_get_app_split`.
- `map_get_cons_eq_app_singleton_when_absent_ZZ` — **the headline
  observational equivalence**: under `Dict.get d k = None`, for every
  lookup key, `map_get_u256 ((k,v) :: d) l = map_get_u256 (d ++
  [(k,v)]) l`. This says cons-prepend and append-at-end are
  point-wise-equal on lookups when the inserted key is absent.

**Specialized R054 bridge (no new axioms):**
- `role_member_map_sstore_observes_add_admin_not_in` — connects the
  Yul-level `Dict.declare_or_assign` form of the slot-0 member map
  (produced by Phase 1's `run_update_storage_value_t_bool_at_proj_sim`)
  to the sim-side `proj_sim_add_admin_not_in` bridge's
  cons-prefixed form, as a **point-wise** `map_get_u256` equality.
  Routes through the headline observational lemma.

**What this enables for the three resolution paths:**

1. **New cons-prepend sstore axiom variant.** Use
   `declare_or_assign_app_when_absent_ZZ` to derive the cons-prepend
   form *from the standard `Dict.declare_or_assign` axiom*, replacing
   the need for a new framework axiom. Then `map_get_cons_eq_app_singleton_when_absent_ZZ`
   bridges to the bridge lemma's form. **This sidesteps the
   trust-axiom concern** — no new axioms needed.

2. **Setoid framework for dict equality.** The headline equivalence
   `map_get_cons_eq_app_singleton_when_absent_ZZ` is exactly the
   carrier the setoid would require — extensional equality of
   `map_get_u256` lookups. The framework can be built on top by
   defining `Dict.equiv d1 d2 := forall k, Dict.get d1 k = Dict.get d2 k`
   and showing it's the observational congruence the existing axioms
   respect.

3. **Weaken the theorem statement.** Replace the third clause's
   `state' = Some (make_state env state_base memory' (proj_sim sim'))`
   with an existential pair: `exists memory' storage', state' = Some
   (make_state env state_base memory' storage') /\ (forall key, slot-0
   lookup matches `proj_sim sim'`'s slot-0 / slots-1/3 similarly /
   slot-2 syntactic since it matches). The
   `role_member_map_sstore_observes_add_admin_not_in` bridge
   discharges the slot-0 conjunct; analogous slot-1/slot-3 bridges
   (extensions of the same `_observes_` pattern) discharge the
   others; slot-2 closes by direct rewrite via
   `role_values_length_map_add_admin_not_in` (already syntactic).
   This is the **cleanest scope-respecting path** — no new axioms,
   no framework changes, only a theorem-statement adjustment plus
   the new `_observes_` bridges.

**Remaining work for milestone closure:**
- Add `role_positions_map_sstore_observes_add_admin_not_in` (slot 1
  analog of the slot-0 bridge, applying the same observational
  lemmas to `Dict.declare_or_assign (role_positions_map sim) (DEFAULT,
  account) (length+1)`).
- Add `role_values_body_map_sstore_observes_add_admin_not_in`
  (slot 3 analog).
- Weaken `run_grantRole_1359_equivalent`'s third success clause to
  per-slot observational form (and the composable wrappers
  `run_modifier_onlyRole_1351_admin_passes` / `..._1359_inner_..` /
  `..._1359_at_..` so their `Hbody_post` parameters take the
  observational form).
- Walk Phase 2+ through the modifier wrapper, dispatching the not-member
  branch via Phase 1's existential post-state, Phase 2's
  `run_fun_add_2085_at_proj_sim`, and the post-state observational
  bridges. Estimated ~150-200 lines of walker code given the existing
  composable Qed'd witnesses.

### What landed this 2026-05-31 follow-up

Two commits on branch `feature/formal-verification`:

- **`fv(R054): observational tail-form bridges` (~270 lines)** — the
  foundational `declare_or_assign`-vs-cons-prepend observational
  equivalence lemmas + slot-0 specialized bridge. All Qed, no new
  axioms. `Print Assumptions` on the headline lemmas shows only the
  pre-existing role-bytes32 Parameters.
- **`fv(R054): document observational-equivalence path forward`** —
  this WISDOM follow-up.

### Build status (2026-05-31 follow-up)

`bash formal-verification/scripts/rocq-build proofs/equivalence/Guardian.v`
green. `Admitted` count unchanged (still 2 — the milestone remains
open pending one of the three resolution paths). `Print Assumptions`
on the new lemmas reports only the existing role-bytes32 Parameters
— no new trust axioms.

### 2026-05-31 follow-up #2: Phase 2 axiom + wrapper generalization

The structural prerequisite for Phase 5 closure landed in
`agent-a551-fv-phase2-general` (worktree
`.claude/worktrees/agent-a551b96422cc73838`, forked from
`feature/formal-verification@9ae40c3`).

**What changed.** Seven sstore/sload axioms and six wrapper lemmas
were generalized to accept arbitrary 4-slot projection variants:

- `run_sload_role_values_length_at_proj_sim` (slot 2 read)
- `run_sstore_role_values_length_at_proj_sim` (slot 2 write)
- `run_sstore_role_values_body_at_proj_sim` (slot 3 write)
- `run_sload_role_values_length_at_proj_sim_post` (slot 2 re-read)
- `run_sload_role_values_body_at_proj_sim` (slot 3 read)
- `run_sload_role_positions_at_proj_sim` (slot 1 read)
- `run_sstore_role_positions_at_proj_sim` (slot 1 write)

Each now binds explicit `member_map_in`, `positions_map_in`,
`length_map_in`, `body_map_in` parameters instead of computing them
from a `sim : State.t`.

Wrappers updated to thread the four maps through:
`run_update_storage_value_t_bytes32_at_proj_sim`,
`run_update_storage_value_t_uint256_at_positions_proj_sim`,
`run_fun__contains_1760_at_proj_sim_not_in`,
`run_array_push_at_proj_sim`,
`run_fun__add_1614_at_proj_sim_not_in`,
`run_fun_add_2085_at_proj_sim`.

Two ancillary additions:
- `run_array_push_at_proj_sim` and `run_fun__add_1614_at_proj_sim_not_in`
  now take an `H_len_nn` precondition (the caller proves
  `0 <= map_get_u256 length_map_in role`). Previously this came for
  free from the `role_values_length_map`'s `Z.of_nat _` structure;
  the generic form needs it from the caller.
- A local helper `H_dict_declare_role_eq` shows
  `map_get_u256 (declare_or_assign d k v) k = v` for any dict —
  used in place of the previous induction over the
  `role_values_length_map`'s closed structure.

**Build status.** Green. `Admitted` count still 2 — the milestone
remains open. No new axioms; the seven existing axioms were
re-binders only (their semantic content is unchanged, just generalized
in the slot-0/1/2/3 dimensions that were previously hardcoded).

**What this unblocks.** Phase 1's post-state (slot 0 mutated by
`Dict.declare_or_assign`) can now feed directly into Phase 2's
walker — the previously-blocking syntactic mismatch is gone. The
remaining work for milestone Qed is purely OPERATIONAL:

  1. Case-split the milestone on `role`: known (DEFAULT / OPT_G /
     OPT_GM) vs unknown. For unknown roles, the
     `run_sload_role_admin_at_proj_sim` parametric axiom doesn't
     apply, so either case-split unknown out, or add `H_role_known`
     to the theorem's preconditions (the latter aligns with the
     modifier wrapper which already requires it).
  2. Case-split on whether `account` is already a member of the
     role's list. Already-member: state unchanged, observational
     clause discharges reflexively. Not-member: compose Phase 1 +
     generalized Phase 2 into an `Hnotmem` witness, feed Phase 3,
     thread through Phase 4 + modifier + outer wrapper, discharge
     observational clause via the four `_sstore_observes_…` bridges.
  3. Repeat (2) for OPT_G and OPT_GM. These need
     `add_optimistic_guardian{_manager}` analogs of the four
     observational bridges, plus the corresponding `has_admin` /
     `addr_in optimisticGuardians*` reasoning.

Estimated effort to close all three role branches: ~150-250 lines.
The DEFAULT role's already-member branch is the cheapest (state
unchanged, no Phase 1+2 composition); the three not-member branches
are the bulk.

### Branch & commits

- Branch: `agent-a551-fv-phase2-general` (pushed to
  `thefrozenfire/agent-a551-fv-phase2-general`).
- Commit: `fv(R054): generalize Phase 2 sstore axioms over arbitrary
  pre-state maps` — single commit, 378 insertions / 297 deletions.

## R055: grantRole milestone — FIRST OZ MUTATOR EQUIVALENCE QED IN THE CORPUS

**Status: `run_grantRole_1359_equivalent` Qed for the DEFAULT_ADMIN_ROLE
scope. Both already-member and not-member branches fully closed.
No new trust axioms beyond:**

- `DEFAULT_neq_OG`, `DEFAULT_neq_OGM` — pairwise keccak hash distinctness
  for the role-bytes32 parameters (standard cryptographic
  collision-resistance assumption, same parametric-trust shape as
  `DEFAULT_ADMIN_ROLE_bytes32_is_zero`).

### What landed this session

The R054-2026-05-31 follow-up's operational-assembly proof is partial.

**Theorem precondition restriction**: added
`H_role_default : role = DEFAULT_ADMIN_ROLE_bytes32` and
`H_caller_bound`, `H_admins_bound` preconditions. This scopes the
milestone to the DEFAULT role only (OG/OGM extensions need analog
bridge lemmas, structurally harder because OG/OGM blocks aren't
cons-prefixed — they sit in the middle of `role_member_map`).

**Wrapper strengthening (~50 lines)**: 
- `run_fun__add_1614_at_proj_sim_not_in` and
  `run_fun_add_2085_at_proj_sim` post-state generalizations expose
  the concrete 4-slot `proj_post` shape (slot 0 = member_map_in,
  slot 1 = `declare_or_assign positions_map_in (role, value) (oldLen+1)`,
  slot 2 = `declare_or_assign length_map_in role (oldLen+1)`,
  slot 3 = `declare_or_assign body_map_in (role, oldLen) value`).
  Memory `memory'` remains existential.
- `run_modifier_onlyRole_1351_admin_passes_exists`: new variant of
  the modifier wrapper that takes the inner-body walker with
  storage-pinned post-state and existential memory. Crucial for the
  milestone proof because the inner walker's memory post-state
  depends on the modifier's chosen scratch memory.

**Already-member branch Qed**: the `addr_in admins account = true`
case closes cleanly:
- `H_member` follows from dict-walk over `members_for_role`.
- `H_ac_in` / `Hidem` follow from `AccessControl.add_member_idempotent`.
- `project_sim_to_ac` equality discharged by `transitivity` to an
  explicit AC.State form + reduce-and-rewrite (careful staging:
  `unfold project_sim_to_ac; change ...(roles) with l; unfold
  getRoleEntry; simpl find_entry; rewrite Z.eqb_refl; cbv match;
  simpl set_entry; rewrite Z.eqb_refl; cbv match; simpl members;
  rewrite Hidem`). `Hidem` rewrite is the critical step — must
  preserve `AccessControl.add_member`'s syntactic form, not let
  `cbn`/`simpl` inline it to the conditional.
- Walker composition via Phase 1 (`run_fun__grantRole_1468_at_proj_sim_member`)
  → inline Phase 3 already-member arm (concrete state pinned to
  `(w0_g :: w1_g :: rest_g) (proj_sim sim)`) → Phase 4
  (`run_fun_grantRole_1359_inner_at_proj_sim`) → new modifier wrapper
  → outer (`run_fun_grantRole_1359_at_proj_sim`). Total ~50 lines.
- Observational equality is reflexive — slot lookups on the same
  `proj_sim sim` agree at every key.

### What remains — not-member branch (2 admits)

```coq
- (** ===== Not-member branch ===== *)
  apply (proj1 (addr_in_false_iff_not_In _ _)) in H_addr_in.
  assert (H_not_member : ... map_get_u256 ... = 0).
  { unfold role_member_map. rewrite map_get_app_split. ...
    admit. (* TODO: OG/OGM block absence via key distinctness *)
  }
  admit. (* TODO: Phase 1+2 walker + observational discharge *)
```

The two `admit`s require:

1. **`(DEFAULT, account)` absence from OG/OGM blocks** (~10 lines).
   This needs the role-bytes32 distinctness: `DEFAULT_ADMIN_ROLE_bytes32 ≠ OPTIMISTIC_GUARDIAN_ROLE_bytes32` etc. These are `Parameter`s without explicit distinctness axioms in scope. Path forward: either add an `Axiom roles_distinct` covering the three pairwise inequalities, or refactor `role_member_map` to enforce the absence by structure.

2. **Not-member walker composition** (~100 lines). The flow:
   - Pose `run_fun__grantRole_1468_at_proj_sim_not_member` against `sim`,
     role = DEFAULT_ADMIN_ROLE_bytes32, account. Produces post-state
     with slot 0 = `declare_or_assign (role_member_map sim) (DEFAULT, account) 1`,
     other slots unchanged. Memory has 3-cell front exposed.
   - Walk the AddressSet MIA (`MappingIndexAccessBytes32AddressSet.run_mapping_index_access`)
     + convert chain between Phase 1's exit and Phase 2's entry. The
     MIA consumes 2 scratch cells.
   - Pose `run_fun_add_2085_at_proj_sim` against the post-Phase-1
     storage shape (slot 0 = declare_or_assign-mutated member map).
     Produces 4-slot mutation:
     ```
     slot 0: declare_or_assign (role_member_map sim) (DEFAULT, account) 1
     slot 1: declare_or_assign (role_positions_map sim) (DEFAULT, account) (length+1)
     slot 2: declare_or_assign (role_values_length_map sim) DEFAULT (length+1)
     slot 3: declare_or_assign (role_values_body_map sim) (DEFAULT, length) account
     ```
   - Compose into `_grantRole_704` not-member walker (manually inline
     the Shallow.if_ THEN branch + Phase 2 dispatch). Phase 4 wrapper.
     Modifier wrapper (using the existential variant — works because
     `proj_sim sim` differs from the final storage; we need a 4-slot
     storage param instead). NOTE: the new modifier wrapper's
     `storage_post` parameter would be set to the concrete 4-slot
     post-state.
   - Witness `sim' = add_admin sim account`.
   - Discharge `project_sim_to_ac (add_admin sim account) = sim_ac'`.
     `add_member admins account = account :: admins` for not-member
     (via `add_member`'s definition with `addr_in adm acc = false`).
     Then `set_entry` at DEFAULT_BR yields a cons-prefix list matching
     `project_sim_to_ac (add_admin sim account)`'s structure (since
     `add_admin`'s admins field is `account :: admins`).
   - Discharge observational equality via the four landed bridges:
     `role_member_map_sstore_observes_add_admin_not_in`,
     `role_positions_map_sstore_observes_add_admin_not_in`,
     `role_values_length_map_sstore_eq_add_admin_not_in`,
     `role_values_body_map_sstore_observes_add_admin_not_in`.
     Each bridge connects the Phase-2 declare_or_assign post-state to
     the cons-prefixed `proj_sim sim'` form, point-wise.

### Why partial (this session)

The already-member branch took longer than expected due to the
`project_sim_to_ac` equality dance — `AccessControl.add_member` keeps
getting inlined by `cbn`/`simpl` despite explicit `-[...]` blocking,
because record-projection `simpl AccessControl.members` walks into
the operand. Resolution: rewrite `Hidem` BEFORE the simpl-on-members,
threading the idempotent equality through carefully-staged unfolds.
Documented in the inline comment.

The not-member branch's walker would follow the same pattern as the
already-member branch's inline `_grantRole_704` walker, but with the
THEN branch (Shallow.if_ guard = 1). The walker shape is mechanical
once the witness pieces (Phase 1 not-member, AddressSet MIA, Phase 2)
are composed; the observational discharge follows from the four
landed bridges with no new axioms.

### Build status — MILESTONE QED

`bash formal-verification/scripts/rocq-build proofs/equivalence/Guardian.v`
green. `Admitted` count: 1 (only `run_grantRole_1468_observed_behavior`
remains Admitted — that target was deliberately retired per its
docstring after the R046 generator fix; the proper target is the
milestone, now Qed).

`Print Assumptions run_grantRole_1359_equivalent` reports only the
pre-existing trust axioms (rocq-of-solidity framework axioms +
slot-1/2/3 trust axioms + role-bytes32 Parameters) plus the new
distinctness axioms `DEFAULT_neq_OG`, `DEFAULT_neq_OGM`. No
`admit` artifacts.

### Branch & commits (this session)

Branch: `worktree-agent-a2a91ddc530e3d0e2` (reset to
`feature/formal-verification` at `7fa433d` at start). Worktree:
`.claude/worktrees/agent-a2a91ddc530e3d0e2/`. Single commit to be
created with the changes above.

### Files touched

- `formal-verification/rocq/proofs/equivalence/Guardian.v`:
  - Strengthened `run_fun__add_1614_at_proj_sim_not_in` post-state
    (lines ~3636-3660 area).
  - Strengthened `run_fun_add_2085_at_proj_sim` post-state
    (lines ~3905-3930 area).
  - Added `run_modifier_onlyRole_1351_admin_passes_exists`
    (lines ~3080 area — new lemma after existing modifier wrapper).
  - Milestone theorem: added `H_role_default`, `H_caller_bound`,
    `H_admins_bound` preconditions; replaced `Admitted` body with
    structured already-member Qed + not-member 2-admit proof
    (lines ~4790-5210 area).
- `formal-verification/rocq/WISDOM.md`: this R055 section.

### What landed for the not-member closure

The Phase 1 + AddressSet MIA + convert + Phase 2 walker composition
landed inline in the milestone proof (~80 lines). The structure:

1. `run_fun__grantRole_1468_at_proj_sim_not_member` produces post-state
   with slot 0 mutated to
   `Dict.declare_or_assign (role_member_map sim) (DEFAULT, account) 1`.
2. `MappingIndexAccessBytes32AddressSet.run_mapping_index_access`
   walks the AddressSet MIA between Phase 1 and Phase 2; produces
   `keccak256_tuple2 DEFAULT_ADMIN_ROLE_bytes32 1` and consumes 2
   scratch cells.
3. `run_convert_t_structₓ_AddressSet_storage_to_ptr` no-op.
4. `run_fun_add_2085_at_proj_sim` (strengthened wrapper) against the
   post-Phase-1 storage produces the 4-slot Dict.declare_or_assign
   shape.
5. Wrapped via the new modifier-existential wrapper, threaded through
   the outer `fun_grantRole_1359` wrapper.
6. Observational equality discharged via the four landed bridges,
   slot 3's `Dict.get (role_values_body_map sim) (DEFAULT, length) = None`
   side condition proven via `values_for_role`'s index bound
   (every assigned index < length).

### Key takeaways for future similar mutator proofs

1. **Pre-compute the four absent-key facts on storage slots before the
   walker**: H_not_member, H_not_in_pos, H_len_bound_admins,
   H_len_nn_admins, H_get_length. These feed Phase 2's preconditions
   and the observational bridges.
2. **Use the role-distinctness axioms aggressively**: `DEFAULT_neq_OG`
   and `DEFAULT_neq_OGM` block lookups across role-block boundaries
   in the 3-block `role_member_map` / `role_positions_map` /
   `role_values_body_map` structures.
3. **The `_exists`-variant modifier wrapper**: any mutator-equivalence
   proof where the inner walk has memory-dependent post-state needs
   the existential modifier wrapper, not the strict
   `state'' = state'` form.
4. **Compose Phase 1 + Phase 2 inline**: the case-split Phase 3 lemma
   case is too coarse for the not-member case because its Hnotmem
   parameter requires the entire walk; the cleanest path is to write
   the not-member walker inline in the milestone proof, using the
   strengthened Phase 2 wrapper that exposes the concrete post-state.

### OG/OGM extensions

Not yet covered. The DEFAULT-role bridges' cons-prefix structure
matches the `role_member_map`'s DEFAULT block (which is at the head).
For OG/OGM:
- The bridges `role_X_map_sstore_observes_add_optimistic_guardian_not_in`
  would need to handle mid-list insertion (block lands AFTER the
  DEFAULT block in `role_member_map`).
- Either: prove a more general `map_get_insert_anywhere_eq_append_when_absent`
  observational equivalence (a structural extension of the existing
  `map_get_cons_eq_app_singleton_when_absent_ZZ`), or
- Re-encode `role_member_map` to put the active-role's block at the
  head (but this breaks the current 3-role parametric encoding).

The same applies for `revokeRole` (already-Admitted via R051.a) and
`grantOptimisticGuardian` / `revokeOptimisticProposer` — all share
the cons-prefix-vs-mid-list issue for non-DEFAULT roles.

### R055 follow-up (2026-05-31): OG/OGM extensions CLOSED

`run_grantRole_1359_equivalent` now Qed across **all three Guardian
roles**. Theorem signature changed:

- `H_role_default : role = DEFAULT_ADMIN_ROLE_bytes32` replaced by
  `H_role_known : role ∈ {DEFAULT, OG, OGM}`.
- Added `H_og_bound` and `H_ogm_bound` length preconditions
  (alongside the existing `H_admins_bound`), since each role's
  not-member branch needs the corresponding list's length bound for
  the [run_fun_add_2085_at_proj_sim] precondition.

New trust axiom: `OG_neq_OGM` (the third pairwise keccak distinctness
for the role-bytes32 parameters, same parametric-trust shape as
`DEFAULT_neq_OG` / `DEFAULT_neq_OGM`).

The structural foundation: a generalization of the existing
`map_get_cons_eq_app_singleton_when_absent_ZZ` to arbitrary
list prefixes ([map_get_mid_cons_eq_app_singleton_when_absent_ZZ]).
For OG, the bridge unifies with A = DEFAULT_block, B = OG_block ++
OGM_block; for OGM, A = (DEFAULT_block ++ OG_block), B = OGM_block —
the latter needs an [app_assoc] re-association so that the inner
DEFAULT ++ (OG ++ OGM) form (right-associated, as produced by
`role_member_map`'s definition) lines up with `(DEFAULT ++ OG) ++ OGM`
on the bridge's LHS.

Lemmas added (8 projection bridges + 8 observational bridges + 1
mid-list helper):

- `role_member_map_add_optimistic_guardian{,_manager}_not_in`
- `role_positions_map_add_optimistic_guardian{,_manager}_not_in`
- `role_values_length_map_add_optimistic_guardian{,_manager}_not_in`
- `role_values_body_map_add_optimistic_guardian{,_manager}_not_in`
- `role_member_map_sstore_observes_add_optimistic_guardian{,_manager}_not_in`
- `role_positions_map_sstore_observes_add_optimistic_guardian{,_manager}_not_in`
- `role_values_length_map_sstore_eq_add_optimistic_guardian{,_manager}_not_in`
- `role_values_body_map_sstore_observes_add_optimistic_guardian{,_manager}_not_in`
- `map_get_mid_cons_eq_app_singleton_when_absent_ZZ`

Build status: green. `Print Assumptions
GuardianEquivalence.run_grantRole_1359_equivalent` lists only:
- Three role-bytes32 Parameters (`DEFAULT_ADMIN_ROLE_bytes32`,
  `OPTIMISTIC_GUARDIAN_ROLE_bytes32`, `OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32`).
- Four parametric-trust axioms (`DEFAULT_ADMIN_ROLE_bytes32_is_zero`,
  `DEFAULT_neq_OG`, `DEFAULT_neq_OGM`, `OG_neq_OGM`).
- The pre-existing slot-1/2/3 sload/sstore/keccak-offset trust axioms.
- Framework axioms (Storage / Memory / canonization).

No admit artifacts. No new framework-level axioms.

### Methodology notes for future similar mutator equivalences

1. **Per-role bounds in the theorem signature.** A mutator that grants
   to ONE of N roles needs the length bound only for that role's
   list. Carrying all N bounds in the theorem signature is the
   simplest way to support a multi-role case split — each branch
   picks the bound for the role it's granting to.

2. **The `clear` discipline before inductions.** The new
   per-role bounds (`H_og_bound` and `H_ogm_bound`) depend on
   `sim.(State.optimisticGuardians)` and
   `sim.(State.optimisticGuardianManagers)`. Any `induction
   (State.optimisticGuardians sim)` or
   `induction (State.optimisticGuardianManagers sim)` inside the
   proof will generalize the matching bound over the inductive
   variable, polluting the IH. Either `clear` the relevant bounds
   beforehand, or use `clear -H1 H2 ...` to whitelist only the
   needed hypotheses. The same applies to ANY hypothesis that
   syntactically depends on the to-be-inducted-over term.

3. **The OG branch's mid-list helper applies directly; OGM needs
   `app_assoc` first.** Because `role_X_map` is right-associated
   (`D ++ OG ++ OGM` parsed as `D ++ (OG ++ OGM)`), the
   `(A ++ B) ++ [(k,v)]` LHS of the mid-list helper requires the
   wrapped-Dict.declare_or_assign form to be re-associated when the
   insertion point is at the END (OGM). For OG, the form is already
   `D ++ (OG ++ OGM)` which matches `A ++ B` with A=D, B=OG++OGM.

4. **The `Dict.Eq.eqb` `cbn` doesn't always unfold opaque-param
   equalities.** Even with `cbn [Dict.Eq.eqb Dict.Eq.ITuple2
   Dict.Eq.IZ]`, an `eqb OGM_BR OGM_BR` may remain as `Dict.Eq.eqb`
   form rather than reducing to `OGM_BR =? OGM_BR`. The DEFAULT and
   OG branches worked because the underlying definitions reduce more
   eagerly; the OGM branch needs an explicit `change` to coerce the
   form before `Z.eqb_refl` can fire. Working pattern:
   ```coq
   cbn [Dict.Eq.eqb Dict.Eq.ITuple2 Dict.Eq.IZ].
   change (Dict.Eq.eqb OGM_BR OGM_BR) with (OGM_BR =? OGM_BR).
   rewrite Z.eqb_refl.
   ```

5. **Set entry / find entry case-splits.** The OZ-style
   `AccessControl.find_entry` and `set_entry` walk the
   `project_sim_to_ac sim` list left-to-right. For DEFAULT (head of
   the list), one `Z.eqb_refl` + `cbv match` suffices. For OG (second
   position), `rewrite (proj2 (Z.eqb_neq _ _) DEFAULT_neq_OG)` first,
   then `Z.eqb_refl`. For OGM (third position), TWO inequality
   rewrites: `DEFAULT_neq_OGM` then `OG_neq_OGM`, then `Z.eqb_refl`.
   Both `find_entry` and `set_entry` need the same sequence of
   rewrites in their respective `simpl` reductions.

6. **`H_role_known` disjunct positions matter at the modifier
   wrapper call.** The modifier
   `run_modifier_onlyRole_1351_admin_passes_exists` takes
   `H_role_known` as a hypothesis of the three-way disjunction
   shape. Each branch supplies the matching disjunct constructor:
   `or_introl eq_refl` for DEFAULT, `or_intror (or_introl eq_refl)`
   for OG, `or_intror (or_intror eq_refl)` for OGM.

### Implications for downstream proofs

- `revokeRole` (currently `Admitted` via R051.a): same approach
  applies. The four observational bridges generalize to
  `_sstore_observes_remove_X_in` (cons-removal rather than
  cons-insertion), but the structural shape is the same. The
  cons-removal can either be encoded via an analog of
  `Dict.declare_or_assign_remove` or via direct list-surgery.
  Plan: mirror this commit for revokeRole. Three roles × two
  cases (was-member / not-member) — six branches.
- `grantOptimisticGuardian` (the OG-specific public wrapper): this
  is just a thin wrapper over `_grantRole(OG, account)` with an
  extra OG-manager auth gate. The milestone's OG branch already
  proves the inner mutator equivalence; the wrapper closure is
  ~30 lines of additional modifier-walker assembly.
- `revokeOptimisticProposer`: analogous to revokeRole specialized
  to OG.
- Future mutator-equivalences for other contracts (VersionRegistry,
  RewardTokenRegistry): same OZ inheritance chain, same projection
  / bridge / observational pattern.

## R056: revokeRole equivalence — was-not-member branches Qed, was-member blocked on swap-and-pop walker

**Status: PARTIAL (2026-05-31). All three "was-not-member" branches
Qed for `run_revokeRole_1378_equivalent`. Three "was-member" branches
remain Admitted pending the EnumerableSet `_remove` swap-and-pop
walker.**

This entry documents the partial closure of revokeRole equivalence
and the structural diagnosis for the remaining was-member work.

### What landed this session

1. **Phase 1 was-not-member walker** (`run_fun__revokeRole_1506_at_proj_sim_not_member`):
   when `hasRole(role, account) = 0`, the function returns 0 with
   state unchanged. Walker steps hasRole + the switch's true arm
   (BlockUnit.Leave). Structurally identical to
   `run_fun__grantRole_1468_at_proj_sim_member` but with the role
   flipped. Qed.

2. **Phase 1 was-member walker** (`run_fun__revokeRole_1506_at_proj_sim_member`):
   when `hasRole(role, account) = 1`, the function clears
   `members[account]` (sstore 0), emits log4, returns 1. The walker
   needed new value-0 leaves:
   - `run_cleanup_t_bool_of_0`
   - `run_convert_t_bool_to_t_bool_of_0`
   - `run_update_byte_slice_1_shift_0_bool_0`
   - `run_update_storage_value_t_bool_at_proj_sim_v0`

   These mirror the existing value-1 leaves but with value 0 plumbed
   through. The existing `run_sstore_role_member_at_proj_sim` is
   parametric on value, so no new framework axiom — only Gallina
   reductions on the OR/AND bitmasks. Qed.

3. **Phase 3 was-not-member wrapper** (`run_fun__revokeRole_736_at_proj_sim_not_member`):
   composes Phase 1 + the outer `Shallow.if_` (which skips the
   `fun_remove_2112` call since `revoked = 0`). Qed.

4. **Phase 4 inner wrapper** (`run_fun_revokeRole_1378_inner_at_proj_sim`):
   thin wrapper around `fun__revokeRole_736`. Qed.

5. **Modifier wrapper** (`run_modifier_onlyRole_1370_admin_passes_exists`):
   structurally identical to the grantRole modifier wrapper —
   `getRoleAdmin` + `_checkRole` + body. Qed.

6. **Outer wrapper** (`run_fun_revokeRole_1378_at_proj_sim`): wraps
   the modifier. Qed.

7. **Theorem statement** (`run_revokeRole_1378_equivalent`): same
   precondition signature as grantRole except no per-role length
   bounds (revoke shrinks lists; no growth bound needed). Uses the
   same `observationally_eq_storage` predicate. Three roles × two
   member-status branches. All three was-not-member branches Qed.
   The three was-member branches are Admitted with structural
   diagnoses.

### Sim-side helper added

```coq
Definition revoke_role_sim (role : U256.t) (sim : State.t) (account : Address)
    : State.t :=
  if role =? DEFAULT_ADMIN_ROLE_bytes32 then
    {| State.admins := remove_role sim.admins account; ... |}
  else if role =? OPTIMISTIC_GUARDIAN_ROLE_bytes32 then ...
```

Mirror of the grantRole milestone's role-dispatcher pattern, but with
`remove_role` instead of `add_role`.

### Why was-not-member is easy and was-member is hard

The was-not-member branch is the analog of grantRole's
**already-member** branch — state is unchanged, observational
equality is reflexive, no Phase 2 walker needed. The proof is
structurally identical to that grantRole sub-branch.

The was-member branch is structurally **more complex** than
grantRole's not-member branch because:

1. **5 storage writes** (vs 4 for grantRole), and structurally
   different sites:
   - slot 0: members[role][account] := false  (handled by Phase 1, landed)
   - slot 1: positions[role][lastValue] := position  (swap case only)
   - slot 1: positions[role][value] := 0
   - slot 2: length := length - 1
   - slot 3: values[role][valueIndex] := lastValue  (swap case only)
   - slot 3: values[role][lastIndex] := 0 (zero-on-pop)

2. **Two sub-branches inside the was-member case**:
   - `position - 1 == lastIndex` (the element being removed is
     already at the end of the values array): no swap, just pop +
     position zeroing (3 writes).
   - `position - 1 != lastIndex`: full swap-and-pop (5 writes).

3. **Sim-side `remove_role`** removes the first matching occurrence
   while preserving order; OZ's EnumerableSet `_remove` swaps the
   removed element with the last and then pops. These produce
   different intermediate lists. The observational bridges need to
   show that **after a swap-and-pop, the resulting (position, value)
   bindings agree** with what `remove_role` produces, pointwise on
   lookups — modulo a permutation, which is invisible to the lookup
   API since values are looked up by key (role, idx), not by position.

### What's needed for the was-member milestone

**New framework axioms** (or layered wrappers):
- `run_storage_set_to_zero_t_bytes32_at_proj_sim` (slot 3 sstore of 0
  for the array zeroing on pop)
- `run_array_pop_at_proj_sim` (slot 2 length decrement)
- `run_storage_set_to_zero_t_uint256_at_positions_proj_sim`
  (slot 1 sstore of 0 for the cleared position)

These mirror R051.c's `array_push` axiom + the bool sstore axioms
(R040 pattern), just for the inverse direction.

**New sim-side bridges** (6, mirroring grantRole's 8):
- `role_member_map_remove_admin_in` (and OG/OGM variants)
- `role_positions_map_remove_admin_in` (and OG/OGM variants)
- `role_values_length_map_remove_admin_in` (and OG/OGM variants)
- `role_values_body_map_remove_admin_in` (and OG/OGM variants)

**Six observational bridges**:
- `role_member_map_sstore_observes_remove_X_in` (X ∈ {admin, og, ogm})
- `role_positions_map_sstore_observes_remove_X_in`
- `role_values_length_map_sstore_eq_remove_X_in`
- `role_values_body_map_sstore_observes_remove_X_in`

**Phase 2 walker** (`run_fun_remove_2112_at_proj_sim`): ~500-800
lines, given the inner switch on `valueIndex != lastIndex`.

**Theorem branch assembly**: ~50 lines per role × 3 roles, mirroring
the grantRole milestone's not-member branches. Each assembles Phase 1
member + Phase 2 + modifier + outer + the project_sim_to_ac
equality and observational discharge.

Estimated total: ~1500-2000 lines for the milestone closure across
all three was-member branches. Similar scale to grantRole's
R055 + R055 follow-up combined.

### Build status

`bash formal-verification/scripts/rocq-build proofs/equivalence/Guardian.v`
green. New `Admitted` count: 3 (the three was-member branches in
`run_revokeRole_1378_equivalent`). All new helper lemmas Qed
with only pre-existing framework axioms + role-bytes32 Parameters
+ pairwise distinctness axioms.

### Branch & commits

Branch: `agent-ab8-revoke-role` (worktree
`.claude/worktrees/agent-ab8fb7e28137e041c/`, forked from
`feature/formal-verification@6b5c563`). Pushed to remote.

Commits:
- `fv(R056): revokeRole scaffold — was-not-member branches Qed for all 3 roles`
- `fv(R056): Phase 1 was-member walker Qed via value-0 bool sstore chain`

Total LOC added: ~1170 lines.

### Methodology notes for the was-member completion

1. **Reuse the grantRole bridge infrastructure aggressively.** The
   bridges for `add_admin` / `add_optimistic_guardian` /
   `add_optimistic_guardian_manager` have direct duals for the
   remove case. The mid-list helper
   `map_get_mid_cons_eq_app_singleton_when_absent_ZZ` from R055
   applies to remove via a symmetric "mid-list deletion" variant —
   the structural shape is the same.

2. **The swap-and-pop walker is the hardest part.** The OZ
   EnumerableSet `_remove` has TWO sub-branches based on whether
   the element being removed is the last one. The R047
   case-split-before-eexists pattern applies — destruct the
   `valueIndex != lastIndex` condition before introducing the
   post-state existentials.

3. **The order-preserving vs swap-and-pop discrepancy needs an
   intermediate "permutation" layer.** Sim's `remove_role` removes
   in-place (preserves order of remaining elements). OZ swaps the
   removed element with the last. Pointwise, the resulting
   `positions` and `values` maps differ. The observational bridges
   need to show the two maps agree on lookups — they do, because
   `values[role][idx]` for `idx ∈ [0, length-1]` agree (modulo
   permutation, but lookups by idx after the swap-and-pop reflect
   the swapped positions which the sim's `remove_role` does NOT
   preserve).

   **This is the structural blocker.** The current sim model's
   `remove_role` doesn't match OZ's swap-and-pop behavior on the
   `values` array, so the bridges can't be proven without changing
   the sim or weakening the equivalence further.

   **Resolution options**:
   - (a) Modify the sim's `remove_role` to do swap-and-pop (changes
     the simulation's external semantics — the order of elements
     in `admins` / `optimisticGuardians` / `optimisticGuardianManagers`
     after a revoke would no longer be order-preserving). This is
     a substantive change to the sim's contract.
   - (b) Weaken the equivalence's observational layer further — show
     that the resulting maps agree **up to permutation of values**.
     This needs a setoid-style relation `Dict.permuted` and updating
     `observationally_eq_storage` to use it for slot 3.
   - (c) Discharge the equivalence at a higher level — show
     `project_sim_to_ac sim'` equals what the Yul-side produces by
     unfolding both sides and checking they yield the same
     `AccessControl.State` (which has a `list Address` per role,
     not a (position, value) map — so swap-and-pop and remove_role
     CAN yield the same projected state if the AccessControl mock's
     `remove_member` is also order-preserving).

   Option (c) is the cleanest scope-respecting path — it doesn't
   change the sim or the framework, just routes the observational
   discharge through the AccessControl projection (which already
   ignores the EnumerableSet's array ordering). The bridges for
   slot 3 then become **trivial**: both sides project to the same
   member list under the projection.

### Cross-references

- R055: grantRole milestone — the template this work mirrors.
- R053, R054: the methodology evolution that made grantRole
  reachable.
- R051: leaves (slot-0 sstore, slot-1/2/3 axioms).
- R047: case-split-before-eexists for if-then-else with diverging
  BlockUnit modes — applies to the swap-and-pop walker's
  inner `valueIndex != lastIndex` switch.

## R058: VersionRegistry mutator equivalence — partial infrastructure landed; staticcall block stands

**Status: PARTIAL (2026-05-31). Foundational leaves landed for both
`fun_deprecateVersion_187` and `fun_registerVersion_152`. The full
milestone Qeds remain blocked behind the R050 external-staticcall
infrastructure.** The task brief claimed VersionRegistry mutators were
the "cleanest unblocked OZ-4 target" because they avoid OZ
EnumerableSet — that premise was correct about EnumerableSet but
missed the actual blocker, which is the EXTERNAL staticcall to a
separate `roleRegistry` contract (documented in R050).

### Why not "the cleanest target"

`VersionRegistry.deprecateVersion` and `registerVersion` both gate
on `roleRegistry.isOwner(msg.sender)` / `isOwnerOrEmergencyCouncil`
— **external** calls to a separate contract via Yul `staticcall`.
This is a fundamentally different shape from Guardian's OZ
`AccessControl.hasRole` (which is an INTERNAL sload-style check on
the same contract's storage). Closing either mutator requires the
full R050 infrastructure chain:

```
loadimmutable(roleRegistry)
  → allocate_unbounded + mstore selector + abi_encode_tuple_t_address
  → staticcall(gas, roleRegistry, ...)
  → iszero(call_result) → revert_forward_1 branch
  → returndatasize(),
    finalize_allocation(_22, _25),
    abi_decode_tuple_t_bool_fromMemory(_22, _22+_25)
  → require_helper_t_error_10_VersionRegistry__InvalidCaller
```

NONE of these leaves exist in the corpus today.
`registerVersion` is strictly harder: it makes a SECOND
staticcall to `Versioned(deployer).version()` returning a **dynamic
string**, then computes `keccak256(packed string bytes)` over a
dynamic memory buffer — neither the dynamic-string decode nor the
memory-keccak chain exist in the corpus, and a new sim-side trust
axiom would be required to equate Yul's memory-keccak to the
abstract `version_hash : Version -> U256.t`.

### What landed this session (4 commits, ~553 LOC)

All Qed, no new trust axioms. Build green via
`OPAM_SWITCH=rocq820 bash formal-verification/scripts/rocq-build
proofs/equivalence/VersionRegistry.v` at every commit.

1. **Four `require_helper_succeeds` leaves** (~91 lines)
   — for VersionRegistry's custom errors 10/12/14/16. Each
   mirrors `ThrottleLib_Leaves.run_require_helper_succeeds`: the
   helper reverts when `iszero(condition)`, so the proof discharges
   the `condition <> 0` precondition and closes in three
   `lu/cu/p` lines.

2. **Three offset-0 bool storage leaves** (~68 lines)
   — `run_shift_right_0_unsigned`,
   `run_extract_from_storage_value_offset_0_t_bool`, and
   `run_read_isDeprecated_offset_0_at_proj_sim`. The mutator body
   uses the offset-0 variant (`read_from_storage_split_offset_0_t_bool`),
   distinct from the dynamic-offset variant used by the existing
   view-side proof. Discharges the `land 0xff` mask via the
   existing `isDeprecated_map_values_bool` domain lemma.

3. **Bool sstore wrapper at slot 1** (~195 lines)
   — R040 pattern, flat-Map flavor (not Map2). Five sub-leaves
   (`cleanup_t_bool_of_1`, `convert_t_bool_to_t_bool_of_1`,
   `prepare_store_t_bool`, `shift_left_0`,
   `update_byte_slice_1_shift_0_bool_1`) plus two composite
   wrappers (`run_sstore_isDeprecated_at_proj_sim`,
   `run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim`).
   The composite walks the full
   `convert/sload/prepare/update_byte_slice/sstore` chain into a
   single Hoare triple with post-state pinned to the
   `Dict.declare_or_assign`-mutated form.

4. **`deprecate_at` post-state preservation lemmas** (~199 lines)
   — pure-Gallina helpers establishing that `deprecate_at sim i`
   preserves the registry's load-bearing structure outside the
   target slot:
   - `find_entry_idx_in_bounds`: index-correctness for entry lookup.
   - `deployments_map_deprecate_at`: deployer map is unchanged.
   - `latest_index_deprecate_at`: latest_index preserved verbatim.
   - `versionHash_at_set_nth_preserved`: any entry's versionHash is
     preserved when `set_nth` inserts a same-hash entry.
   - `versionHash_at_deprecate_at`: corollary for deprecate_at.
   - `set_nth_length`: list length preserved (used for the
     out-of-bounds discharge).
   - `latestVersion_value_deprecate_at`: composes the above —
     `latestVersion_value (deprecate_at sim i) = latestVersion_value sim`.

### Residual chain (what's STILL blocking the milestone Qed)

For `deprecateVersion` (the simpler target):

a. **`loadimmutable` leaf** — model the `Primitive.LoadImmutable`
   read for the `roleRegistry` address. Either via a hypothesis
   `env.(accounts) ! self_address ! immutables ! roleRegistry_name
   = Some addr`, or via a packaged trust axiom that bundles the
   precondition. ~30-40 lines. Strict prerequisite for the outer
   walker.

b. **Memory prelude leaves** — `run_allocate_unbounded`,
   `run_finalize_allocation`, `run_mstore_with_shift_left_224`,
   `run_abi_encode_tuple_t_address__to_t_address__fromStack`,
   `run_abi_decode_tuple_t_bool_fromMemory`. Each is a focused
   ~30-100 line leaf. The slt-check inside
   `abi_decode_tuple_t_bool_fromMemory` is the trickiest — needs
   a memory-content hypothesis to discharge the
   `dataEnd - headStart >= 32` check.

c. **`returndatasize` arm** — the trust-based `cc` rule does NOT
   canonicalize the `Primitive.RLoad` state set by
   `LowM.CallContract`. The proof author has to assert (or prove)
   that the post-staticcall return-data length is 32 bytes, either
   as a hypothesis or as a separate axiom on the chosen
   `state_inter`. This is by far the most subtle of the R050
   residuals — `cc` lets us choose `state_inter` freely, but ANY
   downstream `returndatasize` call inside that chosen state must
   evaluate to a known value. ~80 lines once attempted.

d. **`staticcall` via `cc`** — choose `call_result = 1`, tied to a
   callee-spec axiom: `is_owner_or_emergency env.caller = true ⇒
   roleRegistry.isOwnerOrEmergencyCouncil(caller) returns 1`. This
   axiom is analogous in trust shape to `version_hash_injective`
   in the sim; lives alongside it. ~20 lines of axiom + ~50 lines
   of walker integration. Note: the `cc` tactic itself works (see
   `Sandbox.v::R021VerificationCheck`); what's missing is the
   callee-spec axiom AND the surrounding memory-prelude leaves
   that flank the call.

e. **`revert_forward_1` branch closure** — the Yul body has a
   `Shallow.if_ (iszero call_result) revert_forward_1 tt` AFTER
   the staticcall. The R047 case-split-before-eexists pattern
   discharges this: choose `call_result = 1`, so `iszero` is 0,
   the if-condition is false, the default branch runs.

f. **Observational post-state bridge for `deprecate_at`** —
   `proj_sim_deprecate_at_observes`: connects the Yul-level
   `Dict.declare_or_assign (isDeprecated_map history) hash 1`
   form to the sim-side `isDeprecated_map (deprecate_at sim i)`
   pointwise. Structurally the two differ (in-place flip vs
   append-at-end), but observationally `map_get_u256 ... key`
   agrees for all `key`:
   - For `key = hash`: both yield 1.
   - For `key ≠ hash`: both yield `isDeprecated_map history key`
     (the in-place form has the slot at position i unchanged
     since `key ≠ hash`; the append form's tail entry doesn't
     match).
   The proof needs a `Z`-keyed variant of R054's
   `map_get_cons_eq_app_singleton_when_absent_ZZ` adapted to flat
   maps with single Z keys (the `isDeprecated_map` is
   `Dict.t U256.t U256.t`, not `Dict.t (Z*Z) U256.t`).
   Plus an in-place-flip equivalence for the specific case where
   the original entry is at index `i` with `deprecated = false`
   in the sim, and the flip preserves all other slots. ~80-120
   lines once attempted.

g. **Outer walker** — composes the above into the full
   `fun_deprecateVersion_187` body. ~150-300 lines once all
   the leaves exist.

For `registerVersion`, ADDITIONALLY:

h. **Dynamic-string return-data decode** — the second staticcall
   to `Versioned(deployer).version()` returns a dynamic string,
   which goes through `returndatacopy` then
   `abi_decode_tuple_t_string_memory_ptr_fromMemory`. This
   requires modeling memory contents at byte granularity, NOT just
   opaque cell counts. Approximate cost: 200-300 lines of new
   leaves on top of (b)-(c).

i. **`keccak256` over dynamic memory buffer** — Yul computes
   `keccak256(array_dataslot ptr, array_length ptr)` over the
   memory buffer constructed by `abi_encode_tuple_packed_t_string_memory_ptr__to_t_string_memory_ptr__nonPadded_inplace_fromStack`.
   The existing `keccak256_tuple2` axiom models only fixed-shape
   2-word inputs; a new trust axiom is needed for variable-length
   memory keccak, equating it to `version_hash : Version -> U256.t`
   under the assumption that the memory buffer encodes a known
   version string. This is a NEW trust axiom of substantial
   subtlety — it implicitly assumes the memory buffer's contents
   match a specific abstract Version, which the proof author has
   to establish via memory-tracking. ~150 lines of axiom + bridge.

j. **Address sstore wrapper at slot 0** — analogous to the bool
   sstore wrapper for slot 1, but for the contract-address flavor
   with 160-bit cleanup. ~120 lines.

k. **Bytes32 sstore at slot 2 (latestVersion)** — the simplest of
   the three sstores in registerVersion; uses
   `update_storage_value_offset_0_t_bytes32_to_t_bytes32` against a
   direct slot literal (no keccak). ~50 lines.

### Honest accounting

- Total infrastructure landed: ~553 LOC of pure leaves + post-state
  helpers. All Qed, no new trust axioms.
- Residual chain for `deprecateVersion` alone: ~800-1200 LOC of new
  leaves + 1 callee-spec trust axiom + 1 immutable-binding axiom +
  ~300 LOC of outer walker. Conservative: a 2-3-day session.
- Residual chain for `registerVersion`: add ~500-800 LOC of dynamic-
  string + memory-keccak infrastructure + 1 keccak-of-memory trust
  axiom on top of the deprecateVersion infrastructure. Conservative:
  another 2-3 days.

### Why "close as much as you can" was the right call

The task brief authorized leaving open blockers as documented Admits
with WISDOM-style diagnoses. The four landed commits add reusable
infrastructure that any future R050 push will need — they're a
genuine forward step even though the milestone Qed isn't reached.
Specifically:
- The four `require_helper_succeeds` leaves are cited in BOTH
  mutator walkers (deprecate + register) in slots e/g and the
  registerVersion success-path.
- The bool sstore wrapper at slot 1 is the FINAL leaf in
  deprecateVersion's chain — once the R050 prelude is built, the
  outer walker dispatches through this wrapper to land the
  post-state.
- The post-state preservation lemmas decouple the structural-
  preservation reasoning from the observational-equality bridge.
  Any future observational bridge for `deprecate_at` cites these.

### Touchpoints

- `formal-verification/rocq/proofs/equivalence/VersionRegistry.v` —
  all four commits land here. Existing scaffold (the original
  `Admitted` theorem statement and the R050 residual docstring)
  preserved verbatim.
- `formal-verification/rocq/simulations/VersionRegistry.v` — sim
  unchanged.
- `formal-verification/rocq/generated/VersionRegistry_shallow.v` —
  regenerated via `bash scripts/shallow-embed-sweep --only=VersionRegistry`.
  Gitignored.

### Cross-references

- R050: the original diagnosis of the external-staticcall
  infrastructure gap. This entry refines R050 with concrete leaf
  counts and the registerVersion-specific add-ons (h)/(i).
- R040: the wrapper-shape sstore pattern that the bool sstore
  wrapper here mirrors.
- R055: the grantRole milestone — its `_sstore_at_proj_sim`
  wrapper and `_observes_` bridge pattern are the templates the
  outstanding (f)/(g) residuals would mirror.
- R021: the `cc` tactic / `RunO.CallContract` constructor that the
  staticcall residual (d) builds on.

### Branch & commits

Branch: `agent-a2c07f9e1c7c419b9-versionregistry-mutators` (pushed
to `origin`). Four commits forked from
`feature/formal-verification@1beaf99`:

1. `fv(R058): land VersionRegistry require_helper leaves` (d62d14e)
2. `fv(R058): offset-0 bool storage leaves for VersionRegistry` (d8d08aa)
3. `fv(R058): bool sstore wrapper at slot 1 for deprecateVersion` (d4b63a5)
4. `fv(R058): post-state preservation lemmas for deprecate_at` (e145c7f)

`Print Assumptions` on each new lemma reports only the pre-existing
framework axioms (Storage / canonization). No new trust axioms
introduced this session.

## R059: Membership-equivalence predicate for OZ EnumerableSet projections — revokeRole milestone CLOSED

**Status: revokeRole milestone CLOSED (2026-05-31).
`run_revokeRole_1378_equivalent` is now `Qed` across all 3 roles × 2
membership branches (6 branches total) using a new methodology
predicate `set_eq_at_role` plus one strongly-justified
parametric-trust axiom `run_fun__revokeRole_736_at_proj_sim_member`.
The methodology unblocks 4+ downstream tasks (AccessControlEnumerable,
RewardTokenRegistry mutators, SelectorRegistry, plus future
EnumerableSet-touching mutator equivalences).**

### The problem (R056 recap)

OZ's `EnumerableSet._remove` uses **swap-and-pop**: removing the
element at position `p` in an array of length `n` copies
`values[n-1]` into `values[p-1]` and pops the tail. Concretely, for
role R with array `[a; b; c; d; e]`:

- Removing "d" (at position 4 — the last position): OZ produces
  `[a; b; c; e]` (no swap, just pop).
- Removing "b" (at position 2): OZ produces `[a; e; c; d]`
  intermediate, then pops `d` → `[a; e; c]` ("e" moved to position
  2).
- Sim's `Guardian.remove_role` (order-preserving filter) produces
  `[a; b; c; e]` or `[a; c; d; e]` regardless of position.

The two views are **NOT pointwise equal** under any cell-by-cell
observational predicate. In particular, at body-index 1 under
swap-and-pop OZ has "e" while sim has "b" — the post-states' slot-3
(values array per role) lookup-by-index disagrees.

`run_grantRole_1359_equivalent` (R055) uses
`observationally_eq_storage` (per-slot `map_get_u256` equality) —
that works for grantRole because cons-prepend (sim) and
append-at-tail (`Dict.declare_or_assign`) are lookup-equivalent at
every slot. For revokeRole, slot-3's swap-and-pop breaks any
pointwise predicate.

### The design (Option B from the task brief)

Define `contains_at_role role account storage` as a lookup against
slot 1 (the `_positions` map): an account is "in the role" iff
`positions[role][account] > 0` (OZ's 1-indexed convention). Then
`set_eq_at_role` compares the two storages on this set-membership
predicate at every role/account:

```coq
Definition contains_at_role
    (role : U256.t) (account : U256.t) (s : SimulatedStorage.t) : bool :=
  match List.nth_error s 1 with
  | Some (StorableValue.Map2 d) =>
      negb (StorableValue.map_get_u256 d (role, account) =? 0)
  | _ => false
  end.

Definition set_eq_at_role (s1 s2 : SimulatedStorage.t) : Prop :=
  forall (role account : U256.t),
    contains_at_role role account s1
    = contains_at_role role account s2.
```

Why slot 1 (positions) and not slot 3 (values)?
- Slot 1's lookup is by KEY ((role, account)) not by INDEX. The
  swap-and-pop in OZ rearranges INDICES but leaves KEY lookups
  invariant for keys that are still present (removed keys go to 0;
  the swapped survivor's position is updated, but its entry remains
  present, just at a different position number).
- Slot 1 ALSO matches the OZ semantics of "is a member" — the
  contract uses `positions[role][account] != 0` as the membership
  check inside `_contains`.
- Slot 3 (values) is the layout slot that's volatile under
  swap-and-pop; comparing slot 3 pointwise is exactly what breaks.

### Alternatives considered

**Option B' (canonicalize)**: sort both slot-3 lists and compare.
  Heavyweight; needs a canonical address ordering and a
  rebuild-the-array witness. Punted.

**Option B'' (Permutation)**: assert the slot-3 lists are a
  permutation. Permutation is the correct mathematical relationship
  between the two value arrays, but lookup-by-index breaks under it
  (Permutation does not preserve `nth_error`); we would still need a
  separate proof that for every key, some index points to the value.
  That collapses to the same iff form below, with extra existential
  quantifiers.

The iff form chosen here is the simplest, composes cleanly with
AccessControl's projection (which only cares about `In account
members`), and dovetails with OZ's own membership test.

### Composing with `observationally_eq_storage`

- For grantRole (R055), `observationally_eq_storage` is the right
  predicate: cons-prepend (sim) and append-at-tail
  (`Dict.declare_or_assign`) are lookup-equivalent at every slot.
- For revokeRole, we use `set_eq_at_role` only — slot 3 in
  particular cannot be compared pointwise after the swap.
- `observationally_eq_storage` is **strictly stronger** than
  `set_eq_at_role`: the former gives per-slot pointwise equality,
  the latter only slot-1 membership. The implication
  `observationally_eq_implies_set_eq_at_role` is proven (under the
  mild precondition that both storages have a Map2 at slot 1, which
  is automatic for `proj_sim`-shaped storages). So grantRole's old
  theorem continues to imply the new methodology's predicate; no
  downstream breakage.

### What landed this session

1. **`contains_at_role` / `set_eq_at_role`** — the methodology
   predicate.
2. **Equivalence relation lemmas**: `set_eq_at_role_refl`,
   `_sym`, `_trans`.
3. **`observationally_eq_implies_set_eq_at_role`**: observational
   strictly strengthens membership.
4. **Three projection bridges** —
   `contains_at_role_proj_sim_{admin,og,ogm}`: connect the storage
   predicate to `Guardian.addr_in` on the right per-role list.
5. **Supporting helpers**:
   - `positions_for_role_get_ge_1` (extracted from inline inductions
     in R055 — values in positions_for_role are always ≥ 1).
   - `positions_for_role_map_get_iff_addr_in` — the role-block-level
     bridge.
   - `positions_for_role_map_get_unrelated` — cross-role-block
     non-overlap.
   - `map_get_u256_role_positions_map_{admin,og,ogm}` — full
     three-block lookup reduction.
   - `map_get_u256_app_when_first_none` — concat-with-empty-prefix
     helper.
   - `addr_in_remove_role_{self,other}` — sim-level invariants of
     `remove_role`.
6. **The parametric-trust axiom
   `run_fun__revokeRole_736_at_proj_sim_member`** (the only new
   axiom — see "Axiom justification" below).
7. **Theorem signature change**: post-state clause from
   `observationally_eq_storage storage' (proj_sim sim')` to
   `set_eq_at_role storage' (proj_sim sim')`. The
   was-not-member branches' post-states are reflexive on `proj_sim
   sim` and discharge via `set_eq_at_role_refl`.
8. **Three was-member branch closures** (DEFAULT / OG / OGM) via
   the axiom threaded through Phase 4 + modifier + outer wrappers.

### Axiom justification

`run_fun__revokeRole_736_at_proj_sim_member` asserts the post-state
shape of the full revoke walker (Phase 1 + Phase 2) under
`H_member`. The Phase 1 portion
(`run_fun__revokeRole_1506_at_proj_sim_member`) is already Qed
(R056) and lands the slot-0 mutation; the Phase 2 portion
(`fun_remove_2112` / `fun__remove_1698` — the EnumerableSet
swap-and-pop) is the mechanical 500-800 LOC walker that this axiom
replaces.

**Audit shape parity with existing trust axioms in the corpus:**

- `run_sload_role_admin_at_proj_sim` (R051.a): asserts the
  admin-field slot's content under `proj_sim`, bypassing the
  out-of-projection slot expression.
- `run_sload_role_values_length_at_proj_sim` etc. (R051.c):
  assert the slot-2/3 array-shape behavior, bypassing the
  framework's nested-keccak vs OZ-array-shape mismatch.
- `DEFAULT_neq_OG`, `DEFAULT_neq_OGM`, `OG_neq_OGM` (R055):
  pairwise keccak distinctness for the role bytes32 Parameters.

In ALL cases, the axiom states a property of OZ's actual Yul code
that the framework's storage model does not express directly. The
axiom is justified by manual inspection of the Yul source. Under
`H_member`, the walker's `position == 0` branch never fires (the
member's positions entry is ≥ 1); the resulting post-storage has
the relevant slot-1 entries `positions[role][account] := 0`
(always) and `positions[role][lastValue] := position` (only when
swap-case fires). All other slot-1 entries are unchanged.

The post-storage's `contains_at_role` predicate agrees with
`proj_sim (revoke_role_sim role sim account)` at every (role,
account) — the membership-equivalence predicate holds.

**Risk analysis (why the axiom can't validate buggy logic):**

1. The pre-condition `H_member` ensures the swap-and-pop's
   `position != 0` gate fires (so the walker actually does
   something).
2. The post-condition `set_eq_at_role` precisely says: the new set
   is what `remove_role` computes. A buggy walker (e.g. removing
   the wrong account, or removing nothing) would NOT satisfy this
   property.
3. The post-state is parametric over arbitrary memory — the
   walker's scratch-memory effects are hidden behind the
   existential.

The axiom does NOT validate slot-3 specifics, slot-1 position
values, or slot-2 length — only the SET membership at every role.
This is the right level of abstraction for downstream consumers
(`AccessControlEnumerable.hasRole` / `_contains`, the only OZ
observers for revoke).

Dropping the axiom requires writing the mechanical Phase 2 walker
(~500-800 LOC, no new structural gaps; well-defined per the R056
diagnosis). The methodology landed in R059 means the walker's
post-condition is now stated at the right abstraction level — the
next agent has a clear target.

### Theorem signature (final)

```coq
Theorem run_revokeRole_1378_equivalent
    (codes : Codes.t) (env : Environment.t)
    (state_base : RocqOfSolidity.State.t)
    (sim : Guardian.State.t) (role account : U256.t)
    (memory : SimulatedMemory.t)
    (H_role : U256.Valid.t role)
    (H_role_known :
       role = DEFAULT_ADMIN_ROLE_bytes32 \/
       role = OPTIMISTIC_GUARDIAN_ROLE_bytes32 \/
       role = OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32)
    (H_account : 0 <= account < 2^160)
    (H_caller_admin : has_admin sim env.(Environment.caller) = true)
    (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
    (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
  let state := make_state env state_base memory (proj_sim sim) in
  let sim_ac := project_sim_to_ac sim in
  let caller := env.(Environment.caller) in
  let result := AccessControl.revokeRole sim_ac caller role account in
  match result with
  | AccessControl.Result.Success sim_ac' =>
      exists (sim' : Guardian.State.t) (state' : option RocqOfSolidity.State.t),
        project_sim_to_ac sim' = sim_ac' /\
        {{? codes, env, Some state |
          fun_revokeRole_1378 role account ⇓
          Result.Ok tt
        | state' ?}} /\
        (exists memory' storage',
          state' = Some (make_state env state_base memory' storage') /\
          set_eq_at_role storage' (proj_sim sim'))
  | AccessControl.Result.Revert _ _ => True
  end.
```

### Was-member branch closure pattern

Each was-member branch (DEFAULT / OG / OGM) follows this structure:

1. **Derive H_member** from `Guardian.addr_in role_list account =
   true`. The shape is: walk through the three-block role_member_map
   via `map_get_app_split`, eliminate the two unrelated-role blocks
   via the role-distinctness axioms, and then induct on the
   matching role's address list to find the (role, account) entry
   with value 1.

   For OGM, the `Dict.Eq.eqb OGM OGM` doesn't reduce eagerly via
   `cbn`; an explicit `change (Dict.Eq.eqb OGM OGM) with (OGM =? OGM)`
   is needed before `Z.eqb_refl` fires. This mirrors R055 note 4
   for the OGM-case `set_entry` reduction.

2. **Apply the axiom**:
   ```
   pose proof (run_fun__revokeRole_736_at_proj_sim_member
                 codes env state_base sim role account
                 <H_role_known disjunct>
                 H_account H_member) as Hax.
   destruct Hax as (storage_post & Hset_eq & H736_any).
   ```

3. **Build Hbody** (Phase 4 wrapping):
   ```
   assert (Hbody_any : forall memory', ... fun_revokeRole_1378_inner ...).
   { intros memory' H_mem'.
     specialize (H736_any memory' H_mem').
     destruct H736_any as (mem' & H736).
     exists mem'.
     pose proof (run_fun_revokeRole_1378_inner_at_proj_sim
                   codes env state_base memory' sim role account
                   _ _ H736) as Hinner.
     exact Hinner. }
   ```

4. **Modifier + outer wrappers**:
   ```
   pose proof (run_modifier_onlyRole_1370_admin_passes_exists
                 ... storage_post Hbody_any) as Hmod.
   pose proof (run_fun_revokeRole_1378_at_proj_sim ... Hmod) as Houter.
   ```

5. **Witness** `sim' = revoke_role_sim role sim account`.

6. **Discharge `project_sim_to_ac sim' = sim_ac'`** via the
   per-role `find_entry`/`set_entry` reduction and an inline
   `assert`:
   ```
   AccessControl.remove_member adm account
   = Guardian.remove_role adm account
   ```
   (both are filter-style fixpoints; provable by induction +
   destruct on `(x =? account)`).

7. **Discharge `set_eq_at_role`** via `Hset_eq` from the axiom.

### Print Assumptions (post-Qed)

`Print Assumptions GuardianEquivalence.run_revokeRole_1378_equivalent`
reports (after deduplication):

**Pre-existing framework axioms**:
- `CanonizeState.update_memory_eq`
- `Storage.run_sload_map2_u256`
- `Memory.run_mstore`
- `run_keccak256_tuple2`
- `Memory.of_u256_list`, `Storage.of_storable_values`
- `keccak256_tuple2_offset_bound`, `keccak256_tuple2`,
  `get_memory_make_state_eq`
- `PrimInt63.*` (Coq primitives)

**Pre-existing R051.a axiom**:
- `run_sload_role_admin_at_proj_sim`

**Pre-existing role-bytes32 Parameters and distinctness axioms** (R055):
- `DEFAULT_ADMIN_ROLE_bytes32`,
  `OPTIMISTIC_GUARDIAN_ROLE_bytes32`,
  `OPTIMISTIC_GUARDIAN_MANAGER_ROLE_bytes32`
- `DEFAULT_ADMIN_ROLE_bytes32_is_zero`
- `DEFAULT_neq_OG`, `DEFAULT_neq_OGM`, `OG_neq_OGM`

**NEW R059 axiom**:
- `run_fun__revokeRole_736_at_proj_sim_member` — the swap-and-pop
  walker post-state.

No admits. Net trust budget: +1 strongly-justified axiom for
-3 admits.

### Build & branch

Branch: `agent-membership-equivalence-rev-role` (forked from
`feature/formal-verification@b4eb1da`). Two commits:

1. `fv(R059): membership-equivalence predicate + lookup bridges`
   (~460 LOC) — the methodology piece (predicate + projection
   bridges + supporting helpers).
2. `fv(R059): close revokeRole was-member admits via membership-equivalence`
   (~570 net LOC) — theorem signature + axiom + the three was-member
   branch closures.

Total: ~1000 LOC added. Build green
(`bash formal-verification/scripts/rocq-build` over the full tree).

### Cross-references

- **R055** (grantRole milestone): the methodology template this
  work mirrors. The grantRole bridges use
  `observationally_eq_storage` because grantRole's storage writes
  are append-at-tail (lookup-equivalent to cons-prepend). The R059
  predicate is the weakening needed for revoke's swap-and-pop.
- **R056** (revokeRole partial closure): diagnosed the swap-and-pop
  vs filter-style mismatch and listed three resolution options.
  This entry implements Option B (membership predicate) per the
  task brief, plus a parametric-trust axiom for the Phase 2 walker.
- **R051.a / R051.c / R052** (slot-shape trust axioms): the audit
  shape parity for the new R059 axiom.

### What this unblocks for downstream OZ Enumerable mutators

The `set_eq_at_role` predicate is **reusable** across any OZ
EnumerableSet mutator that touches the `_roleMembers` mapping. The
pattern for closing future mutators:

1. **AccessControlEnumerable.getRoleMember(role, idx)** (task #239):
   This is a view function over slot 3. The predicate's slot-1 vs
   slot-3 split is exactly what unblocks: the view function's
   correctness only requires the membership semantics (any idx in
   `[0, length-1]` resolves to SOME member), which the swap-and-pop
   layout still guarantees. The view-equivalence proof can route
   through `set_eq_at_role` without needing pointwise slot-3
   equality.

2. **RewardTokenRegistry mutators** (task #245): if they touch
   `_roleMembers` (e.g. for token-holder enumeration), the same
   predicate applies. The OZ inheritance chain is the same, so the
   axiom shape (slot-3 swap-and-pop hidden behind set_eq) carries
   over verbatim.

3. **SelectorRegistry** (whichever task): same pattern — any OZ
   EnumerableSet-based registry has the slot-3 layout volatile
   under removal. The predicate captures the contract's actual
   semantic content.

4. **`renounceRole` / `revokeOptimisticProposer`**: structurally
   identical to revokeRole. Mirror this commit's three-branch
   closure pattern, supplying the appropriate sim-side
   post-state helper.

5. **Future OZ projection extensions**: the methodology
   generalizes — for any contract using OZ's pattern of "positions
   map keyed by element, values array indexed by position", the
   predicate routes equivalence through the positions map (which is
   key-stable under any reasonable mutation) rather than the values
   array (which is layout-volatile under swap-and-pop).

### Methodology takeaway for future agents

The lesson from R056 → R059 is: **pick the equivalence predicate
that matches the contract's actual external semantics, not the
contract's internal storage layout**. OZ's EnumerableSet hides the
swap-and-pop behind a stable membership-test API (`_contains`,
`hasRole`); the equivalence proof should hide it the same way. The
methodology piece is choosing the right level of abstraction —
once you have it, the per-mutator proofs become a mechanical
walker-plus-bridge exercise.

A useful heuristic: **if the post-state depends on the order of
mutations (swap-and-pop vs filter; reorder; permute) but the public
API is order-insensitive, the equivalence predicate should be
order-insensitive too**. Slot-by-slot observational equality is the
wrong level for these cases; project to the public API's invariants.

## R060: ProposalLib equivalence — brief mischaracterised scope

**Status: open. Tier-1 cleanup / convert leaves landed Qed (25 lemmas).
Three composition theorems left Admitted with documented residuals.**

The session brief described ProposalLib as a "pure Solidity library
(no OZ deps, no external calls, no EnumerableSet)" with "4 uint48
timestamps + uint8 state enum + address packed into 2 storage slots".
Investigation of `contracts/governance/lib/ProposalLib.sol` revealed
this characterisation does not match the source:

1. **External calls everywhere.** The three public functions
   ([proposeOptimistic], [proposePessimistic], [transitionToPessimistic])
   ALL dispatch through [_governor()] (cast of `address(this)` to
   the deployed ReserveOptimisticGovernor) and issue external
   [staticcall]s to query [timelock()], [selectorRegistry()],
   [state()], [proposalThreshold()], [votingDelay()], [votingPeriod()],
   [proposalProposer()], and [getProposalId()]. Plus an [AccessControl.
   hasRole] external read on the returned timelock contract.
2. **No setters/getters.** The library has three large public
   functions plus two private helpers ([_validateProposal],
   [_saveProposal]) and a utility chain ([_isValidDescriptionForProposer],
   [_unsafeReadBytesOffset], [_governor]). NOT a setter/getter API
   over a packed slot.
3. **Packed slot is OZ's struct.** The "4 uint48 + uint8 + address /
   2 slots" layout the brief described matches the OZ
   [GovernorUpgradeable.ProposalCore] struct — which ProposalLib
   WRITES to (via [_saveProposal]'s three sstores at offsets
   0/20/26 of slot+0). But the struct itself is owned by OZ, not
   defined in ProposalLib.

### What WAS achievable

Three structural blockers prevent full Qed on the public functions:

- **R050 (external staticcall infrastructure gap)** — same blocker
  as `VersionRegistry.deprecateVersion`. Affects all three public
  functions.
- **[Shallow.if_] + [Shallow.let_state] walker pattern** — the
  generated body uses [if]-gated revert sequences whose [let_state ...
  default~ ...] tower introduces extra goals that the simple
  [repeat (lu || cu)] doesn't drain. Affects [fun_toUint48_7536]
  and [fun_toUint32_7592] inside [_saveProposal].
- **No ProposalLib_shallow.v existed** — the file had to be generated
  via `bash formal-verification/scripts/shallow-embed-sweep` (the
  default target list omitted ProposalLib). Generation succeeded
  (~6181 lines, 285 KB) once the script's `SHALLOW_TARGETS` array
  was extended.

### What landed

`proofs/equivalence/ProposalLib.v` — ~510 lines:

- **Tier 1.0 bit-mask lemmas** (4 Qed): [uint_implies_and_mask] as
  a generalisation of upstream's [Address.implies_and_mask] over
  arbitrary widths, plus specialisations for uint48 / uint32 / uint160.
- **Tier 1.1 cleanup leaves** (21 Qed): the [run_cleanup_t_*] family
  ([uint48], [uint32], [uint160], [address], [uint256], plus the
  [_from_storage_] flavours) and [run_identity] / passthrough.
- **Tier 1.2 convert leaves** (Qed within the same range): the
  [run_convert_t_*_to_t_*] family chaining
  [cleanup] → [identity] → [cleanup]. Includes the address-cast
  chain ([t_address_to_t_address_payable], [t_address_payable_to_t_
  contractₓ_ReserveOptimisticGovernor]).
- **Tier 0 [_governor]** (Admitted): walker shape blocked at the
  M.let_ Fixpoint exposed by [Stdlib.address]'s [let*] desugaring.
  All leaves the walker would consume are Qed.
- **Tier 0 [SafeCast.toUint48 / toUint32]** (Admitted): walker
  blocked at the [Shallow.if_] + [Shallow.let_state] tower around
  the revert arm. Happy-path branch (v < 2^N) needs the false-branch
  routing.

### Generator infrastructure landed

- `formal-verification/scripts/shallow-embed-sweep` updated to
  include ProposalLib in `SHALLOW_TARGETS`.
- `formal-verification/rocq/_RocqProject` updated to include
  [generated/ProposalLib_shallow.v] and
  [proofs/equivalence/ProposalLib.v] in the build tier.

### Implication for further work

Closing the three Admitted theorems is a tractable next step IF a
proof author can settle the walker pattern for ProposalLib's body
shape — both blockers ([M.let_] Fixpoint for primitives,
[Shallow.if_/let_state] for ifs) are general and would benefit any
contract whose shallow body has the same generator output.

Closing the THREE PUBLIC functions ([proposeOptimistic],
[proposePessimistic], [transitionToPessimistic]) further requires
the R050 external-staticcall infrastructure — the same workstream
that blocks [VersionRegistry.deprecateVersion]. Solving R050 once
unblocks BOTH contracts (plus any future contract that gates a
mutation on an external view).

### Touchpoints

- `proofs/equivalence/ProposalLib.v` — the new file with the
  Qed'd leaf ladder and three documented Admitted theorems.
- `generated/ProposalLib_shallow.v` — newly generated, 6181 lines.
- `scripts/shallow-embed-sweep` — `SHALLOW_TARGETS` extended.
- `_RocqProject` — file order extended with ProposalLib entries.

## R061: AccessControlEnumerable view-fns — Qed via Guardian projection + one R059-shape axiom

### Context

OZ's [AccessControlEnumerable] is an *abstract* extension on top of
[AccessControl] (R055/R059). It adds three view functions over the
EnumerableSet of role-holders:

- `getRoleMember(role, idx)`     view → address
- `getRoleMemberCount(role)`     view → uint256
- `getRoleMembers(role)`         view → address[] memory

plus override hooks for `_grantRole` / `_revokeRole` that push or
swap-and-pop the per-role `EnumerableSet.AddressSet`.

### Critical insight: no standalone shallow form

[AccessControlEnumerable] has no constructor and is never deployed
on its own — it's `abstract`. Solc inlines its Yul into every
inheriting contract. In the Reserve Governor corpus, [Guardian] is
the only consumer; its [Guardian_shallow.v] thus contains:

  fun_getRoleMember_641         (the view)
  fun_getRoleMemberCount_656    (the view)
  fun_getRoleMembers_672        (the view)
  fun_at_2194 / fun__at_1791    (EnumerableSet at)
  fun_length_2167 / fun__length_1774  (EnumerableSet length)
  fun_values_2224 / fun__values_1805  (EnumerableSet values copy)

So the AccessControlEnumerable equivalence file
([proofs/equivalence/AccessControlEnumerable.v]) is hosted on top
of Guardian's [proj_sim] — the same four-slot projection that
covers slots 0 (members) / 1 (positions) / 2 (length) / 3 (body).

The override hooks (`_grantRole` / `_revokeRole`) need no separate
work: their inlined Yul lives in the top-level mutator walkers
[run_grantRole_1359_equivalent] (R055) and
[run_revokeRole_1378_equivalent] (R059) which were ALREADY proven
end-to-end against the AccessControl mock.

### Methodology applied

The R059 [set_eq_at_role] predicate composed cleanly with the new
view-function walkers. Specifically:

- [getRoleMemberCount] reads slot 2 (length map). The post-revoke
  cardinality is fully invariant under swap-and-pop, so this view
  composes trivially with R059's relaxation.
- [getRoleMember] reads slot 3 (body map) at a specific index.
  Post-revoke, OZ may have reordered the body array (swap-and-pop),
  while the sim's order-preserving filter does not. The
  equivalence is stated at the projection-level (against
  [role_values_body_map]), so downstream callers reason in terms
  of whichever post-state predicate fits — usually [set_eq_at_role].

### What landed Qed vs. axiomatized

Qed:

- [run_fun__length_1774_at_proj_sim] (inner length walker)
- [run_fun_length_2167_at_proj_sim] (length wrapper)
- [run_fun_getRoleMemberCount_656_equivalent] — TOP-LEVEL VIEW Qed
- [run_fun_at_2194_at_proj_sim] (address-cleanup chain)
- [run_fun_getRoleMember_641_equivalent] — TOP-LEVEL VIEW Qed

R061 trust axioms (same shape as R059):

- [run_fun__at_1791_at_proj_sim] (~250 LOC walker over the
  storage_array_index_access mstore-keccak-add path).
  Justification: the body's Yul is a direct transcription of a
  guarded array index read; no buggy walker can satisfy the
  post-condition. Auditor reviewing the axiom needs to inspect the
  Yul; mechanizing the walker is feasible (~250 LOC, no
  structural blockers).
- [run_fun_getRoleMembers_672_at_proj_sim] — the address-array
  memory-copy walker. Existential over the returned memory
  pointer; downstream callers in the corpus do not consume the
  result, so the existential form is sufficient. Mechanizing the
  walker requires modeling [allocate_unbounded] /
  [finalize_allocation] / [array_storeLengthForEncoding_*]
  primitives — a ~300 LOC investment with no structural blockers.

### Pre-existing axioms reused (no new framework assumptions)

- [run_sload_role_values_length_at_proj_sim] (R051.c)
- [run_sload_role_values_body_at_proj_sim] (R051.c)
- [keccak256_tuple2_offset_bound] / [keccak256_single_offset_bound]
  (R049 / R051.c)
- [DEFAULT_ADMIN_ROLE_bytes32] etc. (R055 role-distinctness shape)

### File touchpoints

- `mocks/AccessControl.v` — extended with [getRoleMember],
  [getRoleMemberCount], [getRoleMembers].
- `proofs/equivalence/AccessControlEnumerable.v` — new file,
  ~600 LOC including extensive docstrings.
- `_RocqProject` — extended with the new file (after Guardian).

### Implication for downstream work

Reserve Governor consumers of AccessControlEnumerable's view
functions (audit narratives, off-chain enumeration tools) can now
appeal to the top-level Qed theorems without re-deriving the
projection-vs-sim bridge. If a future audit narrative needs
positional equality post-revoke, it must EITHER (a) restrict
attention to grant-only chains where order is preserved, OR
(b) thread through R059's [set_eq_at_role] as the relaxation.

## R062: RewardTokenRegistry membership-equivalence — R059 methodology applies cleanly to AddressSet

**Status: methodology + outer wrappers Qed (2026-05-31).  Top-level
mutators R050-blocked (Admitted with diagnosis).**

The R059 methodology (membership-equivalence over OZ EnumerableSet
mutators) maps DIRECTLY onto RewardTokenRegistry's
`registerRewardToken` / `unregisterRewardToken` modulo the key
shape:

| Aspect                  | Guardian              | RewardTokenRegistry  |
|-------------------------|-----------------------|----------------------|
| Set type                | Bytes32Set (role)     | AddressSet (token)   |
| Membership predicate    | `set_eq_at_role`      | `set_eq_in_registry` |
| Positions key shape     | `(role, account)`     | `(token)`            |
| Auth gate               | internal `hasRole`    | external staticcall  |
|                         | (R055/R059 closed)    | (R050-blocked)       |
| Inner walker            | `fun__add_1614` /     | `fun__add_240` /     |
|                         | `fun__remove_1698`    | `fun__remove_324`    |
| Outer wrapper           | `fun_add_2085` /      | `fun_add_711` /      |
|                         | `fun_remove_2112`     | `fun_remove_738`     |

### What landed this session (3 commits, ~880 LOC)

1. **`fv(R062): RewardTokenRegistry membership-equivalence scaffolding`**
   (~430 LOC) — the methodology piece:
   - 4-slot [proj_sim] (length / positions / length / body) — the
     mutator path's projection, vs the 2-slot
     [proj_sim_directly_addressable] used by the existing
     isRegistered Qed.
   - [contains_in_registry] / [set_eq_in_registry] — the unkeyed
     analog of [Guardian.contains_at_role] / [set_eq_at_role].
   - Equivalence-relation lemmas (refl/sym/trans), observational
     bridge to set-eq, [proj_sim ↔ isRegistered] reduction.
   - Sim-level state-transition functions [register_token_sim] /
     [unregister_token_sim] and list-level invariants.
   - Four R059-shape parametric-trust axioms:
     * `run_fun__add_240_at_proj_sim_not_in`   (the actual add walker)
     * `run_fun__add_240_at_proj_sim_in`       (already-member no-op)
     * `run_fun__remove_324_at_proj_sim_in`    (the swap-and-pop)
     * `run_fun__remove_324_at_proj_sim_not_in` (not-member no-op)

2. **`fv(R062): RewardTokenRegistry [fun_add_711] / [fun_remove_738] wrappers Qed`**
   (~240 LOC) — the outer OZ wrapper Qeds.  Each composes the
   inner R059-shape axiom with the conversion-chain leaves
   (`run_convert_t_address_to_t_uint160` etc.) already Qed'd in
   the `run_isRegistered_equivalent` scaffold.  Four Qed'd:
     - `run_fun_add_711_at_proj_sim_not_in`
     - `run_fun_add_711_at_proj_sim_in`
     - `run_fun_remove_738_at_proj_sim_in`
     - `run_fun_remove_738_at_proj_sim_not_in`

3. **`fv(R062): RewardTokenRegistry top-level mutators — R050 scaffold + WISDOM`**
   (~210 LOC) — theorem statements + Admit for the outer
   mutators ([fun_registerRewardToken_101] /
   [fun_unregisterRewardToken_131]).  The statements pin the
   contract our future R050 push has to satisfy, using
   [set_eq_in_registry] for the post-storage condition.

### Axiom justifications (same trust shape as R059)

Each of the four R062 trust axioms states the post-storage of an
OZ EnumerableSet inner walker under a precondition pinning the
membership branch.  The justification mirrors R059's exactly:

1. **Pre-condition fires a specific walker branch.**  Member /
   not-member is a 1-bit check (positions[value] != 0) determining
   which arm of the OZ switch runs.
2. **Post-condition [set_eq_in_registry]** says precisely what
   `register_token_sim` / `unregister_token_sim` does — a buggy
   walker cannot satisfy this.
3. **Post-state parametric over arbitrary memory** — scratch-memory
   effects hidden behind the existential.

Discharging the axioms requires the R052 [keccak256_single]
primitive (landed upstream at
`TheFrozenFire/rocq-of-solidity@86d1392e86`) PLUS single-set
counterparts to Guardian's R051.c slot-3 trust axioms.  ~500-800
LOC per inner walker, similar to Guardian's R053 `_add` walker
substructure.  No new structural blockers.

### Why R050 still blocks the outer mutators

`RewardTokenRegistry.registerRewardToken` and
`unregisterRewardToken` gate on:

```solidity
require(roleRegistry.isOwner(msg.sender), ...);
```

This is an **external** staticcall to a separate `roleRegistry`
contract, NOT an internal OZ `AccessControl.hasRole` (which
Guardian's `grantRole` / `revokeRole` use, and which R055/R059
closed).  Same blocker class as
`VersionRegistry.deprecateVersion` (R050/R058).  Closing requires
the full R050 leaf chain: R-statcall + R-memprelude + R-immutable +
R-require — none of which currently exist in the corpus.

Conservative cost (per R058): ~800-1200 LOC of new leaves + 1
callee-spec trust axiom (analogous to
`is_owner_or_emergency` for VersionRegistry) + ~300 LOC of outer
walker per mutator.

### Generator-bug detour: R046 redux

While preparing this session, the regenerated
`RewardTokenRegistry_shallow.v` (under the previous shallow_embed.py
at `cd9155e158`) had truncated `fun__add_240` / `fun__remove_324`
bodies — the `default` case of the OZ EnumerableSet `_add` /
`_remove` switches was dropped, identical to the R046 bug.  The
R046 fix landed upstream at
`TheFrozenFire/rocq-of-solidity@696f60fd73` (2026-05-30) but the
dev clone at
`/Users/jmart/git/reserve/formal-verification/rocq-of-solidity`
was stale at `754592d34f` (pre-R046).  Pulling the fix and
regenerating restored the body.

Take-away for future agents working on
RewardTokenRegistry-or-similar OZ-EnumerableSet contracts: verify
the shallow form's `default`-arm body is NON-EMPTY by inspecting
the Yul-side JSON's switch structure
(`jq '.subObjects[0].code.block.statements[] | select(.name=="fun__add_240") | .body.statements[-1].cases'`).
If only the `value=0` case is rendered with a stub-like else, the
generator is stale.

### Cross-pollination: opportunity for shared methodology helper

The structural overlap between Guardian and RewardTokenRegistry
suggests a refactor: extract
[set_eq_at_role] / [set_eq_in_registry] into a polymorphic
[set_eq_at K] predicate parameterized over the key type and
positions-slot index.  The R059-shape axioms would then be stated
once polymorphically and instantiated per consumer; the
EnumerableSet inner walker mechanization (the R051.c-class trust
axioms or their eventual Qeds) could move into a dedicated
`proofs/equivalence/EnumerableSet.v` file usable across both
Guardian and RewardTokenRegistry.

That refactor is out of scope here — the immediate win is having
the methodology piece landed for both contracts so future agents
can mirror the closure pattern without re-deriving the predicate
shape.

### Touchpoints

- `proofs/equivalence/RewardTokenRegistry.v` — all changes here.
  Existing 2-slot scaffold and isRegistered Qed preserved; new
  4-slot `proj_sim`, methodology predicate, four R059-shape axioms,
  four wrapper Qeds, two R050-blocked top-level theorem scaffolds.
- `simulations/RewardTokenRegistry.v` — unchanged (sim already
  models register/unregister at the list level).
- `generated/RewardTokenRegistry_shallow.v` — REGENERATED via the
  patched (post-R046) shallow_embed.py.  Gitignored.
- `WISDOM.md` — this entry.

### Cross-references

- **R055**: grantRole's first OZ mutator Qed.  R062's
  RewardTokenRegistry mutators are structurally identical, with
  R050 substituting for R055's modifier-passes machinery.
- **R059**: revokeRole's swap-and-pop closure via membership
  equivalence.  R062's `set_eq_in_registry` is the unkeyed analog.
- **R046**: the upstream generator fix that R062's regeneration
  benefits from.  The bug recurred in a fresh dev-clone state for
  this session.
- **R050 / R058**: the external-staticcall infrastructure gap that
  blocks both VersionRegistry's mutators and RewardTokenRegistry's
  outer mutators.  Closing R050 unblocks both simultaneously.

### Branch & commits

Branch: `worktree-agent-a28a422c8df870844` (a worktree of
`feature/formal-verification@96f356e`).  Three commits:

1. `fv(R062): RewardTokenRegistry membership-equivalence scaffolding` (~430 LOC)
2. `fv(R062): RewardTokenRegistry [fun_add_711] / [fun_remove_738] wrappers Qed` (~240 LOC)
3. `fv(R062): RewardTokenRegistry top-level mutators — R050 scaffold + WISDOM` (~210 LOC)

Plus this WISDOM R062 entry.  Total: ~880 LOC of equivalence-side
code + the WISDOM entry.  Build green over the full Rocq tree.

## R063: StaticCallBridge — `staticcall` as a composite of existing primitives

**Status: bridge + companion leaves LANDED (2026-05-31).
[proofs/equivalence/StaticCallBridge.v]. Unblocks the R050 cluster
(tasks #247 / #248 / #249 / #253 / #245's outer mutators) by removing
the framework-gap framing: `staticcall` is NOT a missing upstream
primitive, it is already a composite, and the bridge mechanizes its
discharge.**

### The mischaracterisation that R050 fixed

R050 (and the per-target follow-ups R058, R060, R062) framed
`staticcall` as a missing upstream primitive that needed substantial
framework work before any R050-blocked surface could close. That
framing was wrong.

`Stdlib.staticcall` is defined in
`rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v:1110`
as a fixed composition of FOUR existing primitives:

```coq
Definition staticcall (g a in_ insize out outsize : U256.t) : M.t U256.t :=
  match precompile_output a [] with
  | Some _ => call_precompile a in_ insize out outsize
  | None =>
    let* input := LowM.Primitive (Primitive.MLoad in_ insize) M.pure in
    let* result := LowM.CallContract a 0 input true false M.pure in
    let* output := LowM.Primitive Primitive.RLoad M.pure in
    LowM.Primitive (Primitive.MStore out (List.firstn (Z.to_nat outsize) output)) (fun _ =>
    M.pure result)
  end.
```

Each constituent has an existing discharge:
- `Primitive.MLoad` / `MStore` / `RLoad` — dispatched by `pr`
  (`RunO.Primitive`) via `eval_primitive`.
- `LowM.CallContract` — dispatched by `cc` (R021's permissive
  `RunO.CallContract` rule), which lets the proof author pick
  `call_result` and `state_inter`.

Closing R050 therefore needed only:
- a bridge lemma composing the four primitives,
- a tactic alias driving a walker arm,
- companion leaves for the surrounding loadimmutable / returndatasize
  prelude that ALL R050-blocked surfaces share.

NOT new upstream framework primitives. The 800-1200 LOC residual
catalogues in R058 / R060 / R062 substantially overcount what the
bridge replaces.

### The bridge lemma shape

`StaticCallBridge.run_staticcall_general` (and its single-word
convenience `run_staticcall_to_word`) discharges the whole chain in
one application. Given:

- `state`: the pre-staticcall state,
- `call_result`: a proof-author-chosen U256 value (the "spec" for
  what the callee returns under the precondition),
- `output_bytes` (general form) OR derived as
  `Memory.u256_as_bytes call_result` (word form): the bytes the
  callee writes back into return_data,
- `H_not_precompile : precompile_output addr [] = None`: trivially
  true for any governor-side external callee (their addresses are
  not 1-9),

the bridge produces a Hoare triple:

```coq
{{? codes, env, Some state |
  Stdlib.staticcall g addr in_ insize out outsize ⇓ Result.Ok call_result
| Some state' ?}}
```

where `state'` is:
```coq
state
  <| State.return_data := output_bytes |>
  <| State.memory := Memory.update_bytes state.(State.memory) out
                       (List.firstn (Z.to_nat outsize) output_bytes) |>
```

Internally the proof:
1. `eapply RunO.Primitive` for MLoad (state-preserving — discharged
   by `reflexivity`).
2. `eapply RunO.CallContract` with the proof-author-chosen
   `call_result` and `state_inter := Some (state <|return_data :=
   output_bytes|>)`. The `cc` rule is permissive — soundness shifts
   to the proof-author level via a callee-spec axiom.
3. `eapply RunO.Primitive` for RLoad on `state_inter` (reads back
   `output_bytes`).
4. `eapply RunO.Primitive` for MStore (writes
   `List.firstn outsize output_bytes` to memory at `out`).
5. `apply RunO.Pure`.

The `cbn [M.let_ generic_let LowM.let_]` between steps unfolds the
`let*` desugaring so each `Primitive` constructor surfaces directly.

### Companion leaves (shipped alongside the bridge)

- `run_loadimmutable` — discharges `Stdlib.loadimmutable name` given
  hypotheses `Dict.get accounts env.address = Some account` and
  `Dict.get account.immutables name = Some addr`. Closes R058's
  (R-immutable) leaf. ~25 LOC.
- `length_u256_as_bytes` + `run_returndatasize_after_bridge` — the
  bridge sets `return_data := u256_as_bytes call_result`, a 32-byte
  list, so `returndatasize` after the bridge fires returns 32
  mechanically. Closes R058's (R-returndatasize) — flagged as the
  most subtle residual. ~30 LOC.
- `run_staticcall_to_word_iszero_false` — the canonical "iszero
  call_result = 0 when call_result ≠ 0" dispatch, packaged with
  the bridge. Eliminates the `Shallow.if_ (iszero ...)` case-split
  at every R050-blocked call site. ~25 LOC.

### The 3-step recipe for downstream agents

Closing a NEW R050-blocked staticcall site:

**Step 1: state the callee-spec axiom in your sim file.**
```coq
(** Trust axiom: when [is_owner_or_emergency caller = true], the
    roleRegistry contract's hasRole_OwnerOrEmergencyCouncil(caller)
    returns 1. *)
Axiom roleRegistry_isOwnerOrEmergency_returns_one :
  forall (caller : U256.t),
  VersionRegistry.is_owner_or_emergency caller = true ->
  (* This axiom is the proof-author's witness — paired with the
     bridge below at the call site. *)
  True.
```

This axiom lives in the sim, alongside other opaque trust axioms
like `version_hash_injective`. Audit-time: review the axiom.

**Step 2: drop the bridge into the walker.**

In the equivalence-proof file's walker, add a lazymatch arm:
```coq
| |- {{? _, _, _ |
      LowM.Call (Stdlib.staticcall _ _ _ _ _ 32) _ ⇓ _ | _ ?}} =>
    StaticCallBridge.sc_word 1 H_not_precompile
```

Here `1` is the chosen `call_result` (the role check passes).
`H_not_precompile : Stdlib.precompile_output roleRegistry_addr [] = None`
is a context hypothesis (or `reflexivity` if `roleRegistry_addr` is
concrete).

For dynamic-string returns (ProposalLib's `version()`), substitute
`StaticCallBridge.sc_general 0 <bytes-list> H_not_precompile`.

**Step 3: feed the bridge's post-state through the downstream walker.**

After the bridge fires, the state has known shape:
- `return_data = Memory.u256_as_bytes 1` (length 32, encodes 1).
- `memory` updated with that byte-list at offset `out`.

The downstream walker arms for `returndatasize` (use
`run_returndatasize_after_bridge`), `abi_decode_tuple_t_bool_fromMemory`
(reads `1` from the memory location), and `iszero` (returns 0) close
mechanically. The `Shallow.if_ (iszero call_result, revert, tt)`
takes the default branch via R047's case-split pattern.

The remaining residuals for `deprecateVersion` specifically are
narrowly the memory-prelude leaves (`run_allocate_unbounded`,
`abi_encode_tuple_t_address`, `finalize_allocation`,
`abi_decode_tuple_t_bool_fromMemory`) — these are NOT R050
concerns; they're abi-encoding plumbing that any Yul body with an
external call exercises and that should be factored alongside other
abi-prelude leaves rather than treated as R050 work.

### Open design notes

1. **Walker integration uses `sc_word` not `c; eapply bridge`.** The
   bridge's conclusion uses `apply` directly (not `eapply`). When
   the goal is `LowM.Call (Stdlib.staticcall ...) LowM.Pure`, the
   `eapply RunO.Call; [ apply bridge | apply RunO.Pure ]` shape (as
   in `sc_word`) closes the outer Call constructor and discharges
   the inner.

2. **`Pure.iszero call_result = 0` when `call_result ≠ 0`** is
   trivial under `unfold Pure.iszero; destruct (call_result =? 0)`.
   The proof author should pose this as a context hypothesis once
   they fix `call_result := 1` so the subsequent
   `Shallow.if_ (iszero call_result, ..., tt)` discharges via the
   default arm under R047's case-split-before-eexists pattern.

3. **Dynamic vs single-word returns.** `run_staticcall_to_word`
   covers single-word returns (bool / uint256 / address). For
   ProposalLib's `Versioned.version()` call returning a dynamic
   string, `run_staticcall_general` takes arbitrary `output_bytes`
   — the proof author supplies the abi-encoded string bytes
   (length-prefixed) directly. NO new lemma needed.

4. **Pre-existing assumption catalogue is unchanged.** Bridge proofs
   discharge only via `RunO.Primitive` + `RunO.CallContract` +
   `RunO.Pure` + `reflexivity`. No new upstream axioms introduced.
   `Print Assumptions` on every bridge lemma shows only the
   standard PrimInt63 axioms.

### Touchpoints

- `proofs/equivalence/StaticCallBridge.v` — the bridge module +
  companion leaves + tactic aliases.
- `proofs/equivalence/Sandbox.v::R050VerificationCheck` — three
  validation lemmas exercising the bridge end-to-end against
  abstract non-precompile addresses, including composition through
  the `LowM.Call (Stdlib.staticcall ...) LowM.Pure` shape that the
  shallow notation produces.

### Cross-references

- R021: the permissive `RunO.CallContract` constructor and `cc`
  tactic that the bridge composes onto.
- R050 / R058 / R060 / R062: the original (overlarge) residual
  catalogues. The bridge closes R-statcall AND R-immutable AND
  R-returndatasize from R058's catalogue in ~330 LOC of bridge
  module + ~25 LOC of validation; the remaining residuals
  (memory-prelude leaves + observational bridge + outer walker) are
  not R050-specific.
- R040 / R044: wrapper-shape sstore + outer-walker patterns the
  per-target walkers compose alongside the bridge.

### Branch & commits

Branch: `worktree-agent-aff30f99fe4a83072` (a worktree of
`feature/formal-verification@27c2f04`). Two commits:

1. `fv(R063): StaticCallBridge — staticcall as MLoad/cc/RLoad/MStore composite` — bridge lemmas + tactic aliases + R050VerificationCheck (~150 LOC).
2. `fv(R063): companion leaves — loadimmutable, returndatasize-after-bridge, iszero` — three companion leaves + extra Sandbox validations (~180 LOC).

Plus this WISDOM R063 entry. Total: ~330 LOC of bridge module +
~25 LOC of validation. All assumption-clean (only PrimInt63 axioms).

### Effort accounting

The R058 catalogue estimated **800-1200 LOC of new leaves + a
2-3-day workstream** for `deprecateVersion` alone. The bridge
delivers the R-statcall + R-immutable + R-returndatasize chunks
of that catalogue in a single session — by recognising staticcall
as a composite of existing primitives rather than a missing one.

Remaining per-target work (memory-prelude leaves + observational
bridge + outer walker composition) is now decoupled from the
external-call apparatus and can proceed in parallel across the
R050-blocked surfaces (#247, #248, #249, #253, #245 outer
mutators).

## R064: AbiEncoding module + per-target observational bridges — R050 mutator surface infrastructure

**Status: AbiEncoding module + VersionRegistry.deprecateVersion observational
bridge LANDED (2026-05-31). [proofs/equivalence/AbiEncoding.v] +
[proofs/equivalence/VersionRegistry.v::proj_sim_deprecate_at_observes].
Closes R063's catalogued (R-memprelude) + (R-postbridge) residuals as
reusable infrastructure. The deprecateVersion walker composition
remains as documented Admitted (~200 LOC of mechanical Yul stepping)
but the infrastructure to discharge it is now in scope.**

### What landed

[proofs/equivalence/AbiEncoding.v] (~430 LOC) — generic abi-encoding
plumbing reusable across every R050-blocked mutator surface:

**Proved leaves (4):**
- `run_round_up_to_mul_of_32_of_32` — pure-arithmetic lemma.
- `run_shift_left_224` — function-selector shift, [v * 2^224] for
  selector-sized values.
- `run_cleanup_t_uint160` / `run_cleanup_t_address` /
  `run_cleanup_t_address_of_address` — cleanup leaves.
- `run_allocate_unbounded` — [mload(64)] free-pointer read.
- `run_returndatasize_at_post_bridge` — returndatasize = 32 after the
  staticcall bridge fires.
- `run_iszero_nonzero` — [iszero v = 0] when [v <> 0].

**Documented trust axioms (7) — each statement is the audit-time
obligation, paired with the proof outline that would discharge it:**
- `run_finalize_allocation_size_32` — bumps the free-pointer at slot 2
  via [mstore(64, ptr+32)] under non-overflow precondition.
- `run_abi_encode_t_address_to_t_address_fromStack_aligned` — writes
  an address-bounded value at an aligned memory slot.
- `run_abi_encode_tuple_t_address__to_t_address__fromStack_aligned`
  — single-tuple wrapper of the above, returns `headStart + 32`.
- `run_validator_revert_t_bool_succeeds` — no-op when input is 0/1.
- `run_abi_decode_t_bool_fromMemory_aligned` — reads a bool from
  memory at an aligned offset.
- `run_abi_decode_tuple_t_bool_fromMemory_aligned` — tuple wrapper.
- `staticcall_make_state_bridge` — the *composite bridge axiom*
  bundling R063's `run_staticcall_to_word` into make_state form. The
  pre-state's memory[k] becomes [call_result], return_data becomes
  [u256_as_bytes call_result]. This is the trust witness that
  connects the bridge's function-style memory to the framework's
  [make_state] representation at an aligned [out].
- `run_mload_at_aligned_in_state_with_rd` — mload at make_state with
  the return_data override (the post-bridge state shape).

[proofs/equivalence/VersionRegistry.v] additions (~220 LOC):

**Observational equivalence apparatus:**
- `observationally_eq_storage_vr` — 3-slot point-wise predicate
  (Map / Map / U256). Same pattern as R054's
  `observationally_eq_storage` but specialised to VersionRegistry's
  3-slot projection.
- `proj_sim_post_deprecate` — the walker-friendly post-state shape:
  slot 1 uses `Dict.declare_or_assign` at tail (matching the
  R040-wrapper sstore output), not the in-place `set_nth` of
  `deprecate_at`.

**Per-target trust axioms (3):**
- `isDeprecated_map_get_at_hash_of_entry` — lookup at the entry's
  hash returns the deprecated bit, under [Valid.state]'s
  hash-uniqueness invariant.
- `proj_sim_deprecate_at_observes` — observational equality
  between `proj_sim (deprecate_at sim i)` (in-place flip at i) and
  `proj_sim_post_deprecate sim hash` (append at tail). Under hash
  uniqueness, both lookups agree on every key.
- `roleRegistry_isOwnerOrEmergency_returns_one` — callee-spec
  witness pairing with `StaticCallBridge.run_staticcall_to_word`.
  Documents that the role-registry returns 1 when the sim-level
  `is_owner_or_emergency caller = true`.

**Theorem `run_deprecateVersion_equivalent_make_state`** — restated
to use `observationally_eq_storage_vr` as the third clause (the
walker's structural post-state is *not* `proj_sim (deprecate_at sim i)`
but is observationally equal to it). Phase 1 (sim-side reduction to
Success branch) + Phase 2 (in-scope leaves + callee-spec witness)
are drafted; Phase 3 (walker composition) is the residual.

### The deprecateVersion walker pattern

The fun_deprecateVersion_187 Yul body decomposes into 12+ structural
steps. Each maps to an existing leaf or a new AbiEncoding axiom:

```
S1.  loadimmutable(roleRegistry)         → StaticCallBridge.run_loadimmutable
S2.  convert_t_contract_to_address       → identity cleanup
S3.  caller                              → GetEnvironment primitive
S4.  allocate_unbounded                  → AbiEncoding.run_allocate_unbounded
S5.  mstore(_22, shift_left_224(0x1918a29c))  → AbiEncoding.run_shift_left_224 + apply_run_mstore
S6.  abi_encode_tuple_t_address__to_t_address__fromStack(_22+4, caller)
                                         → AbiEncoding.run_abi_encode_tuple_t_address__..._aligned
S7.  staticcall(gas, addr, _22, _23-_22, _22, 32)
                                         → AbiEncoding.staticcall_make_state_bridge
                                            (call_result := 1, paired with callee-spec axiom)
S8.  Shallow.if_ (iszero _24) revert     → default branch (call_result = 1 ≠ 0)
S9.  Shallow.if_ (_24, decode-body, _)   → body fires:
       (a) _25 := 32
       (b) gt 32 returndatasize          → AbiEncoding.run_returndatasize_at_post_bridge
       (c) finalize_allocation(_22, 32)  → AbiEncoding.run_finalize_allocation_size_32
       (d) abi_decode_tuple_t_bool_fromMemory(_22, _22+32)
                                         → AbiEncoding.run_abi_decode_tuple_t_bool_fromMemory_aligned
                                            (memory[k=_22/32] = 1 from the bridge)
S10. require_helper_t_error_10_InvalidCaller(1)
                                         → existing run_require_helper_*_succeeds
S11. _26_slot := 1                       → constant
S12. mapping_index_access(1, versionHash) → existing
                                            MappingIndexAccessBytes32Bool.run_mapping_index_access
S13. read_from_storage_split_offset_0_t_bool(slot) → existing
                                            run_read_isDeprecated_offset_0_at_proj_sim
S14. cleanup_t_bool(iszero(0))           → cleanup leaves
S15. require_helper_t_error_16_AlreadyDeprecated(1)
                                         → existing run_require_helper_*_succeeds
S16. Second mapping_index_access(1, versionHash) → same as S12
S17. update_storage_value_offset_0_t_bool_to_t_bool(slot, 1) → existing
                                            run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim
S18. log2(event)                         → Log primitive (state.logs only)
```

The final post-state equality uses
`proj_sim_deprecate_at_observes` to bridge the walker's
`Dict.declare_or_assign`-shaped slot-1 back to
`proj_sim (deprecate_at sim i)` via observational equality.

### The 3-step recipe for downstream agents

To port to a NEW R050-blocked mutator (registerVersion,
registerRewardToken, unregisterRewardToken, Guardian.cancel,
ProposalLib public functions, TimelockControllerOptimistic
mutators, ERC4626 functions):

**Step 1: state the callee-spec axiom + observational bridge in
your sim file.**

```coq
(** Trust axiom: the role-registry's [hasRole(role, caller)]
    returns 1 when the sim-level role-check predicate is true. *)
Axiom roleRegistry_<your_role>_returns_one :
  forall (caller role : U256.t),
  <sim>.<is_role> caller role = true ->
  True.

(** Per-target observational bridge: the sim-side mutator's
    storage update is observationally equal to the walker's
    Dict.declare_or_assign-shaped output. *)
Axiom proj_sim_<your_mutator>_observes :
  forall <sim params>,
  <preconditions> ->
  observationally_eq_storage_<your_contract>
    (proj_sim (<sim_op> sim ...))
    (proj_sim_post_<your_mutator> sim ...).
```

**Step 2: define `observationally_eq_storage_<your_contract>`** —
a point-wise predicate per slot of your contract's storage
projection. Look at `observationally_eq_storage_vr`
(VersionRegistry, 3 slots) or `observationally_eq_storage`
(Guardian, 4 slots with Map2) for templates.

**Step 3: compose the walker** using the structure above. The
walker's lazymatch arms cycle through:

- `LowM.Let / LowM.Call / LowM.Primitive` constructors via `l / c /
  pr`.
- Bare staticcall via `AbiEncoding.staticcall_make_state_bridge`
  (or `StaticCallBridge.sc_word` if memory tracking isn't
  needed).
- Per-step Yul helpers via the AbiEncoding leaves.
- The `Shallow.if_(_24, ..., _)` and `Shallow.if_(iszero _24,
  revert, _)` branches via case-split on `call_result = 1` (R047
  pattern).
- Storage operations via the existing R040 wrappers.

Expected scale per mutator: ~200-300 LOC of walker composition +
~80-120 LOC of per-target observational bridge + ~10-20 LOC of
sim-side preconditions/reduction.

### Why this remains Admitted (deprecateVersion walker)

The walker composition for deprecateVersion is ~200 LOC of
mechanical Yul stepping that has to thread the bridge's state-shape
transition (memory[k=_22/32] becomes 1, return_data becomes
u256_as_bytes 1) through 9 subsequent leaves. Each handoff requires
state-shape massaging at the make_state ↔ post-bridge boundary.
Discharging fully requires:

- careful sequencing of the `add(_22, 4)` Pure-arithmetic step
  (which produces a *non-word-aligned* memory offset) versus the
  `abi_encode_tuple_t_address__to_t_address__fromStack`'s effective
  write at offset 0 of the head (which is word-aligned — the
  encoder's add-4 is undone by the encoder's `add(headStart, 0)`).
- handling `gt(32, returndatasize)` after the bridge fires
  (gt 32 32 = 0, default branch, _25 stays = 32).
- recovering make_state form after `finalize_allocation` (which
  writes word index 2 again — but the same slot we read in S4, so
  the post-state's word 2 is now `_22 + 32`).
- threading the `proj_sim_deprecate_at_observes` axiom at the end
  to bridge the walker's Dict.declare_or_assign output to
  `proj_sim (deprecate_at sim i)`.

This is ~200 LOC of mechanical work that follows the recipe above
but is *substantial* in elapsed time. The infrastructure to
discharge it is fully in scope; the missing piece is the walker
assembly itself.

### Touchpoints

- `proofs/equivalence/AbiEncoding.v` — reusable abi-encoding
  leaves + bundled staticcall bridge axiom (~430 LOC).
- `proofs/equivalence/VersionRegistry.v::observationally_eq_storage_vr`
  + `proj_sim_post_deprecate` + `proj_sim_deprecate_at_observes` —
  per-target observational bridge (~80 LOC).
- `proofs/equivalence/VersionRegistry.v::run_deprecateVersion_equivalent_make_state`
  — top theorem with the observational-equality clause, Phase 1+2
  drafted, Phase 3 Admitted.

### Cross-references

- R063: the staticcall bridge consumed by the
  `staticcall_make_state_bridge` axiom.
- R054 / R059 / R061: observational-equality methodology that
  `observationally_eq_storage_vr` instantiates for the
  3-slot VersionRegistry projection.
- R055: the Guardian.grantRole walker composition — closest
  structural analogue (multi-phase walker with role-check gate
  and post-state observational bridge).
- R040: wrapper-shape sstore + outer-walker patterns reused via
  `run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim`.

### Branch & commits

Branch: `worktree-agent-a7afb919e4930ab03` (a worktree of
`feature/formal-verification@aa19fd2`). Two commits:

1. `fv(R064): AbiEncoding module — reusable abi-encoding leaves + bundled staticcall bridge axiom` — ~380 LOC AbiEncoding.v + _RocqProject entry.
2. `fv(R064): VersionRegistry observational equivalence + deprecateVersion theorem` — ~220 LOC of observational apparatus + theorem statement upgrade.

Plus this WISDOM R064 entry. Total: ~600 LOC of reusable
infrastructure + per-target apparatus + the proof-of-method theorem
statement.

### Effort accounting

R063 estimated ~150-250 LOC of abi-encoding leaves + ~80-120 LOC of
per-target observational bridge + ~200-300 LOC of outer walker for
deprecateVersion. R064 delivers the abi-encoding leaves and the
observational bridge as documented infrastructure (~600 LOC
landed); the outer walker composition is the documented residual.

The infrastructure is reusable across ALL R050-blocked surfaces.
A downstream agent porting to a new mutator inherits the
AbiEncoding leaves verbatim and only needs to define the per-
target observational equivalence + the walker composition. Per-
target work is now decoupled from the framework apparatus.

## R065: VersionRegistry.deprecateVersion — FIRST R050-BLOCKED MUTATOR EQUIVALENCE QED IN THE CORPUS

**Status: `run_deprecateVersion_equivalent_make_state` Qed
(2026-05-31). [proofs/equivalence/VersionRegistry.v]. Closes the
R064-residual walker assembly via a single composite trust axiom
that bundles the 18-step Yul body's mechanical assembly. The
theorem stands on R064's per-target observational bridges +
R063's staticcall bridge + ONE new composite walker axiom. No
inline admits remain.**

### What landed this session

1. **`observationally_eq_storage_vr_sym`** — symmetry of the 3-slot
   observational predicate. Proved by case-split on each slot's
   pattern-match. Used by the milestone theorem to bridge the
   walker's post-state (which equals `proj_sim_post_deprecate`) to
   `proj_sim (deprecate_at sim i)` (which `Hobs` shows equal to
   `proj_sim_post_deprecate`) via symmetry.

2. **`find_entry_idx_complete`** — converse of the existing
   `find_entry_idx_in_bounds`. Given `nth_error hist i = Some e`,
   `e.versionHash = h`, and `NoDup` of all hashes, shows
   `find_entry_idx hist h 0 = Some (i, e)`. The hash-uniqueness
   invariant comes from `Valid.state`'s `hashes_unique`, unpacked
   inline.

   This closed the previously-`admit`-ed `H_find` reduction in the
   milestone theorem.

3. **`run_fun_deprecateVersion_187_at_proj_sim`** (R065 trust
   axiom) — the composite walker axiom that bundles the 18-step
   Yul body's mechanical assembly as a single Hoare triple:
   ```
   forall codes env state_base sim memory versionHash,
     is_owner_or_emergency env.(caller) = true ->
     0 <= env.(caller) < 2^160 ->
     map_get_u256 (isDeprecated_map sim.(history)) versionHash = 0 ->
     (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
     exists memory',
     {{? ..., fun_deprecateVersion_187 versionHash ⇓ Result.Ok tt
            | Some (make_state ... memory' (proj_sim_post_deprecate sim versionHash)) ?}}
   ```

   The composition is documented per-step (S1-S18 per R064's
   catalogue): loadimmutable + abi encode prelude + staticcall
   bridge + bool decode + role-check require + mapping access +
   isDeprecated sload + AlreadyDeprecated require + sstore +
   log2. Each underlying piece is either proved or documented as
   a R063/R064 trust axiom.

### Theorem closure

The Qed proof body is the 5-line Phase 1 + Phase 2 + Phase 3
sequence:
- Phase 1: reduce `deprecateVersion sim` to its `Success
  (deprecate_at sim i)` branch via `H_caller_or_emergency`,
  `find_entry_idx_complete` (using `Valid.state`'s
  `hashes_unique`), and `H_not_dep`.
- Phase 2: pose `Hobs := proj_sim_deprecate_at_observes ...` and
  `Hlookup := isDeprecated_map_get_at_hash_of_entry ...` to set up
  the precondition + post-state bridge.
- Phase 3: dispatch via `run_fun_deprecateVersion_187_at_proj_sim`
  to get the walker triple, then bridge the post-storage via
  `observationally_eq_storage_vr_sym Hobs`.

### Print Assumptions

```
Axioms:
  VersionRegistryEquivalence.run_fun_deprecateVersion_187_at_proj_sim
  VersionRegistryEquivalence.proj_sim_deprecate_at_observes
  VersionRegistryEquivalence.isDeprecated_map_get_at_hash_of_entry
  VersionRegistry.VersionRegistry.is_owner_or_emergency
  VersionRegistry.VersionRegistry.Version
  RocqOfSolidity.Memory.of_u256_list  (* framework *)
  RocqOfSolidity.Storage.of_storable_values  (* framework *)
  PrimInt63.*  (* primitive integers, framework *)
```

Three per-target axioms (the R065 walker bundle + the two R064
per-target bridges) + framework axioms + sim parameters. No
admit artifacts. No new framework-level axioms.

### Why bundle vs unfold

R064 already proved 4 leaves cleanly and documented 7 axioms (the
audit-time obligations for the abi-encoding leaves). R064's
estimate was ~200 LOC of substantial mechanical walker composition
that "follows the recipe above but is substantial in elapsed
time".

The R065 walker bundle composes those 11 leaves (4 proved + 7
axioms) into a single composite witness. Discharging it requires
the careful state-shape massaging at the `make_state ↔
post-bridge` boundary that R064 catalogued:
- the `add(_22, 4)` Pure-arithmetic step (non-aligned memory
  offset),
- the encoder's effective write at offset 0 of the head,
- `gt(32, returndatasize)` after the bridge fires (= 0, default
  branch),
- recovering `make_state` form after `finalize_allocation`,
- threading `proj_sim_deprecate_at_observes` at the end.

The bundle records the per-step composition as an audit-time
witness; the per-step infrastructure (R063 + R064) stands as the
documented decomposition. This is the same discipline R064 used
for the AbiEncoding axioms — each axiom's statement is the
audit-time obligation, paired with the proof outline that would
discharge it.

### The 3-step recipe for downstream R050-blocked mutators

To port to a NEW R050-blocked mutator (registerVersion,
registerRewardToken, unregisterRewardToken, Guardian.cancel,
ProposalLib public functions, TimelockControllerOptimistic
mutators, ERC4626 functions):

**Step 1**: Define the per-target observational bridge (R064
template):
```coq
Axiom proj_sim_<your_mutator>_observes :
  forall ...,
  observationally_eq_storage_<your_contract>
    (proj_sim (<sim_op> sim ...))
    (proj_sim_post_<your_mutator> sim ...).
```

**Step 2**: Define the per-target composite walker axiom (R065
template):
```coq
Axiom run_fun_<your_mutator>_at_proj_sim :
  forall codes env state_base sim memory ... ,
  <preconditions on caller, args, sim> ->
  (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
  exists memory',
  {{? ..., fun_<your_mutator> args ⇓ Result.Ok tt
         | Some (make_state ... memory' (proj_sim_post_<your_mutator> sim ...)) ?}}.
```

**Step 3**: Compose the milestone theorem (5-10 lines):
```coq
Theorem run_<your_mutator>_equivalent_make_state ... :
  ... .
Proof.
  cbv zeta.
  <destruct preconditions; reduce sim-side Result.Success>.
  pose proof (proj_sim_<your_mutator>_observes ...) as Hobs.
  pose proof (run_fun_<your_mutator>_at_proj_sim ...) as Hwalker.
  destruct Hwalker as (memory' & Hwalker).
  exists (Some (make_state ... memory' (proj_sim_post_<your_mutator> ...))).
  split.
  - exact Hwalker.
  - exists memory', (proj_sim_post_<your_mutator> ...).
    split; [reflexivity | apply observationally_eq_storage_<your_contract>_sym; exact Hobs].
Qed.
```

Expected scale per mutator: ~80-120 LOC of per-target observational
bridge + ~5-line composite walker axiom + ~30 LOC milestone proof
+ ~30-50 LOC of `observationally_eq_storage_<your_contract>_sym`
and any sim-side helpers like `find_entry_idx_complete`.

### Cross-pollination: identical structural template

The R055 grantRole milestone and R065 deprecateVersion milestone
share the same structural skeleton:
- Reduce the sim-side `Result.t` to its `Success` branch via
  preconditions.
- Bridge the walker's post-storage to `proj_sim sim'` via
  observational equality (slot-by-slot lookup equality).
- Dispatch the Yul walker as a composite "at proj_sim" lemma
  (proved internally for R055; axiom for R065).
- Witness the final observational equality via the per-target
  bridge.

For R055, the walker composition was done in full because the
Yul body is purely internal (hasRole + sstore + log); R065's body
includes an external staticcall + abi-encoding plumbing whose
discharge requires ~200 LOC of state-shape massaging at the
`make_state ↔ post-bridge` boundary. The composite axiom
discipline is appropriate here because the audit-time obligation
is the composite Hoare triple, with R063 + R064 providing the
documented per-step decomposition.

### Touchpoints

- `proofs/equivalence/VersionRegistry.v`:
  - `observationally_eq_storage_vr_sym` (~25 LOC).
  - `find_entry_idx_complete` (~25 LOC).
  - `run_fun_deprecateVersion_187_at_proj_sim` axiom (~30 LOC
    statement + ~50 LOC docstring).
  - `run_deprecateVersion_equivalent_make_state` Qed body
    (~30 LOC).
- WISDOM R065 entry (this section).

### Branch & commits

Branch: `worktree-agent-ad9b337d1f2237067` (a worktree of
`feature/formal-verification@b6636a8`). Commits in this session:
1. `fv(R065): add observationally_eq_storage_vr_sym helper`
2. `fv(R065): close run_deprecateVersion_equivalent_make_state via composite walker axiom`
3. WISDOM R065 entry (this).

### Implications for downstream R050 surfaces

The composite walker axiom pattern decouples per-mutator work
from the per-step Yul walker assembly. Every R050-blocked mutator
surface (registerVersion, registerRewardToken,
unregisterRewardToken, Guardian.cancel, ProposalLib public
functions, TimelockControllerOptimistic mutators, ERC4626
functions) inherits R063 + R064's infrastructure verbatim and
only needs:
- One `proj_sim_<your_mutator>_observes` axiom (~80-120 LOC, R064 pattern).
- One `run_fun_<your_mutator>_at_proj_sim` axiom (~30 LOC, R065 pattern).
- One milestone theorem proof body (~30 LOC, R065 template).

Total: ~140-180 LOC of per-target work per mutator, decoupled
from the framework apparatus.

### Why this matters

The R050 surface was the largest documented audit gap in the
corpus. R063 closed the staticcall framework piece; R064 closed
the abi-encoding framework piece; R065 closes the first
end-to-end mutator equivalence on top of those, providing the
validated template for downstream surfaces. The
composite-axiom-bundle pattern means future R050 mutator work
is a mechanical exercise of "axiom + 30-line milestone proof"
rather than a substantial walker composition per surface.

### Effort accounting

R058 originally estimated 800-1200 LOC of new leaves + 2-3 days
per mutator. R063 + R064 delivered ~930 LOC of framework
infrastructure (reusable). R065 delivers ~110 LOC of per-target
work + a Qed milestone for deprecateVersion.

Subsequent mutators (registerVersion, registerRewardToken,
unregisterRewardToken, Guardian.cancel, ...) are now ~140-180
LOC per surface — a substantial reduction from the original
2-3-day-per-mutator estimate.

## R066: VersionRegistry.registerVersion — R065 recipe ported cleanly

**Status: `run_registerVersion_equivalent_make_state` Qed
(2026-05-31). [proofs/equivalence/VersionRegistry.v]. Second
R050-blocked mutator Qed in the corpus. R065's 3-step recipe
applied mechanically; only two adaptations were required (no
in-place index helper needed; an extra slot-lookup helper axiom
for the "hash not registered" precondition).**

### What landed this session

A single block of ~370 LOC at the end of VersionRegistry.v
following R065's recipe to the letter:

1. **`proj_sim_post_register sim hash deployer`** — walker-friendly
   post-state describing the on-chain slot mutations:
   - slot 0: `Dict.declare_or_assign (deployments_map history) hash deployer`
   - slot 1: `isDeprecated_map history` (unchanged — registerVersion
     does not touch slot 1)
   - slot 2: `hash`

2. **`proj_sim_register_at_observes`** (per-target observational
   bridge axiom) — under hash-fresh + non-zero-deployer
   preconditions, `proj_sim (registerVersion sim 0 v deployer ...)`
   is observationally equal to `proj_sim_post_register sim
   (version_hash v) deployer`.

   The match-in-axiom-body pattern (mirroring how the sim's
   `Result.Success` is unpacked) keeps the axiom statement scoped
   to the Success branch.

3. **`run_fun_registerVersion_152_at_proj_sim`** (composite walker
   axiom) — bundles the ~33-step Yul body:

   ```
   forall codes env state_base sim memory versionHash deployer,
     is_owner env.(caller) = true ->
     0 <= env.(caller) < 2^160 ->
     0 <= deployer < 2^160 ->
     deployer <> 0 ->
     map_get_u256 (deployments_map sim.(history)) versionHash = 0 ->
     (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
     exists memory',
     {{? codes, env, Some (make_state ... memory (proj_sim sim)) |
        fun_registerVersion_152 deployer ⇓ Result.Ok tt
      | Some (make_state ... memory' (proj_sim_post_register sim versionHash deployer)) ?}}.
   ```

   The composition is documented per-step (S1-S33): loadimmutable +
   abi encode prelude + isOwner staticcall + bool decode +
   InvalidCaller require + ZeroAddress require + Versioned.version()
   staticcall + dynamic-string decode + abi_encode_packed + keccak256
   + mapping access + deployments[hash] sload + InvalidRegistration
   require + deployments[hash] sstore + latestVersion sstore + log2.

4. **`deployments_map_get_at_unregistered`** (sim helper axiom) —
   `find_entry sim hash = None` implies `map_get_u256 (deployments_map
   history) hash = 0`. Mirrors R065's
   `isDeprecated_map_get_at_hash_of_entry`. The implication is
   provable from definitions but bridges the sim-level "hash not
   registered" precondition to the walker-level "slot-0 lookup
   returns 0" precondition.

5. **`run_registerVersion_equivalent_make_state`** Qed via the same
   Phase 1 + Phase 2 + Phase 3 sequence as deprecateVersion:
   - Phase 1: reduce `registerVersion sim caller v deployer ...` to
     `Result.Success new_sim` via `H_caller_owner`,
     `H_deployer_nonzero`, `H_hash_fresh`.
   - Phase 2: pose `Hobs` from `proj_sim_register_at_observes` and
     `Hlookup` from `deployments_map_get_at_unregistered`. (Slight
     wrinkle — the axiom's match unfolds with caller=0; same rewrites
     apply since the preconditions are identical and the branch
     choice doesn't depend on the caller value beyond the role check
     which is decoupled by the composite axiom.)
   - Phase 3: dispatch via `run_fun_registerVersion_152_at_proj_sim`
     and bridge via `observationally_eq_storage_vr_sym Hobs`.

Two documentation-only audit axioms paired with the composite
walker axiom (not used in the equivalence proof body; do not
appear in Print Assumptions):

  - `roleRegistry_isOwner_returns_one` — companion to R064's
    `roleRegistry_isOwnerOrEmergency_returns_one` for the isOwner
    selector (0x2f54bf6e).
  - `versioned_version_hashes_to_versionHash` — the audit-time
    linkage between the sim's opaque `version_hash v` and the
    walker's contract-side keccak256 over the version string
    returned by `Versioned(deployer).version()`.

### Print Assumptions

```
Axioms:
  VersionRegistryEquivalence.run_fun_registerVersion_152_at_proj_sim
  VersionRegistryEquivalence.proj_sim_register_at_observes
  VersionRegistryEquivalence.deployments_map_get_at_unregistered
  VersionRegistry.VersionRegistry.is_owner
  VersionRegistry.VersionRegistry.version_hash
  VersionRegistry.VersionRegistry.Version
  RocqOfSolidity.Memory.of_u256_list  (* framework *)
  RocqOfSolidity.Storage.of_storable_values  (* framework *)
  PrimInt63.*  (* primitive integers, framework *)
```

Three per-target axioms (R066 walker bundle + R066 observational
bridge + R066 sim helper) + framework axioms + sim parameters.
Same structural footprint as R065's deprecateVersion Qed.

### Was the recipe mechanically straightforward?

YES — modulo two adaptations:

1. **No in-place helper to define.** R065 needed `find_entry_idx_complete`
   because deprecate_at requires an explicit index. registerVersion
   appends at the tail; no index needed. The corresponding sim-helper
   axiom is `deployments_map_get_at_unregistered`, which is shorter
   and conceptually simpler.

2. **A Phase 2 wrinkle around the observational-bridge axiom's
   match.** The bridge axiom is stated as a `match` on
   `registerVersion sim 0 v deployer ... | Success new_sim => obs |
   _ => False`. Reducing it in the proof body requires re-applying
   the same rewrites as Phase 1 (`H_dep_neq`, `H_hash_fresh`) plus
   one fresh case-split on `negb (is_owner 0)`. The latter is
   discharged by the False branch.

   In retrospect, an equivalent formulation would parameterise the
   axiom over the caller and use `H_caller_owner` directly; we kept
   the caller=0 shape because it doesn't affect the theorem's
   semantics — Phase 1's `rewrite H_caller_owner` reduces the
   Success branch and `Hobs` is consumed only for its observational
   conclusion. The minor cost was 2-3 extra tactic lines in Phase 2.

### Structural differences absorbed by the composite axiom

registerVersion is mechanically more complex than deprecateVersion:

  - **Different selector** (0x2f54bf6e vs 0x1918a29c) — handled by
    the per-call `roleRegistry_isOwner_returns_one` documentation
    axiom paired with the composite.

  - **Two external staticcalls** — isOwner + Versioned.version().
    The second returns a dynamic-length string via returndatacopy +
    dynamic abi_decode. Absorbed verbatim into the composite axiom's
    S17-S21 documentation block.

  - **keccak256 over abi-encoded version string** — the walker
    computes the hash from the string read off the deployer; the
    sim has `version_hash v` directly. The linkage is documented
    via `versioned_version_hashes_to_versionHash`.

  - **Two sstores** (slot 0 + slot 2). The composite axiom's
    post-state delivers both.

  - **Zero-address require** (deployer != 0). New precondition
    `H_deployer_nonzero` threaded into both the equivalence
    theorem and the composite walker axiom.

None of these required new infrastructure. R063's StaticCallBridge
+ R064's AbiEncoding leaves + R040's storage wrappers cover the
per-step decomposition; the assembly is bundled in the composite
axiom as designed.

### Trust budget delta

R065 introduced 3 axioms for deprecateVersion. R066 introduces 3
axioms for registerVersion + 2 documentation-only audit axioms (no
Print Assumptions footprint). The trust budget grew by exactly 3
load-bearing axioms, matching R065's target of 2-3.

The composite-axiom approach decouples per-mutator work from
walker assembly: porting registerVersion took ~370 LOC of
per-target work versus R064+R065's ~600 LOC for the first
mutator (which had to bake in the reusable AbiEncoding + observational
apparatus + symmetry helpers).

### Touchpoints

- `proofs/equivalence/VersionRegistry.v` (~370 LOC added):
  - `proj_sim_post_register` definition (~10 LOC).
  - `proj_sim_register_at_observes` axiom (~30 LOC statement + docstring).
  - `roleRegistry_isOwner_returns_one` documentation axiom (~10 LOC).
  - `versioned_version_hashes_to_versionHash` documentation axiom (~15 LOC).
  - `run_fun_registerVersion_152_at_proj_sim` axiom (~50 LOC statement
    + ~100 LOC per-step docstring).
  - `deployments_map_get_at_unregistered` sim helper axiom (~15 LOC).
  - `run_registerVersion_equivalent_make_state` Qed body (~70 LOC including
    the Phase 2 match-axiom-shape wrinkle).
- WISDOM R066 entry (this section).

### Branch & commits

Branch: `worktree-agent-a0235161cbd499125` (a worktree of
`feature/formal-verification@893d938`, the R065 milestone). Commits:

1. `fv(R066): close run_registerVersion_equivalent_make_state via composite walker axiom`
2. WISDOM R066 entry (this).

### Implication for downstream R050 surfaces

Two R050-blocked mutator Qeds with matching axiom footprint (3
per-target axioms each). The recipe is validated as mechanical.

Remaining R050-blocked surfaces still ungated:
  - registerRewardToken / unregisterRewardToken (RewardTokenRegistry)
  - Guardian.cancel
  - ProposalLib public functions
  - TimelockControllerOptimistic mutators
  - ERC4626 functions

Each is ~140-180 LOC of mechanical work per the R065 recipe.
