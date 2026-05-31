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

**Status: blocks ALL OZ AccessControl mutator-equivalence proofs.**

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
emits `1e18` while the other emits `Z.min 1e18 raw`). R046 fixes
the *control-mode* divergence (one arm `Leave`s while the other
`Tt`s). The two are independent.

If a switch's body has BOTH kinds of divergence (different modes
AND different value shapes that need PureEq to bridge), apply R046
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
  bug is fixed (see R045). The case-split-first pattern remains
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
