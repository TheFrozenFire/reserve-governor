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
