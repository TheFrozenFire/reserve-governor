(** Task #235 — OpenZeppelin Checkpoints (Trace208) equivalence.

    Standalone sanity-check proof against the mock at
    [mocks/Trace208.v]. The natural target — binding the [push] /
    [upperLookupRecent] / [latest] entries of OZ's [Checkpoints.Trace208]
    to a shallow form derived from any consumer ([StakingVault]'s
    optimistic-vote checkpoint history, or the inherited [ERC20Votes]
    checkpoint storage) — is blocked by two upstream items:

      * R046 — [shallow_embed.py] drops the [sstore] body in the
        success arm of OZ mutators (the same generator bug that
        blocks the natural EnumerableSet binding via
        AccessControlEnumerable).
      * R035 — neither [StakingVault] nor [ERC20Votes] has a
        shallow form yet (both contracts are heavyweight enough
        that the generator hits independent issues even before
        R046 surfaces).

    Until both land, no equivalence-tier binding for the Trace208
    mutators is feasible.

    R048 — pure-function library variant of R045
    --------------------------------------------

    R045 captures the [with_X body] symbolic-expansion pattern for OZ
    *modifiers* and *precondition-shape* helpers — each call site
    expands into a wrapping or sequenced body, and the lemmas prove
    properties of that expansion. R048 (the EnumerableSet companion)
    documents a third shape: *pure-function libraries* (Solidity
    `library` keyword, all entries operate over a state reference
    passed in by the caller). At the Yul / shallow-form level, a
    consumer's call to [Checkpoints.push] expands as

      let prev_state = sload(...);   // the Trace208 storage slot(s)
      let res         = Checkpoints_push(prev_state, key, value);
      sstore(...);                    // commit the updated state

    rather than as a wrapping [with_X body] form. The "sanity check"
    for a pure-function library is therefore not a [with_X] wrapper
    but a set of standalone consistency theorems: that the mock's
    [push] / [upperLookupRecent] / [latest] / [Valid.t] obey the
    abstract checkpoint semantics callers will rely on. This file
    delivers that consistency proof — seven sanity-check theorems —
    all Qed.

    Each lemma cross-references the mock's existing primitive lemma
    where applicable; we do not re-prove from scratch.

    Once R046 + R035 are resolved upstream, a future equivalence-tier
    file will bind each call site to the mock's [push] /
    [upperLookupRecent] using R040 (wrapper-shape for sstore) + R033
    (PureEq for branches) + R036 (upfront-pose for evar scope) — same
    pattern as [proofs/equivalence/RewardTokenRegistry.v]'s
    [positions_map_aux] bridge. The lemmas below characterise the
    abstract semantics that binding will preserve. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.Trace208.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module CheckpointsEquivalence.

  Import Trace208.

  (** ----- 1. empty checkpoint history reads back as zero -----

      OZ surface: [Trace208.latest()] on an empty trace returns 0
      (Checkpoints.sol:97-100: [pos == 0 ? 0 : ...]).
      OZ surface: [Trace208.upperLookupRecent(k)] on an empty trace
      returns 0 (Checkpoints.sol:74-92: [pos == 0 ? 0 : ...]).

      Direct computational identity on the mock. *)
  Lemma empty_latest_is_zero :
    latest empty = 0.
  Proof. reflexivity. Qed.

  Lemma empty_lookup_is_zero :
    forall (k : U256.t),
      upperLookupRecent empty k = 0.
  Proof. intro k. reflexivity. Qed.

  (** ----- 2. push then latest reads back the pushed value -----

      OZ surface: pushing [(key, value)] with [key > last_key]
      appends a new checkpoint; [latest()] then returns [value]
      (Checkpoints.sol::_insert append branch + Checkpoints.sol:97).

      Cross-references the mock's [latest_after_push]. *)
  Lemma push_monotone_then_latest :
    forall (tr : t) (k v : U256.t),
      (match tr.(entries) with
       | [] => True
       | _  => fst (last_entry tr.(entries)) < k
       end) ->
      latest (push tr k v) = v.
  Proof. exact latest_after_push. Qed.

  (** ----- 3. upperLookupRecent below the first key returns 0 -----

      OZ surface: the binary search in [_upperBinaryLookup] returns
      [pos = 0] when no checkpoint has key <= query, and the wrapper
      returns 0 in that case (Checkpoints.sol:91).

      Cross-references the mock's [upperLookupRecent_returns_0_below_first].
      Requires [Valid.t] (sortedness) to discharge the "all keys are
      > q" obligation. *)
  Lemma upper_lookup_below_first_is_zero :
    forall (tr : t) (q : U256.t),
      Valid.t tr ->
      match tr.(entries) with
      | [] => True
      | (k0, _) :: _ => q < k0
      end ->
      upperLookupRecent tr q = 0.
  Proof. exact upperLookupRecent_returns_0_below_first. Qed.

  (** ----- 4. latest agrees with upperLookupRecent at the last key -----

      OZ surface: querying [upperLookupRecent] at exactly the last
      stored key returns the value of that last checkpoint, which
      [latest()] also returns (Checkpoints.sol:74-92 vs :97-100).

      Cross-references the mock's [latest_eq_upperLookup_at_last_key]. *)
  Lemma latest_equals_upper_lookup_at_last_key :
    forall (tr : t),
      Valid.t tr ->
      match tr.(entries) with
      | [] => True
      | _  => upperLookupRecent tr (fst (last_entry tr.(entries))) =
              latest tr
      end.
  Proof. exact latest_eq_upperLookup_at_last_key. Qed.

  (** ----- 5. upperLookupRecent above the last key returns latest -----

      OZ surface: queries above the last key fall through to the last
      checkpoint and return [latest()] — the binary search reaches
      [pos = len], so [pos - 1] indexes the final entry whose value
      is [latest()].

      We prove the closed-form analog on the worked example from
      [Examples] for the headline shape — the [tr_demo] trace has
      last key 300, and querying at 500 returns the value at 300
      (which equals [latest]). *)
  Lemma upper_lookup_above_last_returns_latest_example :
    upperLookupRecent Examples.tr_demo 500 = latest Examples.tr_demo.
  Proof. vm_compute. reflexivity. Qed.

  (** ----- 6. push_checked reverts on key regression -----

      OZ surface: [_insert] reverts with [CheckpointUnorderedInsertion]
      when [key < last_key] (Checkpoints.sol::_insert require). The
      mock's [push_checked] returns [None] in this case
      (mocks/Trace208.v:122-133), while the relaxed [push] silently
      overwrites — the audit-flagged fidelity gap.

      Cross-references the mock's [push_checked_reverts_below_last]. *)
  Lemma push_checked_reverts_on_regression :
    forall (tr : t) (k v : U256.t),
      (match tr.(entries) with
       | [] => False
       | _  => k < fst (last_entry tr.(entries))
       end) ->
      push_checked tr k v = None.
  Proof. exact push_checked_reverts_below_last. Qed.

  (** ----- 7. push preserves the sortedness invariant -----

      OZ surface: the [_insert] path either appends (when key is
      strictly greater than the last) or overwrites in place at
      equal-key — both preserve the [Trace*]'s implicit invariant
      that checkpoint keys are strictly ascending. The mock's
      [Valid.t] encodes that invariant; the lemma below certifies
      its preservation across [push].

      Cross-references the mock's [push_preserves_sortedness]. *)
  Lemma push_preserves_valid :
    forall (tr : t) (k v : U256.t),
      Valid.t tr ->
      (match tr.(entries) with
       | [] => True
       | _  => fst (last_entry tr.(entries)) <= k
       end) ->
      Valid.t (push tr k v).
  Proof. exact push_preserves_sortedness. Qed.

End CheckpointsEquivalence.
