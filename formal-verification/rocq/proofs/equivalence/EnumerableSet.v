(** Task #232 — OpenZeppelin EnumerableSet equivalence (foundation tier).

    Standalone sanity-check proof against the mock at
    [mocks/EnumerableSet.v]. The natural target — binding the [_add],
    [_remove], [_contains] internal helpers of OZ's
    [EnumerableSet.Bytes32Set] / [.AddressSet] to a shallow form
    derived from any consumer (e.g. [AccessControlEnumerable] or the
    open-coded set-with-positions idiom in [RewardTokenRegistry]) —
    is blocked by WISDOM R046: [shallow_embed.py] drops the [sstore]
    body in the success arm of OZ mutators (the same generator bug
    that blocks [_grantRole] / [_revokeRole] / [_setRoleAdmin]).
    Until that lands upstream, no equivalence-tier binding for the
    EnumerableSet mutators is feasible.

    R045 — variant for pure-function libraries
    ------------------------------------------

    R045 documents the [with_X] symbolic-expansion pattern for OZ
    *modifiers* (e.g. [nonReentrant]) and *precondition-shape* helpers
    (e.g. [_useCheckedNonce]). Each call site expands into a wrapping
    or sequenced body and the lemmas prove properties of that
    expansion against the surrounding state. EnumerableSet does not
    fit either shape — it is a pure-function library (`library`
    keyword in Solidity, with operations over a `Set storage`
    reference passed in by the caller). At the Yul / shallow-form
    level, a call site looks like

      let prev_state = sload(...);   // _values length / _positions[v]
      let res         = EnumerableSet_add(prev_state, value);
      sstore(...);                    // commit the updated state

    rather than a wrapping `with_X body` form. The "sanity check" for
    a pure-function library is therefore not a [with_X] wrapper but a
    set of standalone consistency theorems: that the mock's
    [add] / [remove] / [contains] / [length] / [at_index] obey the
    abstract set semantics callers will rely on. This file delivers
    that consistency proof — five sanity-check theorems plus two
    helpers — all Qed.

    Once R046 is fixed upstream, a future equivalence-tier file will
    bind each call site to the mock's [add] / [remove] using
    R040 (wrapper-shape for sstore) + R033 (PureEq for branches) +
    R036 (upfront-pose for evar scope) — same pattern as
    [proofs/equivalence/RewardTokenRegistry.v]'s [positions_map_aux]
    bridge. The lemmas below characterise the abstract semantics that
    binding will preserve. *)

Require Import ReserveGovernor.mocks.EnumerableSet.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module EnumerableSetEquivalence.

  Import EnumerableSet.
  Import EnumerableSet.Bytes32Set.

  (** ----- 1. add inserts and is observable via contains -----

      The classic "set add post-condition": adding [x] to [s] yields
      a state in which [contains _ x = true]. *)
  Lemma contains_after_add_is_true :
    forall (s : t) (x : elt),
      contains (fst (add s x)) x = true.
  Proof.
    intros s x.
    unfold add.
    destruct (contains s x) eqn:Hc; simpl.
    - exact Hc.
    - apply contains_true_iff_In.
      apply in_or_app. right. left. reflexivity.
  Qed.

  (** ----- 2. remove idempotent on absent + add inserts -----

      Composing [remove] then [add] on an absent element collapses
      [remove] to a no-op and then [add] inserts. The composition
      witnesses that the mock's [remove]/[add] interact via
      [contains] as expected — when the element is absent, [remove]
      doesn't break anything that [add] then needs to do. *)
  Lemma add_remove_inverts_when_absent :
    forall (s : t) (x : elt),
      contains s x = false ->
      let (s1, _) := remove s x in
      fst (add s1 x) = s ++ [x].
  Proof.
    intros s x Hc.
    rewrite (remove_idempotent_on_absent _ _ Hc).
    simpl. rewrite (add_inserts_when_absent _ _ Hc). reflexivity.
  Qed.

  (** ----- 3. length grows strictly with add of new element -----

      Direct re-export of the mock's [length_after_add_absent] under
      a more domain-flavored name. *)
  Lemma length_grows_strictly_with_add_of_new :
    forall (s : t) (x : elt),
      contains s x = false ->
      length (fst (add s x)) = length s + 1.
  Proof. apply length_after_add_absent. Qed.

  (** ----- 4. length unchanged on add of present (idempotency) ----- *)
  Lemma length_unchanged_on_add_of_present :
    forall (s : t) (x : elt),
      contains s x = true ->
      length (fst (add s x)) = length s.
  Proof. apply length_after_add_present. Qed.

  (** ----- 5. length decreases by 1 after successful remove ----- *)
  Lemma length_after_successful_remove :
    forall (s : t) (x : elt) (s' : t),
      remove s x = (s', true) ->
      length s' = length s - 1.
  Proof.
    intros s x s' Hr.
    assert (Hne : s <> []).
    { intro He. subst s. unfold remove in Hr. simpl in Hr. discriminate. }
    unfold length.
    rewrite (length_after_remove_present s x s' Hr).
    destruct s as [|y rest]; [contradiction|].
    simpl Datatypes.length. simpl Nat.pred. lia.
  Qed.

  (** ----- 6. at_index returns Some iff index is in bounds -----

      The standalone iff form combining [at_index_in_bounds] and
      [at_index_out_of_bounds]. Witnesses that the mock's bounded
      access matches OZ's [_at] requirement
      ([index] < [_length(set)]). *)
  Lemma at_index_some_iff_in_bounds :
    forall (s : t) (i : Z),
      (exists v, at_index s i = Some v) <-> 0 <= i < length s.
  Proof.
    intros s i. split.
    - intros [v Hv].
      destruct (Z_le_dec 0 i) as [Hlo|Hlo].
      + destruct (Z_lt_dec i (length s)) as [Hhi|Hhi].
        * split; assumption.
        * exfalso.
          rewrite at_index_out_of_bounds in Hv by (intros [_ ?]; contradiction).
          discriminate.
      + exfalso.
        rewrite at_index_out_of_bounds in Hv by (intros [? _]; contradiction).
        discriminate.
    - intro Hb. apply at_index_in_bounds. exact Hb.
  Qed.

  (** ----- 7. position_of nonzero iff contains true -----

      OZ's [_contains] is implemented as [positions[v] != 0]. This
      lemma certifies that boolean check against the
      list-membership-based [contains], proving the [_positions] map
      is faithful to the [_values] array under the standing invariant.
      The R046 generator bug is exactly the missing sstore that would
      have established this invariant after a mutator runs; the
      mock-level direction is sound. *)
  Lemma position_of_nonzero_iff_contains :
    forall (s : t) (x : elt),
      position_of s x <> 0 <-> contains s x = true.
  Proof.
    intros s x.
    split; intro H.
    - destruct (contains s x) eqn:Hc; [reflexivity|].
      exfalso. apply H. apply position_of_zero_iff_contains_false. exact Hc.
    - intro Hz. apply position_of_zero_iff_contains_false in Hz. congruence.
  Qed.

End EnumerableSetEquivalence.
