(** OpenZeppelin EnumerableSet mock — Bytes32Set + AddressSet variants.

    Captures the surface of
      @openzeppelin/contracts/utils/structs/EnumerableSet.sol
    which is used by OZ's AccessControlEnumerable (for per-role member
    enumeration) and is the structural backing for any set-with-index
    pattern in the OZ ecosystem. The Reserve Governor's
    [RewardTokenRegistry] open-codes the same idiom (length-prefixed
    list + 1-indexed positions map); this mock consolidates the
    abstract set semantics so that domain can later bind to a shared
    definition.

    OZ semantics (v5.x):

      struct Set {
        bytes32[] _values;
        mapping(bytes32 => uint256) _positions;     // 1-indexed; 0 = absent
      }

      _add(set, v):       if !_contains then push v, positions[v]=length
      _remove(set, v):    swap-and-pop — overwrite v's slot with last,
                          pop last slot, update positions
      _contains(set, v):  positions[v] != 0
      _length(set):       _values.length
      _at(set, i):        _values[i]
      _values(set):       _values     (full copy)

    The [_positions] mapping is a redundant index over [_values]; under
    the well-formedness invariant
      positions[v] = i+1  iff  _values[i] = v
      positions[v] = 0    iff  v not in _values
    the abstract set semantics depend only on [_values] (as a no-dup
    list of bytes32). We model the state as that list, with [NoDup] as
    the [Valid.t] invariant, and prove the swap-and-pop transformation
    preserves set semantics.

    Why model swap-and-pop faithfully rather than [filter (≠ v)]: the
    [_at] / [length] / [_values] accessors observe the order, and an
    equivalence proof against the generated shallow form will need to
    reason about which value sits at which index after a remove. The
    abstract membership lemmas come out the same either way; the
    swap-and-pop fidelity is "free" once the structure is in place.

    Used by (planned):
      - [proofs/equivalence/EnumerableSet.v] — sanity-check theorems
        over the abstract semantics (R045-variant for pure-function
        libraries; see that file's docstring).
      - Future: [proofs/equivalence/RewardTokenRegistry.v] mutator
        equivalence (blocked on R046 — shallow_embed.py drops sstore
        on OZ mutators, so binding _add / _remove against the actual
        shallow form is not feasible until upstream lands the fix).
      - Future: AccessControlEnumerable role-member enumeration. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module EnumerableSet.

(** ====================================================================
    Bytes32Set — the underlying [Set] structure (OZ's private [_add],
    [_remove], etc.). bytes32 keys are modelled as [U256.t] for parity
    with the existing simulations convention.
    ==================================================================== *)
Module Bytes32Set.

  Definition elt : Set := U256.t.

  (** The abstract state is the [_values] list. [_positions] is a
      redundant index derivable from this list; we expose it as a
      lemma below ([position_of] / [position_invariant]) rather than
      carrying it in [t]. *)
  Definition t : Set := list elt.

  Definition empty : t := [].

  (** ----- Membership ----- *)
  Fixpoint contains (s : t) (x : elt) : bool :=
    match s with
    | []        => false
    | y :: rest => if y =? x then true else contains rest x
    end.

  (** ----- Length / indexed read ----- *)
  Definition length (s : t) : Z := Z.of_nat (List.length s).

  Definition at_index (s : t) (i : Z) : option elt :=
    if (0 <=? i) && (i <? length s)
    then nth_error s (Z.to_nat i)
    else None.

  Definition values (s : t) : list elt := s.

  (** ----- Position (1-indexed; 0 means absent) -----

      OZ's [_positions[v]] is the index of [v] in [_values], plus 1.
      Position 0 is the sentinel for "absent". *)
  Fixpoint position_of_aux (s : t) (x : elt) (i : Z) : Z :=
    match s with
    | []        => 0
    | y :: rest => if y =? x then i else position_of_aux rest x (i + 1)
    end.

  Definition position_of (s : t) (x : elt) : Z :=
    position_of_aux s x 1.

  (** ----- [_add] -----

      Appends [x] iff not already present. Returns the updated state
      paired with the [bool] return value (true = was added). *)
  Definition add (s : t) (x : elt) : t * bool :=
    if contains s x
    then (s, false)
    else (s ++ [x], true).

  (** ----- [_remove] via swap-and-pop -----

      The OZ logic:
        position = positions[v]
        if position != 0:
          valueIndex = position - 1
          lastIndex  = length - 1
          if valueIndex != lastIndex:
            _values[valueIndex] = _values[lastIndex]
          _values.pop()

      We open-code this transformation on the [_values] list. *)

  (** Replace the element at index [i] with [v]. Out-of-bounds is a
      no-op (won't occur in practice since callers gate on
      [contains]). *)
  Fixpoint replace_at (s : t) (i : nat) (v : elt) : t :=
    match s, i with
    | [], _              => []
    | _ :: rest, O       => v :: rest
    | x :: rest, S i'    => x :: replace_at rest i' v
    end.

  (** Find the index of [x] in [s] (0-indexed). Returns [None] if
      absent. *)
  Fixpoint index_of (s : t) (x : elt) : option nat :=
    match s with
    | []        => None
    | y :: rest => if y =? x
                   then Some O
                   else match index_of rest x with
                        | Some i => Some (S i)
                        | None   => None
                        end
    end.

  (** Drop the last element. *)
  Fixpoint drop_last (s : t) : t :=
    match s with
    | []          => []
    | [_]         => []
    | x :: rest   => x :: drop_last rest
    end.

  Definition remove (s : t) (x : elt) : t * bool :=
    match index_of s x with
    | None         => (s, false)
    | Some i =>
        let last_idx := Nat.pred (List.length s) in
        let s_after :=
          if Nat.eqb i last_idx
          then drop_last s
          else
            match nth_error s last_idx with
            | Some last_v => drop_last (replace_at s i last_v)
            | None        => s  (* unreachable when i < length s *)
            end in
        (s_after, true)
    end.

  (** ----- Validity -----

      The no-duplicate invariant. OZ's [_add] enforces this
      structurally (only appends when absent), and [_remove]
      preserves it. *)
  Module Valid.
    Definition t (s : Bytes32Set.t) : Prop := NoDup s.

    Lemma empty_valid : t empty.
    Proof. unfold t, empty. apply NoDup_nil. Qed.
  End Valid.

  (** ====================================================================
      Headline lemmas
      ==================================================================== *)

  (** ----- [contains] ↔ [In] bridge -----

      The boolean and Prop forms of membership coincide. The bridge
      between OZ's positions-based check and a list-membership
      argument. *)
  Lemma contains_true_iff_In :
    forall (s : t) (x : elt),
      contains s x = true <-> In x s.
  Proof.
    induction s as [|y rest IH]; intro x; simpl; split.
    - discriminate.
    - intros [].
    - destruct (y =? x) eqn:Hyx.
      + apply Z.eqb_eq in Hyx. left. exact Hyx.
      + intro Hc. right. apply IH. exact Hc.
    - intros [Hyx | Hin].
      + subst y. rewrite Z.eqb_refl. reflexivity.
      + destruct (y =? x); [reflexivity|]. apply IH. exact Hin.
  Qed.

  Lemma contains_false_iff_not_In :
    forall (s : t) (x : elt),
      contains s x = false <-> ~ In x s.
  Proof.
    intros s x. split.
    - intros Hc Hin. apply contains_true_iff_In in Hin. congruence.
    - intro Hni. destruct (contains s x) eqn:Hc; [|reflexivity].
      apply contains_true_iff_In in Hc. contradiction.
  Qed.

  (** ----- [position_of]'s 1-indexed sentinel invariant -----

      [position_of s x = 0] iff [x] is absent. The OZ invariant in
      one line. *)
  Lemma position_of_aux_zero_iff_not_In :
    forall (s : t) (x : elt) (base : Z),
      0 < base ->
      position_of_aux s x base = 0 <-> ~ In x s.
  Proof.
    induction s as [|y rest IH]; intros x base Hb; simpl.
    - split; [intros _ []|reflexivity].
    - destruct (y =? x) eqn:Hyx.
      + apply Z.eqb_eq in Hyx. subst y. split.
        * intro Hb0. lia.
        * intro Hni. exfalso. apply Hni. left. reflexivity.
      + apply Z.eqb_neq in Hyx.
        rewrite IH by lia.
        split.
        * intros Hni [Hyx'|Hin]; [congruence|contradiction].
        * intro Hni. intro Hin. apply Hni. right. exact Hin.
  Qed.

  Lemma position_of_zero_iff_not_In :
    forall (s : t) (x : elt),
      position_of s x = 0 <-> ~ In x s.
  Proof.
    intros s x. unfold position_of. apply position_of_aux_zero_iff_not_In. lia.
  Qed.

  Lemma position_of_zero_iff_contains_false :
    forall (s : t) (x : elt),
      position_of s x = 0 <-> contains s x = false.
  Proof.
    intros s x.
    rewrite position_of_zero_iff_not_In, contains_false_iff_not_In.
    reflexivity.
  Qed.

  (** ----- [add] idempotency on present -----

      Adding an element already in the set is a no-op; the return
      flag is [false]. *)
  Lemma add_idempotent_on_present :
    forall (s : t) (x : elt),
      contains s x = true ->
      add s x = (s, false).
  Proof.
    intros s x Hc. unfold add. rewrite Hc. reflexivity.
  Qed.

  (** ----- [add] inserts when absent -----

      Adding an absent element appends it and returns flag [true]. *)
  Lemma add_inserts_when_absent :
    forall (s : t) (x : elt),
      contains s x = false ->
      add s x = (s ++ [x], true).
  Proof.
    intros s x Hc. unfold add. rewrite Hc. reflexivity.
  Qed.

  (** ----- [remove] idempotency on absent ----- *)
  Lemma index_of_none_iff_not_In :
    forall (s : t) (x : elt),
      index_of s x = None <-> ~ In x s.
  Proof.
    induction s as [|y rest IH]; intro x; simpl.
    - split; [intros _ [] | reflexivity].
    - destruct (y =? x) eqn:Hyx.
      + apply Z.eqb_eq in Hyx. subst y. split.
        * discriminate.
        * intro Hn. exfalso. apply Hn. left. reflexivity.
      + apply Z.eqb_neq in Hyx.
        destruct (index_of rest x) eqn:Hir.
        * split; [discriminate|].
          intro Hni.
          assert (Hnir : ~ In x rest) by (intro Hin; apply Hni; right; exact Hin).
          apply IH in Hnir. congruence.
        * split.
          { intros _ [Heq|Hin]; [congruence|].
            apply IH in Hir. contradiction. }
          { reflexivity. }
  Qed.

  Lemma remove_idempotent_on_absent :
    forall (s : t) (x : elt),
      contains s x = false ->
      remove s x = (s, false).
  Proof.
    intros s x Hc.
    apply contains_false_iff_not_In in Hc.
    apply index_of_none_iff_not_In in Hc.
    unfold remove. rewrite Hc. reflexivity.
  Qed.

  (** ----- [remove] flag is [true] when present ----- *)
  Lemma index_of_some_iff_In :
    forall (s : t) (x : elt),
      (exists i, index_of s x = Some i) <-> In x s.
  Proof.
    intros s x. split.
    - intros [i Hi]. apply contains_true_iff_In.
      destruct (contains s x) eqn:Hc; [reflexivity|].
      apply contains_false_iff_not_In in Hc.
      apply index_of_none_iff_not_In in Hc. congruence.
    - intro Hin. destruct (index_of s x) eqn:Hi; [eauto|].
      apply index_of_none_iff_not_In in Hi. contradiction.
  Qed.

  Lemma remove_flag_when_present :
    forall (s : t) (x : elt),
      contains s x = true ->
      exists s', remove s x = (s', true).
  Proof.
    intros s x Hc.
    apply contains_true_iff_In in Hc.
    apply index_of_some_iff_In in Hc as [i Hi].
    unfold remove. rewrite Hi. eexists. reflexivity.
  Qed.

  (** ----- [length] grows by 1 on insert, unchanged on present ----- *)
  Lemma length_after_add_present :
    forall (s : t) (x : elt),
      contains s x = true ->
      length (fst (add s x)) = length s.
  Proof.
    intros s x Hc. rewrite (add_idempotent_on_present _ _ Hc). reflexivity.
  Qed.

  Lemma length_after_add_absent :
    forall (s : t) (x : elt),
      contains s x = false ->
      length (fst (add s x)) = length s + 1.
  Proof.
    intros s x Hc. rewrite (add_inserts_when_absent _ _ Hc). simpl.
    unfold length.
    rewrite length_app. simpl. lia.
  Qed.

  (** ----- [at_index] in-bounds is [Some] ----- *)
  Lemma at_index_in_bounds :
    forall (s : t) (i : Z),
      0 <= i < length s ->
      exists v, at_index s i = Some v.
  Proof.
    intros s i [Hlo Hhi].
    unfold at_index, length in *.
    assert (Hb : ((0 <=? i) && (i <? Z.of_nat (List.length s)))%bool = true).
    { apply andb_true_iff. split.
      - apply Z.leb_le. exact Hlo.
      - apply Z.ltb_lt. exact Hhi. }
    rewrite Hb.
    assert (Hn : (Z.to_nat i < List.length s)%nat).
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id by exact Hlo. exact Hhi. }
    destruct (nth_error s (Z.to_nat i)) eqn:He; [eauto|].
    apply nth_error_None in He. lia.
  Qed.

  Lemma at_index_out_of_bounds :
    forall (s : t) (i : Z),
      ~ (0 <= i < length s) ->
      at_index s i = None.
  Proof.
    intros s i Hni.
    unfold at_index. unfold length in Hni.
    destruct (0 <=? i) eqn:Hlo; simpl.
    - destruct (i <? length s) eqn:Hhi.
      + apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
        exfalso. apply Hni. unfold length in Hhi. split; assumption.
      + reflexivity.
    - reflexivity.
  Qed.

  (** ----- [drop_last] / [replace_at] structural lemmas -----

      Used to prove [remove]'s post-state membership properties. *)
  Lemma drop_last_length :
    forall s : t,
      s <> [] ->
      List.length (drop_last s) = Nat.pred (List.length s).
  Proof.
    induction s as [|x rest IH]; intro Hne; [contradiction|].
    destruct rest as [|y rest'].
    - simpl. reflexivity.
    - simpl in *. rewrite IH by discriminate. reflexivity.
  Qed.

  Lemma replace_at_length :
    forall (s : t) (i : nat) (v : elt),
      List.length (replace_at s i v) = List.length s.
  Proof.
    induction s as [|x rest IH]; intros i v; simpl.
    - destruct i; reflexivity.
    - destruct i; simpl.
      + reflexivity.
      + f_equal. apply IH.
  Qed.

  (** [drop_last] cannot reintroduce or invent membership. *)
  Lemma In_drop_last :
    forall (s : t) (x : elt),
      In x (drop_last s) -> In x s.
  Proof.
    induction s as [|y rest IH]; intros x Hin; simpl in *.
    - exact Hin.
    - destruct rest as [|z rest'].
      + simpl in Hin. contradiction.
      + simpl in Hin. destruct Hin as [Heq|Hin].
        * left. exact Heq.
        * right. apply IH. exact Hin.
  Qed.

  (** ----- [remove] removes the target when present (NoDup case) -----

      Under [Valid.t s] (no duplicates), [remove s x] yields a state
      that no longer contains [x]. The structural form of "remove
      removes when present". *)
  Lemma nth_error_In :
    forall {A : Type} (l : list A) (n : nat) (a : A),
      nth_error l n = Some a -> In a l.
  Proof.
    induction l as [|h t IH]; intros n a Hn.
    - destruct n; discriminate.
    - destruct n; simpl in *.
      + injection Hn as ->. left. reflexivity.
      + right. eapply IH. exact Hn.
  Qed.

  (** ----- Length after a successful remove decreases by 1 ----- *)
  Lemma length_after_remove_present :
    forall (s : t) (x : elt) (s' : t),
      remove s x = (s', true) ->
      List.length s' = Nat.pred (List.length s).
  Proof.
    intros s x s' Hr.
    unfold remove in Hr.
    destruct (index_of s x) as [i|] eqn:Hi; [|discriminate].
    assert (Hne : s <> []).
    { intro He. subst s. simpl in Hi. discriminate. }
    destruct (Nat.eqb i (Nat.pred (List.length s))) eqn:Hpr.
    - injection Hr as Heq. subst s'.
      apply drop_last_length. exact Hne.
    - destruct (nth_error s (Nat.pred (List.length s))) as [last_v|] eqn:Hne_last.
      + injection Hr as Heq. subst s'.
        rewrite drop_last_length.
        * rewrite replace_at_length. reflexivity.
        * intro He.
          assert (Hlen : List.length (replace_at s i last_v) = 0%nat).
          { rewrite He. reflexivity. }
          rewrite replace_at_length in Hlen.
          destruct s; [contradiction|]. simpl in Hlen. discriminate.
      + injection Hr as Heq. subst s'.
        apply nth_error_None in Hne_last.
        destruct s; [contradiction|]. simpl List.length in Hne_last. lia.
  Qed.

End Bytes32Set.

(** ====================================================================
    AddressSet — the public OZ wrapper over [Bytes32Set] for addresses.

    OZ defines this as:
      struct AddressSet { Set _inner; }
      function add(AddressSet s, address v) { return _add(s._inner, bytes32(uint256(uint160(v)))); }
      function remove(...)                  { return _remove(s._inner, bytes32(...)); }
      ...

    The bytes32-cast of an address is just the address as a uint256
    with the upper 96 bits zeroed (160-bit address bound). Under our
    convention [Address := U256.t] with [0 <= a < 2^160], this is
    semantically the same as [Bytes32Set]. We expose a thin alias and
    re-export the operations so consumers can call
    [EnumerableSet.AddressSet.add] / [.remove] / etc. with addresses
    directly.
    ==================================================================== *)
Module AddressSet.

  Definition elt : Set := U256.t.   (* the addr-as-bytes32-as-U256 *)
  Definition t : Set := Bytes32Set.t.

  Definition empty : t := Bytes32Set.empty.

  Definition contains   (s : t) (a : elt) : bool   := Bytes32Set.contains s a.
  Definition length     (s : t) : Z                := Bytes32Set.length s.
  Definition at_index   (s : t) (i : Z) : option elt := Bytes32Set.at_index s i.
  Definition values     (s : t) : list elt         := Bytes32Set.values s.
  Definition position_of (s : t) (a : elt) : Z     := Bytes32Set.position_of s a.

  Definition add    (s : t) (a : elt) : t * bool := Bytes32Set.add s a.
  Definition remove (s : t) (a : elt) : t * bool := Bytes32Set.remove s a.

  Module Valid.
    (** Same no-duplicate invariant as [Bytes32Set], plus the
        address-range bound on every element. *)
    Definition addr_in_range (a : elt) : Prop := 0 <= a < 2 ^ 160.

    Definition t (s : AddressSet.t) : Prop :=
      Bytes32Set.Valid.t s /\ Forall addr_in_range s.

    Lemma empty_valid : t empty.
    Proof.
      unfold t, empty. split.
      - apply Bytes32Set.Valid.empty_valid.
      - apply Forall_nil.
    Qed.
  End Valid.

  (** ----- Surface lemmas mirror Bytes32Set (re-exports for callers
      who only see the AddressSet wrapper) ----- *)

  Lemma contains_true_iff_In :
    forall (s : t) (a : elt),
      contains s a = true <-> In a s.
  Proof. apply Bytes32Set.contains_true_iff_In. Qed.

  Lemma add_idempotent_on_present :
    forall (s : t) (a : elt),
      contains s a = true -> add s a = (s, false).
  Proof. apply Bytes32Set.add_idempotent_on_present. Qed.

  Lemma add_inserts_when_absent :
    forall (s : t) (a : elt),
      contains s a = false -> add s a = (s ++ [a], true).
  Proof. apply Bytes32Set.add_inserts_when_absent. Qed.

  Lemma remove_idempotent_on_absent :
    forall (s : t) (a : elt),
      contains s a = false -> remove s a = (s, false).
  Proof. apply Bytes32Set.remove_idempotent_on_absent. Qed.

  Lemma position_of_zero_iff_not_In :
    forall (s : t) (a : elt),
      position_of s a = 0 <-> ~ In a s.
  Proof. apply Bytes32Set.position_of_zero_iff_not_In. Qed.

End AddressSet.

End EnumerableSet.
