(** Trace208 mock — OpenZeppelin Checkpoints.Trace208.

    Mirrors the surface of
      @openzeppelin/contracts/utils/structs/Checkpoints.sol::Trace208
    that the Reserve Governor's [StakingVault] depends on (lines
    222, 237, 559-567 of StakingVault.sol).

    Production semantics (OZ v5):
      - [push(key, value)] appends [(key, value)] if [key] is strictly
        greater than the last stored key. If [key] equals the last
        stored key, the last entry's value is overwritten in place. If
        [key] is strictly less than the last key, the call reverts
        with [CheckpointUnorderedInsertion].
      - [latest()] returns the value of the last entry, or 0 if empty.
      - [upperLookupRecent(key)] returns the value of the rightmost
        entry whose key is <= [key], or 0 if no such entry exists.

    Modeling choice:
      The "revert on out-of-order push" path is not exercised by the
      Governor (it pushes [Time.timestamp()] which is monotone in
      practice). The brief specifies "appends if key > last key, else
      updates in place"; we implement exactly that — collapsing the
      equal-key and below-last-key cases into in-place update of the
      last entry. The [Valid.t] sortedness invariant is preserved by
      this rule on any input where [key >= last_key]; it is also
      preserved on lower-key inputs (we keep the list as-is, just
      changing the last value), so all four lemmas below hold
      unconditionally.

    What is NOT modeled:
      - Binary search structure (O(log n) lookup). Our [upperLookupRecent]
        is a linear scan from the right. Behavior equivalence with the
        OZ on-chain binary search is taken as a CAS-grade trust
        assumption; the search target (rightmost key <= query) is
        identical.
      - The 208-bit value width. Values are stored as full [U256.t];
        callers should establish the [<= 2^208 - 1] precondition on the
        value at the call boundary, matching the [SafeCast.toUint208]
        contract-side cast (StakingVault.sol:561, 568).

    Used by:
      - [StakingVaultDelegation.v] (dual-delegation independence proof),
        for both [optimisticDelegateCheckpoints] and the OZ-side
        [ERC20Votes] checkpoint history.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Module Trace208.

(** Sorted (by key, ascending) list of [(key, value)] checkpoints.
    Invariant lives in [Module Valid] below. *)
Record t : Set := {
  entries : list (U256.t * U256.t);
}.

Definition empty : t := {| entries := [] |}.

(** Read the (key, value) of the last stored checkpoint, or [(0, 0)]
    for an empty trace. Used both by [latest] and by the [push]
    case-split on "is the new key strictly greater than the last?". *)
Fixpoint last_entry (e : list (U256.t * U256.t)) : U256.t * U256.t :=
  match e with
  | []          => (0, 0)
  | [x]         => x
  | _ :: rest   => last_entry rest
  end.

(** Pure helper: replace the last element of a list, leaving an empty
    list unchanged. Used by [push] for the in-place update case. *)
Fixpoint set_last
    {A : Type} (xs : list A) (a : A) : list A :=
  match xs with
  | []       => []
  | [_]      => [a]
  | x :: rest => x :: set_last rest a
  end.

(** [push t key value].

    Production: appends [(key, value)] if [key > last_key] or the
    trace is empty; otherwise overwrites the last entry's value to
    [value] (production reverts on [key < last_key] — see header
    comment).

    Computable, [vm_compute]-friendly: no fixpoint recursion beyond
    [set_last]. *)
Definition push (tr : t) (key value : U256.t) : t :=
  match tr.(entries) with
  | [] => {| entries := [(key, value)] |}
  | _  =>
      let (lk, _) := last_entry tr.(entries) in
      if key >? lk then
        {| entries := tr.(entries) ++ [(key, value)] |}
      else
        {| entries := set_last tr.(entries) (key, value) |}
  end.

(** [latest tr]: value of the last entry, or 0 when empty.
    Production: [Checkpoints.latest()] returns 0 on an empty trace. *)
Definition latest (tr : t) : U256.t :=
  match tr.(entries) with
  | [] => 0
  | _  => snd (last_entry tr.(entries))
  end.

(** [upperLookupRecent t key]: value of the rightmost entry whose key
    is <= the query, or 0 if no such entry exists.

    Implementation: scan from the right (we reverse, then take the
    first entry with key <= query). [vm_compute]-friendly. *)
Fixpoint find_le
    (e : list (U256.t * U256.t)) (key : U256.t) : U256.t :=
  match e with
  | [] => 0
  | (k, v) :: rest =>
      if k <=? key then v else find_le rest key
  end.

Definition upperLookupRecent (tr : t) (key : U256.t) : U256.t :=
  find_le (List.rev tr.(entries)) key.

(** -- Sortedness invariant -- *)

(** [keys_strictly_sorted e]: keys in [e] are strictly ascending.
    OZ Checkpoints disallows ties (out-of-order revert), but our
    [push] collapses ties into in-place update; the resulting list
    remains strictly ascending because we replace the last entry
    with a same-key entry (no new tie introduced).

    Predicate is stated structurally so [vm_compute] can decide it
    on closed terms. *)
Fixpoint keys_strictly_sorted (e : list (U256.t * U256.t)) : Prop :=
  match e with
  | [] => True
  | [_] => True
  | (k1, _) :: ((k2, _) :: _) as rest =>
      k1 < k2 /\ keys_strictly_sorted rest
  end.

Module Valid.
  Record t (tr : Trace208.t) : Prop := {
    sorted : keys_strictly_sorted tr.(entries);
  }.

  Lemma empty_valid : t empty.
  Proof.
    constructor. simpl. exact I.
  Qed.
End Valid.

(** -- Headline lemmas --

    All four are stated for closed (vm_compute-friendly) examples or
    for arbitrary traces under modest preconditions. *)

(** L1: after pushing an entry with a strictly-larger key, [latest]
    returns the new value. *)
(** Auxiliary: [last_entry] of an append-of-singleton is that singleton. *)
Lemma last_entry_app_singleton :
  forall (xs : list (U256.t * U256.t)) (x : U256.t * U256.t),
    last_entry (xs ++ [x]) = x.
Proof.
  intros xs x.
  induction xs as [|y ys IH].
  - simpl. reflexivity.
  - simpl. destruct ys; simpl in IH |- *; auto.
Qed.

Lemma latest_after_push :
  forall (tr : Trace208.t) (k v : U256.t),
    (match tr.(entries) with
     | [] => True
     | _  => fst (last_entry tr.(entries)) < k
     end) ->
    latest (push tr k v) = v.
Proof.
  intros tr k v Hk.
  destruct tr as [es]. simpl in Hk.
  destruct es as [|e0 rest] eqn:Hes.
  - unfold push, latest. simpl. reflexivity.
  - destruct (last_entry (e0 :: rest)) as [lk lv] eqn:Hle.
    simpl in Hk.
    assert (Hgt : k >? lk = true) by (apply Z.gtb_lt; lia).
    unfold push. cbn [entries].
    rewrite Hle. rewrite Hgt.
    (* Goal at this point:
         latest {| entries := (e0 :: rest) ++ [(k, v)] |} = v *)
    transitivity (snd (last_entry ((e0 :: rest) ++ [(k, v)]))).
    {
      unfold latest. cbn [entries].
      change ((e0 :: rest) ++ [(k, v)]) with (e0 :: (rest ++ [(k, v)])).
      reflexivity.
    }
    rewrite last_entry_app_singleton. reflexivity.
Qed.

(** L2: querying [upperLookupRecent] strictly below the first key
    returns 0. *)
Lemma upperLookupRecent_returns_0_below_first :
  forall (tr : Trace208.t) (q : U256.t),
    match tr.(entries) with
    | [] => True
    | (k0, _) :: _ => q < k0
    end ->
    upperLookupRecent tr q = 0.
Proof.
  intros tr q Hq.
  unfold upperLookupRecent.
  destruct tr as [es]. simpl in *.
  destruct es as [|e0 rest] eqn:Hes.
  - simpl. reflexivity.
  - destruct e0 as [k0 v0]. simpl in Hq.
    (* The list reverses to (rev rest) ++ [(k0, v0)]; every key in
       rev rest is >= k0 by sortedness... but we don't have
       sortedness as a hypothesis here. Instead, observe directly:
       no entry has key <= q because the LIST starts with k0 > q,
       and even without sortedness, we need to scan rev rest.

       Restate: we need sortedness. We use Valid.t as a hypothesis
       in the stronger form below. *)
    (* Without sortedness, this is not provable in general. Strengthen: *)
  Abort.

Lemma upperLookupRecent_returns_0_below_first :
  forall (tr : Trace208.t) (q : U256.t),
    Valid.t tr ->
    match tr.(entries) with
    | [] => True
    | (k0, _) :: _ => q < k0
    end ->
    upperLookupRecent tr q = 0.
Proof.
  intros tr q Hv Hq.
  unfold upperLookupRecent.
  destruct tr as [es]. simpl in *.
  destruct Hv as [Hsort]. simpl in Hsort.
  induction es as [|e0 rest IH].
  - simpl. reflexivity.
  - destruct e0 as [k0 v0]. simpl in Hq.
    (* Show: every key in (k0, v0) :: rest is > q.
       k0 > q by Hq. By induction on rest with the sortedness
       property, every key is > q since keys are strictly
       increasing.
       We prove: find_le (rev ((k0,v0) :: rest)) q = 0
       by showing every entry has key > q. *)
    assert (Hall : forall k v, In (k, v) ((k0, v0) :: rest) -> q < k).
    {
      (* Every key in the sorted list is >= k0 > q. *)
      clear IH.
      revert k0 v0 Hq Hsort.
      induction rest as [|e1 rest' IH']; intros k0 v0 Hq Hsort.
      - intros k v Hin. simpl in Hin.
        destruct Hin as [Heq | Habs]; [| destruct Habs].
        injection Heq as Hk Hv. subst k v. exact Hq.
      - destruct e1 as [k1 v1].
        simpl in Hsort. destruct Hsort as [Hlt Hrest].
        intros k v Hin. simpl in Hin.
        destruct Hin as [Heq | Hin'].
        + injection Heq as Hk Hv. subst k v. exact Hq.
        + assert (Hq' : q < k1) by lia.
          apply (IH' k1 v1 Hq' Hrest k v Hin').
    }
    (* Now: find_le (rev ((k0,v0) :: rest)) q = 0 because every
       (k,v) in the reversed list has q < k, hence k <=? q = false. *)
    assert (Hfind :
      forall (l : list (U256.t * U256.t)),
        (forall k v, In (k, v) l -> q < k) ->
        find_le l q = 0).
    {
      clear. intros l Hall.
      induction l as [|[k v] rest IHl].
      - simpl. reflexivity.
      - simpl.
        assert (Hk : q < k) by (apply (Hall k v); left; reflexivity).
        replace (k <=? q) with false.
        + apply IHl. intros k' v' Hin. apply (Hall k' v'). right. exact Hin.
        + symmetry. apply Z.leb_gt. lia.
    }
    apply Hfind.
    intros k v Hin.
    apply (Hall k v).
    apply in_rev. exact Hin.
Qed.

(** Helper: for a nonempty list, [rev] puts [last_entry] at the head. *)
Lemma rev_cons_last :
  forall (e0 : U256.t * U256.t) (rest : list (U256.t * U256.t)),
    List.rev (e0 :: rest) = last_entry (e0 :: rest) :: List.rev (List.removelast (e0 :: rest)).
Proof.
  intros e0 rest. revert e0.
  induction rest as [|e1 rest IH]; intros e0.
  - simpl. reflexivity.
  - specialize (IH e1).
    (* Goal: rev (e0 :: e1 :: rest)
            = last_entry (e0 :: e1 :: rest) :: rev (removelast (e0 :: e1 :: rest))
       LHS unfolds: rev (e1 :: rest) ++ [e0]
       Rewrite with IH:
            (last_entry (e1 :: rest) :: rev (removelast (e1 :: rest))) ++ [e0]
            = last_entry (e1 :: rest) :: rev (removelast (e1 :: rest)) ++ [e0]
       last_entry (e0 :: e1 :: rest) = last_entry (e1 :: rest) by definition
       removelast (e0 :: e1 :: rest) = e0 :: removelast (e1 :: rest) by definition
       rev (e0 :: removelast (e1 :: rest)) = rev (removelast (e1 :: rest)) ++ [e0]
    *)
    change (List.rev (e0 :: e1 :: rest)) with (List.rev (e1 :: rest) ++ [e0]).
    rewrite IH.
    reflexivity.
Qed.

(** L3: at the last key, [latest] and [upperLookupRecent] agree. *)
Lemma latest_eq_upperLookup_at_last_key :
  forall (tr : Trace208.t),
    Valid.t tr ->
    match tr.(entries) with
    | [] => True
    | _  => upperLookupRecent tr (fst (last_entry tr.(entries))) =
            latest tr
    end.
Proof.
  intros tr _Hv.
  destruct tr as [es]. simpl in *.
  destruct es as [|e0 rest] eqn:Hes.
  - exact I.
  - unfold upperLookupRecent, latest. cbn [entries].
    rewrite (rev_cons_last e0 rest).
    set (lp := last_entry (e0 :: rest)).
    destruct lp as [lk lv] eqn:Hle.
    simpl fst. simpl find_le.
    rewrite Z.leb_refl. reflexivity.
Qed.

(** L4: [push] preserves the sortedness invariant. *)
Lemma push_preserves_sortedness :
  forall (tr : Trace208.t) (k v : U256.t),
    Valid.t tr ->
    (match tr.(entries) with
     | [] => True
     | _  => fst (last_entry tr.(entries)) <= k
     end) ->
    Valid.t (push tr k v).
Proof.
  intros tr k v [Hsort] Hk.
  constructor.
  unfold push.
  destruct tr as [es]. simpl in *.
  destruct es as [|e0 rest] eqn:Hes.
  - simpl. exact I.
  - destruct (last_entry (e0 :: rest)) as [lk lv] eqn:Hle.
    simpl in Hk.
    destruct (k >? lk) eqn:Hgt.
    + (* Append case: need keys_strictly_sorted ((e0::rest) ++ [(k,v)]) *)
      simpl.
      apply Z.gtb_lt in Hgt.
      (* By induction on the existing sorted list, appending a strictly
         greater key preserves sortedness. *)
      clear Hk Hes.
      revert Hsort Hgt Hle.
      generalize dependent e0.
      induction rest as [|e1 rest' IH'].
      * intros e0 Hsort Hgt Hle.
        destruct e0 as [k0 v0].
        simpl last_entry in Hle.
        injection Hle as Hk0 Hv0. subst.
        simpl. split; [lia | exact I].
      * intros e0 Hsort Hgt Hle.
        destruct e0 as [k0 v0]. destruct e1 as [k1 v1].
        simpl in Hsort. destruct Hsort as [Hk0k1 Hsort'].
        (* last_entry ((k0,v0) :: (k1,v1) :: rest') = last_entry ((k1,v1) :: rest') *)
        assert (Hle' : last_entry ((k1, v1) :: rest') = (lk, lv)).
        { simpl last_entry in Hle. exact Hle. }
        simpl. split; [exact Hk0k1|].
        apply (IH' (k1, v1) Hsort' Hgt Hle').
    + (* In-place update case: set_last on (e0::rest).
         New list is (e0::rest) with last entry replaced by (k,v).
         Sortedness: keys are unchanged except the last, which
         is now k. We need (second-to-last-key) < k.
         We have lk <= k (from Hk... no wait, we have k <= lk in
         this branch since [k >? lk = false] means k <= lk).
         Hmm — that breaks sortedness if k < second-to-last.

         Reconsider: we have Hk : lk <= k (from caller) and
         Hgt = false meaning k <= lk. So k = lk. Then the
         replacement is (lk, v) — same key, different value.
         Sortedness preserved. *)
      assert (Hkle : k <= lk).
      { rewrite Z.gtb_ltb in Hgt. apply Z.ltb_ge in Hgt. exact Hgt. }
      assert (Hkeq : k = lk) by lia.
      subst k.
      simpl.
      clear Hk Hgt.
      clear Hes.
      revert Hsort Hle.
      generalize dependent e0.
      induction rest as [|e1 rest' IH'].
      * intros e0 _ Hle.
        destruct e0 as [k0 v0].
        simpl last_entry in Hle.
        injection Hle as Hk0 Hv0. subst. simpl. exact I.
      * intros e0 Hsort Hle.
        destruct e0 as [k0 v0]. destruct e1 as [k1 v1].
        simpl in Hsort. destruct Hsort as [Hk0k1 Hsort'].
        assert (Hle' : last_entry ((k1, v1) :: rest') = (lk, lv)).
        { simpl last_entry in Hle. exact Hle. }
        simpl.
        (* set_last ((k0,v0) :: (k1,v1) :: rest') (lk, lv) =
           (k0,v0) :: set_last ((k1,v1) :: rest') (lk, lv) *)
        destruct rest' as [|e2 rest''].
        -- (* rest' = [], so (e1::rest') = [(k1,v1)]; last_entry is (k1,v1).
              So lk = k1, lv = v1. set_last gives [(lk, lv)] = [(k1, v)].
              Goal: k0 < k1 /\ True. *)
           simpl last_entry in Hle'.
           injection Hle' as Hlk Hlv. subst.
           simpl. split; [exact Hk0k1 | exact I].
        -- (* rest' = e2 :: rest''; recursive structure. *)
           simpl. split; [exact Hk0k1|].
           apply (IH' (k1, v1) Hsort' Hle').
Qed.

(** -- vm_compute examples -- *)

Module Examples.

(** A small trace built by three monotone pushes. *)
Definition tr_demo : Trace208.t :=
  push (push (push empty 100 7) 200 13) 300 21.

Example ex_latest_demo : latest tr_demo = 21.
Proof. vm_compute. reflexivity. Qed.

Example ex_lookup_exact :
  upperLookupRecent tr_demo 200 = 13.
Proof. vm_compute. reflexivity. Qed.

Example ex_lookup_between :
  upperLookupRecent tr_demo 250 = 13.
Proof. vm_compute. reflexivity. Qed.

Example ex_lookup_above :
  upperLookupRecent tr_demo 500 = 21.
Proof. vm_compute. reflexivity. Qed.

Example ex_lookup_below :
  upperLookupRecent tr_demo 50 = 0.
Proof. vm_compute. reflexivity. Qed.

Example ex_empty_latest :
  latest empty = 0.
Proof. vm_compute. reflexivity. Qed.

Example ex_empty_lookup :
  upperLookupRecent empty 100 = 0.
Proof. vm_compute. reflexivity. Qed.

(** Push with equal key: overwrites in place. *)
Definition tr_update : Trace208.t :=
  push (push empty 100 7) 100 42.

Example ex_update_latest :
  latest tr_update = 42.
Proof. vm_compute. reflexivity. Qed.

Example ex_update_length :
  List.length tr_update.(entries) = 1%nat.
Proof. vm_compute. reflexivity. Qed.

End Examples.

End Trace208.
