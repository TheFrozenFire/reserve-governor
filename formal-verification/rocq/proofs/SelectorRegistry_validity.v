(** OptimisticSelectorRegistry validity preservation.

    Storage-level invariants the contract maintains (see
    [SelectorRegistry.Valid.state]):

      targets_nd : NoDup on the targets list.
      keys_nd    : NoDup on the keys of the allowed-selectors map.
      sels_nd    : NoDup on each per-target selector list.
      is_pruned  : no per-target entry has an empty selector list.
      cross_inv  : target in targets <-> allowed list for target is
                   non-empty.

    [addSelector] and [removeSelector] are the only state-mutating
    operations. We show each preserves [Valid.state]:

      addSelector_preserves_validity
      removeSelector_preserves_validity

    Plus:
      empty_state_valid       — initial state satisfies everything
                                vacuously.
      add_then_remove_restores — strengthened restoration: a fresh
                                (t, sel) added then removed yields
                                the original state structurally
                                when [t] had no prior selectors.

    Plus a [vm_compute] cross-check that the four invariants survive
    a concrete add/remove cycle. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import ReserveGovernor.proofs.SelectorRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module SelectorRegistryValidity.

Import ReserveGovernor.simulations.SelectorRegistry.
Import SelectorRegistry.
Import SelectorRegistry.Valid.
Import SelectorRegistryProofs.

(** ============================================================
    Section: list_contains / list_remove helpers.
    ============================================================ *)

(** [list_contains] coincides with set-theoretic [In]. *)
Lemma list_contains_In (xs : list U256.t) (x : U256.t) :
  list_contains xs x = true <-> In x xs.
Proof.
  induction xs as [|y rest IH]; simpl.
  - split; [discriminate | intros H; destruct H].
  - destruct (y =? x) eqn:Hyx.
    + apply Z.eqb_eq in Hyx. split; intros _; [left; exact Hyx | reflexivity].
    + apply Z.eqb_neq in Hyx. split.
      * intros Hc. right. apply IH. exact Hc.
      * intros [Heq | Hin]; [contradiction (Hyx Heq) | apply IH; exact Hin].
Qed.

Lemma list_contains_false_iff (xs : list U256.t) (x : U256.t) :
  list_contains xs x = false <-> ~ In x xs.
Proof.
  destruct (list_contains xs x) eqn:Hc.
  - split; [discriminate|]. intros Hnin.
    apply list_contains_In in Hc. contradiction.
  - split; [|reflexivity]. intros _ Hin.
    apply list_contains_In in Hin. rewrite Hin in Hc. discriminate.
Qed.

(** Membership in [list_remove xs x] implies membership in [xs]. *)
Lemma list_remove_subset (xs : list U256.t) (x y : U256.t) :
  In y (list_remove xs x) -> In y xs.
Proof.
  induction xs as [|z rest IH]; simpl.
  - intros [].
  - destruct (z =? x) eqn:Hzx.
    + intros Hin. right. apply IH. exact Hin.
    + intros [Heq | Hin]; [left; exact Heq | right; apply IH; exact Hin].
Qed.

(** Removing [x] from a list does not introduce duplicates. *)
Lemma NoDup_list_remove (xs : list U256.t) (x : U256.t) :
  NoDup xs -> NoDup (list_remove xs x).
Proof.
  induction 1 as [|y rest Hni Hnd IH]; simpl.
  - constructor.
  - destruct (y =? x) eqn:Hyx.
    + exact IH.
    + constructor; [|exact IH].
      intros Hin. apply Hni. apply list_remove_subset in Hin. exact Hin.
Qed.

(** After removing [x], [x] is no longer in the list. *)
Lemma list_remove_removes (xs : list U256.t) (x : U256.t) :
  ~ In x (list_remove xs x).
Proof.
  induction xs as [|y rest IH]; simpl.
  - intros [].
  - destruct (y =? x) eqn:Hyx.
    + exact IH.
    + apply Z.eqb_neq in Hyx. intros [Heq | Hin].
      * apply Hyx. exact Heq.
      * apply IH. exact Hin.
Qed.

(** Removing [x] does not affect membership of any other element. *)
Lemma list_remove_preserves_other (xs : list U256.t) (x y : U256.t) :
  x <> y ->
  In y xs <-> In y (list_remove xs x).
Proof.
  intros Hxy. induction xs as [|z rest IH]; simpl.
  - reflexivity.
  - destruct (z =? x) eqn:Hzx.
    + apply Z.eqb_eq in Hzx. split.
      * intros [Heq | Hin]; [|apply IH; exact Hin].
        exfalso. apply Hxy. rewrite <- Hzx, Heq. reflexivity.
      * intros Hin. right. apply IH. exact Hin.
    + simpl. split.
      * intros [Heq | Hin]; [left; exact Heq | right; apply IH; exact Hin].
      * intros [Heq | Hin]; [left; exact Heq | right; apply IH; exact Hin].
Qed.

Lemma list_contains_remove_other (xs : list U256.t) (x y : U256.t) :
  x <> y ->
  list_contains (list_remove xs x) y = list_contains xs y.
Proof.
  intros Hxy.
  destruct (list_contains xs y) eqn:Hy.
  - apply list_contains_In in Hy.
    apply list_contains_In, list_remove_preserves_other; [exact Hxy | exact Hy].
  - apply list_contains_false_iff in Hy.
    apply list_contains_false_iff. intros Hin.
    apply Hy. apply list_remove_preserves_other in Hin; [|exact Hxy]. exact Hin.
Qed.

(** Removing an absent element is a no-op. *)
Lemma list_remove_not_in (xs : list U256.t) (x : U256.t) :
  ~ In x xs -> list_remove xs x = xs.
Proof.
  induction xs as [|y rest IH]; simpl.
  - reflexivity.
  - intros Hnin. destruct (y =? x) eqn:Hyx.
    + apply Z.eqb_eq in Hyx. exfalso. apply Hnin. left. exact Hyx.
    + f_equal. apply IH. intros Hin. apply Hnin. right. exact Hin.
Qed.

(** ============================================================
    Section: set_allowed_for / allowed_for helpers.
    ============================================================ *)

(** [allowed_for] after [set_allowed_for] at a different target is
    unchanged. *)
Lemma allowed_for_set_other
    (mp : list (Address * list Selector))
    (target other : Address) (new_sels : list Selector) :
  target <> other ->
  allowed_for (set_allowed_for mp target new_sels) other
  = allowed_for mp other.
Proof.
  intros Hne. induction mp as [|[t' sels'] rest IH]; simpl.
  - destruct (target =? other) eqn:Heq.
    + apply Z.eqb_eq in Heq. contradiction.
    + reflexivity.
  - destruct (t' =? target) eqn:Ht; simpl.
    + apply Z.eqb_eq in Ht. rewrite Ht.
      destruct (target =? other) eqn:Heq.
      * apply Z.eqb_eq in Heq. contradiction.
      * reflexivity.
    + destruct (t' =? other) eqn:Hto.
      * reflexivity.
      * exact IH.
Qed.

(** [set_allowed_for] preserves [Forall P] when [P] holds of the new
    [(target, new_sels)] pair. *)
Lemma set_allowed_for_Forall
    (P : Address * list Selector -> Prop)
    (mp : list (Address * list Selector))
    (target : Address) (new_sels : list Selector) :
  Forall P mp ->
  P (target, new_sels) ->
  Forall P (set_allowed_for mp target new_sels).
Proof.
  intros HF HP. induction HF as [|[t' sels'] rest Hh HF IH]; simpl.
  - apply Forall_cons; [exact HP | apply Forall_nil].
  - destruct (t' =? target) eqn:Ht.
    + apply Z.eqb_eq in Ht. subst t'.
      apply Forall_cons; [exact HP | exact HF].
    + apply Forall_cons; [exact Hh | exact IH].
Qed.

(** [set_allowed_for] preserves the key list as a set: every key is
    either [target] or already in [mp]. *)
Lemma set_allowed_for_keys_In_iff
    (mp : list (Address * list Selector))
    (target : Address) (new_sels : list Selector) (k : Address) :
  In k (map fst (set_allowed_for mp target new_sels)) <->
  k = target \/ In k (map fst mp).
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - split.
    + intros [Heq | Habs]; [left; exact (eq_sym Heq) | destruct Habs].
    + intros [Heq | Habs]; [|destruct Habs]. left. exact (eq_sym Heq).
  - destruct (t' =? target) eqn:Ht; simpl.
    + apply Z.eqb_eq in Ht. subst t'.
      split.
      * intros [Heq | Hin]; [left; symmetry; exact Heq | right; right; exact Hin].
      * intros [Heq | Hsum].
        -- left. symmetry. exact Heq.
        -- exact Hsum.
    + split.
      * intros Hin. destruct Hin as [Heq | Hin2].
        -- right. left. exact Heq.
        -- apply IH in Hin2. destruct Hin2 as [Hk | Hk]; [left; exact Hk | right; right; exact Hk].
      * intros [Heq | Hsum].
        -- right. apply IH. left. exact Heq.
        -- destruct Hsum as [Heq2 | Hin2].
           ++ left. exact Heq2.
           ++ right. apply IH. right. exact Hin2.
Qed.

(** [set_allowed_for] preserves [NoDup] on the key list (the underlying
    function either updates an existing key or appends a new one). *)
Lemma set_allowed_for_NoDup_keys
    (mp : list (Address * list Selector))
    (target : Address) (new_sels : list Selector) :
  NoDup (map fst mp) ->
  NoDup (map fst (set_allowed_for mp target new_sels)).
Proof.
  intros Hnd. induction mp as [|[t' sels'] rest IH]; simpl.
  - apply NoDup_cons; [intros []|]. apply NoDup_nil.
  - destruct (t' =? target) eqn:Ht; simpl.
    + (* updating in place: keys unchanged *)
      exact Hnd.
    + (* recurse and re-add t' *)
      simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hndr].
      apply NoDup_cons.
      * intros Hin. apply set_allowed_for_keys_In_iff in Hin.
        destruct Hin as [Heq | Hin].
        -- subst t'. rewrite Z.eqb_refl in Ht. discriminate.
        -- contradiction.
      * apply IH. exact Hndr.
Qed.

(** ============================================================
    Section: prune_allowed helpers.
    ============================================================ *)

(** prune_allowed yields a map in which every per-target list is
    non-empty. *)
Lemma prune_allowed_pruned (mp : list (Address * list Selector)) :
  Forall (fun ts => (length (snd ts) > 0)%nat) (prune_allowed mp).
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - apply Forall_nil.
  - destruct sels' as [|sel sels''].
    + exact IH.
    + apply Forall_cons; [simpl; lia | exact IH].
Qed.

(** prune_allowed preserves [Forall P]: it only drops entries. *)
Lemma prune_allowed_Forall
    (P : Address * list Selector -> Prop)
    (mp : list (Address * list Selector)) :
  Forall P mp ->
  Forall P (prune_allowed mp).
Proof.
  induction 1 as [|[t' sels'] rest Hh _ IH]; simpl.
  - apply Forall_nil.
  - destruct sels' as [|sel sels''].
    + exact IH.
    + apply Forall_cons; [exact Hh | exact IH].
Qed.

(** The key list of [prune_allowed mp] is a sub-list of [map fst mp];
    in particular membership is preserved one way. *)
Lemma prune_allowed_keys_In
    (mp : list (Address * list Selector)) (k : Address) :
  In k (map fst (prune_allowed mp)) -> In k (map fst mp).
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - intros [].
  - destruct sels' as [|sel sels''].
    + intros Hin. right. apply IH. exact Hin.
    + simpl. intros [Heq | Hin]; [left; exact Heq | right; apply IH; exact Hin].
Qed.

(** prune_allowed preserves [NoDup] on keys. *)
Lemma prune_allowed_NoDup_keys
    (mp : list (Address * list Selector)) :
  NoDup (map fst mp) ->
  NoDup (map fst (prune_allowed mp)).
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - intros _. apply NoDup_nil.
  - intros Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hndr].
    destruct sels' as [|sel sels''].
    + apply IH. exact Hndr.
    + simpl. apply NoDup_cons.
      * intros Hin. apply Hni. apply prune_allowed_keys_In in Hin. exact Hin.
      * apply IH. exact Hndr.
Qed.

(** prune_allowed preserves [allowed_for] when the target's list is
    non-empty. *)
Lemma allowed_for_prune_nonempty
    (mp : list (Address * list Selector)) (target : Address) :
  allowed_for mp target <> [] ->
  allowed_for (prune_allowed mp) target = allowed_for mp target.
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - intros Hne. contradiction.
  - destruct (t' =? target) eqn:Ht.
    + destruct sels' as [|sel sels''].
      * intros Hne. contradiction (Hne eq_refl).
      * intros _. simpl. rewrite Ht. reflexivity.
    + destruct sels' as [|sel sels''].
      * exact IH.
      * simpl. rewrite Ht. exact IH.
Qed.

(** When the input map is already pruned, [prune_allowed] is a no-op
    on [allowed_for]. *)
Lemma allowed_for_prune_already_pruned
    (mp : list (Address * list Selector)) (target : Address) :
  Forall (fun ts => (length (snd ts) > 0)%nat) mp ->
  allowed_for (prune_allowed mp) target = allowed_for mp target.
Proof.
  induction 1 as [|[t' sels'] rest Hh _ IH]; simpl.
  - reflexivity.
  - destruct sels' as [|sel sels''].
    + simpl in Hh. lia.
    + simpl. destruct (t' =? target) eqn:Ht.
      * reflexivity.
      * exact IH.
Qed.

(** When the key [target] does not appear in [map fst mp],
    [allowed_for mp target] is the empty list. *)
Lemma allowed_for_not_in_keys
    (mp : list (Address * list Selector)) (target : Address) :
  ~ In target (map fst mp) ->
  allowed_for mp target = [].
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - reflexivity.
  - intros Hnin. destruct (t' =? target) eqn:Ht.
    + apply Z.eqb_eq in Ht. exfalso. apply Hnin. left. exact Ht.
    + apply IH. intros Hin. apply Hnin. right. exact Hin.
Qed.

(** When the input map is pruned, setting target's value to [] then
    pruning yields a lookup at [tgt <> target] equal to the original. *)
Lemma allowed_for_prune_set_empty_other
    (mp : list (Address * list Selector)) (target tgt : Address) :
  target <> tgt ->
  Forall (fun ts => (length (snd ts) > 0)%nat) mp ->
  allowed_for (prune_allowed (set_allowed_for mp target [])) tgt
  = allowed_for mp tgt.
Proof.
  intros Hne. induction mp as [|[t' sels'] rest IH]; simpl.
  - intros _. destruct (target =? tgt) eqn:Hb;
      [apply Z.eqb_eq in Hb; contradiction|reflexivity].
  - intros Hpr. apply Forall_cons_iff in Hpr. destruct Hpr as [Hh Hpr_r].
    destruct (t' =? target) eqn:Ht.
    + apply Z.eqb_eq in Ht. subst t'.
      destruct sels' as [|sel sels''].
      * simpl in Hh. exfalso. lia.
      * simpl.
        destruct (target =? tgt) eqn:Hb; [apply Z.eqb_eq in Hb; contradiction|].
        apply allowed_for_prune_already_pruned. exact Hpr_r.
    + destruct sels' as [|sel sels''].
      * simpl in Hh. exfalso. lia.
      * simpl. destruct (t' =? tgt) eqn:Htg.
        -- reflexivity.
        -- apply IH. exact Hpr_r.
Qed.

(** When the input map has unique keys, replacing target's entry with
    [] and then pruning yields a map without target as a key — hence
    [allowed_for ... target = []]. *)
Lemma allowed_for_prune_set_empty_unique
    (mp : list (Address * list Selector)) (target : Address) :
  NoDup (map fst mp) ->
  allowed_for (prune_allowed (set_allowed_for mp target [])) target = [].
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - intros _. reflexivity.
  - intros Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hndr].
    destruct (t' =? target) eqn:Ht.
    + (* t' = target. set_allowed_for ... = (target, []) :: rest.
         prune drops (target, []). Need allowed_for (prune rest) target = [].
         Since target = t' is not in keys of rest (by NoDup), allowed_for rest
         target = []. prune of rest also has target not in keys, so still []. *)
      apply Z.eqb_eq in Ht. subst t'.
      (* set_allowed_for ((target, sels') :: rest) target [] = (target, []) :: rest.
         prune_allowed drops (target, []). Goal reduces to
         allowed_for (prune_allowed rest) target = []. *)
      simpl.
      apply allowed_for_not_in_keys.
      intros Hin. apply prune_allowed_keys_In in Hin. apply Hni. exact Hin.
    + (* t' <> target. *)
      destruct sels' as [|sel sels''].
      * (* sels' = []. Then prune_allowed of head drops it. So result is
           prune_allowed (set_allowed_for rest target []). Apply IH. *)
        apply IH. exact Hndr.
      * (* sels' = sel :: sels''. prune_allowed keeps head; we then look up
           in (t', sel :: sels'') :: prune (set_allowed_for rest target []).
           Since t' <> target, recurse. *)
        simpl. rewrite Ht. apply IH. exact Hndr.
Qed.

(** Helper: a target listed in the original allowed-selectors map's
    keys has [allowed_for] equal to the value stored in the first
    entry for that key. We use the slightly weaker statement that
    [allowed_for] gives a [list_contains] of any selector in the
    stored list. *)
Lemma allowed_for_NoDup_extract
    (mp : list (Address * list Selector)) (target : Address) :
  NoDup (map fst mp) ->
  Forall (fun ts => NoDup (snd ts)) mp ->
  NoDup (allowed_for mp target).
Proof.
  intros _ HF.
  induction HF as [|[t' sels'] rest Hh _ IH]; simpl.
  - apply NoDup_nil.
  - destruct (t' =? target) eqn:Ht.
    + exact Hh.
    + exact IH.
Qed.

(** ============================================================
    Section: empty_state validity.
    ============================================================ *)

Lemma empty_state_valid : Valid.state empty_state.
Proof.
  constructor; simpl.
  - apply NoDup_nil.
  - apply NoDup_nil.
  - apply Forall_nil.
  - apply Forall_nil.
  - unfold cross_invariant. intros target. simpl.
    split; [discriminate | lia].
Qed.

(** ============================================================
    Section: validity preservation for addSelector.
    ============================================================ *)

Lemma addSelector_preserves_validity
    (s s' : State.t) (forbidden : list Address)
    (target : Address) (selector : Selector) :
  Valid.state s ->
  addSelector s forbidden target selector = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hnd_t Hnd_k Hnd_s Hpr Hcross].
  unfold no_dup_targets in Hnd_t.
  unfold no_dup_keys in Hnd_k.
  unfold no_dup_selectors in Hnd_s.
  unfold pruned in Hpr.
  unfold addSelector in Hok.
  destruct (is_forbidden forbidden target) eqn:Hfb; [discriminate|].
  destruct (selector =? zero_selector) eqn:Hz; [discriminate|].
  set (sels := allowed_for s.(State.allowedSelectors) target) in *.
  destruct (list_contains sels selector) eqn:Hin.
  - (* idempotent path: state unchanged *)
    injection Hok as Hs'. rewrite <- Hs'.
    constructor; assumption.
  - (* fresh-insertion path *)
    set (new_sels := selector :: sels) in *.
    set (allowed' := set_allowed_for s.(State.allowedSelectors) target new_sels) in *.
    set (targets' :=
      if list_contains s.(State.targets) target
      then s.(State.targets)
      else target :: s.(State.targets)) in *.
    injection Hok as Hs'. rewrite <- Hs'.
    (* Establish: NoDup new_sels. *)
    assert (Hsels_nd : NoDup sels)
      by (apply allowed_for_NoDup_extract; assumption).
    assert (Hnewsels_nd : NoDup new_sels).
    { apply NoDup_cons; [|exact Hsels_nd].
      apply list_contains_false_iff. exact Hin. }
    constructor; simpl.
    + (* targets_nd *)
      unfold targets'.
      destruct (list_contains s.(State.targets) target) eqn:Htin.
      * exact Hnd_t.
      * apply NoDup_cons; [|exact Hnd_t].
        apply list_contains_false_iff. exact Htin.
    + (* keys_nd: NoDup keys of allowed' *)
      unfold allowed'.
      apply set_allowed_for_NoDup_keys. exact Hnd_k.
    + (* sels_nd *)
      unfold allowed'.
      apply set_allowed_for_Forall; [exact Hnd_s | simpl; exact Hnewsels_nd].
    + (* is_pruned *)
      unfold allowed'.
      apply set_allowed_for_Forall; [exact Hpr | simpl; lia].
    + (* cross_inv *)
      unfold cross_invariant in *. intros tgt. simpl.
      unfold targets', allowed'.
      destruct (Z.eq_dec target tgt) as [Heq | Hne].
      * rewrite <- Heq.
        rewrite set_allowed_then_allowed_for.
        split; intros _.
        -- simpl. lia.
        -- destruct (list_contains s.(State.targets) target) eqn:Htin.
           ++ exact Htin.
           ++ simpl. rewrite Z.eqb_refl. reflexivity.
      * rewrite allowed_for_set_other; [|exact Hne].
        destruct (list_contains s.(State.targets) target) eqn:Htin.
        -- exact (Hcross tgt).
        -- simpl.
           assert (Hbool : (target =? tgt) = false)
             by (apply Z.eqb_neq; exact Hne).
           rewrite Hbool.
           exact (Hcross tgt).
Qed.

(** ============================================================
    Section: validity preservation for removeSelector.
    ============================================================ *)

Lemma removeSelector_preserves_validity
    (s s' : State.t) (target : Address) (selector : Selector) :
  Valid.state s ->
  removeSelector s target selector = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hnd_t Hnd_k Hnd_s Hpr Hcross].
  unfold no_dup_targets in Hnd_t.
  unfold no_dup_keys in Hnd_k.
  unfold no_dup_selectors in Hnd_s.
  unfold pruned in Hpr.
  unfold removeSelector in Hok.
  set (sels := allowed_for s.(State.allowedSelectors) target) in *.
  destruct (list_contains sels selector) eqn:Hin.
  - set (new_sels := list_remove sels selector) in *.
    set (allowed_pre := set_allowed_for s.(State.allowedSelectors) target new_sels) in *.
    set (allowed' := prune_allowed allowed_pre) in *.
    set (targets' :=
      match new_sels with
      | [] => list_remove s.(State.targets) target
      | _ :: _ => s.(State.targets)
      end) in *.
    injection Hok as Hs'. rewrite <- Hs'.
    assert (Hsels_nd : NoDup sels)
      by (apply allowed_for_NoDup_extract; assumption).
    assert (Hnewsels_nd : NoDup new_sels)
      by (unfold new_sels; apply NoDup_list_remove; exact Hsels_nd).
    constructor; simpl.
    + (* targets_nd *)
      unfold targets'. destruct new_sels as [|x xs].
      * apply NoDup_list_remove. exact Hnd_t.
      * exact Hnd_t.
    + (* keys_nd: prune then set keeps NoDup keys *)
      unfold allowed', allowed_pre.
      apply prune_allowed_NoDup_keys.
      apply set_allowed_for_NoDup_keys. exact Hnd_k.
    + (* sels_nd *)
      unfold allowed', allowed_pre.
      apply prune_allowed_Forall.
      apply set_allowed_for_Forall; [exact Hnd_s | simpl; exact Hnewsels_nd].
    + (* is_pruned *)
      unfold allowed'. apply prune_allowed_pruned.
    + (* cross_inv *)
      unfold cross_invariant in *. intros tgt. simpl.
      unfold targets', allowed'.
      destruct (Z.eq_dec target tgt) as [Heq | Hne].
      * (* tgt = target *)
        rewrite <- Heq.
        destruct new_sels as [|x xs] eqn:Hns.
        -- (* new_sels = [] : drop target from targets, allowed' has
              no entry for target. *)
           split.
           ++ intros Hc. apply list_contains_In in Hc.
              apply list_remove_removes in Hc. contradiction.
           ++ intros Hlen. exfalso.
              unfold allowed_pre in *.
              rewrite allowed_for_prune_set_empty_unique in Hlen; [|exact Hnd_k].
              simpl in Hlen. lia.
        -- (* new_sels = x :: xs : target stays in targets *)
           split; intros _.
           ++ unfold allowed_pre.
              assert (Hap : allowed_for (set_allowed_for s.(State.allowedSelectors) target (x :: xs)) target = x :: xs)
                by apply set_allowed_then_allowed_for.
              rewrite allowed_for_prune_nonempty; [|rewrite Hap; discriminate].
              rewrite Hap. simpl. lia.
           ++ apply Hcross.
              (* sels = y :: ys is non-empty (it contains selector). *)
              unfold sels in *.
              destruct (allowed_for s.(State.allowedSelectors) target) as [|y ys]; [discriminate|].
              simpl. lia.
      * (* tgt <> target *)
        unfold allowed_pre.
        (* Split on new_sels to handle the empty / non-empty case
           independently — set_allowed_for_Forall (with pruning
           predicate) only applies in the non-empty case. *)
        unfold new_sels.
        destruct (list_remove sels selector) as [|x xs] eqn:Hns.
        -- (* new_sels = [] *)
           pose proof (allowed_for_prune_set_empty_other
             s.(State.allowedSelectors) target tgt Hne Hpr) as Hrw.
           (* The goal subterm has [length] vs [Datatypes.length], or
              another notation idiosyncrasy: use [setoid_rewrite]. *)
           setoid_rewrite Hrw.
           rewrite list_contains_remove_other; [|exact Hne].
           exact (Hcross tgt).
        -- (* new_sels = x :: xs *)
           rewrite allowed_for_prune_already_pruned.
           ++ rewrite allowed_for_set_other; [|exact Hne].
              exact (Hcross tgt).
           ++ apply set_allowed_for_Forall.
              ** exact Hpr.
              ** simpl. lia.
  - injection Hok as Hs'. rewrite <- Hs'.
    constructor; assumption.
Qed.

(** ============================================================
    Section: add_then_remove_restores.
    ============================================================

    A strengthened restoration lemma. The existing
    [xcheck_add_then_remove_restores] in the cross-check file
    verifies a concrete instance by computation. Here we prove the
    general statement: when [target] is not already in the targets
    list (so [allowed_for s target = []]), adding (target, selector)
    then removing (target, selector) yields the original state
    structurally — no leftover entries, no membership drift. *)
Lemma add_then_remove_restores
    (s : State.t) (forbidden : list Address)
    (target : Address) (selector : Selector) :
  Valid.state s ->
  is_forbidden forbidden target = false ->
  selector <> zero_selector ->
  list_contains s.(State.targets) target = false ->
  allowed_for s.(State.allowedSelectors) target = [] ->
  match addSelector s forbidden target selector with
  | Result.Success s1 =>
      removeSelector s1 target selector = Result.Success s
  | _ => False
  end.
Proof.
  intros Hv Hfb Hzn Htnt Halt.
  destruct Hv as [Hnd_t Hnd_k Hnd_s Hpr Hcross].
  unfold no_dup_targets in Hnd_t.
  unfold no_dup_keys in Hnd_k.
  unfold pruned in Hpr.
  unfold addSelector. rewrite Hfb.
  destruct (selector =? zero_selector) eqn:Hz.
  { apply Z.eqb_eq in Hz. contradiction. }
  rewrite Halt. simpl.
  (* sels = [] : list_contains [] selector = false, take fresh-insertion. *)
  rewrite Htnt.
  (* s1 = {targets := target :: s.targets;
            allowedSelectors := set_allowed_for s.allowedSelectors target [selector]}. *)
  unfold removeSelector. simpl.
  rewrite set_allowed_then_allowed_for. simpl.
  rewrite Z.eqb_refl. simpl.
  (* allowed_for s1.(State.allowedSelectors) target = [selector].
     list_contains [selector] selector = true, take removal branch. *)
  (* new_sels = list_remove [selector] selector = []. *)
  rewrite Z.eqb_refl.
  (* Goal: result equals original s. *)
  f_equal.
  (* Two subgoals: targets list back to original, allowedSelectors back. *)
  destruct s as [tg al]. simpl in *.
  f_equal.
  - (* targets: list_remove (target :: tg) target = tg when target not in tg. *)
    apply list_remove_not_in. apply list_contains_false_iff. exact Htnt.
  - (* allowedSelectors: prune_allowed (set_allowed_for ... target []) = al.
       Because original allowed_for al target = []: target not really there
       (its entry is [] or absent), so setting to [] and pruning leaves al
       unchanged. *)
    (* By NoDup keys + pruned, if allowed_for al target = [] then target
       is not in keys of al (every key has non-empty value). Then
       set_allowed_for al target [] = al ++ [(target, [])], and pruning
       drops (target, []), giving al back. *)
    assert (Hnk : ~ In target (map fst al)).
    { (* If target were a key, by pruning its value is non-empty,
         contradicting Halt = []. *)
      intros Hin.
      assert (Hnz : allowed_for al target <> []).
      { clear Hcross Hnd_t Hnd_k Hnd_s Hfb Hz Hzn Htnt Halt.
        induction Hpr as [|[t' sels'] rest Hh _ IH]; simpl.
        - intros _. exact Hin.
        - destruct (t' =? target) eqn:Ht.
          + intros Heq. simpl in Hh. destruct sels'; [simpl in Hh; lia | discriminate].
          + apply Z.eqb_neq in Ht.
            destruct Hin as [Heq | Hin2].
            * exfalso. apply Ht. exact Heq.
            * apply IH. exact Hin2. }
      exact (Hnz Halt). }
    (* Now reduce: set_allowed_for (set_allowed_for al target [selector]) target [].
       Since target is not in keys of al, the inner set appends (target, [selector])
       at the end; the outer set rewrites that entry to (target, []). prune drops it. *)
    clear Hcross Hnd_t Hnd_s Hfb Hz Hzn Htnt Halt Hnd_k.
    induction al as [|[t' sels'] rest IH']; simpl.
    + rewrite Z.eqb_refl. simpl. reflexivity.
    + assert (Ht'_neq : t' <> target).
      { intros Heq. apply Hnk. simpl. left. exact Heq. }
      apply Z.eqb_neq in Ht'_neq. rewrite Ht'_neq.
      simpl. rewrite Ht'_neq.
      destruct sels' as [|sel sels''].
      * exfalso. inversion Hpr as [|? ? Hh _]. simpl in Hh. lia.
      * simpl. f_equal. apply IH'.
        -- inversion Hpr. assumption.
        -- intros Hin. apply Hnk. simpl. right. exact Hin.
Qed.

(** ============================================================
    Section: vm_compute cross-check that the four invariants
    survive a concrete add/remove cycle.
    ============================================================ *)

Module XCheck.

Definition self_addr     : Address := 1.
Definition gov_addr      : Address := 2.
Definition timelock_addr : Address := 3.
Definition token_addr    : Address := 4.
Definition forbidden     : list Address := [self_addr; gov_addr; timelock_addr; token_addr].

(** Run add(10, 1000); add(10, 1001); add(20, 2000); remove(10, 1000). *)
Definition s1 : State.t :=
  match addSelector empty_state forbidden 10 1000 with
  | Result.Success s => s | _ => empty_state end.

Definition s2 : State.t :=
  match addSelector s1 forbidden 10 1001 with
  | Result.Success s => s | _ => empty_state end.

Definition s3 : State.t :=
  match addSelector s2 forbidden 20 2000 with
  | Result.Success s => s | _ => empty_state end.

Definition s4 : State.t :=
  match removeSelector s3 10 1000 with
  | Result.Success s => s | _ => empty_state end.

(** Each of the four invariants computes to True / a NoDup proof
    obligation that we discharge by [vm_compute] and the constructor
    lemmas for NoDup / Forall. *)
Lemma xcheck_targets_nd_s4 :
  NoDup s4.(State.targets).
Proof.
  vm_compute. repeat constructor; simpl; intuition (try discriminate).
Qed.

Lemma xcheck_keys_nd_s4 :
  NoDup (map fst s4.(State.allowedSelectors)).
Proof.
  vm_compute. repeat constructor; simpl; intuition (try discriminate).
Qed.

Lemma xcheck_sels_nd_s4 :
  Forall (fun ts => NoDup (snd ts)) s4.(State.allowedSelectors).
Proof.
  vm_compute. repeat (apply Forall_cons; [|]); try apply Forall_nil;
  repeat constructor; simpl; intuition (try discriminate).
Qed.

Lemma xcheck_pruned_s4 :
  Forall (fun ts => (length (snd ts) > 0)%nat) s4.(State.allowedSelectors).
Proof.
  vm_compute. repeat (apply Forall_cons; [|]); try apply Forall_nil;
  simpl; lia.
Qed.

(** Final state preserves Valid.state. *)
Lemma xcheck_valid_s4 : Valid.state s4.
Proof.
  constructor.
  - exact xcheck_targets_nd_s4.
  - exact xcheck_keys_nd_s4.
  - exact xcheck_sels_nd_s4.
  - exact xcheck_pruned_s4.
  - (* Cross-invariant: case-split on target. *)
    unfold cross_invariant. intros target.
    change s4.(State.targets) with [20%Z; 10%Z].
    change s4.(State.allowedSelectors) with [(10%Z, [1001%Z]); (20%Z, [2000%Z])].
    destruct (Z.eq_dec target 20) as [Ht20|Ht20].
    + subst target.
      change (list_contains [20%Z; 10%Z] 20) with true.
      change (allowed_for [(10%Z, [1001%Z]); (20%Z, [2000%Z])] 20) with [2000%Z].
      split; intros _; [simpl; lia | reflexivity].
    + destruct (Z.eq_dec target 10) as [Ht10|Ht10].
      * subst target.
        change (list_contains [20%Z; 10%Z] 10) with true.
        change (allowed_for [(10%Z, [1001%Z]); (20%Z, [2000%Z])] 10) with [1001%Z].
        split; intros _; [simpl; lia | reflexivity].
      * (* target <> 10, target <> 20: both list_contains and allowed_for
           yield the trivially-false / empty result. *)
        assert (H20 : (20 =? target) = false)
          by (apply Z.eqb_neq; intros H; apply Ht20; symmetry; exact H).
        assert (H10 : (10 =? target) = false)
          by (apply Z.eqb_neq; intros H; apply Ht10; symmetry; exact H).
        unfold list_contains, allowed_for.
        rewrite H20, H10. simpl.
        split.
        -- intros Hc. discriminate.
        -- intros H. exfalso. lia.
Qed.

End XCheck.

End SelectorRegistryValidity.
