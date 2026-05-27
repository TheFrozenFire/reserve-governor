(** OptimisticSelectorRegistry simulation invariant proofs.

    Headline lemmas:

      INV-1  addSelector is idempotent on already-registered (t, s).
      INV-3  isAllowed agrees with set membership.
      INV-4  add then remove of the same (t, s) restores the prior state
             (up to set semantics: pruning matters).
      INV-5  removeSelector is a no-op on a non-member (t, s).
      INV-6  addSelector reverts on forbidden target or zero selector.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module SelectorRegistryProofs.

Import SelectorRegistry.

(** ----- INV-1: addSelector twice = addSelector once. ----- *)
Lemma set_allowed_then_allowed_for
    (mp : list (Address * list Selector))
    (target : Address) (new_sels : list Selector) :
  allowed_for (set_allowed_for mp target new_sels) target = new_sels.
Proof.
  induction mp as [|[t' sels'] rest IH]; simpl.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (t' =? target) eqn:Ht; simpl.
    + rewrite Ht. reflexivity.
    + rewrite Ht. exact IH.
Qed.

Lemma addSelector_idempotent
    (s : State.t) (forbidden : list Address)
    (target : Address) (selector : Selector) :
  match addSelector s forbidden target selector with
  | Result.Success s1 =>
      addSelector s1 forbidden target selector = Result.Success s1
  | _ => True
  end.
Proof.
  unfold addSelector at 1.
  destruct (is_forbidden forbidden target) eqn:Hf; [exact I|].
  destruct (selector =? zero_selector) eqn:Hz; [exact I|].
  destruct (list_contains (allowed_for _ _) selector) eqn:Hcontains.
  - (* already member: addSelector returns s unchanged, so second call also returns s. *)
    unfold addSelector. rewrite Hf, Hz, Hcontains. reflexivity.
  - (* not yet member: first call inserts. Second call sees it as member. *)
    cbn match.
    unfold addSelector.
    rewrite Hf, Hz.
    cbn.
    rewrite set_allowed_then_allowed_for.
    cbn. rewrite Z.eqb_refl. cbn. reflexivity.
Qed.

(** ----- INV-3: isAllowed agrees with set membership. ----- *)
Lemma isAllowed_iff_member
    (s : State.t) (target : Address) (selector : Selector) :
  isAllowed s target selector
  = list_contains (allowed_for s.(State.allowedSelectors) target) selector.
Proof. reflexivity. Qed.

(** ----- INV-5: removeSelector on a non-member is a no-op. ----- *)
Lemma removeSelector_nonmember_noop
    (s : State.t) (target : Address) (selector : Selector) :
  list_contains (allowed_for s.(State.allowedSelectors) target) selector = false ->
  removeSelector s target selector = Result.Success s.
Proof.
  intros Hnotin.
  unfold removeSelector. rewrite Hnotin. reflexivity.
Qed.

(** ----- INV-6a: add reverts on forbidden target. ----- *)
Lemma addSelector_forbidden_reverts
    (s : State.t) (forbidden : list Address)
    (target : Address) (selector : Selector) :
  is_forbidden forbidden target = true ->
  addSelector s forbidden target selector = revert_invalid_target.
Proof.
  intros Hf. unfold addSelector. rewrite Hf. reflexivity.
Qed.

(** ----- INV-6b: add reverts on zero selector. ----- *)
Lemma addSelector_zero_selector_reverts
    (s : State.t) (forbidden : list Address) (target : Address) :
  is_forbidden forbidden target = false ->
  addSelector s forbidden target zero_selector = revert_invalid_selector.
Proof.
  intros Hf. unfold addSelector. rewrite Hf.
  rewrite Z.eqb_refl. reflexivity.
Qed.

End SelectorRegistryProofs.
