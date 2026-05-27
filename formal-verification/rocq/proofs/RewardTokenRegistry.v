(** RewardTokenRegistry simulation invariant proofs.

    Headline lemmas:

      INV-1  register reverts on duplicate;
             unregister reverts on non-member.
             (No silent idempotence — distinct from SelectorRegistry.)
      INV-2  isRegistered agrees with the underlying set membership.
      INV-3  After a successful register, the token is in the set.
             After a successful unregister, the token is gone.
      INV-4  register reverts on the zero address.
      INV-5  register/unregister revert under failed role checks.
      INV-6  register and unregister of the same fresh token round-trip
             to the original state (proved here in the
             [add_then_remove_restores] lemma).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.RewardTokenRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module RewardTokenRegistryProofs.

Import RewardTokenRegistry.

(** ============================================================
    Section: list_contains / list_remove helpers used inside proofs.
    ============================================================ *)

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
    Section: INV-1 — revert on duplicate / non-member.
    ============================================================ *)

Lemma registerRewardToken_duplicate_reverts
    (s : State.t) (token : Address) :
  list_contains s.(State.rewardTokens) token = true ->
  token <> zero_address ->
  registerRewardToken s token true = revert_already_registered.
Proof.
  intros Hin Hnz. unfold registerRewardToken. simpl.
  destruct (token =? zero_address) eqn:Hz.
  - apply Z.eqb_eq in Hz. contradiction.
  - rewrite Hin. reflexivity.
Qed.

Lemma unregisterRewardToken_nonmember_reverts
    (s : State.t) (token : Address) :
  list_contains s.(State.rewardTokens) token = false ->
  unregisterRewardToken s token true = revert_not_registered.
Proof.
  intros Hnin. unfold unregisterRewardToken. simpl.
  rewrite Hnin. reflexivity.
Qed.

(** ============================================================
    Section: INV-2 — isRegistered observability.
    ============================================================ *)

Lemma isRegistered_iff_member
    (s : State.t) (token : Address) :
  isRegistered s token = list_contains s.(State.rewardTokens) token.
Proof. reflexivity. Qed.

(** ============================================================
    Section: INV-3 — post-condition shape of successful ops.
    ============================================================ *)

Lemma registerRewardToken_success_adds
    (s s' : State.t) (token : Address) :
  registerRewardToken s token true = Result.Success s' ->
  isRegistered s' token = true.
Proof.
  intros Hok. unfold registerRewardToken in Hok. simpl in Hok.
  destruct (token =? zero_address) eqn:Hz; [discriminate|].
  destruct (list_contains s.(State.rewardTokens) token) eqn:Hin; [discriminate|].
  injection Hok as Hs'. rewrite <- Hs'.
  unfold isRegistered. simpl.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(** Helper: removing a key from a list leaves the key absent. *)
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

Lemma unregisterRewardToken_success_removes
    (s s' : State.t) (token : Address) :
  unregisterRewardToken s token true = Result.Success s' ->
  isRegistered s' token = false.
Proof.
  intros Hok. unfold unregisterRewardToken in Hok. simpl in Hok.
  destruct (list_contains s.(State.rewardTokens) token) eqn:Hin; [|discriminate].
  injection Hok as Hs'. rewrite <- Hs'.
  unfold isRegistered. simpl.
  apply list_contains_false_iff.
  apply list_remove_removes.
Qed.

(** ============================================================
    Section: INV-4 — zero-address revert.
    ============================================================ *)

Lemma registerRewardToken_zero_reverts
    (s : State.t) :
  registerRewardToken s zero_address true = revert_zero_address.
Proof. reflexivity. Qed.

(** ============================================================
    Section: INV-5 — role-gated reverts.
    ============================================================ *)

Lemma registerRewardToken_not_owner_reverts
    (s : State.t) (token : Address) :
  registerRewardToken s token false = revert_invalid_caller.
Proof. reflexivity. Qed.

Lemma unregisterRewardToken_not_authorized_reverts
    (s : State.t) (token : Address) :
  unregisterRewardToken s token false = revert_invalid_caller.
Proof. reflexivity. Qed.

(** ============================================================
    Section: INV-6 — add_then_remove restores prior state.
    ============================================================
    When [token] is not already registered and is not zero, register
    followed by unregister yields the original state structurally. *)

Lemma add_then_remove_restores
    (s : State.t) (token : Address) :
  token <> zero_address ->
  list_contains s.(State.rewardTokens) token = false ->
  match registerRewardToken s token true with
  | Result.Success s1 =>
      unregisterRewardToken s1 token true = Result.Success s
  | _ => False
  end.
Proof.
  intros Hnz Hnin.
  unfold registerRewardToken.
  cbn [negb].
  destruct (token =? zero_address) eqn:Hz.
  { apply Z.eqb_eq in Hz. contradiction. }
  rewrite Hnin.
  (* Now we know register succeeds with s1 = (token :: rewardTokens). *)
  unfold unregisterRewardToken.
  cbn [negb].
  (* Compute list_contains on the new state. *)
  cbn [State.rewardTokens list_contains].
  rewrite Z.eqb_refl.
  (* list_remove on (token :: rest) at token reduces. *)
  cbn [list_remove].
  rewrite Z.eqb_refl.
  destruct s as [tg]. simpl in *.
  f_equal. f_equal.
  apply list_remove_not_in.
  apply list_contains_false_iff. exact Hnin.
Qed.

End RewardTokenRegistryProofs.
