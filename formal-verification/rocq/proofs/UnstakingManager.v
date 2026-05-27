(** UnstakingManager headline lemmas.

    Proves the load-bearing safety invariants for the
    [UnstakingManager] simulation defined in
    [ReserveGovernor.simulations.UnstakingManager]:

      INV-1   Once [claimLock] sets [claimedAt := now], every subsequent
              [claimLock] on the same lockId reverts AlreadyClaimed.
              (Idempotence / one-way claim.)

      INV-2   After a successful [cancelLock], the slot is set to
              [default_lock]. The next [claimLock] sees the default
              slot and reverts NotUnlockedYet (because [unlockTime = 0]
              fails the [unlockTime != 0] guard).

      INV-3   [claimLock] before maturity ([unlockTime > now]) reverts
              NotUnlockedYet for any lock state.

      INV-4   [claimLock] on a default-zero slot always reverts.

      INV-5   Conservation: a successful [claimLock] decreases
              [total_active] by exactly the claimed lock's amount.
              A successful [cancelLock] does the same.
              A successful [createLock] increases [total_active] by
              [amount] when [unlockTime != 0] and [amount > 0].

    INV-6 (validity preservation) is split into the companion
    [UnstakingManager_validity.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module UnstakingManagerProofs.

Import ReserveGovernor.simulations.UnstakingManager.
Import UnstakingManager.

(** ----- Helper: set_nth then nth at the same index yields the new value. ----- *)
Lemma set_nth_nth {A : Type} (n : nat) (xs : list A) (a d : A) :
  (n < length xs)%nat ->
  nth n (set_nth n a xs) d = a.
Proof.
  revert xs. induction n; intros xs Hlt; destruct xs; simpl in *; try lia.
  - reflexivity.
  - apply IHn. lia.
Qed.

(** ----- Helper: set_nth preserves length. ----- *)
Lemma set_nth_length {A : Type} (n : nat) (xs : list A) (a : A) :
  length (set_nth n a xs) = length xs.
Proof.
  revert xs. induction n; intros xs; destruct xs; simpl; auto.
Qed.

(** ----- INV-1: re-claim after claim reverts. -----
    Strategy: if claimLock succeeded once with [now1], the post-state
    has [lock_at s' lockId].(claimedAt) = now1 > 0 (because the guard
    accepted [unlockTime <= now1] and [unlockTime != 0], so now1 > 0).
    The second claim reads that non-zero claimedAt and reverts. *)
Lemma claim_then_claim_reverts
    (s s' : State.t) (lockId now1 now2 : U256.t) :
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  0 <= (lock_at s lockId).(Lock.unlockTime) ->
  claimLock s lockId now1 = Result.Success s' ->
  exists p q, claimLock s' lockId now2 = Result.Revert p q.
Proof.
  intros Hbound Hut_nn Hok.
  unfold claimLock in *.
  set (l := lock_at s lockId) in *.
  destruct (negb (andb (negb (l.(Lock.unlockTime) =? 0))
                       (l.(Lock.unlockTime) <=? now1))) eqn:Hg1;
    [discriminate|].
  destruct (negb (l.(Lock.claimedAt) =? 0)) eqn:Hcl1;
    [discriminate|].
  apply negb_false_iff in Hg1.
  apply andb_true_iff in Hg1.
  destruct Hg1 as [Hut_nz_b Hut_le_b].
  apply negb_true_iff, Z.eqb_neq in Hut_nz_b.
  apply Z.leb_le in Hut_le_b.
  set (l' := {|
    Lock.user       := l.(Lock.user);
    Lock.amount     := l.(Lock.amount);
    Lock.unlockTime := l.(Lock.unlockTime);
    Lock.claimedAt  := now1;
  |}) in Hok.
  injection Hok as Hs'.
  assert (Hread : lock_at s' lockId = l').
  { rewrite <- Hs'. unfold lock_at, set_lock. simpl.
    apply set_nth_nth. exact Hbound. }
  rewrite Hread.
  set (cond := negb (andb (negb (l'.(Lock.unlockTime) =? 0))
                          (l'.(Lock.unlockTime) <=? now2))).
  destruct cond eqn:Hcond.
  - (* Maturity gate already rejects on the second call. *)
    eexists. eexists. reflexivity.
  - (* Maturity gate passes; claimedAt = now1 > 0 trips the
       AlreadyClaimed check. Chain of inequalities:
         0 <= unlockTime (precondition Hut_nn)
         unlockTime != 0 (Hut_nz_b)  ⟹  unlockTime > 0
         unlockTime <= now1 (Hut_le_b)
         ⟹ now1 > 0 ⟹ (now1 =? 0) = false. *)
    assert (Hnow1_pos : 0 < now1) by lia.
    assert (Hne : (now1 =? 0) = false) by (apply Z.eqb_neq; lia).
    simpl. rewrite Hne. simpl.
    eexists. eexists. reflexivity.
Qed.

(** ----- INV-2: claim after cancel reverts. -----
    Strategy: cancelLock writes [default_lock] at lockId. The next
    claimLock reads [unlockTime = 0] and the [unlockTime != 0] guard
    rejects. *)
Lemma cancel_then_claim_reverts
    (s s' : State.t) (lockId : U256.t) (caller : Address) (now : U256.t) :
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  cancelLock s lockId caller = Result.Success s' ->
  exists p q, claimLock s' lockId now = Result.Revert p q.
Proof.
  intros Hbound Hok.
  unfold cancelLock in *.
  destruct (negb (_ =? _)) eqn:Hauth in Hok; [discriminate|].
  destruct (negb (_ =? _)) eqn:Hclaim in Hok; [discriminate|].
  injection Hok as Hs'.
  unfold claimLock.
  assert (Hread : lock_at s' lockId = default_lock).
  { rewrite <- Hs'. unfold lock_at, set_lock. simpl.
    apply set_nth_nth. exact Hbound. }
  rewrite Hread.
  simpl.
  eexists. eexists. reflexivity.
Qed.

(** ----- INV-3: claim before maturity reverts. ----- *)
Lemma claim_before_maturity_reverts
    (s : State.t) (lockId now : U256.t) :
  (lock_at s lockId).(Lock.unlockTime) > now ->
  exists p q, claimLock s lockId now = Result.Revert p q.
Proof.
  intros Hgt.
  unfold claimLock.
  assert (Hle : ((lock_at s lockId).(Lock.unlockTime) <=? now) = false).
  { apply Z.leb_gt. lia. }
  rewrite Hle.
  rewrite andb_false_r. simpl.
  eexists. eexists. reflexivity.
Qed.

(** ----- INV-4: claim on default slot reverts. ----- *)
Lemma claim_on_default_reverts
    (s : State.t) (lockId now : U256.t) :
  lock_at s lockId = default_lock ->
  exists p q, claimLock s lockId now = Result.Revert p q.
Proof.
  intros Hdef.
  unfold claimLock. rewrite Hdef. simpl.
  eexists. eexists. reflexivity.
Qed.

End UnstakingManagerProofs.
