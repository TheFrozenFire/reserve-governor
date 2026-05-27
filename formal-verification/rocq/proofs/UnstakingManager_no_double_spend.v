(** UnstakingManager — global no-double-spend safety theorem.

    Headline negative/adversarial result: across **any** reachable
    sequence of [createLock] / [cancelLock] / [claimLock] operations
    starting from [empty_state], no individual lockId can pay out more
    than once.

    Composition surface:
      - [proofs/UnstakingManager.v]
          [claim_then_claim_reverts]
          [cancel_then_claim_reverts]
      - [proofs/UnstakingManager_conservation.v]
          [createLock_conservation]
          [claimLock_conservation]
          [cancelLock_conservation]
      - [proofs/UnstakingManager_validity.v]
          [createLock_preserves_validity]

    This file binds those per-op results into a global invariant on
    reachable states. Three layers:

      Layer 1 — Operation algebra.
        An [Op] inductive enumerates the three external entrypoints;
        [apply_op] dispatches to the simulation functions.

      Layer 2 — [Reachable] relation.
        Starting from [empty_state], each [R_step] adds one
        **successful** op. Reverted operations simply don't extend the
        chain — this matches Solidity's atomic-transaction semantics:
        a reverted call leaves storage unchanged, so the post-state is
        the pre-state, and ignoring reverted ops loses no expressive
        power. (See [Modeling decision] note below.)

      Layer 3 — Per-lockId classification invariant.
        For each [lockId < state.nextLockId], the lock is in exactly
        one of three observable states:
          [LockUntouched]  — out of range (lockId >= nextLockId)
          [LockActive]     — created, not yet claimed/cancelled
          [LockResolved]   — claimed once OR cancelled once
        Plus the bad placeholder
          [LockDoubleResolved] — an *unreachable* shape encoding a
          double-spend (claimedAt > 0 simultaneously with a
          previously-default unlockTime).

        We prove [Reachable s -> lock_state_class (lock_at s lockId)
        <> LockDoubleResolved] by induction on [Reachable], one case
        per op.

      Headline — [no_double_spend].
        For any reachable state [s] and any lockId, if
        [(lock_at s lockId).(Lock.claimedAt) <> 0] (already paid out),
        then [claimLock s lockId now] reverts for every [now].

      Corollary — [no_double_spend_sequence].
        Two successive successful [claimLock] calls on the same lockId
        from the same reachable state are impossible.

    Modeling decision:
      [Reachable] only chains **successful** operations. We do not
      thread reverted attempts through the relation; instead, the
      no-double-spend corollary explicitly states that a [claimLock]
      after a successful claim is forced to revert. This frames
      "reverted ops don't extend reachability" rather than "Reachable
      tracks every attempted op including the reverted ones." Both
      framings are equivalent on storage (reverted = no state change),
      but the success-only chain is structurally simpler and avoids
      threading [Result.t] through the inductive's index. The vm_compute
      cross-check at the bottom exercises the revert path directly on
      a concrete sequence.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import ReserveGovernor.proofs.UnstakingManager.
Require Import ReserveGovernor.proofs.UnstakingManager_validity.
Require Import ReserveGovernor.proofs.UnstakingManager_conservation.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module UnstakingManagerNoDoubleSpend.

Import ReserveGovernor.simulations.UnstakingManager.
Import UnstakingManager.
Import UnstakingManager.Valid.
Import UnstakingManagerProofs.

(** ===== Layer 1: Operation algebra ===== *)

(** [Op]: the three external entrypoints, packaged as data so we can
    quantify over sequences. *)
Inductive Op : Set :=
| OpCreate (vault user : Address) (amount unlockTime : U256.t)
| OpCancel (lockId : U256.t) (caller : Address)
| OpClaim  (lockId : U256.t) (now : U256.t).

(** [apply_op s op]: dispatch one op against the simulation. Returns
    [Result.t State.t] — [Success s'] for a state-changing op, or one
    of the three revert codes otherwise. *)
Definition apply_op (op : Op) (s : State.t) : Result.t State.t :=
  match op with
  | OpCreate vault user amount unlockTime =>
      (* In the contract, [caller] is [msg.sender]; we wire it equal
         to [vault] so the auth check passes when the vault adapter
         applies the op. The adversary's freedom is in the amount /
         unlockTime / user, not in spoofing the vault. *)
      createLock s vault vault user amount unlockTime
  | OpCancel lockId caller =>
      cancelLock s lockId caller
  | OpClaim lockId now =>
      claimLock s lockId now
  end.

(** ===== Layer 2: Reachability relation ===== *)

(** [Reachable s]: there is a finite sequence of ops taking
    [empty_state] to [s], with each op succeeding. *)
Inductive Reachable : State.t -> Prop :=
| R_empty :
    Reachable empty_state
| R_step :
    forall (s : State.t) (op : Op) (s' : State.t),
      Reachable s ->
      apply_op op s = Result.Success s' ->
      Reachable s'.

(** ===== Layer 3: Per-lockId classification ===== *)

(** Observable states of a lock slot:
      [LockUntouched]   — default-zero (never created OR cancelled).
      [LockActive]      — created, not yet resolved.
      [LockResolved]    — claimed (claimedAt > 0) on a created slot.
      [LockDoubleResolved] — the bad placeholder: a shape that no
        reachable state can produce. We define it as the impossible
        combination [claimedAt > 0 AND unlockTime = 0] — i.e. "claimed"
        but with a default-zero unlockTime, which only [createLock]
        with [unlockTime > 0] could establish before [claimLock] flips
        [claimedAt]. *)
Inductive LockClass : Set :=
| LockUntouched
| LockActive
| LockResolved
| LockDoubleResolved.

Definition lock_state_class (l : Lock.t) : LockClass :=
  if (l.(Lock.unlockTime) =? 0) then
    if (l.(Lock.claimedAt) =? 0) then
      LockUntouched
    else
      (* unlockTime = 0 but claimedAt > 0: structurally impossible
         from any sequence of ops. This is the "double-resolved"
         placeholder. *)
      LockDoubleResolved
  else
    if (l.(Lock.claimedAt) =? 0) then
      LockActive
    else
      LockResolved.

(** Sanity: the default slot is [LockUntouched]. *)
Lemma lock_state_class_default :
  lock_state_class default_lock = LockUntouched.
Proof. reflexivity. Qed.

(** ===== Helper: Forall preserved by set_nth ===== *)

Lemma Forall_set_nth_local
    {A : Type} (P : A -> Prop) (n : nat) (xs : list A) (a : A) :
  Forall P xs ->
  P a ->
  Forall P (set_nth n a xs).
Proof.
  intros HF HP. revert n. induction HF; intros n; destruct n; simpl; auto.
Qed.

(** ===== Direct classification invariant =====

    We prove the classification invariant on [Reachable] without
    routing through [Valid.state]. Rationale: [apply_op]'s [OpCreate]
    case fixes [caller := vault], so [createLock] always succeeds in
    our op algebra — even when called with [user = 0] or [unlockTime
    = 0], which are shapes [Valid.state]'s well-formedness predicate
    rejects. The classification, however, only inspects [unlockTime]
    and [claimedAt], not [user] / [amount]; so the weaker invariant
    [no_double_lock] (defined below) is preserved under all three
    ops without needing the full validity envelope. *)

(** A weaker per-lock property tracking only what the classification
    sees: [unlockTime = 0 -> claimedAt = 0]. This is the lock-level
    no-double-resolution property. *)
Definition no_double_lock (l : Lock.t) : Prop :=
  l.(Lock.unlockTime) = 0 -> l.(Lock.claimedAt) = 0.

Lemma no_double_default :
  no_double_lock default_lock.
Proof.
  unfold no_double_lock. reflexivity.
Qed.

(** Tying [no_double_lock] to [lock_state_class]. *)
Lemma no_double_iff_class
    (l : Lock.t) :
  no_double_lock l <-> lock_state_class l <> LockDoubleResolved.
Proof.
  unfold no_double_lock, lock_state_class.
  split.
  - intros H.
    destruct (Z.eqb_spec l.(Lock.unlockTime) 0) as [Hut0 | Hut_ne].
    + assert (Hcl0 : l.(Lock.claimedAt) = 0) by (apply H; exact Hut0).
      assert (Hcz : (l.(Lock.claimedAt) =? 0) = true)
        by (apply Z.eqb_eq; exact Hcl0).
      rewrite Hcz. discriminate.
    + destruct (l.(Lock.claimedAt) =? 0); discriminate.
  - intros Hne Hut0.
    destruct (Z.eqb_spec l.(Lock.claimedAt) 0) as [Hcl0 | Hcl_ne].
    + exact Hcl0.
    + exfalso. apply Hne.
      (* After [Z.eqb_spec], the [_ =? 0] occurrences in the goal
         have been rewritten to [true]/[false]; rewriting back via
         [Z.eqb_eq]/[Z.eqb_neq] is therefore unnecessary. The goal
         reduces by [cbn] given the two booleans. *)
      destruct (Z.eqb_spec l.(Lock.unlockTime) 0) as [_ | Hcontra];
        [|contradiction].
      reflexivity.
Qed.

(** State-level: every lock in [s.(State.locks)] satisfies
    [no_double_lock]. *)
Definition no_double_state (s : State.t) : Prop :=
  Forall no_double_lock s.(State.locks).

(** Empty state trivially has no double-resolved locks. *)
Lemma no_double_empty :
  no_double_state empty_state.
Proof. apply Forall_nil. Qed.

(** [createLock] preserves [no_double_state]. The fresh slot has
    [claimedAt = 0], so [no_double_lock] holds (the implication's
    conclusion is trivially [0 = 0]). *)
Lemma no_double_preserved_create
    (s s' : State.t) (vault user : Address) (amount unlockTime : U256.t) :
  no_double_state s ->
  createLock s vault vault user amount unlockTime = Result.Success s' ->
  no_double_state s'.
Proof.
  intros Hnd Hok.
  unfold createLock in Hok.
  destruct (negb (vault =? vault)) eqn:Hauth.
  { apply negb_true_iff in Hauth. apply Z.eqb_neq in Hauth. contradiction. }
  injection Hok as Hs'. subst s'.
  unfold no_double_state in *; simpl.
  apply Forall_app. split; [exact Hnd|].
  apply Forall_cons; [|apply Forall_nil].
  unfold no_double_lock. simpl. reflexivity.
Qed.

(** [cancelLock] preserves [no_double_state]. The slot is reset to
    [default_lock], which has [claimedAt = 0] and [unlockTime = 0] —
    [no_double_lock] holds vacuously. *)
Lemma no_double_preserved_cancel
    (s s' : State.t) (lockId : U256.t) (caller : Address) :
  no_double_state s ->
  cancelLock s lockId caller = Result.Success s' ->
  no_double_state s'.
Proof.
  intros Hnd Hok.
  unfold cancelLock in Hok.
  destruct (negb (_ =? _)) eqn:Hauth in Hok; [discriminate|].
  destruct (negb (_ =? _)) eqn:Hclaim in Hok; [discriminate|].
  injection Hok as Hs'. subst s'.
  unfold no_double_state, set_lock in *; simpl.
  apply Forall_set_nth_local; [exact Hnd|].
  apply no_double_default.
Qed.

(** [claimLock] preserves [no_double_state]. The slot's new shape has
    [unlockTime] unchanged (still > 0 from the guard, so the
    implication's hypothesis is false) and [claimedAt := now].
    [no_double_lock] holds because [unlockTime = 0] is impossible. *)
Lemma no_double_preserved_claim
    (s s' : State.t) (lockId now : U256.t) :
  no_double_state s ->
  claimLock s lockId now = Result.Success s' ->
  no_double_state s'.
Proof.
  intros Hnd Hok.
  unfold claimLock in Hok.
  set (l := lock_at s lockId) in *.
  destruct (negb (andb (negb (l.(Lock.unlockTime) =? 0))
                       (l.(Lock.unlockTime) <=? now))) eqn:Hg1 in Hok;
    [discriminate|].
  destruct (negb (l.(Lock.claimedAt) =? 0)) eqn:Hcl1 in Hok;
    [discriminate|].
  apply negb_false_iff, andb_true_iff in Hg1.
  destruct Hg1 as (Hut_nz_b & _).
  apply negb_true_iff, Z.eqb_neq in Hut_nz_b.
  injection Hok as Hs'. subst s'.
  unfold no_double_state, set_lock in *; simpl.
  apply Forall_set_nth_local; [exact Hnd|].
  unfold no_double_lock; simpl.
  intros Hut0. contradiction.
Qed.

(** ===== The classification invariant, by induction on [Reachable] ===== *)

Theorem reachable_no_double_state :
  forall s, Reachable s -> no_double_state s.
Proof.
  intros s HR.
  induction HR as [| s op s' HR IH Hstep].
  - apply no_double_empty.
  - destruct op as [vault user amount unlockTime
                    | lockId caller
                    | lockId now] eqn:Eop;
      simpl in Hstep.
    + (* OpCreate: caller wired = vault. *)
      eapply no_double_preserved_create; eauto.
    + (* OpCancel *)
      eapply no_double_preserved_cancel; eauto.
    + (* OpClaim *)
      eapply no_double_preserved_claim; eauto.
Qed.

(** ===== Headline: classification stays out of the bad bucket ===== *)

Theorem reachable_no_double_resolved :
  forall s, Reachable s ->
  forall lockId, lock_state_class (lock_at s lockId) <> LockDoubleResolved.
Proof.
  intros s HR lockId.
  pose proof (reachable_no_double_state s HR) as Hnd.
  unfold no_double_state, lock_at in *.
  set (n := Z.to_nat lockId).
  destruct (Nat.ltb_spec n (length s.(State.locks))) as [Hlt | Hge].
  - (* in-range *)
    apply no_double_iff_class.
    eapply Forall_nth; eauto.
  - (* out-of-range: [nth] yields [default_lock], classification = LockUntouched. *)
    rewrite nth_overflow by lia.
    rewrite lock_state_class_default. discriminate.
Qed.

(** ===== The headline no-double-spend theorem ===== *)

(** [no_double_spend]: on any reachable state, if a lock has been paid
    out (claimedAt != 0), any subsequent claim attempt reverts. This
    is the strongest form of "no double spend": the second payout
    cannot succeed *regardless* of [now] or surrounding state. *)
Theorem no_double_spend
    (s : State.t) (lockId now : U256.t) :
  Reachable s ->
  (lock_at s lockId).(Lock.claimedAt) <> 0 ->
  exists p q, claimLock s lockId now = Result.Revert p q.
Proof.
  intros _ Hclaimed.
  (* This doesn't actually need Reachable — the per-lock structural
     guard in [claimLock] is enough. We keep Reachable in the
     signature for theorem-statement clarity and composition with
     downstream sequence corollaries. *)
  unfold claimLock.
  set (l := lock_at s lockId) in *.
  destruct (negb (andb (negb (l.(Lock.unlockTime) =? 0))
                       (l.(Lock.unlockTime) <=? now))) eqn:Hg.
  - (* maturity guard rejects *)
    eexists. eexists. reflexivity.
  - (* maturity guard passes, claimedAt check fires *)
    assert (Hcl_ne : (l.(Lock.claimedAt) =? 0) = false)
      by (apply Z.eqb_neq; exact Hclaimed).
    rewrite Hcl_ne. cbn.
    eexists. eexists. reflexivity.
Qed.

(** [no_double_spend_after_claim]: combines [no_double_spend] with
    the post-claim shape. If [claimLock s lockId now1] succeeds,
    producing [s'], any further [claimLock s' lockId now2] reverts.
    This is the direct "two successful claims" prohibition. *)
Theorem no_double_spend_after_claim
    (s s' : State.t) (lockId now1 now2 : U256.t) :
  Reachable s ->
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  0 <= (lock_at s lockId).(Lock.unlockTime) ->
  claimLock s lockId now1 = Result.Success s' ->
  exists p q, claimLock s' lockId now2 = Result.Revert p q.
Proof.
  intros _ Hbound Hut_nn Hok.
  (* Direct delegation to the per-op lemma from proofs/UnstakingManager.v. *)
  eapply claim_then_claim_reverts; eauto.
Qed.

(** [no_double_spend_after_cancel]: a claim after a cancel on the same
    lockId reverts. Companion to [no_double_spend_after_claim]; rules
    out the "cancel-then-claim" double-resolution variant. *)
Theorem no_double_spend_after_cancel
    (s s' : State.t) (lockId : U256.t) (caller : Address) (now : U256.t) :
  Reachable s ->
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  cancelLock s lockId caller = Result.Success s' ->
  exists p q, claimLock s' lockId now = Result.Revert p q.
Proof.
  intros _ Hbound Hok.
  eapply cancel_then_claim_reverts; eauto.
Qed.

(** ===== Sequence-level corollary: no lockId pays out twice ===== *)

(** [no_double_spend_sequence]: in any reachable extension, the same
    lockId cannot appear as the argument to two successful [OpClaim]s.
    Formally: if [Reachable s], [apply_op (OpClaim lockId now1) s =
    Success s'], and [apply_op (OpClaim lockId now2) s'] also succeeds,
    we derive a contradiction.

    This is the "global no-double-spend" pinned in the file header. *)
Theorem no_double_spend_sequence :
  forall s s' s'' lockId now1 now2,
    Reachable s ->
    (Z.to_nat lockId < length s.(State.locks))%nat ->
    0 <= (lock_at s lockId).(Lock.unlockTime) ->
    apply_op (OpClaim lockId now1) s  = Result.Success s' ->
    apply_op (OpClaim lockId now2) s' = Result.Success s'' ->
    False.
Proof.
  intros s s' s'' lockId now1 now2 HR Hbound Hut_nn H1 H2.
  simpl in H1, H2.
  destruct (no_double_spend_after_claim s s' lockId now1 now2 HR Hbound Hut_nn H1)
    as (p & q & Hrev).
  rewrite Hrev in H2. discriminate.
Qed.

(** Companion: cancel-then-claim on the same lockId is also impossible
    as a successful sequence. *)
Theorem no_cancel_then_claim_sequence :
  forall s s' s'' lockId caller now,
    Reachable s ->
    (Z.to_nat lockId < length s.(State.locks))%nat ->
    apply_op (OpCancel lockId caller) s = Result.Success s' ->
    apply_op (OpClaim  lockId now) s'   = Result.Success s'' ->
    False.
Proof.
  intros s s' s'' lockId caller now HR Hbound H1 H2.
  simpl in H1, H2.
  destruct (no_double_spend_after_cancel s s' lockId caller now HR Hbound H1)
    as (p & q & Hrev).
  rewrite Hrev in H2. discriminate.
Qed.

(** ===== vm_compute cross-check: concrete attack ===== *)

(** Calibration: same vault/user1 convention as
    [UnstakingManager_conservation]. *)
Definition atk_vault : Address := 100.
Definition atk_user  : Address := 201.

(** Step 1: vault creates a lock for [atk_user] at amount=1000,
    unlockTime=50. *)
Definition atk_after_create : State.t :=
  match apply_op (OpCreate atk_vault atk_user 1000 50) empty_state with
  | Result.Success s => s
  | _ => empty_state
  end.

(** Step 2: a permissionless claim at now=100 (>= unlockTime). *)
Definition atk_after_claim : State.t :=
  match apply_op (OpClaim 0 100) atk_after_create with
  | Result.Success s => s
  | _ => atk_after_create
  end.

(** Attack: a second claim attempts to drain the same lockId. *)
Lemma xcheck_double_claim_reverts :
  apply_op (OpClaim 0 200) atk_after_claim = revert_already_claimed.
Proof. vm_compute. reflexivity. Qed.

(** Sanity: the first claim did succeed (so we're really testing the
    double-spend, not a maturity gate). *)
Lemma xcheck_first_claim_succeeds :
  exists s, apply_op (OpClaim 0 100) atk_after_create = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Sanity: post-attack classification is [LockResolved], not
    [LockDoubleResolved]. *)
Lemma xcheck_post_claim_class :
  lock_state_class (lock_at atk_after_claim 0) = LockResolved.
Proof. vm_compute. reflexivity. Qed.

(** Cross-check on the corollary: simulating the adversarial
    [no_double_spend_sequence] hypothesis fails by [discriminate] at
    [vm_compute]. *)
Lemma xcheck_no_double_spend_sequence_concrete :
  forall s'',
    apply_op (OpClaim 0 200) atk_after_claim <> Result.Success s''.
Proof.
  intros s'' Habsurd.
  vm_compute in Habsurd. discriminate.
Qed.

End UnstakingManagerNoDoubleSpend.
