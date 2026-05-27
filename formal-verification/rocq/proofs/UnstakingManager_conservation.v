(** UnstakingManager conservation deltas.

    This file proves INV-5 — the conservation invariant listed in the
    [UnstakingManager.v] header but previously only stated abstractly.
    Each of the three storage-mutating operations changes the running
    [total_active] sum by a known, exact delta:

      INV-5.a  [createLock] with [unlockTime > 0]:
                 total_active post = total_active pre + amount

      INV-5.b  [createLock] with [unlockTime = 0]:
                 total_active post = total_active pre
               (the fresh slot is shaped like [default_lock] for the
               purposes of [active_amount].)

      INV-5.c  [cancelLock] success:
                 total_active post = total_active pre
                                     - active_amount (lock_at pre lockId)

      INV-5.d  [claimLock] success:
                 total_active post = total_active pre - lock.amount
               where [lock = lock_at pre lockId] (the pre-claim slot).

    Plus a U256-bound result tying [total_active] to the per-lock
    [amount] field, and a [vm_compute] cross-check pinning a concrete
    (create, claim, cancel) sequence.

    The helper lemmas about [total_active] over append and [set_nth]
    are reproduced locally rather than imported from
    [Integration_withdraw_lockup.v]: that file sits later in the
    [_RocqProject] (after the [StakingVaultExchange] tier) and the
    helpers themselves are short. Reproducing them keeps the layering
    clean and the dependency footprint minimal.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import ReserveGovernor.proofs.UnstakingManager.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module UnstakingManagerConservation.

Import ReserveGovernor.simulations.UnstakingManager.
Import UnstakingManager.
Import UnstakingManagerProofs.

(** ===== Local helpers ===== *)

(** Appending one lock to the locks list adds exactly its
    [active_amount] to the running sum. *)
Lemma total_active_app_singleton (locks : list Lock.t) (new_lock : Lock.t) :
  total_active (locks ++ [new_lock])
    = total_active locks + active_amount new_lock.
Proof.
  induction locks as [|l rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** Replacing one entry of the locks list changes [total_active] by
    exactly the difference in [active_amount]. *)
Lemma total_active_set_nth (locks : list Lock.t) (n : nat) (l_new : Lock.t) :
  (n < length locks)%nat ->
  total_active (set_nth n l_new locks)
  = total_active locks
    - active_amount (nth n locks default_lock)
    + active_amount l_new.
Proof.
  revert n.
  induction locks as [|x rest IH]; intros n Hlen; simpl in Hlen.
  - lia.
  - destruct n; simpl.
    + lia.
    + rewrite IH by lia. lia.
Qed.

(** [active_amount default_lock = 0]. *)
Lemma active_amount_default :
  active_amount default_lock = 0.
Proof. reflexivity. Qed.

(** The [active_amount] of a freshly-created lock equals [amount]
    when [unlockTime > 0]. *)
Lemma active_amount_fresh_active
    (user : Address) (amount unlockTime : U256.t) :
  0 < unlockTime ->
  active_amount {|
    Lock.user       := user;
    Lock.amount     := amount;
    Lock.unlockTime := unlockTime;
    Lock.claimedAt  := 0;
  |} = amount.
Proof.
  intros Hut.
  unfold active_amount; simpl.
  assert (Hne : (unlockTime =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hne. simpl. reflexivity.
Qed.

(** And the [active_amount] of a fresh lock with [unlockTime = 0] is
    zero (the slot is indistinguishable from [default_lock] under
    [active_amount]). *)
Lemma active_amount_fresh_zero_unlock
    (user : Address) (amount : U256.t) :
  active_amount {|
    Lock.user       := user;
    Lock.amount     := amount;
    Lock.unlockTime := 0;
    Lock.claimedAt  := 0;
  |} = 0.
Proof.
  unfold active_amount; simpl. reflexivity.
Qed.

(** ===== INV-5.a: createLock conservation (active branch) ===== *)

(** A successful [createLock] with [unlockTime > 0] increases
    [total_active] by exactly [amount]. The precondition rules out
    the degenerate default-zero shape (proved separately below). *)
Theorem createLock_conservation
    (s s' : State.t)
    (vault caller user : Address)
    (amount unlockTime : U256.t) :
  0 < unlockTime ->
  createLock s vault caller user amount unlockTime = Result.Success s' ->
  total_active s'.(State.locks)
    = total_active s.(State.locks) + amount.
Proof.
  intros Hut Hok.
  unfold createLock in Hok.
  destruct (negb (caller =? vault)) eqn:Hauth; [discriminate|].
  injection Hok as Hs'. subst s'.
  simpl.
  rewrite total_active_app_singleton.
  rewrite active_amount_fresh_active by exact Hut.
  reflexivity.
Qed.

(** ===== INV-5.b: createLock with zero unlockTime is a no-op ===== *)

(** A successful [createLock] with [unlockTime = 0] leaves
    [total_active] unchanged. The newly-appended lock has
    [active_amount = 0] (its [unlockTime = 0] zeros out the contribution),
    so the sum is preserved. Corner case for completeness; production
    [withdraw_with_lockup] always supplies
    [block.timestamp + unstakingDelay], which is strictly positive. *)
Theorem createLock_with_zero_unlock_no_delta
    (s s' : State.t)
    (vault caller user : Address)
    (amount : U256.t) :
  createLock s vault caller user amount 0 = Result.Success s' ->
  total_active s'.(State.locks)
    = total_active s.(State.locks).
Proof.
  intros Hok.
  unfold createLock in Hok.
  destruct (negb (caller =? vault)) eqn:Hauth; [discriminate|].
  injection Hok as Hs'. subst s'.
  simpl.
  rewrite total_active_app_singleton.
  rewrite active_amount_fresh_zero_unlock.
  lia.
Qed.

(** ===== INV-5.c: cancelLock conservation ===== *)

(** A successful [cancelLock] decreases [total_active] by exactly
    the cancelled lock's pre-cancel [active_amount]. If the slot was
    already default (active_amount = 0), the auth check would fail
    first and the operation would not be a success — so this delta is
    only realized when the slot was meaningful pre-cancel. *)
Theorem cancelLock_conservation
    (s s' : State.t) (lockId : U256.t) (caller : Address) :
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  cancelLock s lockId caller = Result.Success s' ->
  total_active s'.(State.locks)
    = total_active s.(State.locks)
      - active_amount (lock_at s lockId).
Proof.
  intros Hbound Hok.
  unfold cancelLock in Hok.
  destruct (negb (_ =? _)) eqn:Hauth in Hok; [discriminate|].
  destruct (negb (_ =? _)) eqn:Hclaim in Hok; [discriminate|].
  injection Hok as Hs'. subst s'.
  unfold set_lock. simpl.
  rewrite total_active_set_nth by exact Hbound.
  unfold lock_at.
  rewrite active_amount_default.
  lia.
Qed.

(** ===== INV-5.d: claimLock conservation ===== *)

(** A successful [claimLock] decreases [total_active] by exactly the
    claimed lock's [amount]. The pre-claim lock had [claimedAt = 0]
    and [unlockTime > 0] (the maturity guards passed), so its
    pre-claim [active_amount = amount]. The post-claim lock has
    [claimedAt = now] where [now >= unlockTime > 0], so its post-claim
    [active_amount = 0]. The net delta is therefore [-amount].

    Precondition [0 <= (lock_at s lockId).(Lock.unlockTime)] is the
    same non-negativity assumption used in
    [UnstakingManager.claim_then_claim_reverts]; it is satisfied on-chain
    because all storage slots are U256 values (non-negative by
    construction). Without it [claimLock]'s [unlockTime <= now] guard
    plus [unlockTime != 0] does not entail [now != 0] in the underlying
    [Z], breaking the [active_amount post = 0] step. *)
Theorem claimLock_conservation
    (s s' : State.t) (lockId now : U256.t) :
  (Z.to_nat lockId < length s.(State.locks))%nat ->
  0 <= (lock_at s lockId).(Lock.unlockTime) ->
  claimLock s lockId now = Result.Success s' ->
  total_active s'.(State.locks)
    = total_active s.(State.locks)
      - (lock_at s lockId).(Lock.amount).
Proof.
  intros Hbound Hut_nn Hok.
  unfold claimLock in Hok.
  set (l := lock_at s lockId) in *.
  destruct (negb (andb (negb (l.(Lock.unlockTime) =? 0))
                       (l.(Lock.unlockTime) <=? now))) eqn:Hg1 in Hok;
    [discriminate|].
  destruct (negb (l.(Lock.claimedAt) =? 0)) eqn:Hcl1 in Hok;
    [discriminate|].
  apply negb_false_iff in Hg1.
  apply andb_true_iff in Hg1.
  destruct Hg1 as (Hut_nz_b & Hut_le_b).
  apply negb_true_iff, Z.eqb_neq in Hut_nz_b.
  apply Z.leb_le in Hut_le_b.
  apply negb_false_iff, Z.eqb_eq in Hcl1.
  injection Hok as Hs'. subst s'.
  unfold set_lock. simpl.
  rewrite total_active_set_nth by exact Hbound.
  (* Recognise the nth-read as l. *)
  change (nth (Z.to_nat lockId) s.(State.locks) default_lock) with l.
  (* Pre-claim active_amount = l.amount. *)
  assert (Hpre : active_amount l = l.(Lock.amount)).
  { unfold active_amount.
    rewrite Hcl1.
    assert (Hut_ne : (l.(Lock.unlockTime) =? 0) = false)
      by (apply Z.eqb_neq; exact Hut_nz_b).
    rewrite Hut_ne. simpl. reflexivity. }
  (* now > 0 chain: 0 <= unlockTime, unlockTime != 0 ⟹ unlockTime > 0,
     unlockTime <= now ⟹ now > 0. *)
  assert (Hnow_pos : 0 < now) by lia.
  (* Post-claim active_amount = 0. *)
  assert (Hpost : active_amount {|
    Lock.user       := l.(Lock.user);
    Lock.amount     := l.(Lock.amount);
    Lock.unlockTime := l.(Lock.unlockTime);
    Lock.claimedAt  := now;
  |} = 0).
  { unfold active_amount; simpl.
    assert (Hne : (now =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hne. simpl. reflexivity. }
  rewrite Hpost. rewrite Hpre. lia.
Qed.

(** ===== Bound: total_active is dominated by sum of amounts ===== *)

(** Sum of the [amount] field over all locks. An upper bound on
    [total_active] independent of which locks are active vs. claimed
    vs. cancelled. *)
Fixpoint total_amount (locks : list Lock.t) : U256.t :=
  match locks with
  | [] => 0
  | l :: rest => l.(Lock.amount) + total_amount rest
  end.

(** Pointwise: [active_amount l <= l.(amount)] (it is either equal to
    [amount] when the lock is active, or zero otherwise). *)
Lemma active_amount_le_amount (l : Lock.t) :
  0 <= l.(Lock.amount) ->
  active_amount l <= l.(Lock.amount).
Proof.
  intros Ha. unfold active_amount.
  destruct (andb _ _); lia.
Qed.

(** [active_amount] is non-negative when [amount] is. *)
Lemma active_amount_nonneg (l : Lock.t) :
  0 <= l.(Lock.amount) ->
  0 <= active_amount l.
Proof.
  intros Ha. unfold active_amount.
  destruct (andb _ _); lia.
Qed.

(** [total_active <= total_amount] when each amount is non-negative.
    Combined with [Forall (fun l => U256.Valid.t l.(Lock.amount)) locks]
    and a bound on [total_amount], this yields a U256 bound on
    [total_active]. *)
Theorem total_active_bounded_by_total_amount (locks : list Lock.t) :
  Forall (fun l => 0 <= l.(Lock.amount)) locks ->
  total_active locks <= total_amount locks.
Proof.
  intros HF. induction HF as [|l rest Hl Hrest IH]; simpl.
  - lia.
  - pose proof (active_amount_le_amount l Hl). lia.
Qed.

(** [total_active] is non-negative whenever every per-lock [amount] is.
    Sets up a clean lower bound for the U256 bound proof. *)
Theorem total_active_nonneg (locks : list Lock.t) :
  Forall (fun l => 0 <= l.(Lock.amount)) locks ->
  0 <= total_active locks.
Proof.
  intros HF. induction HF as [|l rest Hl Hrest IH]; simpl.
  - lia.
  - pose proof (active_amount_nonneg l Hl). lia.
Qed.

(** Headline U256 bound: if every per-lock amount is U256-valid AND
    the sum of amounts fits in U256, then [total_active] fits in U256
    as well. The [total_amount] bound is the load-bearing hypothesis;
    a Solidity-side overflow check on the running sum of locked
    amounts would satisfy it directly. *)
Theorem total_active_bounded_by_max_locks (locks : list Lock.t) :
  Forall (fun l => U256.Valid.t l.(Lock.amount)) locks ->
  U256.Valid.t (total_amount locks) ->
  U256.Valid.t (total_active locks).
Proof.
  intros HF Hbound.
  unfold U256.Valid.t in *.
  assert (Hnn : Forall (fun l => 0 <= l.(Lock.amount)) locks).
  { eapply Forall_impl; [|exact HF].
    intros l Hl. unfold U256.Valid.t in Hl. lia. }
  split.
  - apply total_active_nonneg; exact Hnn.
  - pose proof (total_active_bounded_by_total_amount locks Hnn) as Hle.
    lia.
Qed.

(** ===== Cross-check: concrete create / claim / cancel sequence ===== *)

(** Calibration addresses, mirroring the [UnstakingManager_xcheck]
    file's CAS conventions: vault = 100, three users 201/202/203. *)
Definition cc_vault : Address := 100.
Definition cc_user1 : Address := 201.
Definition cc_user2 : Address := 202.

(** Step 1: createLock for user1 with amount=500, unlockTime=100. *)
Definition cc_state_after_create1 : State.t :=
  match createLock empty_state cc_vault cc_vault cc_user1 500 100 with
  | Result.Success s => s
  | _ => empty_state
  end.

(** Step 2: createLock for user2 with amount=300, unlockTime=200. *)
Definition cc_state_after_create2 : State.t :=
  match createLock cc_state_after_create1
          cc_vault cc_vault cc_user2 300 200 with
  | Result.Success s => s
  | _ => cc_state_after_create1
  end.

(** Step 3: claimLock for lockId=0 (user1's lock) at now=150
    (>= unlockTime=100). *)
Definition cc_state_after_claim0 : State.t :=
  match claimLock cc_state_after_create2 0 150 with
  | Result.Success s => s
  | _ => cc_state_after_create2
  end.

(** Step 4: cancelLock for lockId=1 (user2's lock) by user2. *)
Definition cc_state_after_cancel1 : State.t :=
  match cancelLock cc_state_after_claim0 1 cc_user2 with
  | Result.Success s => s
  | _ => cc_state_after_claim0
  end.

(** XCheck 1: after both creates, total_active = 800. *)
Lemma xcheck_total_active_after_creates :
  total_active cc_state_after_create2.(State.locks) = 800.
Proof. vm_compute. reflexivity. Qed.

(** XCheck 2: after claim of lock 0 (amount 500), total_active = 300. *)
Lemma xcheck_total_active_after_claim :
  total_active cc_state_after_claim0.(State.locks) = 300.
Proof. vm_compute. reflexivity. Qed.

(** XCheck 3: after cancel of lock 1 (amount 300), total_active = 0. *)
Lemma xcheck_total_active_after_cancel :
  total_active cc_state_after_cancel1.(State.locks) = 0.
Proof. vm_compute. reflexivity. Qed.

(** XCheck 4: end-to-end delta. The sequence of two creates (+500, +300),
    one claim (-500), one cancel (-300) lands at total_active = 0 from
    a starting total_active = 0. *)
Lemma xcheck_full_sequence_conservation :
  total_active cc_state_after_cancel1.(State.locks)
    = total_active empty_state.(State.locks) + 500 + 300 - 500 - 300.
Proof. vm_compute. reflexivity. Qed.

End UnstakingManagerConservation.
