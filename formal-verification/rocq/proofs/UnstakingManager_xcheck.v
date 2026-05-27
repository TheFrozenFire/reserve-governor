(** UnstakingManager simulation × CAS witness cross-check.

    Evaluates the [UnstakingManager] simulation on the same scenarios
    used by [cas/unstaking_manager/lock_lifecycle.gp] and asserts
    identical outcomes. Any divergence between the Rocq simulation and
    the CAS witness corpus fails the build.

    Scenarios reproduced:
      - INV-1: re-claim after claim reverts (AlreadyClaimed).
      - INV-2: claim after cancel reverts (NotUnlockedYet).
      - INV-4: claim on a default-zero slot reverts.
      - INV-5: conservation across create / claim / cancel.
      - INV-6: re-cancel after cancel reverts (Unauthorized).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import Coq.Lists.List.
Import ListNotations.

Module UnstakingManagerXCheck.

Import UnstakingManager.

(** CAS addresses, encoded as the same small U256.t values it uses. *)
Definition vault : Address := 100.
Definition user1 : Address := 201.
Definition user2 : Address := 202.
Definition user3 : Address := 203.

(** ----- INV-4: claim on default slot reverts. CAS reports
    "revert (NotUnlockedYet)". Our [revert_not_unlocked] uses
    offsets (32, 32). ----- *)
Lemma xcheck_claim_default_slot_reverts :
  claimLock {| State.nextLockId := 1;
               State.locks := [default_lock] |} 0 99999
  = revert_not_unlocked.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-1: re-claim after successful claim reverts AlreadyClaimed.
    CAS sequence: create(user=200, amt=1000, t=50), claim@100, claim@200.
    The second claim should hit the AlreadyClaimed branch. ----- *)
Definition cas_inv1_state : State.t :=
  match createLock empty_state vault vault 200 1000 50 with
  | Result.Success s => s
  | _ => empty_state
  end.

Definition cas_inv1_after_first_claim : State.t :=
  match claimLock cas_inv1_state 0 100 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_first_claim_succeeds :
  exists s, claimLock cas_inv1_state 0 100 = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_reclaim_reverts :
  claimLock cas_inv1_after_first_claim 0 200 = revert_already_claimed.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: cancel then claim reverts NotUnlockedYet.
    CAS sequence: create(user=200, amt=1000, t=50), cancel by user, claim@9999. ----- *)
Definition cas_inv2_after_cancel : State.t :=
  match cancelLock cas_inv1_state 0 200 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_cancel_succeeds :
  exists s, cancelLock cas_inv1_state 0 200 = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_claim_after_cancel_reverts :
  claimLock cas_inv2_after_cancel 0 9999 = revert_not_unlocked.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: re-cancel after cancel reverts Unauthorized.
    The second cancel observes user = 0 != caller. ----- *)
Lemma xcheck_recancel_reverts :
  cancelLock cas_inv2_after_cancel 0 200 = revert_unauthorized.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-5: conservation. CAS sequence: 3 creates (500, 300, 700)
    -> balance=1500; claim(0) -> 1000; cancel(2) -> 300. ----- *)
Definition cas_inv5_after_creates : State.t :=
  match createLock empty_state vault vault user1 500 100 with
  | Result.Success s1 =>
    match createLock s1 vault vault user2 300 200 with
    | Result.Success s2 =>
      match createLock s2 vault vault user3 700 150 with
      | Result.Success s3 => s3
      | _ => empty_state
      end
    | _ => empty_state
    end
  | _ => empty_state
  end.

Lemma xcheck_total_active_after_creates :
  total_active cas_inv5_after_creates.(State.locks) = 1500.
Proof. vm_compute. reflexivity. Qed.

Definition cas_inv5_after_claim0 : State.t :=
  match claimLock cas_inv5_after_creates 0 100 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_total_active_after_claim0 :
  total_active cas_inv5_after_claim0.(State.locks) = 1000.
Proof. vm_compute. reflexivity. Qed.

Definition cas_inv5_after_cancel2 : State.t :=
  match cancelLock cas_inv5_after_claim0 2 user3 with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_total_active_after_cancel2 :
  total_active cas_inv5_after_cancel2.(State.locks) = 300.
Proof. vm_compute. reflexivity. Qed.

End UnstakingManagerXCheck.
