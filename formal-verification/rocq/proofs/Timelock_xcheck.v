(** Timelock simulation x CAS witness cross-check.

    Evaluates the [Timelock] simulation on the same scenarios used by
    [cas/timelock/scheduling_ordering.gp] and asserts identical
    outcomes. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build (via [vm_compute] reflexivity).

    Scenarios reproduced:
      - INV-1: execute before maturity reverts NotReady.
      - INV-2: re-execute after Done reverts NotReady.
      - INV-3: execute after cancel reverts NotReady.
      - INV-4: bypass without PROPOSER_ROLE reverts Unauthorized.
      - INV-5: bypass(B) after scheduleBatch(A) leaves A's
        executableAt unchanged and A still Waiting.
      - INV-6: bypass on an already-scheduled id reverts
        OperationConflict.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Timelock.
Require Import Coq.Lists.List.
Import ListNotations.

Module TimelockXCheck.

Import Timelock.

(** Same minDelay = 100 as the CAS probe. *)
Definition s0 : State.t := empty_state 100.

(** ---- INV-1: execute before maturity reverts NotReady ----
    CAS sequence: scheduleBatch(id=42, delay=200, now=1000)
    -> op ready at 1200; execute at now=1199 should revert. *)
Definition cas_inv1_sched : State.t :=
  match scheduleBatch s0 42 200 1000 true with
  | Result.Success s => s
  | _ => s0
  end.

Lemma xcheck_inv1_execute_early_reverts :
  executeBatch cas_inv1_sched 42 1199 true = revert_not_ready.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv1_execute_at_maturity_succeeds :
  exists s, executeBatch cas_inv1_sched 42 1200 true = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

(** ---- INV-2: re-execute after Done reverts NotReady ----
    Sequence: scheduleBatch(id=7, delay=100, now=500), execute@700,
    then re-execute@800. *)
Definition cas_inv2_sched : State.t :=
  match scheduleBatch s0 7 100 500 true with
  | Result.Success s => s
  | _ => s0
  end.

Definition cas_inv2_after_exec : State.t :=
  match executeBatch cas_inv2_sched 7 700 true with
  | Result.Success s => s
  | _ => s0
  end.

Lemma xcheck_inv2_first_execute_succeeds :
  exists s, executeBatch cas_inv2_sched 7 700 true = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_inv2_reexecute_reverts :
  executeBatch cas_inv2_after_exec 7 800 true = revert_not_ready.
Proof. vm_compute. reflexivity. Qed.

(** ---- INV-3: execute after cancel reverts NotReady ----
    Sequence: scheduleBatch(id=9, delay=100, now=500), cancel@550,
    execute@9999. *)
Definition cas_inv3_sched : State.t :=
  match scheduleBatch s0 9 100 500 true with
  | Result.Success s => s
  | _ => s0
  end.

Definition cas_inv3_after_cancel : State.t :=
  match cancel cas_inv3_sched 9 550 true with
  | Result.Success s => s
  | _ => s0
  end.

Lemma xcheck_inv3_cancel_succeeds :
  exists s, cancel cas_inv3_sched 9 550 true = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_inv3_execute_after_cancel_reverts :
  executeBatch cas_inv3_after_cancel 9 9999 true = revert_not_ready.
Proof. vm_compute. reflexivity. Qed.

(** ---- INV-4: bypass without PROPOSER_ROLE reverts Unauthorized ---- *)
Lemma xcheck_inv4_bypass_no_proposer_reverts :
  executeBatchBypass s0 11 1000 false true = revert_unauthorized.
Proof. vm_compute. reflexivity. Qed.

(** ---- INV-5: scheduleBatch(A); bypass(B) leaves A unchanged ----
    Same constants as CAS: idA=100, idB=200, delay=500, nowS=1000,
    nowB=1100. *)
Definition cas_inv5_after_sched : State.t :=
  match scheduleBatch s0 100 500 1000 true with
  | Result.Success s => s
  | _ => s0
  end.

Definition cas_inv5_after_bypass : State.t :=
  match executeBatchBypass cas_inv5_after_sched 200 1100 true true with
  | Result.Success s => s
  | _ => s0
  end.

(** A's executableAt before bypass: nowS + delay = 1500. *)
Lemma xcheck_inv5_A_ts_before : get_ts cas_inv5_after_sched 100 = 1500.
Proof. vm_compute. reflexivity. Qed.

(** A's executableAt after bypass: still 1500 (unchanged). *)
Lemma xcheck_inv5_A_ts_after  : get_ts cas_inv5_after_bypass 100 = 1500.
Proof. vm_compute. reflexivity. Qed.

(** A is still Waiting at nowB = 1100. *)
Lemma xcheck_inv5_A_waiting :
  op_status cas_inv5_after_bypass 100 1100 = OpWaiting.
Proof. vm_compute. reflexivity. Qed.

(** B has transitioned to Done. *)
Lemma xcheck_inv5_B_done :
  op_status cas_inv5_after_bypass 200 1100 = OpDone.
Proof. vm_compute. reflexivity. Qed.

(** A becomes Ready at its original maturity. *)
Lemma xcheck_inv5_A_ready_at_maturity :
  op_status cas_inv5_after_bypass 100 1500 = OpReady.
Proof. vm_compute. reflexivity. Qed.

(** Early-execute attempt on A reverts. *)
Lemma xcheck_inv5_A_early_execute_reverts :
  executeBatch cas_inv5_after_bypass 100 1100 true = revert_not_ready.
Proof. vm_compute. reflexivity. Qed.

(** ---- INV-6: bypass on an already-scheduled op reverts ----
    Sequence: scheduleBatch(id=77, delay=200, now=1000), bypass@1100. *)
Definition cas_inv6_sched : State.t :=
  match scheduleBatch s0 77 200 1000 true with
  | Result.Success s => s
  | _ => s0
  end.

Lemma xcheck_inv6_bypass_collision_reverts :
  executeBatchBypass cas_inv6_sched 77 1100 true true = revert_op_conflict.
Proof. vm_compute. reflexivity. Qed.

End TimelockXCheck.
