(** Guardian simulation × CAS witness cross-check.

    Evaluates the [Guardian] simulation on the same probes used by
    [cas/guardian/role_gated_cancel.gp] and asserts identical
    outputs. Any divergence between the Rocq simulation and the CAS
    witness corpus fails the build.

    The CAS script tabulates the cancel authorization truth table and
    the grant/revoke gate; the lemmas below verify the simulation
    produces the same revert vs success outcomes under [vm_compute].

    Calibration:
      ADMIN_ADDR    = 0x0A           (some non-zero address)
      GUARD_ADDR    = 0x14
      MANAGER_ADDR  = 0x1E
      OTHER_ADDR    = 0x28           (no roles)
      GOV_ADDR      = 0x32
      TL_ADDR       = 0x3C
      PID           = 0x100          (opaque oracle output)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Guardian.
Require Import Coq.Lists.List.
Import ListNotations.

Module GuardianXCheck.

Import Guardian.

(** ----- Fixture addresses ----- *)
Definition ADMIN_ADDR   : Address := 10.
Definition GUARD_ADDR   : Address := 20.
Definition MANAGER_ADDR : Address := 30.
Definition OTHER_ADDR   : Address := 40.
Definition GOV_ADDR     : Address := 50.
Definition TL_ADDR      : Address := 60.
Definition NEW_GUARD    : Address := 70.

(** ----- A canonical seed state mirroring a deployed Guardian ----- *)
Definition seed_state : State.t := {|
  State.admins                     := [ADMIN_ADDR];
  State.optimisticGuardians        := [GUARD_ADDR];
  State.optimisticGuardianManagers := [ADMIN_ADDR; MANAGER_ADDR];
|}.

(** ----- Always-true / always-false oracle stubs for vm_compute. ----- *)
Definition always_optimistic (_ : ProposalId) : bool := true.
Definition never_optimistic  (_ : ProposalId) : bool := false.

Definition state_active   (_ : ProposalId) : ProposalState := PSActive.
Definition state_defeated (_ : ProposalId) : ProposalState := PSDefeated.

Definition gpi_const (k : ProposalKey.t) : ProposalId := 256.
Definition has_code_yes (_ : Address) : bool := true.
Definition has_code_no  (_ : Address) : bool := false.
Definition tl_oracle    (_ : Address) : Address := TL_ADDR.

Definition some_key : ProposalKey.t := {|
  ProposalKey.targets   := [];
  ProposalKey.values    := [];
  ProposalKey.calldatas := [];
  ProposalKey.descHash  := 0;
|}.

(** ===== INV-1 truth-table xchecks =====

    Eight diagnostic probes spanning the cancel authorization gate.
    Compare to the CAS INV-1 sweep (cancel_authorized). *)

(** Admin, optimistic+active : Success. *)
Lemma xcheck_admin_optimistic_active :
  exists ev,
    cancel seed_state always_optimistic state_active gpi_const has_code_yes
      ADMIN_ADDR GOV_ADDR some_key
    = Result.Success ev.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Admin, pessimistic+defeated : still Success (admin bypasses checks). *)
Lemma xcheck_admin_pessimistic_defeated :
  exists ev,
    cancel seed_state never_optimistic state_defeated gpi_const has_code_yes
      ADMIN_ADDR GOV_ADDR some_key
    = Result.Success ev.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Guardian, optimistic+active : Success. *)
Lemma xcheck_guardian_optimistic_active :
  exists ev,
    cancel seed_state always_optimistic state_active gpi_const has_code_yes
      GUARD_ADDR GOV_ADDR some_key
    = Result.Success ev.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Guardian, optimistic+defeated : Revert (defeated branch). *)
Lemma xcheck_guardian_optimistic_defeated :
  exists p s,
    cancel seed_state always_optimistic state_defeated gpi_const has_code_yes
      GUARD_ADDR GOV_ADDR some_key
    = Result.Revert p s.
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** Guardian, pessimistic+active : Revert (not_optimistic branch). *)
Lemma xcheck_guardian_pessimistic_active :
  exists p s,
    cancel seed_state never_optimistic state_active gpi_const has_code_yes
      GUARD_ADDR GOV_ADDR some_key
    = Result.Revert p s.
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** Unknown caller : Revert (unauthorized branch). *)
Lemma xcheck_unauthorized :
  exists p s,
    cancel seed_state always_optimistic state_active gpi_const has_code_yes
      OTHER_ADDR GOV_ADDR some_key
    = Result.Revert p s.
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** Admin, governor with no code : Revert (invalid_governor). *)
Lemma xcheck_admin_no_code_governor :
  exists p s,
    cancel seed_state always_optimistic state_active gpi_const has_code_no
      ADMIN_ADDR GOV_ADDR some_key
    = Result.Revert p s.
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** Admin, governor = 0 : Revert (invalid_governor). *)
Lemma xcheck_admin_zero_governor :
  exists p s,
    cancel seed_state always_optimistic state_active gpi_const has_code_yes
      ADMIN_ADDR 0 some_key
    = Result.Revert p s.
Proof. vm_compute. do 2 eexists. reflexivity. Qed.

(** ===== INV-2 grant gate xchecks ===== *)

(** Manager + non-zero account : Success, account inserted. *)
Lemma xcheck_grant_by_manager :
  match grantOptimisticGuardian seed_state MANAGER_ADDR NEW_GUARD with
  | Result.Success s' =>
      addr_in s'.(State.optimisticGuardians) NEW_GUARD = true /\
      addr_in s'.(State.optimisticGuardians) GUARD_ADDR = true
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** Admin is also a manager in seed_state (constructor mirrors
    Guardian.sol#L47). Verify admin can grant. *)
Lemma xcheck_grant_by_admin :
  exists s',
    grantOptimisticGuardian seed_state ADMIN_ADDR NEW_GUARD = Result.Success s'.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Non-manager caller : Revert. *)
Lemma xcheck_grant_by_other :
  grantOptimisticGuardian seed_state OTHER_ADDR NEW_GUARD = revert_missing_manager.
Proof. vm_compute. reflexivity. Qed.

(** Manager + zero account : Revert. *)
Lemma xcheck_grant_zero_account :
  grantOptimisticGuardian seed_state MANAGER_ADDR 0 = revert_zero_address.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-3 revoke gate xchecks ===== *)

(** Admin caller, valid governor + timelock : Success. *)
Lemma xcheck_revoke_by_admin :
  exists ev,
    revokeOptimisticProposer seed_state tl_oracle has_code_yes
      ADMIN_ADDR GOV_ADDR NEW_GUARD = Result.Success ev.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Manager-only caller : Revert (missing admin). *)
Lemma xcheck_revoke_by_manager :
  revokeOptimisticProposer seed_state tl_oracle has_code_yes
    MANAGER_ADDR GOV_ADDR NEW_GUARD = revert_missing_admin.
Proof. vm_compute. reflexivity. Qed.

(** Guardian-only caller : Revert. *)
Lemma xcheck_revoke_by_guardian :
  revokeOptimisticProposer seed_state tl_oracle has_code_yes
    GUARD_ADDR GOV_ADDR NEW_GUARD = revert_missing_admin.
Proof. vm_compute. reflexivity. Qed.

(** Admin caller, governor with no code : Revert (invalid_governor). *)
Lemma xcheck_revoke_no_code_gov :
  revokeOptimisticProposer seed_state tl_oracle has_code_no
    ADMIN_ADDR GOV_ADDR NEW_GUARD = revert_invalid_governor.
Proof. vm_compute. reflexivity. Qed.

(** ===== INV-4 grant monotonicity xcheck ===== *)

(** Granting an account already present is a no-op on the set. *)
Lemma xcheck_grant_idempotent :
  match grantOptimisticGuardian seed_state MANAGER_ADDR GUARD_ADDR with
  | Result.Success s' =>
      s'.(State.optimisticGuardians) = seed_state.(State.optimisticGuardians)
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End GuardianXCheck.
