(** StakingVaultDelegation × CAS witness cross-check.

    Evaluates the [StakingVaultDelegation] simulation on the same
    scenarios used by
    [cas/staking_vault/dual_delegation_independence.gp] and asserts
    identical outputs. Any divergence between the Rocq model and the
    CAS witness corpus fails the build.

    Address convention (matches the CAS script):
      ZERO_ADDR = 0     (address(0))
      ADDR_A    = 2
      ADDR_B    = 3
      ADDR_C    = 4
      ADDR_D    = 5

    Three scenarios are pinned:
      A: mint 100 to A, A.opt -> C, A.std -> D, transfer 30 A -> B.
      B: mint 137 to A, A.opt -> C, then A.opt -> D (full re-point).
      C: mint 40 to A and 60 to B, both A.opt = B.opt = C; transfer
         25 A -> B (shared-delegate no-op).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.proofs.StakingVaultDelegation.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.

Module StakingVaultDelegationXCheck.

Import StakingVaultDelegation.
Import StakingVaultDelegationProofs.

Definition ADDR_A : Address := 2.
Definition ADDR_B : Address := 3.
Definition ADDR_C : Address := 4.
Definition ADDR_D : Address := 5.

(** ---- Scenario A ---- *)
Definition scenarioA : State.t :=
  let s0 := empty_state in
  let s1 := transfer s0 zero_address ADDR_A 100 in
  let s2 := set_opt_delegate s1 ADDR_A ADDR_C in
  let s3 := set_std_delegate s2 ADDR_A ADDR_D in
  transfer s3 ADDR_A ADDR_B 30.

Lemma xcheck_scenarioA_balances_A :
  scenarioA.(State.balances) ADDR_A = 70.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioA_balances_B :
  scenarioA.(State.balances) ADDR_B = 30.
Proof. vm_compute. reflexivity. Qed.

(** After transfer A -> B (30), A still delegates opt -> C; B doesn't
    delegate (defaults to zero_address). So 30 votes move from
    opt[C] (the original 100) into opt[zero], which is a no-op since
    the zero-address sink doesn't get credited.
    Therefore opt[C] drops from 100 to 70.

    Standard side: A delegates -> D, B's delegate is zero_address.
    So std[D] drops from 100 to 70. *)
Lemma xcheck_scenarioA_opt_C_70 :
  scenarioA.(State.opt).(Ledger.votes) ADDR_C = 70.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioA_std_D_70 :
  scenarioA.(State.std).(Ledger.votes) ADDR_D = 70.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioA_opt_B_0 :
  scenarioA.(State.opt).(Ledger.votes) ADDR_B = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioA_std_B_0 :
  scenarioA.(State.std).(Ledger.votes) ADDR_B = 0.
Proof. vm_compute. reflexivity. Qed.

(** ---- Scenario B: full balance migrates on re-point ---- *)
Definition scenarioB : State.t :=
  let s0 := empty_state in
  let s1 := transfer s0 zero_address ADDR_A 137 in
  let s2 := set_opt_delegate s1 ADDR_A ADDR_C in
  set_opt_delegate s2 ADDR_A ADDR_D.

Lemma xcheck_scenarioB_opt_C_zero :
  scenarioB.(State.opt).(Ledger.votes) ADDR_C = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioB_opt_D_137 :
  scenarioB.(State.opt).(Ledger.votes) ADDR_D = 137.
Proof. vm_compute. reflexivity. Qed.

(** ---- Scenario C: shared-delegate transfer no-op ----
    Both A and B optimistic-delegate to C. A transfer between them
    is a no-op on the opt vote vector (move_votes from=to short
    circuit). *)
Definition scenarioC_pre : State.t :=
  let s0 := empty_state in
  let s1 := transfer s0 zero_address ADDR_A 40 in
  let s2 := transfer s1 zero_address ADDR_B 60 in
  let s3 := set_opt_delegate s2 ADDR_A ADDR_C in
  set_opt_delegate s3 ADDR_B ADDR_C.

Definition scenarioC_post : State.t :=
  transfer scenarioC_pre ADDR_A ADDR_B 25.

Lemma xcheck_scenarioC_opt_C_pre_100 :
  scenarioC_pre.(State.opt).(Ledger.votes) ADDR_C = 100.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_scenarioC_opt_C_post_100 :
  scenarioC_post.(State.opt).(Ledger.votes) ADDR_C = 100.
Proof. vm_compute. reflexivity. Qed.

(** Stronger no-op cross-check: the post-transfer opt vote function
    is structurally identical to the pre-transfer one (CAS INV-4).
    Stated at the [Ledger.votes] field level so [vm_compute] can fully
    reduce both maps to the same underlying [if]-tree. *)
Lemma xcheck_scenarioC_opt_votes_unchanged :
  scenarioC_post.(State.opt).(Ledger.votes)
    = scenarioC_pre.(State.opt).(Ledger.votes).
Proof. vm_compute. reflexivity. Qed.

(** ---- move_votes direct probes (CAS INV-4 sanity checks) ---- *)
Lemma xcheck_move_votes_same_target :
  forall (v : Map) (a : Address) (amount : Z),
    move_votes v a a amount = v.
Proof. intros. apply StakingVaultDelegationProofs.move_votes_same_target. Qed.

Lemma xcheck_move_votes_amount_zero :
  forall (v : Map) (from to : Address),
    move_votes v from to 0 = v.
Proof. intros. apply StakingVaultDelegationProofs.move_votes_amount_zero. Qed.

(** ---- CAS INV-5: zero-address sink/source numeric probes ----
    From the CAS scenario: after mint(80, A) with A.opt -> C and
    A.std -> D, the optimistic and standard zero-address slots are
    still 0. *)
Definition mint_scenario : State.t :=
  let s0 := empty_state in
  let s1 := set_opt_delegate s0 ADDR_A ADDR_C in
  let s2 := set_std_delegate s1 ADDR_A ADDR_D in
  transfer s2 zero_address ADDR_A 80.

Lemma xcheck_mint_opt_C_80 :
  mint_scenario.(State.opt).(Ledger.votes) ADDR_C = 80.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mint_std_D_80 :
  mint_scenario.(State.std).(Ledger.votes) ADDR_D = 80.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mint_opt_zero_0 :
  mint_scenario.(State.opt).(Ledger.votes) zero_address = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_mint_std_zero_0 :
  mint_scenario.(State.std).(Ledger.votes) zero_address = 0.
Proof. vm_compute. reflexivity. Qed.

(** Now burn 30 from A. opt[C] drops to 50, std[D] drops to 50,
    both zero-address slots remain 0. *)
Definition burn_scenario : State.t :=
  transfer mint_scenario ADDR_A zero_address 30.

Lemma xcheck_burn_opt_C_50 :
  burn_scenario.(State.opt).(Ledger.votes) ADDR_C = 50.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_burn_std_D_50 :
  burn_scenario.(State.std).(Ledger.votes) ADDR_D = 50.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_burn_opt_zero_0 :
  burn_scenario.(State.opt).(Ledger.votes) zero_address = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_burn_std_zero_0 :
  burn_scenario.(State.std).(Ledger.votes) zero_address = 0.
Proof. vm_compute. reflexivity. Qed.

End StakingVaultDelegationXCheck.
