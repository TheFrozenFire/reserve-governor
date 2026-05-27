(** RewardTokenRegistry simulation × CAS witness cross-check.

    Evaluates the [RewardTokenRegistry] simulation on the same scenarios
    used by [cas/reward_token_registry/registration_lifecycle.gp] and
    asserts identical outcomes via [vm_compute].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.RewardTokenRegistry.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module RewardTokenRegistryXCheck.

Import RewardTokenRegistry.

(** ----- INV-1: register reverts on duplicate; unregister reverts on
    non-member. ----- *)

Definition inv1_after_first : State.t :=
  match registerRewardToken empty_state 100 true with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_first_register_state :
  inv1_after_first.(State.rewardTokens) = [100].
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_duplicate_register_reverts :
  registerRewardToken inv1_after_first 100 true = revert_already_registered.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_unregister_nonmember_reverts :
  unregisterRewardToken empty_state 999 true = revert_not_registered.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: isRegistered agrees with set membership across a mixed
    sequence.

    Sequence reproduced from the CAS witness:
      register(100); register(200); register(300);
      unregister(200).
    Final state should report:
      isRegistered(100) = true
      isRegistered(200) = false
      isRegistered(300) = true
      isRegistered(400) = false
      isRegistered(0)   = false  *)

Definition inv2_final : State.t :=
  match registerRewardToken empty_state 100 true with
  | Result.Success s1 =>
    match registerRewardToken s1 200 true with
    | Result.Success s2 =>
      match registerRewardToken s2 300 true with
      | Result.Success s3 =>
        match unregisterRewardToken s3 200 true with
        | Result.Success s4 => s4
        | _ => empty_state
        end
      | _ => empty_state
      end
    | _ => empty_state
    end
  | _ => empty_state
  end.

Lemma xcheck_inv2_100_present :
  isRegistered inv2_final 100 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_200_absent :
  isRegistered inv2_final 200 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_300_present :
  isRegistered inv2_final 300 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_400_absent :
  isRegistered inv2_final 400 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_zero_absent :
  isRegistered inv2_final 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-3: register then unregister restores the prior set. ----- *)

Definition inv3_s0 : State.t :=
  match registerRewardToken empty_state 100 true with
  | Result.Success s => s
  | _ => empty_state
  end.

Definition inv3_s1 : State.t :=
  match registerRewardToken inv3_s0 200 true with
  | Result.Success s => s
  | _ => empty_state
  end.

Definition inv3_s2 : State.t :=
  match unregisterRewardToken inv3_s1 200 true with
  | Result.Success s => s
  | _ => empty_state
  end.

Lemma xcheck_register_then_unregister_restores :
  inv3_s2 = inv3_s0.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4: register reverts on the zero address. ----- *)

Lemma xcheck_register_zero_reverts :
  registerRewardToken empty_state 0 true = revert_zero_address.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-5: register/unregister revert under failed role checks. ----- *)

Lemma xcheck_register_not_owner_reverts :
  registerRewardToken empty_state 100 false = revert_invalid_caller.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_unregister_not_authorized_reverts :
  unregisterRewardToken inv1_after_first 100 false = revert_invalid_caller.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: N register, N unregister round-trip to empty. ----- *)

Definition inv6_mid : State.t :=
  match registerRewardToken empty_state 101 true with
  | Result.Success s1 =>
    match registerRewardToken s1 102 true with
    | Result.Success s2 =>
      match registerRewardToken s2 103 true with
      | Result.Success s3 =>
        match registerRewardToken s3 104 true with
        | Result.Success s4 =>
          match registerRewardToken s4 105 true with
          | Result.Success s5 => s5
          | _ => empty_state
          end
        | _ => empty_state
        end
      | _ => empty_state
      end
    | _ => empty_state
    end
  | _ => empty_state
  end.

Definition inv6_end : State.t :=
  match unregisterRewardToken inv6_mid 101 true with
  | Result.Success s1 =>
    match unregisterRewardToken s1 102 true with
    | Result.Success s2 =>
      match unregisterRewardToken s2 103 true with
      | Result.Success s3 =>
        match unregisterRewardToken s3 104 true with
        | Result.Success s4 =>
          match unregisterRewardToken s4 105 true with
          | Result.Success s5 => s5
          | _ => empty_state
          end
        | _ => empty_state
        end
      | _ => empty_state
      end
    | _ => empty_state
    end
  | _ => empty_state
  end.

Lemma xcheck_inv6_mid_size :
  length inv6_mid.(State.rewardTokens) = 5%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv6_end_empty :
  inv6_end.(State.rewardTokens) = [].
Proof. vm_compute. reflexivity. Qed.

End RewardTokenRegistryXCheck.
