(** StakingVaultRewards × CAS witness cross-check.

    Evaluates the [StakingVaultRewards] simulation on the same
    accrual / claim scenarios used by
    [cas/staking_vault/multi_token_rewards.gp].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.

Module StakingVaultRewardsXCheck.

Import StakingVaultRewards.

(** ----- INV-1: 8 accruals at a fixed supply, each with balance_delta
    = 10^18 * k.  rewardIndex after k=8 should equal the sum:
    deltaIndex(k) = (10^18 k * 1e18 * 1e18) / 1e21 = 10^33 k
    so total = 10^33 * (1+2+...+8) = 36 * 10^33. ----- *)
Definition cal_supply : U256.t := 10^21.

Definition cal_rinfo_after_one_accrual : RewardInfo.t :=
  updateRewardIndex empty_reward cal_supply (10^18).

Lemma xcheck_first_accrual_index :
  cal_rinfo_after_one_accrual.(RewardInfo.rewardIndex) = 10^33.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: user with balance 1e20 against the post-state above
    accrues: 1e20 * 10^33 / (1e18 * 1e18) = 10^17. ----- *)
Lemma xcheck_first_user_accrual :
  (accrueUser cal_rinfo_after_one_accrual empty_user (10^20))
    .(UserReward.accruedRewards) = 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4: claim returns exactly the accrued, zeros the user. ----- *)
Lemma xcheck_claim_returns_and_zeros :
  let u := accrueUser cal_rinfo_after_one_accrual empty_user (10^20) in
  let triple := claimUser cal_rinfo_after_one_accrual u in
  snd triple = 10^17
  /\ (snd (fst triple)).(UserReward.accruedRewards) = 0.
Proof. vm_compute. split; reflexivity. Qed.

(** ----- INV-5: totalClaimed = prior_claimed + claim_amount. ----- *)
Lemma xcheck_claim_bumps_totalClaimed :
  let u := accrueUser cal_rinfo_after_one_accrual empty_user (10^20) in
  let triple := claimUser cal_rinfo_after_one_accrual u in
  (fst (fst triple)).(RewardInfo.totalClaimed) = 10^17.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: stable rewardIndex => accrueUser no-op. ----- *)
Lemma xcheck_stable_index_noop :
  let u := {| UserReward.lastRewardIndex := 10^33;
              UserReward.accruedRewards  := 5 |} in
  accrueUser cal_rinfo_after_one_accrual u (10^20) = u.
Proof. vm_compute. reflexivity. Qed.

End StakingVaultRewardsXCheck.
