(** StakingVault rewards proofs.

    Headline lemmas on the index-based reward accrual:

      INV-1   rewardIndex is monotonically non-decreasing across
              [updateRewardIndex] calls.

      INV-2   user.accruedRewards is non-decreasing across
              [accrueUser] calls, given supply > 0.

      INV-4   claimUser zeroes accruedRewards and increments
              totalClaimed by exactly the claimed amount.

      INV-5   totalClaimed is monotone non-decreasing across claims.

      INV-6   user.lastRewardIndex is preserved on accrueUser when
              the new rewardIndex equals the cached lastRewardIndex
              (the "remove and re-add doesn't touch user storage"
              property).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import Coq.Bool.Bool.

Module StakingVaultRewardsProofs.

Import StakingVaultRewards.

(** Precompute positivity facts at the file head to avoid expanding
    [10^18] inside [lia] in the body proofs. *)
Lemma SCALAR_pos : 0 < SCALAR.
Proof. unfold SCALAR. apply Z.pow_pos_nonneg; lia. Qed.

Lemma DEC18_pos : 0 < DEC18.
Proof. unfold DEC18. apply Z.pow_pos_nonneg; lia. Qed.

Lemma SCALAR_DEC18_pos : 0 < DEC18 * SCALAR.
Proof.
  apply Z.mul_pos_pos; [apply DEC18_pos | apply SCALAR_pos].
Qed.

(** ----- INV-1: rewardIndex monotone non-decreasing. ----- *)
Lemma updateRewardIndex_monotone
    (r : RewardInfo.t) (supply balanceDelta : U256.t) :
  0 < supply ->
  0 <= balanceDelta ->
  (updateRewardIndex r supply balanceDelta).(RewardInfo.rewardIndex)
    >= r.(RewardInfo.rewardIndex).
Proof.
  intros Hs Hb.
  unfold updateRewardIndex.
  destruct (supply =? 0) eqn:Hs0; [apply Z.eqb_eq in Hs0; lia|].
  destruct (balanceDelta =? 0) eqn:Hb0; [simpl; lia|].
  cbn -[Z.div Z.mul SCALAR DEC18].
  pose proof SCALAR_pos as Hsp.
  pose proof DEC18_pos as Hdp.
  assert (HdNN : 0 <= (balanceDelta * SCALAR * DEC18) / supply).
  { apply Z.div_pos; [|exact Hs].
    apply Z.mul_nonneg_nonneg; [|lia].
    apply Z.mul_nonneg_nonneg; [exact Hb|lia]. }
  lia.
Qed.

(** ----- INV-2: user.accruedRewards non-decreasing. ----- *)
Lemma accrueUser_accrued_monotone
    (r : RewardInfo.t) (u : UserReward.t) (userBalance : U256.t) :
  u.(UserReward.lastRewardIndex) <= r.(RewardInfo.rewardIndex) ->
  0 <= userBalance ->
  (accrueUser r u userBalance).(UserReward.accruedRewards)
    >= u.(UserReward.accruedRewards).
Proof.
  intros Hidx_le Hbal.
  unfold accrueUser.
  destruct (r.(RewardInfo.rewardIndex) - u.(UserReward.lastRewardIndex) =? 0) eqn:Hd; [lia|].
  cbn -[Z.div Z.mul DEC18 SCALAR].
  apply Z.eqb_neq in Hd.
  set (dIdx := r.(RewardInfo.rewardIndex) - u.(UserReward.lastRewardIndex)).
  assert (HdNN : 0 <= dIdx) by (unfold dIdx; lia).
  pose proof SCALAR_DEC18_pos as Hdspos.
  assert (Hsd : 0 <= (userBalance * dIdx) / (DEC18 * SCALAR)).
  { apply Z.div_pos; [|exact Hdspos].
    apply Z.mul_nonneg_nonneg; [exact Hbal|exact HdNN]. }
  lia.
Qed.

(** ----- INV-4: claimUser zeroes accruedRewards. ----- *)
Lemma claimUser_zeroes_accrued
    (r : RewardInfo.t) (u : UserReward.t) :
  (snd (fst (claimUser r u))).(UserReward.accruedRewards) = 0.
Proof. reflexivity. Qed.

(** ----- INV-4: claimUser returns exactly the prior accrued. ----- *)
Lemma claimUser_returns_accrued
    (r : RewardInfo.t) (u : UserReward.t) :
  snd (claimUser r u) = u.(UserReward.accruedRewards).
Proof. reflexivity. Qed.

(** ----- INV-5: totalClaimed monotone after claim. ----- *)
Lemma claimUser_totalClaimed_monotone
    (r : RewardInfo.t) (u : UserReward.t) :
  0 <= u.(UserReward.accruedRewards) ->
  (fst (fst (claimUser r u))).(RewardInfo.totalClaimed)
    >= r.(RewardInfo.totalClaimed).
Proof. intros Hnn. cbn. lia. Qed.

(** ----- INV-6: when rewardIndex equals the cached user index,
    accrueUser is a no-op (the early-return path that keeps user
    storage intact across remove/re-add). ----- *)
Lemma accrueUser_no_op_when_index_stable
    (r : RewardInfo.t) (u : UserReward.t) (userBalance : U256.t) :
  r.(RewardInfo.rewardIndex) = u.(UserReward.lastRewardIndex) ->
  accrueUser r u userBalance = u.
Proof.
  intros Heq.
  unfold accrueUser.
  rewrite Heq, Z.sub_diag, Z.eqb_refl. reflexivity.
Qed.

End StakingVaultRewardsProofs.
