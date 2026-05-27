(** StakingVault multi-token reward accounting simulation.

    Mirrors the [RewardInfo / UserRewardInfo] machinery in
    contracts/staking/StakingVault.sol (_accrueRewards, _accrueUser,
    claimRewards).

    The contract maintains, per reward token:

      RewardInfo {
        payoutLastPaid       : seconds
        rewardIndex          : D18+decimals {reward/share}
        balanceAccounted     : reward
        balanceLastKnown     : reward
        totalClaimed         : reward
      }

    Plus, per (user, reward token):

      UserRewardInfo {
        lastRewardIndex      : D18+decimals
        accruedRewards       : reward
      }

    Index-based accumulator. On each accrual call:
      deltaIndex     = (balanceDelta * SCALAR * decimals) / supply
      rewardIndex   += deltaIndex
      balanceAccounted += balanceDelta

    On each user accrual:
      uDelta         = (balanceOf(u) * (rewardIndex - lastIdx))
                       / (decimals * SCALAR)
      accruedRewards += uDelta
      lastRewardIndex = rewardIndex     (only when delta != 0)

    The simulation ignores the on-chain time-decayed [handout] formula
    that gates how much of [balanceLastKnown - balanceAccounted]
    becomes [balanceDelta] each accrual; we take the delta as a
    parameter and prove the *index machinery* is faithful regardless
    of how the delta is computed. The decay model itself is validated
    by the CAS witness corpus separately.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module StakingVaultRewards.

Definition SCALAR : Z := 10 ^ 18.
Definition DEC18  : Z := 10 ^ 18.

Module RewardInfo.
  Record t : Set := {
    rewardIndex      : U256.t;   (** D18+decimals {reward/share} *)
    balanceAccounted : U256.t;   (** {reward} *)
    totalClaimed     : U256.t;   (** {reward} *)
  }.
End RewardInfo.

Definition empty_reward : RewardInfo.t := {|
  RewardInfo.rewardIndex      := 0;
  RewardInfo.balanceAccounted := 0;
  RewardInfo.totalClaimed     := 0;
|}.

Module UserReward.
  Record t : Set := {
    lastRewardIndex : U256.t;
    accruedRewards  : U256.t;
  }.
End UserReward.

Definition empty_user : UserReward.t := {|
  UserReward.lastRewardIndex := 0;
  UserReward.accruedRewards  := 0;
|}.

(** Global accrual step. Source: StakingVault.sol#L431-L451.
    [_accrueRewards(rewardToken)] bumps [rewardIndex] by the
    proportional share, and [balanceAccounted] by [balanceDelta]. *)
Definition updateRewardIndex
    (r : RewardInfo.t) (supply : U256.t) (balanceDelta : U256.t)
    : RewardInfo.t :=
  if orb (supply =? 0) (balanceDelta =? 0)
  then r
  else
    let deltaIndex := (balanceDelta * SCALAR * DEC18) / supply in
    {|
      RewardInfo.rewardIndex      := r.(RewardInfo.rewardIndex) + deltaIndex;
      RewardInfo.balanceAccounted := r.(RewardInfo.balanceAccounted) + balanceDelta;
      RewardInfo.totalClaimed     := r.(RewardInfo.totalClaimed);
    |}.

(** Per-user accrual. Source: StakingVault.sol#L453-L470.
    Updates lastRewardIndex only when deltaIndex != 0 (contract-side
    early return). *)
Definition accrueUser
    (r : RewardInfo.t) (u : UserReward.t) (userBalance : U256.t)
    : UserReward.t :=
  let dIdx := r.(RewardInfo.rewardIndex) - u.(UserReward.lastRewardIndex) in
  if dIdx =? 0 then u
  else
    let supplierDelta := (userBalance * dIdx) / (DEC18 * SCALAR) in
    {|
      UserReward.lastRewardIndex := r.(RewardInfo.rewardIndex);
      UserReward.accruedRewards  := u.(UserReward.accruedRewards) + supplierDelta;
    |}.

(** Claim by a user. Returns the new (reward, user, claimed) triple.
    Source: StakingVault.sol#L344-L370. *)
Definition claimUser
    (r : RewardInfo.t) (u : UserReward.t)
    : RewardInfo.t * UserReward.t * U256.t :=
  let claimable := u.(UserReward.accruedRewards) in
  ({|
    RewardInfo.rewardIndex      := r.(RewardInfo.rewardIndex);
    RewardInfo.balanceAccounted := r.(RewardInfo.balanceAccounted);
    RewardInfo.totalClaimed     := r.(RewardInfo.totalClaimed) + claimable;
  |},
   {|
    UserReward.lastRewardIndex := u.(UserReward.lastRewardIndex);
    UserReward.accruedRewards  := 0;
   |},
   claimable).

Module Valid.
  Record reward (r : RewardInfo.t) : Prop := {
    idx_nn     : 0 <= r.(RewardInfo.rewardIndex);
    acc_nn     : 0 <= r.(RewardInfo.balanceAccounted);
    claimed_nn : 0 <= r.(RewardInfo.totalClaimed);
  }.

  Record user (u : UserReward.t) (r : RewardInfo.t) : Prop := {
    lastIdx_le_idx : u.(UserReward.lastRewardIndex)
                       <= r.(RewardInfo.rewardIndex);
    accrued_nn     : 0 <= u.(UserReward.accruedRewards);
  }.
End Valid.

End StakingVaultRewards.
