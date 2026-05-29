(** StakingVault rewards × reentrancy interleaving model.

    Mirrors the [claimRewards] zero-first pattern in
    StakingVault.sol:354-361:

      claimableRewards[i] = userRewardTracker.accruedRewards;  // read
      if (claimableRewards[i] != 0) {
        rewardInfo.totalClaimed += claimableRewards[i];        // global write
        userRewardTracker.accruedRewards = 0;                  // ZERO-FIRST
        SafeERC20.safeTransfer(...);                           // external call
        emit ...
      }

    The external call at the bottom is where a malicious reward
    token could re-enter [claimRewards]. The structural defense:
    [userRewardTracker.accruedRewards] is already 0 when the
    external call happens, so a reentrant call reads 0 and does
    nothing.

    Why model this explicitly:
      The base [StakingVaultRewards] simulation's [claimUser]
      function returns the (state, user, claimable) triple as a
      pure transformation. Reentrancy isn't visible in the pure-
      function model — the external call is just "the function
      returned [claimable], end of story." To prove the zero-first
      pattern actually prevents double-claim, we need to expose
      the interleaving: outer reads, outer zeroes, INNER CALL,
      outer transfers. This file does exactly that.

    The headline theorem [no_double_claim_under_reentrancy] lives
    in proofs/StakingVaultRewardsReentrancy.v and states:

      For any state [s] and user [u] with [u.accruedRewards = a]:
      after the outer-zeros-inner-claims-outer-transfers sequence,
      the total external transfer is exactly [a]. The reentrant
      inner call extracts ZERO.

    Closes OWASP SC08 — the only remaining gap from the
    notes/owasp_2026_coverage.md matrix.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultRewardsReentrancy.

Import StakingVaultRewards.

(** [reentrancy_step]: the exact outer-inner-outer sequence that
    [claimRewards] executes when its external transfer reentries
    [claimRewards] again for the same (user, reward_token) pair.

    Inputs:
      - [r] : the per-token reward info (rewardIndex, balanceAccounted, totalClaimed)
      - [u] : the per-user reward info (lastRewardIndex, accruedRewards)

    Outputs:
      - [r']                : reward info after both calls have updated totalClaimed
      - [u']                : user reward info after both calls (accruedRewards should be 0)
      - [outer_transferred] : amount the outer call passes to safeTransfer
      - [inner_transferred] : amount the inner (reentrant) call passes to safeTransfer

    The inner call observes the OUTER's [user.accruedRewards = 0]
    write, because in the contract ordering the zero is written
    BEFORE the external call (line 359 before line 361). We model
    this by computing the inner call against the already-zeroed
    user state. *)
Definition reentrancy_step
    (r : RewardInfo.t) (u : UserReward.t)
    : RewardInfo.t * UserReward.t * U256.t * U256.t :=
  (* === Outer call begins === *)
  (* Step 1: capture outer-side amount, build the zeroed user *)
  let outer_amount := u.(UserReward.accruedRewards) in
  let u_zeroed := {|
    UserReward.lastRewardIndex := u.(UserReward.lastRewardIndex);
    UserReward.accruedRewards  := 0;
  |} in
  let r_after_outer_zero := {|
    RewardInfo.rewardIndex      := r.(RewardInfo.rewardIndex);
    RewardInfo.balanceAccounted := r.(RewardInfo.balanceAccounted);
    RewardInfo.totalClaimed     := r.(RewardInfo.totalClaimed) + outer_amount;
  |} in
  (* === Interleaving point: external safeTransfer triggers reentry === *)
  (* === Inner call begins (reentrant claimRewards on same user/token) === *)
  let inner_triple := claimUser r_after_outer_zero u_zeroed in
  let r_after_inner := fst (fst inner_triple) in
  let u_after_inner := snd (fst inner_triple) in
  let inner_amount  := snd inner_triple in
  (* === Inner call returns; outer continues to safeTransfer === *)
  (r_after_inner, u_after_inner, outer_amount, inner_amount).

End StakingVaultRewardsReentrancy.
