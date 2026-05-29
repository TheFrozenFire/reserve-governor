(** StakingVault claimRewards — no double-claim under reentrancy.

    Closes the OWASP SC08 gap identified in
    notes/owasp_2026_coverage.md.

    Five theorems on the [reentrancy_step] interleaving:

      REN-1   [no_double_claim_inner_zero] : the reentrant inner
              call extracts EXACTLY ZERO. Direct consequence of
              the zero-first ordering — when the inner call
              executes, [accruedRewards] has already been set
              to 0 by the outer call.

      REN-2   [no_double_claim_outer_unchanged] : the outer call
              transfers exactly the user's pre-claim
              [accruedRewards]. The reentrant call cannot
              perturb the outer call's bookkeeping.

      REN-3   [no_double_claim_total_bounded] : total amount
              transferred across both calls equals the user's
              pre-claim [accruedRewards]. The structural form of
              "no value escapes that wasn't already accrued."

      REN-4   [reentrancy_zeroes_user] : the post-sequence user
              state has [accruedRewards = 0]. After both calls
              complete, the user cannot claim again (until fresh
              rewards accrue).

      REN-5   [reentrancy_totalClaimed_consistent] : the post-
              sequence [totalClaimed] equals the prior value
              plus exactly the user's pre-claim accrued amount.
              The inner reentrant call does not double-count.

    These theorems convert the "zero-first pattern is safe"
    comment in StakingVault.sol:359 into a machine-checked fact.
    The Cantina-postmortem methodology of "load-bearing comments
    must become theorems" applied to the reentrancy guard.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import ReserveGovernor.simulations.StakingVaultRewardsReentrancy.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultRewardsReentrancyProofs.

Import StakingVaultRewards.
Import StakingVaultRewardsReentrancy.

(** Convenience destructor: project the 4-tuple components. *)
Definition r_after  (t : RewardInfo.t * UserReward.t * U256.t * U256.t) := fst (fst (fst t)).
Definition u_after  (t : RewardInfo.t * UserReward.t * U256.t * U256.t) := snd (fst (fst t)).
Definition outer_tx (t : RewardInfo.t * UserReward.t * U256.t * U256.t) := snd (fst t).
Definition inner_tx (t : RewardInfo.t * UserReward.t * U256.t * U256.t) := snd t.

(** ----- REN-1: inner reentrant call extracts zero. -----

    The load-bearing theorem. Witnesses the zero-first defense:
    by the time the inner call reads [user.accruedRewards], the
    outer has already written 0, so the inner's [claimUser]
    returns a 0-claim. *)
Theorem no_double_claim_inner_zero
    (r : RewardInfo.t) (u : UserReward.t) :
  inner_tx (reentrancy_step r u) = 0.
Proof.
  unfold reentrancy_step, inner_tx. simpl.
  (* [claimUser] on a user with [accruedRewards = 0] returns
     [snd] = [accruedRewards] = 0 (claimUser_returns_accrued). *)
  reflexivity.
Qed.

(** ----- REN-2: outer call transfers exactly the pre-claim accrued. -----

    The outer call captures the user's [accruedRewards] BEFORE
    the inner call has a chance to mutate state. So the outer
    amount is exactly the original accrued, regardless of what
    the inner call does. *)
Theorem no_double_claim_outer_unchanged
    (r : RewardInfo.t) (u : UserReward.t) :
  outer_tx (reentrancy_step r u) = u.(UserReward.accruedRewards).
Proof.
  unfold reentrancy_step, outer_tx. simpl. reflexivity.
Qed.

(** ----- REN-3: total transferred = original accrued. -----

    The structural form of "no double-claim." Across the full
    outer-inner-outer interleaving, exactly the user's pre-claim
    accrued amount leaves the vault. Not more, not less. *)
Theorem no_double_claim_total_bounded
    (r : RewardInfo.t) (u : UserReward.t) :
  outer_tx (reentrancy_step r u) + inner_tx (reentrancy_step r u)
    = u.(UserReward.accruedRewards).
Proof.
  rewrite no_double_claim_outer_unchanged.
  rewrite no_double_claim_inner_zero.
  lia.
Qed.

(** ----- REN-4: user.accruedRewards is zero after the sequence. -----

    Confirms the post-state — even though two claim calls
    happened, neither has left the user with extractable value.
    Replays prevented by the zeroing AND by the increment in
    nonce-style storage (claimUser returns a user with
    [accruedRewards = 0]). *)
Theorem reentrancy_zeroes_user
    (r : RewardInfo.t) (u : UserReward.t) :
  (u_after (reentrancy_step r u)).(UserReward.accruedRewards) = 0.
Proof.
  unfold reentrancy_step, u_after. simpl. reflexivity.
Qed.

(** ----- REN-5: totalClaimed increments by exactly the original. -----

    The reward bookkeeping doesn't double-count. After both calls
    complete, [totalClaimed] has grown by exactly the user's
    original accrued amount — the outer call's contribution.
    The inner call's [claimUser] on a zeroed user adds 0 to
    [totalClaimed]. *)
Theorem reentrancy_totalClaimed_consistent
    (r : RewardInfo.t) (u : UserReward.t) :
  (r_after (reentrancy_step r u)).(RewardInfo.totalClaimed)
    = r.(RewardInfo.totalClaimed) + u.(UserReward.accruedRewards).
Proof.
  unfold reentrancy_step, r_after. simpl.
  (* claimUser on a user with accruedRewards=0 increments
     totalClaimed by 0; the outer's +outer_amount remains. *)
  lia.
Qed.

End StakingVaultRewardsReentrancyProofs.
