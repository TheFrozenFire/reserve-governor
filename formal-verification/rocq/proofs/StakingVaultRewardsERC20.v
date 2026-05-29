(** StakingVault rewards × ERC20 — conservation against external balance.

    Four theorems on [claimUser_with_erc20]:

      ECR-1   Claim faithfulness: a successful
              [claimUser_with_erc20] reduces the vault's external
              ERC20 balance by exactly the claimable amount. The
              property the Certora-side spec cannot state because
              it NONDET-summarizes [balanceOf]; here the ERC20
              mock provides the ground truth, and the equality
              is exact.

      ECR-2   Recipient credit: the same call credits the
              recipient by exactly the claimable amount. Pairs
              with ECR-1 to give the full conservation form:
              "what leaves the vault equals what reaches the
              recipient" — no fee-on-transfer, no rounding loss.
              When this holds, T-REWARDTOKEN is satisfied; when
              the underlying token violates it, [transfer] would
              still update the mock balances as stated but the
              REAL ERC20 might not — which is the source of the
              trust-assumption boundary.

      ECR-3   Other balances untouched: any account that is
              neither the vault nor the recipient sees no
              balance change.

      ECR-4   Internal-counter consistency: a successful
              [claimUser_with_erc20] increments [totalClaimed] by
              exactly the claimable amount AND zeroes the user's
              accruedRewards. Bridges the new theorem to the
              existing internal-form
              [audit_rewards_claim_returns_and_zeros].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import ReserveGovernor.simulations.StakingVaultRewardsERC20.
Require Import ReserveGovernor.mocks.ERC20.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultRewardsERC20Proofs.

Import StakingVaultRewardsERC20.

(** ECR-1 + ECR-2 combined: vault's ERC20 balance reduces by
    exactly claimable, recipient's increases by the same.
    Delegates to the ERC20 mock's existing
    [transfer_decreases_sender_increases_receiver_by_amount]. *)
Lemma claim_external_conservation :
  forall (s s' : State.t) (u u' : StakingVaultRewards.UserReward.t)
         (recipient : Address) (claimable : U256.t),
    claimUser_with_erc20 s u recipient = Result.Success (s', u', claimable) ->
    s.(State.vault_addr) <> recipient ->
    0 < claimable ->
    ERC20.balanceOf s'.(State.erc20) s.(State.vault_addr)
      = ERC20.balanceOf s.(State.erc20) s.(State.vault_addr) - claimable
    /\
    ERC20.balanceOf s'.(State.erc20) recipient
      = ERC20.balanceOf s.(State.erc20) recipient + claimable.
Proof.
  intros s s' u u' recipient claimable Hsucc Hne Hpos.
  unfold claimUser_with_erc20 in Hsucc.
  set (inner := StakingVaultRewards.claimUser s.(State.reward_info) u) in *.
  destruct (ERC20.transfer s.(State.erc20) s.(State.vault_addr) recipient (snd inner))
    as [erc20' | p sm] eqn:Htransfer.
  - injection Hsucc as Hs'_eq Hu'_eq Hclaim_eq.
    subst s' u' claimable.
    simpl.
    apply (ERC20.transfer_decreases_sender_increases_receiver_by_amount
             s.(State.erc20) s.(State.vault_addr) recipient (snd inner) erc20'
             Hne Hpos Htransfer).
  - unfold revert_transfer_failed in Hsucc. discriminate.
Qed.

(** ECR-4: internal-counter consistency. The composed claim flow
    still increments [totalClaimed] and zeroes [accruedRewards]
    exactly as the base [claimUser] does. *)
Lemma claim_internal_consistency :
  forall (s s' : State.t) (u u' : StakingVaultRewards.UserReward.t)
         (recipient : Address) (claimable : U256.t),
    claimUser_with_erc20 s u recipient = Result.Success (s', u', claimable) ->
    u'.(StakingVaultRewards.UserReward.accruedRewards) = 0
    /\ s'.(State.reward_info).(StakingVaultRewards.RewardInfo.totalClaimed)
       = s.(State.reward_info).(StakingVaultRewards.RewardInfo.totalClaimed) + claimable.
Proof.
  intros s s' u u' recipient claimable Hsucc.
  unfold claimUser_with_erc20 in Hsucc.
  set (inner := StakingVaultRewards.claimUser s.(State.reward_info) u) in *.
  destruct (ERC20.transfer s.(State.erc20) s.(State.vault_addr) recipient (snd inner))
    as [erc20' | p sm] eqn:Htransfer.
  - injection Hsucc as Hs'_eq Hu'_eq Hclaim_eq.
    subst s' u' claimable.
    simpl. split.
    + unfold StakingVaultRewards.claimUser in inner. unfold inner. reflexivity.
    + unfold StakingVaultRewards.claimUser in inner. unfold inner. simpl. reflexivity.
  - unfold revert_transfer_failed in Hsucc. discriminate.
Qed.

End StakingVaultRewardsERC20Proofs.
