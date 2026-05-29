(** StakingVault rewards × ERC20 — claim-faithfulness binding.

    Layers the ERC20 mock onto [StakingVaultRewards] so the
    conservation theorem can be expressed as a statement about
    the actual on-chain reward-token balance, not just the
    contract's internal [totalClaimed] counter.

    Background — see notes/external_dependencies.md (Priority 2):

      The base [StakingVaultRewards] sim treats [balanceAccounted]
      and [totalClaimed] as plain [U256.t] fields. The conservation
      theorem [audit_rewards_conservation] closes because both
      fields are internal to the simulation; there's no external
      ground truth, so "vault balance decreased by claimable" is
      effectively a tautology on internal counters.

      The Certora-side analog of this theorem (RewardConservation.spec)
      could not close — the NONDET summary of [balanceOf] is too
      loose to constrain conservation. See certora/intent/
      RewardConservation.md for the long-form discussion.

      This file bridges the gap by binding the ERC20 mock into the
      claim flow. After [claimUser_with_erc20], the vault's ERC20
      balance has decreased by exactly the claimable amount. That's
      the property the contract enforces, the property we want
      machine-checked, and the property a future audit would need
      to see in a Rocq theorem rather than implicit in the model.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultRewards.
Require Import ReserveGovernor.mocks.ERC20.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module StakingVaultRewardsERC20.

Definition Address : Set := U256.t.

(** Combined state: the per-reward-token internal accounting from
    StakingVaultRewards plus the external ERC20 state. *)
Module State.
  Record t : Set := {
    reward_info : StakingVaultRewards.RewardInfo.t;
    erc20       : ERC20.State;
    vault_addr  : Address;   (* address of the StakingVault — recipient of the debit *)
  }.
End State.

(** Revert sentinels — the only revert path on claim is the
    ERC20 [insufficient_balance] case, which corresponds to the
    "lying token" / "broken accounting" deployment defect that
    breaks T-REWARDTOKEN. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_transfer_failed {A : Set} : Result.t A := Result.Revert 0 64.

(** [claimUser_with_erc20 s u recipient]:

    Threads the StakingVaultRewards.claimUser internal update
    with the ERC20.transfer call:
      1. compute (r', u', claimable) = claimUser(reward_info, u)
      2. call ERC20.transfer(erc20, vault_addr, recipient, claimable)
         - success: bind the updated state
         - revert: propagate the revert (this is the
           T-REWARDTOKEN-violation path; the vault's accounting
           still claims the user has been paid, but the ERC20
           refused — a fee-on-transfer or balance-lying token)

    Returns the (state, user, claimable) triple on success. *)
Definition claimUser_with_erc20
    (s : State.t) (u : StakingVaultRewards.UserReward.t) (recipient : Address)
    : Result.t (State.t * StakingVaultRewards.UserReward.t * U256.t) :=
  let inner := StakingVaultRewards.claimUser s.(State.reward_info) u in
  let r' := fst (fst inner) in
  let u' := snd (fst inner) in
  let claimable := snd inner in
  match ERC20.transfer s.(State.erc20) s.(State.vault_addr) recipient claimable with
  | ERC20.Result.Revert _ _ => revert_transfer_failed
  | ERC20.Result.Success erc20' =>
      Result.Success (
        {|
          State.reward_info := r';
          State.erc20       := erc20';
          State.vault_addr  := s.(State.vault_addr);
        |},
        u',
        claimable
      )
  end.

End StakingVaultRewardsERC20.
