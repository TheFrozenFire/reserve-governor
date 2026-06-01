(** Cross-domain integration: StakingVault withdraw + immediate
    transfer (the [unstakingDelay = 0] branch).

    The Solidity flow at
    [contracts/staking/StakingVault.sol#L266-L293] handles the
    [unstakingDelay = 0] case by calling [super._withdraw], which
    burns the shares and immediately transfers [_assets] of the
    underlying ERC20 to [_receiver] — no [UnstakingManager.createLock]
    in transit, no lock to claim later.

    The conservation invariant for this branch is therefore stated
    against the ERC20 balance ledger rather than the manager's
    [total_active] sum:

      pre.totalDeposited - post.totalDeposited
        = post.balanceOf(receiver) - pre.balanceOf(receiver)
        = assets

    (The vault's own ERC20 balance also decreases by [assets], so the
    accounting is closed end-to-end. We carry both sides of that
    movement through the proof.)

    Modeling notes:
      - The simulation's [StakingVaultExchange.withdraw] is the
        vault-side legs (totalDeposited, totalSupply, shares).
      - The ERC20 mock from [mocks/ERC20.v] carries the asset
        ledger; [ERC20.transfer] moves the assets vault->receiver.
      - We treat [vault] and [receiver] as distinct addresses (the
        production caller doesn't send to itself). The from-=to and
        amount=0 corners short-circuit in [ERC20.do_transfer] and
        would make the conservation statement trivial — we keep them
        as preconditions instead.
      - The [unstakingDelay] field is implicit: this branch executes
        only when [unstakingDelay = 0], which is reflected in the
        composite's name. The simulation does not store
        [unstakingDelay]; the caller chooses which composite to run.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import ReserveGovernor.mocks.ERC20.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Module IntegrationWithdrawImmediate.

(** ===== Composite operation =====

    Two-leg flow:
      1. [StakingVaultExchange.withdraw s_ex assets]
           - decreases totalDeposited by assets
           - burns the equivalent shares
           - reverts if assets > totalAssets
      2. [ERC20.transfer s_erc20 vault receiver assets]
           - debits vault's balance, credits receiver's
           - reverts if vault's balance < assets

    Returns the pair of post-states on success. Either leg's revert
    short-circuits the whole composite. *)
Definition withdraw_immediate
    (s_ex : StakingVaultExchange.State.t)
    (s_erc20 : ERC20.State)
    (vault receiver : ERC20.Address)
    (assets : U256.t)
    : ERC20.Result.t (StakingVaultExchange.State.t * ERC20.State) :=
  match StakingVaultExchange.withdraw s_ex assets with
  | StakingVaultExchange.Result.Revert p q => ERC20.Result.Revert p q
  | StakingVaultExchange.Result.Success (s_ex', _shares) =>
      match ERC20.transfer s_erc20 vault receiver assets with
      | ERC20.Result.Revert p q => ERC20.Result.Revert p q
      | ERC20.Result.Success s_erc20' =>
          ERC20.Result.Success (s_ex', s_erc20')
      end
  end.

(** ===== Conservation theorem =====

    [withdraw_immediate_conserves_value]: the decrement of the
    vault's [totalDeposited] equals the increment of the receiver's
    ERC20 balance.

    Preconditions:
      - assets > 0 and vault <> receiver (so the ERC20 do_transfer
        short-circuits do not fire — those branches do produce a
        successful [Result.Success s] but with no balance movement,
        making the conservation statement vacuously trivial in a
        misleading way).

    Vault balance evolution is captured as a corollary: the vault
    itself loses [assets] of underlying. ----- *)
Theorem withdraw_immediate_conserves_value
    (s_ex s_ex' : StakingVaultExchange.State.t)
    (s_erc20 s_erc20' : ERC20.State)
    (vault receiver : ERC20.Address)
    (assets : U256.t) :
  0 < assets ->
  vault <> receiver ->
  withdraw_immediate s_ex s_erc20 vault receiver assets
    = ERC20.Result.Success (s_ex', s_erc20') ->
  s_ex.(StakingVaultExchange.State.totalDeposited)
    - s_ex'.(StakingVaultExchange.State.totalDeposited)
  = ERC20.balanceOf s_erc20' receiver - ERC20.balanceOf s_erc20 receiver.
Proof.
  intros Hpos Hne Hok.
  unfold withdraw_immediate in Hok.
  (* Unpack the inner withdraw. *)
  destruct (StakingVaultExchange.withdraw s_ex assets)
    as [inner_pair | p q] eqn:Hwd; [|discriminate].
  destruct inner_pair as (s_ex_inner & shares).
  (* Unpack the inner transfer. *)
  destruct (ERC20.transfer s_erc20 vault receiver assets)
    as [s_erc20_inner | p q] eqn:Htr; [|discriminate].
  injection Hok as Hex_eq Herc_eq.
  subst s_ex'. subst s_erc20'.
  (* Learn totalDeposited delta from the inner withdraw. *)
  unfold StakingVaultExchange.withdraw in Hwd.
  destruct (assets >? StakingVaultExchange.totalAssets s_ex) eqn:Hgt;
    [discriminate|].
  (* New share-bound guard from the OZ inflation-defended form. *)
  destruct ((assets * (s_ex.(StakingVaultExchange.State.totalSupply) + 1)
             + StakingVaultExchange.totalAssets s_ex)
            / (StakingVaultExchange.totalAssets s_ex + 1)
            >? s_ex.(StakingVaultExchange.State.totalSupply)) eqn:Hguard;
    [discriminate|].
  injection Hwd as Hex_inner_eq Hshares_eq.
  subst s_ex_inner.
  (* Learn balance delta from the inner ERC20.transfer.
     vault <> receiver and 0 < assets close the short-circuits. *)
  pose proof
    (ERC20.transfer_decreases_sender_increases_receiver_by_amount
       s_erc20 vault receiver assets s_erc20_inner Hne Hpos Htr)
    as (_ & Hrecv).
  simpl. rewrite Hrecv. lia.
Qed.

(** ===== Vault loses the assets too =====

    The full accounting: the vault's own ERC20 balance also drops by
    [assets]. Combined with [withdraw_immediate_conserves_value],
    this captures the standard ERC20-transfer pair. ----- *)
Theorem withdraw_immediate_debits_vault
    (s_ex s_ex' : StakingVaultExchange.State.t)
    (s_erc20 s_erc20' : ERC20.State)
    (vault receiver : ERC20.Address)
    (assets : U256.t) :
  0 < assets ->
  vault <> receiver ->
  withdraw_immediate s_ex s_erc20 vault receiver assets
    = ERC20.Result.Success (s_ex', s_erc20') ->
  ERC20.balanceOf s_erc20 vault - ERC20.balanceOf s_erc20' vault = assets.
Proof.
  intros Hpos Hne Hok.
  unfold withdraw_immediate in Hok.
  destruct (StakingVaultExchange.withdraw s_ex assets)
    as [inner_pair | p q] eqn:Hwd; [|discriminate].
  destruct inner_pair as (s_ex_inner & shares).
  destruct (ERC20.transfer s_erc20 vault receiver assets)
    as [s_erc20_inner | p q] eqn:Htr; [|discriminate].
  injection Hok as Hex_eq Herc_eq.
  subst s_erc20'.
  pose proof
    (ERC20.transfer_decreases_sender_increases_receiver_by_amount
       s_erc20 vault receiver assets s_erc20_inner Hne Hpos Htr)
    as (Hvault & _).
  rewrite Hvault. lia.
Qed.

End IntegrationWithdrawImmediate.
