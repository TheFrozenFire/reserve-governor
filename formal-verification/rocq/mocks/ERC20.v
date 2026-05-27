(** ERC20 mock — minimal balance-map IERC20 / SafeERC20.

    Captures the OpenZeppelin ERC20 surface that the Reserve Governor's
    [StakingVault] depends on for reward conservation:

      - [balanceOf(addr)]                              (read)
      - [transfer(to, amount)]                         (write, msg.sender = vault)
      - [transferFrom(from, to, amount)]               (write, with allowance)

    This is the "honest-token" ERC20: a list-backed [Address -> U256.t]
    balance map plus a [totalSupply] field. The mock does NOT model:
      - Fee-on-transfer tokens (the [transfer] decreases sender and
        increases receiver by *exactly* [amount]).
      - Allowance state machine in detail. [transferFrom] takes the
        [allowance] as an explicit argument; the production-side
        [_spendAllowance] decrement is left to the caller.
      - ERC20 hooks ([_beforeTokenTransfer], etc.).
      - Mint/burn paths (out of scope for the reward-conservation
        theorem; [totalSupply] is constant across our [transfer] and
        [transferFrom]).

    These restrictions match the "T-REWARDTOKEN" trust assumption
    documented in [external_dependencies.md]: registered reward tokens
    are assumed to behave like this minimal model.

    Used by:
      - [StakingVaultRewards.v] (reward-conservation theorem: the sum
        of per-token [transfer] amounts in [claimRewards] equals the
        change in vault-side [totalClaimed]).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Module ERC20.

(** Address model — opaque [U256.t], matching the existing simulation
    convention (see [StakingVaultDelegation.v]). *)
Definition Address : Set := U256.t.

(** Two-constructor result with reverts on insufficient balance.
    Mirrors the [ProposerThrottle.Result.t] shape so the eventual
    run-* equivalence proof can match Yul offsets if needed. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_insufficient_balance   {A : Set} : Result.t A :=
  Result.Revert 0 32.
Definition revert_insufficient_allowance {A : Set} : Result.t A :=
  Result.Revert 32 32.

(** ERC20 contract storage. *)
Record State : Set := {
  balances    : list (Address * U256.t);
  totalSupply : U256.t;
}.

Definition empty_state (supply : U256.t) : State := {|
  balances := [];
  totalSupply := supply;
|}.

(** [balanceOf s addr]: list-lookup, default 0. Mirrors Solidity's
    mapping-default behavior. *)
Fixpoint balance_lookup (bs : list (Address * U256.t)) (a : Address) : U256.t :=
  match bs with
  | [] => 0
  | (k, v) :: rest => if Z.eqb k a then v else balance_lookup rest a
  end.

Definition balanceOf (s : State) (a : Address) : U256.t :=
  balance_lookup s.(balances) a.

(** [set_balance bs a v]: pointwise update. Adds the [(a, v)] pair if
    missing; replaces in place if present. *)
Fixpoint set_balance
    (bs : list (Address * U256.t)) (a : Address) (v : U256.t)
    : list (Address * U256.t) :=
  match bs with
  | [] => [(a, v)]
  | (k, vv) :: rest =>
      if Z.eqb k a then (a, v) :: rest else (k, vv) :: set_balance rest a v
  end.

(** Internal transfer step: debit [from] and credit [to] by [amount].
    Used by both [transfer] (where [from = caller]) and [transferFrom]
    (where [from] is the spender's victim). The amount-zero and
    from=to short-circuits (matching OZ ERC20.transfer) keep the
    no-op cases honest. *)
Definition do_transfer
    (s : State) (from to : Address) (amount : U256.t) : Result.t State :=
  if Z.eqb amount 0 then
    (* Zero transfer: no state change. OZ ERC20 also returns true. *)
    Result.Success s
  else if Z.eqb from to then
    (* Self-transfer: no net change. *)
    Result.Success s
  else
    let b_from := balanceOf s from in
    if b_from <? amount then
      revert_insufficient_balance
    else
      let b_to := balanceOf s to in
      let bs1  := set_balance s.(balances) from (b_from - amount) in
      let bs2  := set_balance bs1 to (b_to + amount) in
      Result.Success {| balances := bs2; totalSupply := s.(totalSupply) |}.

(** [transfer s from to amount]: a self-initiated transfer. The mock
    takes [from] as an explicit argument (production: msg.sender);
    callers should bind it to the caller's address. *)
Definition transfer
    (s : State) (from to : Address) (amount : U256.t) : Result.t State :=
  do_transfer s from to amount.

(** [transferFrom s caller from to amount allowance]: spending on
    behalf of [from]. The [allowance] is the pre-call allowance
    [caller] holds for [from]; the mock checks it suffices and
    decrements implicitly by reverting if not. Real OZ ERC20 also
    mutates allowance storage; that's out of scope here. *)
Definition transferFrom
    (s : State) (caller from to : Address) (amount allowance : U256.t)
    : Result.t State :=
  let _ := caller in
  if allowance <? amount then
    revert_insufficient_allowance
  else
    do_transfer s from to amount.

(** -- Validity invariant -- *)

Fixpoint sum_balances (bs : list (Address * U256.t)) : U256.t :=
  match bs with
  | [] => 0
  | (_, v) :: rest => v + sum_balances rest
  end.

Fixpoint all_nonneg (bs : list (Address * U256.t)) : Prop :=
  match bs with
  | [] => True
  | (_, v) :: rest => 0 <= v /\ all_nonneg rest
  end.

Module Valid.
  Record t (s : State) : Prop := {
    supply_eq    : sum_balances s.(balances) = s.(totalSupply);
    balances_nn  : all_nonneg s.(balances);
    supply_u256  : U256.Valid.t s.(totalSupply);
  }.

  Lemma empty_valid : forall supply,
    U256.Valid.t supply ->
    supply = 0 ->
    t (empty_state supply).
  Proof.
    intros supply Hu256 Hzero. constructor; simpl.
    - rewrite Hzero. reflexivity.
    - exact I.
    - exact Hu256.
  Qed.
End Valid.

(** -- Headline lemmas --

    Reward-conservation (StakingVault) wants:
      (i) transfers preserve totalSupply,
      (ii) the change in sender's and receiver's balances is exactly
           [amount] (with the right signs),
      (iii) the zero/self-transfer corner is a no-op.
*)

(** L1: [transfer] does not change [totalSupply]. *)
Lemma transfer_preserves_total_supply :
  forall (s : State) (from to : Address) (amount : U256.t) (s' : State),
    transfer s from to amount = Result.Success s' ->
    s'.(totalSupply) = s.(totalSupply).
Proof.
  intros s from to amount s' Htr.
  unfold transfer, do_transfer in Htr.
  destruct (Z.eqb amount 0) eqn:Hamt.
  - injection Htr as Hs'. subst s'. reflexivity.
  - destruct (Z.eqb from to) eqn:Hft.
    + injection Htr as Hs'. subst s'. reflexivity.
    + destruct (balanceOf s from <? amount) eqn:Hbal.
      * discriminate Htr.
      * injection Htr as Hs'. subst s'. simpl. reflexivity.
Qed.

(** Helper: [balance_lookup] of [set_balance] on a *different* key
    returns the original value. *)
Lemma balance_lookup_set_balance_neq :
  forall bs a b v,
    a <> b ->
    balance_lookup (set_balance bs a v) b = balance_lookup bs b.
Proof.
  intros bs a b v Hneq.
  induction bs as [|[k vv] rest IH].
  - simpl. destruct (Z.eqb a b) eqn:Hab.
    + apply Z.eqb_eq in Hab. contradiction.
    + reflexivity.
  - simpl. destruct (Z.eqb k a) eqn:Hka.
    + apply Z.eqb_eq in Hka. subst k.
      simpl. destruct (Z.eqb a b) eqn:Hab.
      * apply Z.eqb_eq in Hab. contradiction.
      * reflexivity.
    + simpl. destruct (Z.eqb k b) eqn:Hkb.
      * reflexivity.
      * exact IH.
Qed.

(** Helper: [balance_lookup] of [set_balance] on the *same* key
    returns the new value. *)
Lemma balance_lookup_set_balance_eq :
  forall bs a v,
    balance_lookup (set_balance bs a v) a = v.
Proof.
  intros bs a v.
  induction bs as [|[k vv] rest IH].
  - simpl. rewrite Z.eqb_refl. reflexivity.
  - simpl. destruct (Z.eqb k a) eqn:Hka.
    + apply Z.eqb_eq in Hka. subst k.
      simpl. rewrite Z.eqb_refl. reflexivity.
    + simpl. rewrite Hka. exact IH.
Qed.

(** L2: a successful transfer with [from != to] and [amount != 0]
    debits exactly [amount] from sender, credits exactly [amount] to
    receiver. *)
Lemma transfer_decreases_sender_increases_receiver_by_amount :
  forall (s : State) (from to : Address) (amount : U256.t) (s' : State),
    from <> to ->
    0 < amount ->
    transfer s from to amount = Result.Success s' ->
    balanceOf s' from = balanceOf s from - amount /\
    balanceOf s' to   = balanceOf s to   + amount.
Proof.
  intros s from to amount s' Hneq Hpos Htr.
  unfold transfer, do_transfer in Htr.
  destruct (Z.eqb amount 0) eqn:Hamt.
  { apply Z.eqb_eq in Hamt. lia. }
  destruct (Z.eqb from to) eqn:Hft.
  { apply Z.eqb_eq in Hft. contradiction. }
  destruct (balanceOf s from <? amount) eqn:Hbal.
  { discriminate. }
  injection Htr as Hs'. subst s'.
  split.
  - (* sender: set_balance bs1 to (...) doesn't touch [from] since
       from <> to; set_balance bs0 from (b_from - amount) hits [from]. *)
    unfold balanceOf at 1. cbn [balances].
    rewrite balance_lookup_set_balance_neq
      by (intro H; apply Hneq; symmetry; exact H).
    rewrite balance_lookup_set_balance_eq.
    reflexivity.
  - (* receiver: outermost set_balance sets [to]. *)
    unfold balanceOf at 1. cbn [balances].
    rewrite balance_lookup_set_balance_eq.
    reflexivity.
Qed.

(** L3: a zero-amount transfer or a self-transfer is a state no-op. *)
Lemma transfer_zero_to_self_noop :
  forall (s : State) (from to : Address) (amount : U256.t),
    (amount = 0 \/ from = to) ->
    transfer s from to amount = Result.Success s.
Proof.
  intros s from to amount [Hamt | Hft].
  - unfold transfer, do_transfer. subst amount.
    rewrite Z.eqb_refl. reflexivity.
  - unfold transfer, do_transfer. subst to.
    destruct (Z.eqb amount 0) eqn:H.
    + reflexivity.
    + rewrite Z.eqb_refl. reflexivity.
Qed.

(** -- vm_compute examples -- *)

Module Examples.

(** Three-account starting state: alice has 100, bob has 50. *)
Definition alice : Address := 1.
Definition bob   : Address := 2.
Definition carol : Address := 3.

Definition s0 : State := {|
  balances := [(alice, 100); (bob, 50)];
  totalSupply := 150;
|}.

(** Successful transfer: alice sends 30 to carol. *)
Example ex_transfer_ok :
  match transfer s0 alice carol 30 with
  | Result.Success s' =>
      balanceOf s' alice = 70 /\
      balanceOf s' carol = 30 /\
      balanceOf s' bob   = 50 /\
      s'.(totalSupply)   = 150
  | _ => False
  end.
Proof. vm_compute. repeat split. Qed.

(** Insufficient balance: alice tries to send 200 (only has 100). *)
Example ex_transfer_revert :
  match transfer s0 alice carol 200 with
  | Result.Revert _ _ => True
  | _ => False
  end.
Proof. vm_compute. exact I. Qed.

(** Zero transfer: state unchanged. *)
Example ex_transfer_zero :
  transfer s0 alice carol 0 = Result.Success s0.
Proof. vm_compute. reflexivity. Qed.

(** transferFrom with sufficient allowance: succeeds. *)
Example ex_transferFrom_ok :
  match transferFrom s0 carol alice bob 20 50 with
  | Result.Success s' =>
      balanceOf s' alice = 80 /\
      balanceOf s' bob   = 70
  | _ => False
  end.
Proof. vm_compute. repeat split. Qed.

(** transferFrom with insufficient allowance: reverts. *)
Example ex_transferFrom_revert :
  match transferFrom s0 carol alice bob 20 10 with
  | Result.Revert _ _ => True
  | _ => False
  end.
Proof. vm_compute. exact I. Qed.

(** Validity holds for s0. *)
Example ex_s0_valid : Valid.t s0.
Proof.
  constructor; cbn.
  - reflexivity.
  - repeat split; lia.
  - unfold U256.Valid.t. lia.
Qed.

End Examples.

End ERC20.
