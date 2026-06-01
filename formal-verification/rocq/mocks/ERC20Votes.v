(** OpenZeppelin ERC20Votes mock — composes ERC20 + Votes.

    Mirrors the surface of
      @openzeppelin/contracts/token/ERC20/extensions/ERC20Votes.sol
      (OZ v5.4.0).

    [ERC20Votes] is the abstract base that overlays per-account voting
    weight + delegation + checkpoint history on top of an ERC20 balance
    ledger.  Its central observation:

      "Voting units = ERC20 balance" (via [_getVotingUnits = balanceOf]).

    Every motion of ERC20 balance MUST be mirrored in the Votes
    checkpoint history; the central override [_update(from, to, value)]
    enforces this by calling [super._update] (the ERC20 ledger
    mutation) followed by [_transferVotingUnits(from, to, value)] (the
    Votes side bookkeeping).

    This mock therefore couples the two mocks' states under a single
    [State] record and provides a composed [_update] that performs
    BOTH effects in one shot.  Downstream proofs reason about the
    composed mutator and project out either side as needed.

    Composition shape:

      [State.erc20] : [ERC20.State]
          balances / totalSupply / allowances

      [State.votes] : [Votes.State.t]
          delegatee / delegate_ckpt / total_ckpt / voting_units / clock

    Coupling invariant (Valid.t):
      - ERC20 supply-eq: [sum balances = totalSupply]
      - Votes [voting_units] mirrors ERC20 [balanceOf]:
          forall a, voting_units a = balanceOf a
        (this is the "_getVotingUnits = balanceOf" override).
      - Both component invariants ([ERC20.Valid.t] and [Votes.Valid.t]).

    Mutator surface:
      - [update s from to value]
            The composed [_update] override.  Calls [erc20_update_pure]
            (a balance-side wrapper that updates [balances]/
            [totalSupply]) AND [Votes.transferVotingUnits].  The
            [voting_units] snapshot inside the Votes substate is kept
            consistent because [transferVotingUnits] already mirrors
            the balance motion in [voting_units].

      - [mint s to value]
            Sugar for [update s 0 to value].  Mirrors
            [ERC20._mint] -> [ERC20._update(0, to, value)] which
            ERC20Votes overrides to also push the total_ckpt.

      - [burn s from value]
            Sugar for [update s from 0 value].  Mirrors
            [ERC20._burn] -> [ERC20._update(from, 0, value)] which
            ERC20Votes overrides to also drop the total_ckpt.

      - [delegate s account new_d]
            Pure Votes-side mutator; ERC20 substate unchanged.

      - [transfer s from to value]
            Composes [update] under the OZ-faithful "from != 0 AND
            to != 0 AND balance >= value" guards.

    Read accessors:
      - [balanceOf s a]            ERC20.balanceOf composed with .erc20
      - [totalSupply s]            ERC20.(totalSupply) composed with .erc20
      - [getVotes s a]             Votes.getVotes composed with .votes
      - [getPastVotes s a t]       Votes.getPastVotes composed
      - [getTotalSupplyVotes s]    Votes.getTotalSupply (=total_ckpt latest)
      - [getPastTotalSupply s t]   Votes.getPastTotalSupply composed
      - [delegates s a]            Votes.delegates composed
      - [numCheckpoints s a]       Trace208.length of delegate_ckpt[a]
      - [checkpoints s a pos]      Trace208.at of delegate_ckpt[a]
      - [clock s]                  Votes.(clock)
      - [CLOCK_MODE]               Constant string sentinel

    What the mock does NOT model:
      - The [_maxSupply] check (`ERC20ExceededSafeSupply`).  We treat
        the uint208 supply bound as a [Valid.t]-side precondition.
      - The `delegateBySig` ECDSA + nonce path (composes the Nonces
        mock with [delegate]; out of scope here, see proofs/equivalence/
        for the composition lemma).
      - The exact ABI-level revert offsets — we use opaque [Revert].

    Used by:
      - This file's companion [proofs/equivalence/ERC20Votes.v]
        (slot-agnostic helpers + Section).
      - StakingVault's inheritance instantiation (task #256).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.Trace208.
Require Import ReserveGovernor.mocks.ERC20.
Require Import ReserveGovernor.mocks.Votes.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module ERC20Votes.

(** Address = U256.t, matching both inherited mocks. *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** ===== Composed state ===== *)

Module State.
  Record t : Set := {
    (** ERC20 ledger substate: balances + totalSupply + allowances. *)
    erc20 : ERC20.State;
    (** Votes substate: delegatee + delegate_ckpt + total_ckpt +
        voting_units snapshot + clock. *)
    votes : Votes.State.t;
  }.
End State.

(** Initial empty composed state — no balances, no checkpoints, clock
    at 0.  Use [init_state clk] when a nonzero starting clock is
    needed. *)
Definition empty_state : State.t := {|
  State.erc20 := ERC20.empty_state 0;
  State.votes := Votes.empty_state;
|}.

Definition init_state (clk : U256.t) : State.t := {|
  State.erc20 := ERC20.empty_state 0;
  State.votes :=
    {| Votes.State.delegatee     := Votes.empty_addr_map;
       Votes.State.delegate_ckpt := Votes.empty_trace_map;
       Votes.State.total_ckpt    := Trace208.empty;
       Votes.State.voting_units  := Votes.empty_units;
       Votes.State.clock         := clk;
    |};
|}.

(** ===== Read accessors ===== *)

Definition balanceOf (s : State.t) (a : Address) : U256.t :=
  ERC20.balanceOf s.(State.erc20) a.

Definition totalSupply (s : State.t) : U256.t :=
  s.(State.erc20).(ERC20.totalSupply).

Definition allowance (s : State.t) (owner spender : Address) : U256.t :=
  ERC20.allowance s.(State.erc20) owner spender.

Definition delegates (s : State.t) (account : Address) : Address :=
  Votes.delegates s.(State.votes) account.

Definition getVotes (s : State.t) (account : Address) : U256.t :=
  Votes.getVotes s.(State.votes) account.

Definition getPastVotes
    (s : State.t) (account : Address) (timepoint : U256.t)
    : Votes.Result.t U256.t :=
  Votes.getPastVotes s.(State.votes) account timepoint.

Definition getTotalSupplyVotes (s : State.t) : U256.t :=
  Votes.getTotalSupply s.(State.votes).

Definition getPastTotalSupply
    (s : State.t) (timepoint : U256.t) : Votes.Result.t U256.t :=
  Votes.getPastTotalSupply s.(State.votes) timepoint.

(** Public read of the OZ surface [numCheckpoints(account)] —
    the count of stored entries in the per-delegate Trace208. *)
Definition numCheckpoints (s : State.t) (account : Address) : Z :=
  Z.of_nat (length
    (s.(State.votes).(Votes.State.delegate_ckpt) account).(Trace208.entries)).

(** Public read of the OZ surface [checkpoints(account, pos)] —
    the (key, value) at position [pos] in the per-delegate Trace208.
    Returns [(0, 0)] for out-of-bounds indices, mirroring the OZ
    behavior under solc unchecked array access. *)
Definition checkpoints
    (s : State.t) (account : Address) (pos : Z) : U256.t * U256.t :=
  let entries := (s.(State.votes).(Votes.State.delegate_ckpt) account).(Trace208.entries) in
  nth (Z.to_nat pos) entries (0, 0).

(** OZ surface [clock()] — returns the configured clock value. *)
Definition clock (s : State.t) : U256.t :=
  s.(State.votes).(Votes.State.clock).

(** ===== Internal helpers ===== *)

(** [erc20_update_pure s from to value] — the ERC20-side balance/
    totalSupply update without revert paths, used to model the
    pre-checked super._update body.  This mirrors [ERC20._update]
    line-for-line but assumes the caller has already validated that
    [from] has sufficient balance (or [from = 0]).

    On the natural [_update(from, to, value)] body:
      if (from == 0) totalSupply += value
      else           balances[from] -= value
      if (to   == 0) totalSupply -= value
      else           balances[to]   += value

    The mock returns a [Result.t]: [Revert] on insufficient balance
    when [from <> 0], otherwise [Success new_state]. *)
Definition erc20_update_pure
    (s : ERC20.State) (from to : Address) (value : U256.t)
    : ERC20.Result.t ERC20.State :=
  if Z.eqb from zero_address then
    (* Mint path: bump totalSupply, credit [to] (if to != 0). *)
    if Z.eqb to zero_address then
      ERC20.Result.Success s
    else
      ERC20.Result.Success {|
        ERC20.balances :=
          ERC20.set_balance s.(ERC20.balances) to
            (ERC20.balanceOf s to + value);
        ERC20.totalSupply := s.(ERC20.totalSupply) + value;
        ERC20.allowances := s.(ERC20.allowances);
      |}
  else
    let b_from := ERC20.balanceOf s from in
    if b_from <? value then
      ERC20.revert_insufficient_balance
    else if Z.eqb to zero_address then
      (* Burn path. *)
      ERC20.Result.Success {|
        ERC20.balances :=
          ERC20.set_balance s.(ERC20.balances) from (b_from - value);
        ERC20.totalSupply := s.(ERC20.totalSupply) - value;
        ERC20.allowances := s.(ERC20.allowances);
      |}
    else
      (* Pure transfer.  from != 0, to != 0. *)
      let bs1 :=
        ERC20.set_balance s.(ERC20.balances) from (b_from - value) in
      let bs2 :=
        ERC20.set_balance bs1 to (ERC20.balanceOf s to + value) in
      ERC20.Result.Success {|
        ERC20.balances := bs2;
        ERC20.totalSupply := s.(ERC20.totalSupply);
        ERC20.allowances := s.(ERC20.allowances);
      |}.

(** Result wrapper for the composed mutator. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_insufficient_balance {A : Set} : Result.t A :=
  Result.Revert 0 32.
Definition revert_invalid_sender {A : Set} : Result.t A :=
  Result.Revert 32 32.
Definition revert_invalid_receiver {A : Set} : Result.t A :=
  Result.Revert 64 32.

(** ===== The composed [_update(from, to, value)] override =====

    OZ shape (ERC20Votes.sol:48-58):
      super._update(from, to, value);   // ERC20 ledger mutation
      if (from == 0) {
        uint256 supply = totalSupply();
        if (supply > _maxSupply()) revert ...;
      }
      _transferVotingUnits(from, to, value);

    The mock omits the [_maxSupply] check (treated as a [Valid.t]
    precondition).  The dual update:

      1. erc20_update_pure  -> updates balances + totalSupply
      2. transferVotingUnits -> pushes total_ckpt (mint/burn) +
                                delegate_ckpt (via moveDelegateVotes) +
                                refreshes voting_units snapshot

    Order matters for the Valid.t coupling — [transferVotingUnits]
    needs to see the *updated* balances to maintain the
    "voting_units = balanceOf" invariant.  But since
    [transferVotingUnits] keeps its own [voting_units] snapshot
    and updates it itself (mirroring the balance motion),
    composing the two side-by-side preserves the invariant:

      voting_units(pre) = balanceOf(pre)
      balanceOf(post) = balanceOf(pre) +/- value
      voting_units(post) = voting_units(pre) +/- value
                         = balanceOf(pre) +/- value
                         = balanceOf(post)

    The Votes [transferVotingUnits] does NOT read [balanceOf]; it
    reads its own [voting_units] snapshot.  So the order of the two
    component calls is observationally equivalent — we run them in
    the production order (ERC20 first, Votes second) for the
    Equivalence proof to lay out clean walker arms. *)
Definition update
    (s : State.t) (from to : Address) (value : U256.t)
    : Result.t State.t :=
  match erc20_update_pure s.(State.erc20) from to value with
  | ERC20.Result.Revert p q => Result.Revert p q
  | ERC20.Result.Success erc20' =>
      let votes' := Votes.transferVotingUnits s.(State.votes) from to value in
      Result.Success {| State.erc20 := erc20'; State.votes := votes' |}
  end.

(** Convenience: [mint], [burn], [pure_transfer].  Sugar on top of
    [update] with the appropriate sentinel address.  These mirror the
    OZ [_mint] / [_burn] / [_transfer] internal helpers — all routed
    through the composed [_update]. *)
Definition mint
    (s : State.t) (to : Address) (value : U256.t) : Result.t State.t :=
  if Z.eqb to zero_address then revert_invalid_receiver
  else update s zero_address to value.

Definition burn
    (s : State.t) (from : Address) (value : U256.t) : Result.t State.t :=
  if Z.eqb from zero_address then revert_invalid_sender
  else update s from zero_address value.

Definition pure_transfer
    (s : State.t) (from to : Address) (value : U256.t) : Result.t State.t :=
  update s from to value.

(** ===== Public Votes mutators =====

    [delegate(account, new_d)] does NOT touch the ERC20 substate —
    only the Votes substate.  We lift the Votes-side mutator
    directly. *)
Definition delegate
    (s : State.t) (account new_d : Address) : State.t :=
  {| State.erc20 := s.(State.erc20);
     State.votes := Votes.delegate s.(State.votes) account new_d;
  |}.

(** ===== Public ERC20 mutators that go through _update ===== *)

(** [transfer s from to value] — uses the composed update under the
    OZ "from != 0 AND to != 0 AND balance >= value" guards.  Returns
    [Revert] on guard failure, [Success new_state] otherwise. *)
Definition transfer
    (s : State.t) (from to : Address) (value : U256.t) : Result.t State.t :=
  if Z.eqb from zero_address then revert_invalid_sender
  else if Z.eqb to zero_address then revert_invalid_receiver
  else update s from to value.

(** ===== Coupling invariant ===== *)

Module Valid.
  (** The composed invariant ties the ERC20 substate and the Votes
      substate together via [_getVotingUnits = balanceOf]. *)
  Record t (s : State.t) : Prop := {
    (** ERC20's standard supply/non-negativity/u256 invariants. *)
    erc20_valid : ERC20.Valid.t s.(State.erc20);
    (** Votes' standard per-delegate + total checkpoint sortedness. *)
    votes_valid : Votes.Valid.t s.(State.votes);
    (** Coupling: [_getVotingUnits = balanceOf].  This is the
        critical link that ERC20Votes establishes — without it the
        composed contract would have inconsistent "voting units" and
        "balance" views. *)
    voting_units_eq_balance :
      forall a,
        s.(State.votes).(Votes.State.voting_units) a
        = ERC20.balanceOf s.(State.erc20) a;
    (** Total checkpoint latest <= 2^208 - 1 (the [_maxSupply]
        bound that ERC20Votes enforces in production via
        [ERC20ExceededSafeSupply]).  Treated as a precondition we
        assume rather than guard against in the mutator body. *)
    total_ckpt_bound :
      Trace208.latest s.(State.votes).(Votes.State.total_ckpt) <= 2^208 - 1;
  }.

  Lemma empty_valid : t empty_state.
  Proof.
    constructor; simpl.
    - apply ERC20.Valid.empty_valid; [unfold U256.Valid.t; lia | reflexivity].
    - apply Votes.Valid.empty_valid.
    - intros a. reflexivity.
    - cbn. lia.
  Qed.
End Valid.

(** ===== Lemmas about the ERC20-side pure update ===== *)

Lemma erc20_update_pure_balance_to_from_zero :
  forall (s : ERC20.State) (to : Address) (value : U256.t) (s' : ERC20.State),
    to <> zero_address ->
    erc20_update_pure s zero_address to value = ERC20.Result.Success s' ->
    ERC20.balanceOf s' to = ERC20.balanceOf s to + value.
Proof.
  intros s to value s' Htz Hok.
  unfold erc20_update_pure in Hok.
  rewrite Z.eqb_refl in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  injection Hok as Hs'. subst s'.
  unfold ERC20.balanceOf. cbn.
  apply ERC20.balance_lookup_set_balance_eq.
Qed.

Lemma erc20_update_pure_balance_other_from_zero :
  forall (s : ERC20.State) (to a : Address) (value : U256.t) (s' : ERC20.State),
    to <> zero_address ->
    a <> to ->
    erc20_update_pure s zero_address to value = ERC20.Result.Success s' ->
    ERC20.balanceOf s' a = ERC20.balanceOf s a.
Proof.
  intros s to a value s' Htz Hane Hok.
  unfold erc20_update_pure in Hok.
  rewrite Z.eqb_refl in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  injection Hok as Hs'. subst s'.
  unfold ERC20.balanceOf. cbn.
  apply ERC20.balance_lookup_set_balance_neq.
  intros Heq. apply Hane. symmetry. exact Heq.
Qed.

Lemma erc20_update_pure_totalSupply_from_zero :
  forall (s : ERC20.State) (to : Address) (value : U256.t) (s' : ERC20.State),
    to <> zero_address ->
    erc20_update_pure s zero_address to value = ERC20.Result.Success s' ->
    s'.(ERC20.totalSupply) = s.(ERC20.totalSupply) + value.
Proof.
  intros s to value s' Htz Hok.
  unfold erc20_update_pure in Hok.
  rewrite Z.eqb_refl in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

Lemma erc20_update_pure_totalSupply_to_zero :
  forall (s : ERC20.State) (from : Address) (value : U256.t) (s' : ERC20.State),
    from <> zero_address ->
    ERC20.balanceOf s from >= value ->
    erc20_update_pure s from zero_address value = ERC20.Result.Success s' ->
    s'.(ERC20.totalSupply) = s.(ERC20.totalSupply) - value.
Proof.
  intros s from value s' Hfz Hbal Hok.
  unfold erc20_update_pure in Hok.
  assert (Hfz' : Z.eqb from zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  rewrite Hfz' in Hok.
  assert (Hltb : (ERC20.balanceOf s from <? value) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hltb in Hok.
  rewrite Z.eqb_refl in Hok.
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

Lemma erc20_update_pure_totalSupply_pure_transfer :
  forall (s : ERC20.State) (from to : Address) (value : U256.t) (s' : ERC20.State),
    from <> zero_address ->
    to <> zero_address ->
    ERC20.balanceOf s from >= value ->
    erc20_update_pure s from to value = ERC20.Result.Success s' ->
    s'.(ERC20.totalSupply) = s.(ERC20.totalSupply).
Proof.
  intros s from to value s' Hfz Htz Hbal Hok.
  unfold erc20_update_pure in Hok.
  assert (Hfz' : Z.eqb from zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  rewrite Hfz' in Hok.
  assert (Hltb : (ERC20.balanceOf s from <? value) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hltb in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  injection Hok as Hs'. subst s'. cbn. reflexivity.
Qed.

(** ===== Composed-mutator headline lemmas ===== *)

(** L_mint_increases_total_supply: minting [value] to a non-zero
    [to] increases [totalSupply] by exactly [value]. *)
Lemma mint_increases_totalSupply :
  forall (s : State.t) (to : Address) (value : U256.t) (s' : State.t),
    to <> zero_address ->
    mint s to value = Result.Success s' ->
    totalSupply s' = totalSupply s + value.
Proof.
  intros s to value s' Htz Hok.
  unfold mint in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  unfold update in Hok.
  destruct (erc20_update_pure s.(State.erc20) zero_address to value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'.
  unfold totalSupply. cbn.
  eapply erc20_update_pure_totalSupply_from_zero; eauto.
Qed.

(** Helper: moveDelegateVotes preserves total_ckpt. *)
Lemma moveDelegateVotes_preserves_total_ckpt :
  forall (s : Votes.State.t) (from to : Address) (amount : Z),
    (Votes.moveDelegateVotes s from to amount).(Votes.State.total_ckpt)
    = s.(Votes.State.total_ckpt).
Proof.
  intros s from to amount.
  unfold Votes.moveDelegateVotes.
  destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; reflexivity.
Qed.

(** Helper: total_ckpt of transferVotingUnits is just push_add on mint
    path.  Proof unfolds the mock and observes that [moveDelegateVotes]
    only touches [delegate_ckpt], not [total_ckpt]. *)
Lemma transferVotingUnits_total_ckpt_mint :
  forall (s : Votes.State.t) (to : Address) (value : U256.t),
    to <> zero_address ->
    (Votes.transferVotingUnits s zero_address to value).(Votes.State.total_ckpt)
    = Votes.push_add s.(Votes.State.total_ckpt) s.(Votes.State.clock) value.
Proof.
  intros s to value Htz.
  assert (Htz' : Z.eqb to Votes.zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  unfold Votes.transferVotingUnits.
  rewrite moveDelegateVotes_preserves_total_ckpt.
  cbn [Votes.State.total_ckpt].
  rewrite Htz'. reflexivity.
Qed.

Lemma transferVotingUnits_total_ckpt_burn :
  forall (s : Votes.State.t) (from : Address) (value : U256.t),
    from <> zero_address ->
    (Votes.transferVotingUnits s from zero_address value).(Votes.State.total_ckpt)
    = Votes.push_sub s.(Votes.State.total_ckpt) s.(Votes.State.clock) value.
Proof.
  intros s from value Hfz.
  assert (Hfz' : Z.eqb from Votes.zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  unfold Votes.transferVotingUnits.
  rewrite moveDelegateVotes_preserves_total_ckpt.
  cbn [Votes.State.total_ckpt].
  rewrite Hfz'. reflexivity.
Qed.

Lemma transferVotingUnits_total_ckpt_pure :
  forall (s : Votes.State.t) (from to : Address) (value : U256.t),
    from <> zero_address ->
    to <> zero_address ->
    (Votes.transferVotingUnits s from to value).(Votes.State.total_ckpt)
    = s.(Votes.State.total_ckpt).
Proof.
  intros s from to value Hfz Htz.
  assert (Hfz' : Z.eqb from Votes.zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  assert (Htz' : Z.eqb to Votes.zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  unfold Votes.transferVotingUnits.
  rewrite moveDelegateVotes_preserves_total_ckpt.
  cbn [Votes.State.total_ckpt].
  rewrite Hfz', Htz'. reflexivity.
Qed.

(** L_mint_pushes_total_ckpt: minting [value] also pushes [+value]
    onto the [_totalCheckpoints]. *)
Lemma mint_pushes_total_ckpt :
  forall (s : State.t) (to : Address) (value : U256.t) (s' : State.t),
    to <> zero_address ->
    mint s to value = Result.Success s' ->
    s'.(State.votes).(Votes.State.total_ckpt)
    = Votes.push_add s.(State.votes).(Votes.State.total_ckpt)
        s.(State.votes).(Votes.State.clock) value.
Proof.
  intros s to value s' Htz Hok.
  unfold mint in Hok.
  assert (Htz' : Z.eqb to zero_address = false)
    by (apply Z.eqb_neq; exact Htz).
  rewrite Htz' in Hok.
  unfold update in Hok.
  destruct (erc20_update_pure s.(State.erc20) zero_address to value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'. cbn [State.votes].
  apply transferVotingUnits_total_ckpt_mint. exact Htz.
Qed.

(** L_burn_decreases_total_supply: burning [value] from a non-zero
    [from] (with sufficient balance) decreases [totalSupply] by exactly
    [value]. *)
Lemma burn_decreases_totalSupply :
  forall (s : State.t) (from : Address) (value : U256.t) (s' : State.t),
    from <> zero_address ->
    ERC20.balanceOf s.(State.erc20) from >= value ->
    burn s from value = Result.Success s' ->
    totalSupply s' = totalSupply s - value.
Proof.
  intros s from value s' Hfz Hbal Hok.
  unfold burn in Hok.
  assert (Hfz' : Z.eqb from zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  rewrite Hfz' in Hok.
  unfold update in Hok.
  destruct (erc20_update_pure s.(State.erc20) from zero_address value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'. unfold totalSupply. cbn.
  eapply erc20_update_pure_totalSupply_to_zero; eauto.
Qed.

(** L_burn_pushes_total_ckpt: burning also pushes [-value] onto
    the [_totalCheckpoints]. *)
Lemma burn_pushes_total_ckpt :
  forall (s : State.t) (from : Address) (value : U256.t) (s' : State.t),
    from <> zero_address ->
    ERC20.balanceOf s.(State.erc20) from >= value ->
    burn s from value = Result.Success s' ->
    s'.(State.votes).(Votes.State.total_ckpt)
    = Votes.push_sub s.(State.votes).(Votes.State.total_ckpt)
        s.(State.votes).(Votes.State.clock) value.
Proof.
  intros s from value s' Hfz Hbal Hok.
  unfold burn in Hok.
  assert (Hfz' : Z.eqb from zero_address = false)
    by (apply Z.eqb_neq; exact Hfz).
  rewrite Hfz' in Hok.
  unfold update in Hok.
  destruct (erc20_update_pure s.(State.erc20) from zero_address value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'. cbn [State.votes].
  apply transferVotingUnits_total_ckpt_burn. exact Hfz.
Qed.

(** L_pure_transfer_preserves_total_supply: pure transfers (both
    [from] and [to] non-zero) preserve [totalSupply]. *)
Lemma pure_transfer_preserves_totalSupply :
  forall (s : State.t) (from to : Address) (value : U256.t) (s' : State.t),
    from <> zero_address ->
    to <> zero_address ->
    ERC20.balanceOf s.(State.erc20) from >= value ->
    pure_transfer s from to value = Result.Success s' ->
    totalSupply s' = totalSupply s.
Proof.
  intros s from to value s' Hfz Htz Hbal Hok.
  unfold pure_transfer, update in Hok.
  destruct (erc20_update_pure s.(State.erc20) from to value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'. unfold totalSupply. cbn.
  eapply erc20_update_pure_totalSupply_pure_transfer with (from := from) (to := to);
    eauto.
Qed.

(** L_pure_transfer_preserves_total_ckpt: pure transfers preserve
    the [_totalCheckpoints] history (no push fires). *)
Lemma pure_transfer_preserves_total_ckpt :
  forall (s : State.t) (from to : Address) (value : U256.t) (s' : State.t),
    from <> zero_address ->
    to <> zero_address ->
    ERC20.balanceOf s.(State.erc20) from >= value ->
    pure_transfer s from to value = Result.Success s' ->
    s'.(State.votes).(Votes.State.total_ckpt)
    = s.(State.votes).(Votes.State.total_ckpt).
Proof.
  intros s from to value s' Hfz Htz Hbal Hok.
  unfold pure_transfer, update in Hok.
  destruct (erc20_update_pure s.(State.erc20) from to value)
    as [erc20' | p q] eqn:Hpure; [|discriminate].
  injection Hok as Hs'. subst s'. cbn [State.votes].
  apply transferVotingUnits_total_ckpt_pure; assumption.
Qed.

(** L_delegate_preserves_erc20: pure delegate is a Votes-only mutator. *)
Lemma delegate_preserves_erc20 :
  forall (s : State.t) (account new_d : Address),
    (delegate s account new_d).(State.erc20) = s.(State.erc20).
Proof.
  intros s account new_d. reflexivity.
Qed.

(** L_delegate_preserves_balanceOf: delegate doesn't move ERC20 balances. *)
Lemma delegate_preserves_balanceOf :
  forall (s : State.t) (account new_d : Address) (a : Address),
    balanceOf (delegate s account new_d) a = balanceOf s a.
Proof.
  intros. unfold balanceOf, delegate. reflexivity.
Qed.

(** L_delegate_preserves_totalSupply. *)
Lemma delegate_preserves_totalSupply :
  forall (s : State.t) (account new_d : Address),
    totalSupply (delegate s account new_d) = totalSupply s.
Proof.
  intros. reflexivity.
Qed.

(** ===== vm_compute examples ===== *)

Module Examples.

  Definition addr_a : Address := 10.
  Definition addr_b : Address := 20.

  Definition s0 : State.t := init_state 100.

  (** Mint 50 to addr_a. *)
  Definition s1 : State.t :=
    match mint s0 addr_a 50 with
    | Result.Success s' => s'
    | _ => s0
    end.

  Example ex_mint_balance :
    balanceOf s1 addr_a = 50.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_mint_totalSupply :
    totalSupply s1 = 50.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_mint_total_ckpt_latest :
    getTotalSupplyVotes s1 = 50.
  Proof. vm_compute. reflexivity. Qed.

  (** Delegate addr_a -> addr_b. *)
  Definition s2 : State.t := delegate s1 addr_a addr_b.

  Example ex_delegate_then_check_delegatee :
    delegates s2 addr_a = addr_b.
  Proof. vm_compute. reflexivity. Qed.

  (** After delegating to addr_b, addr_b should have 50 votes
      (the Votes._delegate runs moveDelegateVotes from address(0)
      [prior delegate, since unset = address(0)] to addr_b at units
      50 [= voting_units(addr_a) after mint]). *)
  Example ex_delegate_then_check_getVotes :
    getVotes s2 addr_b = 50.
  Proof. vm_compute. reflexivity. Qed.

  (** Burn 20 from addr_a: balance and totalSupply drop. *)
  Definition s3 : State.t :=
    match burn s2 addr_a 20 with
    | Result.Success s' => s'
    | _ => s2
    end.

  Example ex_burn_balance :
    balanceOf s3 addr_a = 30.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_burn_totalSupply :
    totalSupply s3 = 30.
  Proof. vm_compute. reflexivity. Qed.

  Example ex_burn_total_ckpt :
    getTotalSupplyVotes s3 = 30.
  Proof. vm_compute. reflexivity. Qed.

  (** addr_b's getVotes drops too, since addr_a delegates to addr_b
      and the burn drops voting_units(addr_a) -> moveDelegateVotes
      from delegates(addr_a)=addr_b to delegates(0)=0 with amount 20.
      addr_b's checkpoint thus decrements by 20. *)
  Example ex_burn_getVotes :
    getVotes s3 addr_b = 30.
  Proof. vm_compute. reflexivity. Qed.

End Examples.

End ERC20Votes.
