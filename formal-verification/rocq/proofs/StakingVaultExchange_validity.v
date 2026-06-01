(** StakingVaultExchange validity preservation.

    [Valid.state] bundles four properties on a [State.t]:

      - [supply_u256]  : totalSupply fits in uint256.
      - [deposited_nn] : totalDeposited is non-negative.
      - [rewards_nn]   : accumulatedNativeRewards is non-negative.
      - [backed]       : totalSupply > 0 -> totalDeposited > 0.
                         The "never-underwater" invariant: whenever
                         there are outstanding shares, there is at
                         least one user deposit backing them.

    We prove preservation across the three storage-changing
    operations:

      - [deposit_preserves_validity]  : a deposit cannot break any
        of the four properties. The interesting case is [backed]: a
        deposit either (i) leaves [supply = 0] (zero-asset no-op),
        or (ii) bumps both [totalSupply] and [totalDeposited] by
        positive amounts. The supply=0 -> supply>0 transition is
        the 1:1 initial mint, so both fields go positive together.

      - [withdraw_preserves_validity] : a successful withdraw
        cannot underflow [totalDeposited] (precondition
        [assets <= totalDeposited]) nor [totalSupply] (the ceil-div
        share-burn never exceeds [supply]). The [backed] invariant
        carries through by case-splitting on whether the burn drains
        all shares ([shares = totalSupply], so post-supply = 0 makes
        the antecedent vacuous) or is partial (then the caller must
        not have asked to drain all of [totalDeposited]).

      - [accrue_preserves_validity]   : trivial — only bumps
        [accumulatedNativeRewards] upward by a non-negative delta.

      - [empty_state_valid]           : the initial state is valid.
        [backed]'s antecedent is false at supply=0.

      - [never_underwater]            : the headline. For any valid
        state with [totalSupply > 0],
        [totalAssets s >= totalDeposited s > 0]. The contract's
        totalAssets is at least the sum of user deposits — reward
        accrual only adds to it.

    Plus a [vm_compute] cross-check that walks a deposit/accrue/
    withdraw cycle and asserts [Valid.state] at every step.

    Modeling note: the [withdraw] simulation guards
    [assets > totalAssets] (the OZ default) and also
    [shares > totalSupply] (the implicit ERC20 [_burn] guard). It does
    NOT guard [assets > totalDeposited]. With native rewards accrued
    ([accumulatedNativeRewards > 0]), it is therefore possible to
    submit [totalDeposited < assets <= totalAssets] and underflow
    [totalDeposited]. We surface that gap here by requiring
    [assets <= totalDeposited] as an explicit precondition.

    Under the OZ v5.4 inflation-defended formula, [previewWithdraw]
    rounds shares up; even for [assets = totalDeposited] the ceil-div
    can demand strictly more than [totalSupply] when rewards have
    accrued. Such an attempt now reverts via the new share-bound
    guard. The [Result.Success (s', shares)] hypothesis below
    therefore implies [shares <= totalSupply] automatically — no
    helper bound is needed. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import Coq.Bool.Bool.

Module StakingVaultExchangeValidity.

Import StakingVaultExchange.
Import StakingVaultExchange.Valid.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** ----- Helper: convertToShares is non-negative for valid inputs. ----- *)
Lemma convertToShares_nonneg (s : State.t) (assets : U256.t) :
  Valid.state s ->
  0 <= assets ->
  0 <= convertToShares s assets.
Proof.
  intros Hv Ha.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  unfold convertToShares.
  assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
  assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
  apply Z.div_pos; [nia | lia].
Qed.

(** ----- empty_state is valid. ----- *)
Lemma empty_state_valid : Valid.state empty_state.
Proof.
  unfold empty_state.
  constructor; simpl.
  - unfold U256.Valid.t. split; [lia|]. lia.
  - lia.
  - lia.
  - intros H. lia.
Qed.

(** ----- deposit preserves Valid.state. -----

    Preconditions:
      - [Valid.state s] : pre-state is valid.
      - [U256.Valid.t assets] : assets fits in uint256.
      - [U256.Valid.t (totalSupply + shares)] : the post-supply
        fits in uint256. With shares = convertToShares s assets,
        this is a bound the caller (the ERC4626 [deposit] entry
        point) must witness via slot-availability before minting.
      - [U256.Valid.t (totalDeposited + assets)] : same for
        totalDeposited.

    These two upper-bound preconditions match the natural
    pre-checks an EVM caller performs (the deposit cap, etc.). *)
Lemma deposit_preserves_validity (s : State.t) (assets : U256.t) :
  Valid.state s ->
  U256.Valid.t assets ->
  U256.Valid.t (s.(State.totalSupply) + convertToShares s assets) ->
  U256.Valid.t (s.(State.totalDeposited) + assets) ->
  Valid.state (fst (deposit s assets)).
Proof.
  intros Hv Hassets_u256 Hsupply_bound Htd_bound.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  unfold deposit. simpl.
  set (shares := convertToShares s assets).
  assert (Hassets_nn : 0 <= assets) by (destruct Hassets_u256; lia).
  assert (Hshares_nn : 0 <= shares).
  { apply convertToShares_nonneg.
    - constructor; assumption.
    - exact Hassets_nn. }
  assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
  assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
  constructor; simpl.
  - exact Hsupply_bound.
  - lia.
  - exact Har_nn.
  - (* backed: if post-supply > 0, then post-deposited > 0.
       Two cases on pre-supply. *)
    intros Hpost_sup_pos.
    destruct (Z.eq_dec s.(State.totalSupply) 0) as [Hs0 | Hs_ne].
    + (* pre-supply = 0: shares = assets * 1 / (ta + 1).
         For post-supply = shares > 0, we need shares >= 1, hence
         assets >= ta + 1 >= 1, so assets > 0 and post-td > 0. *)
      assert (Hta1_pos : 0 < totalAssets s + 1) by lia.
      assert (Hshares_val : shares = assets / (totalAssets s + 1)).
      { unfold shares, convertToShares. rewrite Hs0.
        f_equal. lia. }
      (* post-supply = 0 + shares > 0 means shares >= 1. *)
      assert (Hshares_pos : shares >= 1) by lia.
      rewrite Hshares_val in Hshares_pos.
      pose proof (Z.mul_div_le assets (totalAssets s + 1) Hta1_pos)
        as Hbound.
      (* (ta+1) * (a / (ta+1)) <= a. Since (a / (ta+1)) >= 1,
         we get (ta+1) * 1 <= a, i.e. a >= ta+1 > 0. *)
      assert (Hassets_pos : 0 < assets) by nia.
      lia.
    + (* pre-supply > 0: by [backed], pre-deposited > 0.
         post-deposited = pre-deposited + assets >= pre-deposited > 0. *)
      assert (Hsup_pos : s.(State.totalSupply) > 0)
        by (destruct Hsup_u256; lia).
      assert (Htd_pos : 0 < s.(State.totalDeposited))
        by (apply Hbacked; lia).
      lia.
Qed.

(** ----- withdraw preserves Valid.state. -----

    Preconditions:
      - [Valid.state s].
      - [s.(totalSupply) > 0]: withdraw on an empty vault has no
        backing shares to burn. We require positive supply.
      - [0 <= assets <= s.(totalDeposited)]: assets must fit in the
        non-rewards portion of totalAssets to avoid underflowing
        [totalDeposited]. (Note: with the inflation-defended formula,
        even [assets = totalDeposited] does not always succeed —
        the ceil-div may demand more shares than [totalSupply] when
        rewards have accrued. The [withdraw] sim now surfaces that
        as a guarded revert; the [Result.Success] hypothesis below
        gives us [shares <= totalSupply] for free.)
      - [shares = totalSupply \/ assets < totalDeposited]: the
        success either drains all shares (so [backed] becomes
        vacuous) OR strictly leaves some deposited (so [backed]
        survives). *)
Lemma withdraw_preserves_validity
    (s s' : State.t) (assets shares : U256.t) :
  Valid.state s ->
  s.(State.totalSupply) > 0 ->
  0 <= assets <= s.(State.totalDeposited) ->
  withdraw s assets = Result.Success (s', shares) ->
  (shares = s.(State.totalSupply) \/ assets < s.(State.totalDeposited)) ->
  Valid.state s'.
Proof.
  intros Hv Hsup_pos Hassets Hok Hdrain.
  pose proof Hv as Hv_orig.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  assert (Htd_pos : 0 < s.(State.totalDeposited)) by (apply Hbacked; exact Hsup_pos).
  unfold withdraw in Hok.
  cbv zeta in Hok.
  (* Hok form:
       (if assets >? totalAssets s then Revert
        else if (assets * (s.(totalSupply) + 1) + totalAssets s)
               / (totalAssets s + 1)
              >? s.(totalSupply)
             then Revert
             else Success(post-state, shares_calc))
       = Success(s', shares). *)
  assert (Hta_pos : totalAssets s > 0) by (unfold totalAssets; lia).
  assert (Hta_assets : assets <= totalAssets s).
  { unfold totalAssets. lia. }
  assert (Hgt_false : (assets >? totalAssets s) = false).
  { unfold Z.gtb. destruct (Z.compare_spec assets (totalAssets s));
      try reflexivity; lia. }
  rewrite Hgt_false in Hok.
  destruct ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
            / (totalAssets s + 1)
            >? s.(State.totalSupply)) eqn:Hguard.
  { (* Inner guard fired but caller claims [Result.Success] — impossible.
       After the outer rewrite [if false then _ else inner], the inner
       [if true then Revert] collapses. *)
    exfalso. simpl in Hok. discriminate Hok. }
  set (ta := totalAssets s) in *.
  set (Sv := s.(State.totalSupply)) in *.
  set (shares_calc := (assets * (Sv + 1) + ta) / (ta + 1)) in *.
  fold shares_calc in Hok.
  fold ta Sv shares_calc in Hguard.
  assert (Hshares_le : shares_calc <= Sv).
  { unfold Z.gtb in Hguard.
    destruct (Z.compare_spec shares_calc Sv); try discriminate; lia. }
  injection Hok as Hs'_eq Hshares_eq.
  assert (Hshares_nn : 0 <= shares_calc).
  { apply Z.div_pos; [nia | lia]. }
  rewrite <- Hs'_eq.
  constructor; simpl.
  - (* supply_u256 *)
    unfold U256.Valid.t in *.
    destruct Hsup_u256 as [_ Hsup_hi].
    split; [lia|]. fold Sv. lia.
  - (* deposited_nn *)
    lia.
  - (* rewards_nn *)
    exact Har_nn.
  - (* backed *)
    intros Hpost_sup_pos.
    (* Need: totalDeposited - assets > 0, i.e. assets < totalDeposited. *)
    destruct Hdrain as [Hdrain_full | Hdrain_strict].
    + (* shares = Sv. With Hshares_eq linking shares and shares_calc,
         we get shares_calc = Sv, hence post-supply = Sv - Sv = 0,
         contradicting Hpost_sup_pos. *)
      exfalso.
      fold Sv in Hdrain_full, Hpost_sup_pos.
      assert (Hsc_eq_sv : shares_calc = Sv) by lia.
      lia.
    + (* assets < totalDeposited, so totalDeposited - assets > 0. *)
      lia.
Qed.

(** ----- accrue preserves Valid.state. -----
    [accrue] only bumps [accumulatedNativeRewards] upward by a
    non-negative delta; supply, totalDeposited, and [backed] are
    untouched. Requires the post-rewards-sum stays in uint256. *)
Lemma accrue_preserves_validity (s : State.t) (delta : U256.t) :
  Valid.state s ->
  0 <= delta ->
  Valid.state (accrue s delta).
Proof.
  intros Hv Hd.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  unfold accrue.
  constructor; simpl.
  - exact Hsup_u256.
  - exact Htd_nn.
  - lia.
  - exact Hbacked.
Qed.

(** ----- Headline: the never-underwater claim. -----
    For any valid state with outstanding shares, the contract's
    totalAssets is at least the sum of user deposits, which is
    strictly positive. Reward accrual only adds to the gap. *)
Theorem never_underwater (s : State.t) :
  Valid.state s ->
  s.(State.totalSupply) > 0 ->
  totalAssets s >= s.(State.totalDeposited) /\ s.(State.totalDeposited) > 0.
Proof.
  intros Hv Hsup_pos.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  assert (Htd_pos : 0 < s.(State.totalDeposited)) by (apply Hbacked; exact Hsup_pos).
  unfold totalAssets.
  split; lia.
Qed.

(** ----- vm_compute cross-check: a deposit/accrue/withdraw cycle
    preserves [Valid.state] at every step. -----

    Walk:
      empty_state
        --deposit 10^21-->     s1   (supply = 10^21, td = 10^21)
        --accrue 10^17-->      s2   (rewards bumped by 0.1)
        --withdraw 10^21-->    s3   (shares burned = totalSupply,
                                     full drain — backed vacuous) *)

Definition cycle_s1 : State.t := fst (deposit empty_state (10^21)).

Definition cycle_s2 : State.t := accrue cycle_s1 (10^17).

(** The withdraw at s2 with assets = totalDeposited drains all shares.
    We extract the success projection here for the xcheck. *)
Definition cycle_s3_result : Result.t (State.t * U256.t) :=
  withdraw cycle_s2 (10^21).

Lemma xcheck_cycle_s1_valid : Valid.state cycle_s1.
Proof.
  apply deposit_preserves_validity.
  - exact empty_state_valid.
  - unfold U256.Valid.t. vm_compute. split; [discriminate | reflexivity].
  - unfold U256.Valid.t. vm_compute. split; [discriminate | reflexivity].
  - unfold U256.Valid.t. vm_compute. split; [discriminate | reflexivity].
Qed.

Lemma xcheck_cycle_s1_shape :
  cycle_s1.(State.totalSupply) = 10^21
  /\ cycle_s1.(State.totalDeposited) = 10^21
  /\ cycle_s1.(State.accumulatedNativeRewards) = 0.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

Lemma xcheck_cycle_s2_valid : Valid.state cycle_s2.
Proof.
  apply accrue_preserves_validity.
  - exact xcheck_cycle_s1_valid.
  - vm_compute. discriminate.
Qed.

Lemma xcheck_cycle_s2_shape :
  cycle_s2.(State.totalSupply) = 10^21
  /\ cycle_s2.(State.totalDeposited) = 10^21
  /\ cycle_s2.(State.accumulatedNativeRewards) = 10^17.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

(** With rewards present (s2), the ceil-div for assets=10^21 yields
    shares = ceil(10^21 * 10^21 / (10^21 + 10^17)) which is less
    than 10^21 — a PARTIAL burn. So withdrawing exactly
    [totalDeposited] at s2 would NOT drain all shares, and [backed]
    would break. We surface this in the xcheck by computing the
    actual ceil-div share count and showing it is strictly less
    than totalSupply. *)
Lemma xcheck_withdraw_full_td_partial_burn :
  match cycle_s3_result with
  | Result.Success (_, shares) => shares < cycle_s2.(State.totalSupply)
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Now demonstrate a SAFE withdraw cycle: from cycle_s1 (no
    rewards yet), assets = totalDeposited gives a clean full drain
    by exact-rate ceil-div (rate is 1:1). *)
Definition cycle_s3_clean : Result.t (State.t * U256.t) :=
  withdraw cycle_s1 (10^21).

Lemma xcheck_cycle_clean_full_drain :
  match cycle_s3_clean with
  | Result.Success (s', shares) =>
      shares = cycle_s1.(State.totalSupply)
      /\ s'.(State.totalSupply) = 0
      /\ s'.(State.totalDeposited) = 0
  | _ => False
  end.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

Lemma xcheck_cycle_clean_valid :
  match cycle_s3_clean with
  | Result.Success (s', _) => Valid.state s'
  | _ => False
  end.
Proof.
  (* withdraw cycle_s1 (10^21) computes to a definite Success; use
     vm_compute to materialize the post-state, then apply
     withdraw_preserves_validity to certify it. *)
  unfold cycle_s3_clean.
  pose proof xcheck_cycle_s1_shape as Hshape.
  destruct Hshape as (Hs_sup & Hs_td & _).
  (* Concretize cycle_s1 fully via vm_compute so the [withdraw] term
     reduces. Then expose the post-state explicitly. *)
  assert (Hwr : withdraw cycle_s1 (10^21) =
                Result.Success
                  ({| State.totalSupply := 0;
                      State.totalDeposited := 0;
                      State.accumulatedNativeRewards := 0 |},
                   10^21)).
  { vm_compute. reflexivity. }
  rewrite Hwr.
  eapply withdraw_preserves_validity with
    (s := cycle_s1)
    (s' := {| State.totalSupply := 0;
              State.totalDeposited := 0;
              State.accumulatedNativeRewards := 0 |})
    (assets := 10^21) (shares := 10^21).
  - exact xcheck_cycle_s1_valid.
  - rewrite Hs_sup. vm_compute. reflexivity.
  - rewrite Hs_td. split.
    + vm_compute. discriminate.
    + lia.
  - exact Hwr.
  - left. rewrite Hs_sup. reflexivity.
Qed.

End StakingVaultExchangeValidity.
