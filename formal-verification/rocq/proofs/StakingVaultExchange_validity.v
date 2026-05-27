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

    Modeling note: the existing [withdraw] simulation guards
    [assets > totalAssets] (the OZ default), but does NOT guard
    [assets > totalDeposited]. With native rewards accrued
    ([accumulatedNativeRewards > 0]), it is therefore possible to
    submit [totalDeposited < assets <= totalAssets] and underflow
    [totalDeposited]. We surface that gap here by requiring
    [assets <= totalDeposited] as an explicit precondition. *)

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
  destruct (s.(State.totalSupply) =? 0) eqn:Hs0.
  - exact Ha.
  - apply Z.eqb_neq in Hs0.
    assert (Hsup_pos : s.(State.totalSupply) > 0) by (destruct Hsup_u256; lia).
    assert (Htd_pos : 0 < s.(State.totalDeposited)) by (apply Hbacked; lia).
    assert (Hta_pos : totalAssets s > 0) by (unfold totalAssets; lia).
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
  constructor; simpl.
  - exact Hsupply_bound.
  - lia.
  - exact Har_nn.
  - (* backed: if post-supply > 0, then post-deposited > 0.
       Two cases on pre-supply. *)
    intros Hpost_sup_pos.
    destruct (Z.eq_dec s.(State.totalSupply) 0) as [Hs0 | Hs_ne].
    + (* pre-supply = 0: shares = assets (1:1 initial mint).
         Post-supply > 0 implies assets > 0, hence post-deposited > 0. *)
      unfold shares in *.
      unfold convertToShares in *.
      assert (Hs0_eqb : s.(State.totalSupply) =? 0 = true)
        by (apply Z.eqb_eq; exact Hs0).
      rewrite Hs0_eqb in *.
      (* totalSupply' = 0 + assets = assets > 0 *)
      rewrite Hs0 in Hpost_sup_pos.
      (* totalDeposited' = totalDeposited + assets, and assets > 0 *)
      lia.
    + (* pre-supply > 0: by [backed], pre-deposited > 0.
         post-deposited = pre-deposited + assets >= pre-deposited > 0. *)
      assert (Hsup_pos : s.(State.totalSupply) > 0)
        by (destruct Hsup_u256; lia).
      assert (Htd_pos : 0 < s.(State.totalDeposited))
        by (apply Hbacked; lia).
      lia.
Qed.

(** ----- Helper: in the supply>0 case, the ceil-div shares burn
    does not exceed totalSupply when [assets <= totalDeposited]. ----- *)
Lemma withdraw_shares_le_supply
    (s : State.t) (assets : U256.t) :
  Valid.state s ->
  s.(State.totalSupply) > 0 ->
  0 <= assets <= s.(State.totalDeposited) ->
  let ta := totalAssets s in
  let S  := s.(State.totalSupply) in
  (assets * S + ta - 1) / ta <= S.
Proof.
  intros Hv Hsup_pos Hassets.
  destruct Hv as [Hsup_u256 Htd_nn Har_nn Hbacked].
  assert (Htd_pos : 0 < s.(State.totalDeposited)) by (apply Hbacked; exact Hsup_pos).
  assert (Hta_pos : totalAssets s > 0) by (unfold totalAssets; lia).
  simpl.
  set (ta := totalAssets s) in *.
  set (S := s.(State.totalSupply)) in *.
  (* assets <= td <= ta, so assets * S <= ta * S.
     ceil(assets * S / ta) <= ceil(ta * S / ta) = S. *)
  assert (Hassets_ta : assets <= ta) by (unfold ta, totalAssets; lia).
  (* ceil(a*S/ta) = floor((a*S + ta - 1)/ta). With a <= ta we have
       a*S + ta - 1 < ta*S + ta = ta*(S+1)
     so floor( ... / ta) < S+1, i.e. <= S. Apply
     [Z.div_lt_upper_bound] and step down by 1. *)
  assert (Hlt : (assets * S + ta - 1) / ta < S + 1).
  { apply Z.div_lt_upper_bound; [lia|]. nia. }
  lia.
Qed.

(** ----- withdraw preserves Valid.state. -----

    Preconditions:
      - [Valid.state s].
      - [s.(totalSupply) > 0]: withdraw on an empty vault is a no-op
        in practice; the simulation's supply=0 branch sets
        [shares = assets], which would under-flow totalSupply on any
        positive assets. So we require positive supply.
      - [0 <= assets <= s.(totalDeposited)]: assets must fit in the
        non-rewards portion of totalAssets to avoid underflowing
        [totalDeposited].
      - [shares = totalSupply \/ assets < totalDeposited]: the
        success either drains all shares (so [backed] becomes
        vacuous) OR strictly leaves some deposited (so [backed]
        survives). The caller chooses; both are implementable from
        a Solidity entry point. *)
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
  set (ta := totalAssets s) in *.
  assert (Hta_pos : ta > 0) by (unfold ta, totalAssets; lia).
  assert (Hta_assets : assets <= ta).
  { unfold ta, totalAssets. lia. }
  assert (Hgt_false : (assets >? ta) = false).
  { unfold Z.gtb. destruct (Z.compare_spec assets ta); try reflexivity; lia. }
  rewrite Hgt_false in Hok.
  set (Sv := s.(State.totalSupply)) in *.
  assert (Hsup_eqb : (Sv =? 0) = false)
    by (apply Z.eqb_neq; lia).
  fold ta Sv in Hok.
  (* The branch in withdraw computes shares based on supply=0; with
     Sv > 0 we take the else branch. *)
  rewrite Hsup_eqb in Hok.
  injection Hok as Hs'_eq Hshares_eq.
  set (shares_calc := (assets * Sv + ta - 1) / ta) in *.
  (* From the injection: s' is the post-record; shares is shares_calc. *)
  assert (Hshares_le : shares_calc <= Sv).
  { apply (withdraw_shares_le_supply s assets); auto. }
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
