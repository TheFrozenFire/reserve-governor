(** StakingVault exchange-rate proofs.

    These are about the OZ v5.4 inflation-defended ERC4626 form. The
    effective exchange rate that users see is

      rate = (totalAssets + 1) / (totalSupply + 10^offset)

    with [10^offset = 1] for the StakingVault (no decimalsOffset
    override). The "+1" in both denominators is the virtual-share /
    virtual-asset defense against first-depositor inflation attacks.

    Three headline theorems:

      INV-4  Round-trip rounding: convertToAssets(convertToShares(a))
             <= a. With the inflation-defended form both denominators
             are positive without preconditions, so no [supply > 0]
             hypothesis is required.

      INV-5  Share-value monotonicity: the inflation-defended rate
             (ta+1)/(S+1) is non-decreasing under [accrue delta] for
             delta >= 0. Stated as cross-multiplication to dodge
             fraction-level reasoning:
                 (pre.totalAssets + 1) * (post.supply + 1)
              <= (post.totalAssets + 1) * (pre.supply + 1).

      Deposit  After deposit(assets), totalDeposited' =
               totalDeposited + assets and totalSupply' =
               totalSupply + shares with shares = convertToShares.

      Accrue   accrue preserves totalSupply and totalDeposited, and
               only ever increases accumulatedNativeRewards.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import Coq.Bool.Bool.

Module StakingVaultExchangeProofs.

Import StakingVaultExchange.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** ----- Deposit storage delta is exact. ----- *)
Lemma deposit_storage_delta (s : State.t) (assets : U256.t) :
  let r := deposit s assets in
  (fst r).(State.totalDeposited) = s.(State.totalDeposited) + assets
  /\ (fst r).(State.totalSupply) = s.(State.totalSupply) + snd r
  /\ snd r = convertToShares s assets.
Proof.
  unfold deposit. simpl. split; [reflexivity|]. split; reflexivity.
Qed.

(** ----- accrue preserves totalSupply and totalDeposited. ----- *)
Lemma accrue_preserves_share_book (s : State.t) (delta : U256.t) :
  (accrue s delta).(State.totalSupply) = s.(State.totalSupply)
  /\ (accrue s delta).(State.totalDeposited) = s.(State.totalDeposited).
Proof. split; reflexivity. Qed.

Lemma accrue_increases_rewards (s : State.t) (delta : U256.t) :
  0 <= delta ->
  (accrue s delta).(State.accumulatedNativeRewards)
    >= s.(State.accumulatedNativeRewards).
Proof. simpl. intros Hd. lia. Qed.

(** ----- INV-5: share-value monotonicity under accrue. -----
    Stated as: pre rate <= post rate, via cross-multiply on the
    inflation-defended form. With [accrue] leaving totalSupply
    unchanged, the cross-multiplied claim collapses to
       (ta_pre + 1) * (S + 1) <= (ta_post + 1) * (S + 1)
    which is immediate from delta >= 0 and (S + 1) > 0. No
    precondition on totalSupply is required — virtual shares keep
    the denominator positive even at supply = 0. *)
Lemma accrue_share_rate_monotone (s : State.t) (delta : U256.t) :
  0 <= delta ->
  0 <= s.(State.totalSupply) ->
  (totalAssets s + 1)
    * (s.(State.totalSupply) + 1) <=
  (totalAssets (accrue s delta) + 1)
    * (s.(State.totalSupply) + 1).
Proof.
  intros Hd Hsupply.
  unfold totalAssets. simpl.
  (* (td + ar + 1) * (S + 1) <= (td + ar + delta + 1) * (S + 1)
     because delta >= 0 and (S + 1) > 0. *)
  nia.
Qed.

(** ----- INV-4: round-trip rounding bound.
    convertToAssets (convertToShares s a) <= a.

    With the inflation-defended form both denominators (S+1) and
    (ta+1) are >= 1 unconditionally, so no preconditions on totalSupply
    or totalAssets are required. Both floors only round down, so the
    round-trip is <= a. *)
Lemma round_trip_floor_bound
    (s : State.t) (a : U256.t) :
  0 <= s.(State.totalSupply) ->
  0 <= totalAssets s ->
  0 <= a ->
  convertToAssets s (convertToShares s a) <= a.
Proof.
  intros Hsup Hta Ha.
  unfold convertToShares, convertToAssets.
  set (S1 := s.(State.totalSupply) + 1).
  set (A1 := totalAssets s + 1).
  (* shares := (a * S1) / A1; assets_back := (shares * A1) / S1. *)
  set (shares := (a * S1) / A1).
  assert (HA1_pos : 0 < A1) by (unfold A1; lia).
  assert (HS1_pos : 0 < S1) by (unfold S1; lia).
  pose proof (Z.mul_div_le (a * S1) A1 HA1_pos) as Hshares_mul.
  assert (Hshares_A_le : shares * A1 <= a * S1).
  { unfold shares. lia. }
  apply Z.div_le_upper_bound; [exact HS1_pos|].
  lia.
Qed.

(** ----- convertToShares(0) = 0 and convertToAssets(0) = 0. -----
    With the inflation-defended form denominators are always positive,
    so no preconditions are needed beyond totalAssets being non-negative
    (to keep A+1 > 0; trivially follows from validity). *)
Lemma convertToShares_zero (s : State.t) :
  0 <= totalAssets s ->
  convertToShares s 0 = 0.
Proof.
  intros Hta.
  unfold convertToShares.
  rewrite Z.mul_0_l. apply Z.div_0_l. lia.
Qed.

Lemma convertToAssets_zero (s : State.t) :
  0 <= s.(State.totalSupply) ->
  convertToAssets s 0 = 0.
Proof.
  intros Hsup.
  unfold convertToAssets.
  rewrite Z.mul_0_l. apply Z.div_0_l. lia.
Qed.

End StakingVaultExchangeProofs.
