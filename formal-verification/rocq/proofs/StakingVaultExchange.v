(** StakingVault exchange-rate proofs.

    Three headline theorems:

      INV-4  Round-trip rounding: convertToAssets(convertToShares(a))
             <= a, when supply > 0.

      INV-5  Share-value monotonicity: rate = totalAssets / supply is
             non-decreasing under [accrue delta] for delta >= 0.
             Stated as cross-multiplication to dodge fraction-level
             reasoning: post.totalAssets * pre.supply >=
             pre.totalAssets * post.supply.

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
    Stated as: pre rate <= post rate, via cross-multiply. *)
Lemma accrue_share_rate_monotone (s : State.t) (delta : U256.t) :
  0 <= delta ->
  s.(State.totalSupply) > 0 ->
  totalAssets s * s.(State.totalSupply) <=
    totalAssets (accrue s delta) * s.(State.totalSupply).
Proof.
  intros Hd Hsupply.
  unfold totalAssets. simpl.
  (* (td + ar) * S <= (td + ar + delta) * S because delta >= 0 and S > 0. *)
  nia.
Qed.

(** ----- INV-4: round-trip rounding bound.
    convertToAssets (convertToShares s a) <= a, with supply > 0 and
    totalAssets > 0.

    Strategy: convertToShares floors, convertToAssets floors. Both
    floors only ever round down, so the round-trip is <= a. *)
Lemma round_trip_floor_bound
    (s : State.t) (a : U256.t) :
  s.(State.totalSupply) > 0 ->
  totalAssets s > 0 ->
  0 <= a ->
  convertToAssets s (convertToShares s a) <= a.
Proof.
  intros Hsup Hta Ha.
  unfold convertToShares, convertToAssets.
  destruct (s.(State.totalSupply) =? 0) eqn:Hs0.
  - apply Z.eqb_eq in Hs0. lia.
  - apply Z.eqb_neq in Hs0.
    set (S := s.(State.totalSupply)).
    set (A := totalAssets s).
    (* shares := (a * S) / A; assets_back := (shares * A) / S. *)
    set (shares := (a * S) / A).
    (* Show (shares * A) / S <= a. *)
    assert (HA_pos : 0 < A) by (unfold A; lia).
    pose proof (Z.mul_div_le (a * S) A HA_pos) as Hshares_mul.
    assert (Hshares_A_le : shares * A <= a * S).
    { unfold shares. lia. }
    assert (HS_pos : 0 < S) by (unfold S; lia).
    apply Z.div_le_upper_bound; [exact HS_pos|].
    lia.
Qed.

(** ----- convertToShares(0) = 0 and convertToAssets(0) = 0
    (modulo the supply=0 branch which is 1:1). ----- *)
Lemma convertToShares_zero (s : State.t) :
  s.(State.totalSupply) > 0 ->
  totalAssets s > 0 ->
  convertToShares s 0 = 0.
Proof.
  intros Hsup Hta.
  unfold convertToShares.
  assert (Hne : (s.(State.totalSupply) =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hne.
  rewrite Z.mul_0_l. apply Z.div_0_l. lia.
Qed.

Lemma convertToAssets_zero (s : State.t) :
  s.(State.totalSupply) > 0 ->
  convertToAssets s 0 = 0.
Proof.
  intros Hsup.
  unfold convertToAssets.
  assert (Hne : (s.(State.totalSupply) =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hne.
  rewrite Z.mul_0_l. apply Z.div_0_l. lia.
Qed.

End StakingVaultExchangeProofs.
