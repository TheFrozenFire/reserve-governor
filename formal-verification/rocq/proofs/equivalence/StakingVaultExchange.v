(** Task #254 — StakingVault exchange-rate equivalence.

    Mechanizes the four ERC4626-derived public entry-points on
    [contracts/staking/StakingVault.sol] that exchange shares for the
    underlying asset:

      - [deposit(assets, receiver)]   — mint shares for assets in.
      - [mint(shares, receiver)]      — mint exactly [shares], pay
                                        [previewMint(shares)] assets.
      - [withdraw(assets, receiver, owner)] — burn shares, pay assets out.
      - [redeem(shares, receiver, owner)]   — burn exactly [shares],
                                              pay [previewRedeem(shares)]
                                              assets.

    Source body shapes:
      fun_deposit_4312    — generated/StakingVault_shallow.v:10625
      fun_mint_4356       — generated/StakingVault_shallow.v:13495
      fun_withdraw_4403   — generated/StakingVault_shallow.v:16547
      fun_redeem_4450    — generated/StakingVault_shallow.v:14749

    Each function dispatches into one of two internal ERC4626 helpers
    after a max-cap pre-check and a preview-conversion:

      fun__deposit_630    — internal _deposit(caller, receiver, assets,
                            shares): mutates totalDeposited /
                            nativeBalanceLastKnown via the overridden
                            [_deposit] hook (StakingVault.sol:252), then
                            calls super._deposit which performs the
                            asset.transferFrom + _mint.
      fun__withdraw_736   — internal _withdraw(caller, receiver, owner,
                            assets, shares): mutates totalDeposited /
                            nativeBalanceLastKnown via the overridden
                            [_withdraw] hook (StakingVault.sol:266),
                            then dispatches on unstakingDelay:
                              0  -> super._withdraw: _spendAllowance +
                                    _burn + asset.transfer.
                              !=0 -> _spendAllowance + _burn +
                                    forceApprove + unstakingManager
                                    .createLock + nativeBalanceLastKnown
                                    refresh.

    The internal _deposit / _withdraw paths are wrapped in the
    [accrueRewards(caller, receiver)] modifier (StakingVault.sol:396).
    The reward accrual mutates per-token tracker state but DOES NOT
    affect the share / asset exchange-rate decision — the caller's
    [previewDeposit] / [previewWithdraw] is computed BEFORE the
    accrual (cf. sol:252-261 ordering). For this file we abstract the
    reward accrual as an opaque storage transformation that commutes
    with the exchange-rate updates: the four equivalence theorems
    state the exchange-rate slot transitions; the reward-tracker
    transitions are owned by parallel Wave 2 agent #255 (rewards).

    Methodology (R051 / R070 composite-axiom + R071 milestone Qed):

      1. Sim-side helper lemmas about [simulations/StakingVaultExchange.v]
         that hold pre-existing sim properties forward to the equivalence
         layer (round-trip rounding, validity preservation, share-rate
         monotonicity).
      2. Storage-layout documentation + projection lens for the
         StakingVault's full SimulatedStorage.t (ERC20 + ERC4626 +
         ERC20Votes + ReentrancyGuard + AccessControl + StakingVault-
         specific slots).
      3. Skolemized post-storage [Parameter]s for each of the four
         entry points (R070 shape).
      4. Per-target observational bridge [Axiom]s (R051 shape).
      5. Composite walker [Axiom]s capturing the Yul-body assembly as
         a single Hoare triple per function.
      6. Milestone [Theorem] Qed for each entry point composing
         (3)-(5) per the R071 3-phase recipe.

    Wave-2 integration markers:

      ERC4626 (Wave 1 agent #241):  the abstract base's preview /
        convert / max helpers are documented but not yet bound to a
        slot-agnostic equivalence layer. Markers below indicate where
        Wave 1's `proofs/equivalence/ERC4626.v` will plug in when it
        lands. The composite walker axioms accept the preview/convert
        results as opaque parameters until that integration is wired.

      ERC20Votes (Wave 1 agent #241): the _update override
        (StakingVault.sol:499) chains into Votes.[transferVotingUnits].
        The Votes layer is captured in [proofs/equivalence/Votes.v]
        (Task #240). Section parameter [project_votes] documents the
        slot anchor.

      ReentrancyGuard (Task #238): the [_deposit] / [_withdraw] hooks
        run UNDER the ERC4626 [deposit] / [withdraw] entry-point's
        non-reentrant modifier. R045 [with_nonReentrant] symbolic
        expansion in [proofs/equivalence/ReentrancyGuard.v] supplies
        the pre/post lock invariant.

      AccessControl (Task #237): no exchange-rate entry-point is
        role-gated; the [_deposit] / [_withdraw] paths are public.
        AccessControl appears in this file only via the storage
        layout (its slots are present but invariant across the four
        exchange-rate operations).

      StaticCallBridge (R063): each successful exchange-rate
        operation contains exactly one external token call:

          deposit / mint:   asset.transferFrom(caller, vault, assets)
          withdraw / redeem (unstakingDelay = 0):
                            asset.transfer(receiver, assets)
          withdraw / redeem (unstakingDelay > 0):
                            asset.forceApprove(unstakingManager,
                                               assets) +
                            unstakingManager.createLock(receiver,
                                                       assets, unlock)

        Each external call follows the R063 staticcall composite
        pattern (mstore selector + abi-encode args + staticcall +
        returndatasize + returndatacopy + mload).

    Trust budget:
      - 4 composite walker [Axiom]s (one per entry point).
      - 4 Skolemized post-storage [Parameter]s.
      - 4 per-target slot-indexed observational bridge [Axiom]s
        (per the 2026-05-31 adversarial-review skolemization-
        soundness audit (CCV-1 / CCV-2 / CRIT-V), promoted from
        reflexive [storage_equiv (X) (X)] tautologies to
        content-bearing [eq_at_roles (proj_post_<fn> ...)
        storage_base] claims; an empty-storage adversarial
        instantiation of [proj_post_<fn>] no longer satisfies
        them).
      - 1 sim-environment [Parameter] (now_timestamp).
      - 4 callee-spec [Axiom]s (documentation-only, [True] conclusion).

    Total: 13 axioms / parameters per file. Matches the standard
    R070/R071 envelope (cf. TimelockControllerOptimistic.v: 5 + 5 + 5
    + 1 = 16; ProposalLib.v: 2 + 2 + 2 = 6).

    Note: this file is part of Wave 2 of the equivalence push. It
    scaffolds against the existing [simulations/StakingVaultExchange.v]
    + [proofs/StakingVaultExchange.v] + [proofs/StakingVaultExchange_
    validity.v] without modifying them.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import ReserveGovernor.proofs.equivalence.ReentrancyGuard.
Require Import ReserveGovernor.proofs.equivalence.Votes.

(** Task #299 (R093 consumer): pull in the StakingVault shallow form.
    Binding [fun_X_op] to the shallow [fun_X] definitions (via
    Notation aliases below) is the prerequisite for the R088-style
    walker-Lemma discharge of the four composite walker axioms. *)
Require Import ReserveGovernor.generated.StakingVault_shallow.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module StakingVaultExchangeEquivalence.

  Import StakingVaultExchange.

  Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

  (** ====================================================================
      Section 1 — Sim-side helper lemmas (Qed)
      ====================================================================

      These bridge the existing sim's [simulations/StakingVaultExchange.v]
      properties into the shape the equivalence-layer milestone theorems
      consume. Each lemma is Qed against the pure-Coq sim; no axioms.

      Convention: lemmas with the [run_] prefix later in the file are
      Hoare-triple lemmas about the Yul shallow form. Lemmas here are
      sim-side facts only.
      ==================================================================== *)

  (** ---- 1.1 Deposit storage-delta lemmas (lifted from
      proofs/StakingVaultExchange.v) ---- *)

  Lemma deposit_supply_grows (s : State.t) (assets : U256.t) :
    (fst (deposit s assets)).(State.totalSupply)
    = s.(State.totalSupply) + convertToShares s assets.
  Proof. unfold deposit. reflexivity. Qed.

  Lemma deposit_deposited_grows (s : State.t) (assets : U256.t) :
    (fst (deposit s assets)).(State.totalDeposited)
    = s.(State.totalDeposited) + assets.
  Proof. unfold deposit. reflexivity. Qed.

  Lemma deposit_rewards_preserved (s : State.t) (assets : U256.t) :
    accumulatedNativeRewards (fst (deposit s assets))
    = accumulatedNativeRewards s.
  Proof.
    (* Phase B: [accumulatedNativeRewards] is now derived from
       [nativeBalanceLastKnown - totalDeposited].  Deposit increments
       both fields by [assets], so the difference is preserved. *)
    unfold deposit, accumulatedNativeRewards. simpl.
    destruct (s.(State.nativeBalanceLastKnown) + assets >=?
              s.(State.totalDeposited) + assets) eqn:Hpost;
      destruct (s.(State.nativeBalanceLastKnown) >=?
                s.(State.totalDeposited)) eqn:Hpre.
    - apply Z.geb_le in Hpost. apply Z.geb_le in Hpre. lia.
    - apply Z.geb_le in Hpost.
      rewrite Z.geb_leb in Hpre. apply Z.leb_gt in Hpre. lia.
    - apply Z.geb_le in Hpre.
      rewrite Z.geb_leb in Hpost. apply Z.leb_gt in Hpost. lia.
    - reflexivity.
  Qed.

  Lemma deposit_returns_shares (s : State.t) (assets : U256.t) :
    snd (deposit s assets) = convertToShares s assets.
  Proof. unfold deposit. reflexivity. Qed.

  (** ---- 1.2 Withdraw storage-delta lemmas (success branch) ---- *)

  Lemma withdraw_success_supply_shrinks
      (s s' : State.t) (assets shares : U256.t) :
    withdraw s assets = Result.Success (s', shares) ->
    s'.(State.totalSupply) = s.(State.totalSupply) - shares.
  Proof.
    unfold withdraw. intros H.
    destruct (assets >? totalAssets s) eqn:Hgt; [discriminate|].
    destruct ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
              / (totalAssets s + 1)
              >? s.(State.totalSupply)) eqn:Hguard; [discriminate|].
    injection H as <- <-. reflexivity.
  Qed.

  Lemma withdraw_success_deposited_shrinks
      (s s' : State.t) (assets shares : U256.t) :
    withdraw s assets = Result.Success (s', shares) ->
    s'.(State.totalDeposited) = s.(State.totalDeposited) - assets.
  Proof.
    unfold withdraw. intros H.
    destruct (assets >? totalAssets s) eqn:Hgt; [discriminate|].
    destruct ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
              / (totalAssets s + 1)
              >? s.(State.totalSupply)) eqn:Hguard; [discriminate|].
    injection H as <- <-. reflexivity.
  Qed.

  Lemma withdraw_success_rewards_preserved
      (s s' : State.t) (assets shares : U256.t) :
    withdraw s assets = Result.Success (s', shares) ->
    accumulatedNativeRewards s' = accumulatedNativeRewards s.
  Proof.
    unfold withdraw. intros H.
    destruct (assets >? totalAssets s) eqn:Hgt; [discriminate|].
    destruct ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
              / (totalAssets s + 1)
              >? s.(State.totalSupply)) eqn:Hguard; [discriminate|].
    injection H as <- <-.
    (* Same shape as deposit: both fields shrink by [assets]; the
       getter's conditional flips together pre/post. *)
    unfold accumulatedNativeRewards. simpl.
    destruct (s.(State.nativeBalanceLastKnown) - assets >=?
              s.(State.totalDeposited) - assets) eqn:Hpost;
      destruct (s.(State.nativeBalanceLastKnown) >=?
                s.(State.totalDeposited)) eqn:Hpre.
    - apply Z.geb_le in Hpost. apply Z.geb_le in Hpre. lia.
    - apply Z.geb_le in Hpost.
      rewrite Z.geb_leb in Hpre. apply Z.leb_gt in Hpre. lia.
    - apply Z.geb_le in Hpre.
      rewrite Z.geb_leb in Hpost. apply Z.leb_gt in Hpost. lia.
    - reflexivity.
  Qed.

  (** ---- 1.3 Pre-condition characterisation: withdraw success iff
            both [assets <= totalAssets] AND the inflation-defended
            ceil-div share count fits in totalSupply.

      Under OZ v5.4, withdraw can revert even with [assets <= totalAssets]
      when the inflation-defended ceiling shares exceed totalSupply.
      That happens specifically when [assets ≈ totalAssets] and rewards
      have accrued: the +1 on (S+1) and the +0 on the share-side
      together push the ceil-div above S. T1.2 surfaced this as an
      explicit share-bound guard. The pre-T1.2 statement was

        success  iff  assets <= totalAssets

      which is now FALSE under the corrected sim — kept here in a
      strict-only direction as [withdraw_success_implies_within_assets]
      so downstream proofs that only need the necessary condition
      still go through. The full iff is restated against both guards. *)

  Lemma withdraw_success_implies_within_assets (s : State.t) (assets : U256.t) :
    (exists s' shares, withdraw s assets = Result.Success (s', shares)) ->
    assets <= totalAssets s.
  Proof.
    intros (s' & shares & H).
    unfold withdraw in H.
    destruct (assets >? totalAssets s) eqn:Hgt; [discriminate|].
    unfold Z.gtb in Hgt.
    destruct (Z.compare_spec assets (totalAssets s)); try discriminate; lia.
  Qed.

  Lemma withdraw_success_iff_within_assets (s : State.t) (assets : U256.t) :
    (exists s' shares, withdraw s assets = Result.Success (s', shares))
    <-> (assets <= totalAssets s
         /\ (assets * (s.(State.totalSupply) + 1) + totalAssets s)
              / (totalAssets s + 1)
            <= s.(State.totalSupply)).
  Proof.
    unfold withdraw. split.
    - intros (s' & shares & H).
      destruct (assets >? totalAssets s) eqn:Hgt; [discriminate|].
      destruct ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
                / (totalAssets s + 1)
                >? s.(State.totalSupply)) eqn:Hguard; [discriminate|].
      split.
      + unfold Z.gtb in Hgt.
        destruct (Z.compare_spec assets (totalAssets s)); try discriminate; lia.
      + unfold Z.gtb in Hguard.
        destruct (Z.compare_spec
                    ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
                       / (totalAssets s + 1))
                    s.(State.totalSupply));
          try discriminate; lia.
    - intros [Hle Hguard_le].
      assert (Hgtb : (assets >? totalAssets s) = false).
      { unfold Z.gtb. destruct (Z.compare_spec assets (totalAssets s));
          try reflexivity; lia. }
      rewrite Hgtb.
      assert (Hguard_false :
                ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
                   / (totalAssets s + 1)
                 >? s.(State.totalSupply)) = false).
      { unfold Z.gtb.
        destruct (Z.compare_spec
                    ((assets * (s.(State.totalSupply) + 1) + totalAssets s)
                       / (totalAssets s + 1))
                    s.(State.totalSupply));
          try reflexivity; lia. }
      rewrite Hguard_false.
      do 2 eexists; reflexivity.
  Qed.

  (** ---- 1.4 Round-trip rounding bound (alias of
      [proofs/StakingVaultExchange.v::round_trip_floor_bound]) ----

      Stated here in the equivalence-namespace so downstream milestone
      proofs cite it by local name. *)
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
    set (shares := (a * S1) / A1).
    assert (HA1_pos : 0 < A1) by (unfold A1; lia).
    assert (HS1_pos : 0 < S1) by (unfold S1; lia).
    pose proof (Z.mul_div_le (a * S1) A1 HA1_pos) as Hshares_mul.
    assert (Hshares_A_le : shares * A1 <= a * S1).
    { unfold shares. lia. }
    apply Z.div_le_upper_bound; [exact HS1_pos|].
    lia.
  Qed.

  (** ---- 1.5 Share-value monotonicity under reward accrual ----

      Cross-multiplication form. With supply > 0, post.totalAssets *
      pre.supply >= pre.totalAssets * post.supply. Lifted from
      [proofs/StakingVaultExchange.v::accrue_share_rate_monotone]. *)
  Lemma accrue_share_rate_monotone (s : State.t) (delta now_ : U256.t) :
    0 <= delta ->
    0 <= s.(State.totalSupply) ->
    (totalAssets s + 1)
      * (s.(State.totalSupply) + 1) <=
    (totalAssets (accrue s delta now_) + 1)
      * (s.(State.totalSupply) + 1).
  Proof.
    intros Hd Hsupply.
    unfold totalAssets, accumulatedNativeRewards, accrue. simpl.
    destruct (s.(State.nativeBalanceLastKnown) + delta >=?
              s.(State.totalDeposited)) eqn:Hpost;
      destruct (s.(State.nativeBalanceLastKnown) >=?
                s.(State.totalDeposited)) eqn:Hpre.
    - apply Z.geb_le in Hpost. apply Z.geb_le in Hpre. nia.
    - apply Z.geb_le in Hpost.
      rewrite Z.geb_leb in Hpre. apply Z.leb_gt in Hpre. nia.
    - apply Z.geb_le in Hpre.
      rewrite Z.geb_leb in Hpost. apply Z.leb_gt in Hpost. lia.
    - rewrite Z.geb_leb in Hpost. apply Z.leb_gt in Hpost. nia.
  Qed.

  (** ---- 1.6 convertToShares non-negativity (lift from
      proofs/StakingVaultExchange_validity.v::convertToShares_nonneg) ---- *)
  Lemma convertToShares_nonneg (s : State.t) (assets : U256.t) :
    Valid.state s ->
    0 <= assets ->
    0 <= convertToShares s assets.
  Proof.
    intros Hv Ha.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [Hsup_u256 Htd_nn _ _ _].
    unfold convertToShares.
    assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
    assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
    apply Z.div_pos; [nia | lia].
  Qed.

  Lemma convertToAssets_nonneg (s : State.t) (shares : U256.t) :
    Valid.state s ->
    0 <= shares ->
    0 <= convertToAssets s shares.
  Proof.
    intros Hv Hs.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [Hsup_u256 Htd_nn _ _ _].
    unfold convertToAssets.
    assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
    assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
    apply Z.div_pos; [nia | lia].
  Qed.

  (** ---- 1.7 totalAssets non-negativity ---- *)
  Lemma totalAssets_nonneg (s : State.t) :
    Valid.state s ->
    0 <= totalAssets s.
  Proof.
    intros Hv.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [_ Htd _ _ _]. unfold totalAssets. lia.
  Qed.

  (** ---- 1.8 Empty-state initial mint: 1:1 share-to-asset.
      Under the OZ inflation-defended formula at empty state
      [totalAssets = 0], the computation reduces to
      [assets * 1 / 1 = assets] and [shares * 1 / 1 = shares] —
      still 1:1, but now via the +1 virtuals rather than an
      explicit supply==0 branch. *)
  Lemma convertToShares_empty (assets : U256.t) :
    convertToShares empty_state assets = assets.
  Proof.
    unfold convertToShares, empty_state, totalAssets. simpl.
    rewrite Z.mul_1_r. apply Z.div_1_r.
  Qed.

  Lemma convertToAssets_empty (shares : U256.t) :
    convertToAssets empty_state shares = shares.
  Proof.
    unfold convertToAssets, empty_state, totalAssets. simpl.
    rewrite Z.mul_1_r. apply Z.div_1_r.
  Qed.

  Lemma deposit_initial_mint_1to1 (assets : U256.t) :
    snd (deposit empty_state assets) = assets.
  Proof.
    unfold deposit. simpl. apply convertToShares_empty.
  Qed.

  (** ---- 1.9 Per-operation invariants threaded across the four
            entry points ----

      For each of deposit / mint / withdraw / redeem, we expose a
      sim-side post-state characterization keyed by the
      operation's specific arguments. These are the "preview"-result
      lemmas: previewDeposit returns convertToShares; previewMint
      returns the ceil-div assets needed; previewWithdraw returns
      the ceil-div shares to burn; previewRedeem returns
      convertToAssets. *)

  Definition previewDeposit (s : State.t) (assets : U256.t) : U256.t :=
    convertToShares s assets.

  Definition previewMint (s : State.t) (shares : U256.t) : U256.t :=
    (* OZ ERC4626 previewMint = _convertToAssets(shares, Math.Rounding.Up)
       under the inflation-defended formula (offset = 0):
         ceil(shares * (totalAssets + 1) / (totalSupply + 1))
         = (shares * (totalAssets + 1) + totalSupply) / (totalSupply + 1).
       Denominator is always >= 1, so no supply==0 branch needed. *)
    let supply := s.(State.totalSupply) in
    let ta := totalAssets s in
    (shares * (ta + 1) + supply) / (supply + 1).

  Definition previewWithdraw (s : State.t) (assets : U256.t) : U256.t :=
    (* OZ ERC4626 previewWithdraw = _convertToShares(assets, Math.Rounding.Up)
       under the inflation-defended formula (offset = 0):
         ceil(assets * (totalSupply + 1) / (totalAssets + 1))
         = (assets * (totalSupply + 1) + totalAssets) / (totalAssets + 1). *)
    let supply := s.(State.totalSupply) in
    let ta := totalAssets s in
    (assets * (supply + 1) + ta) / (ta + 1).

  Definition previewRedeem (s : State.t) (shares : U256.t) : U256.t :=
    convertToAssets s shares.

  (** previewDeposit / previewRedeem are the floor-rounding
      conversions; previewMint / previewWithdraw are the ceiling
      conversions (per OZ ERC4626 convention). *)

  Lemma previewDeposit_unfold (s : State.t) (assets : U256.t) :
    previewDeposit s assets = convertToShares s assets.
  Proof. reflexivity. Qed.

  Lemma previewRedeem_unfold (s : State.t) (shares : U256.t) :
    previewRedeem s shares = convertToAssets s shares.
  Proof. reflexivity. Qed.

  Lemma previewMint_empty (shares : U256.t) :
    previewMint empty_state shares = shares.
  Proof.
    unfold previewMint, empty_state, totalAssets. simpl.
    rewrite Z.add_0_r. rewrite Z.mul_1_r. apply Z.div_1_r.
  Qed.

  Lemma previewWithdraw_empty (assets : U256.t) :
    previewWithdraw empty_state assets = assets.
  Proof.
    unfold previewWithdraw, empty_state, totalAssets. simpl.
    rewrite Z.add_0_r. rewrite Z.mul_1_r. apply Z.div_1_r.
  Qed.

  (** previewMint is non-negative for valid inputs. *)
  Lemma previewMint_nonneg (s : State.t) (shares : U256.t) :
    Valid.state s ->
    0 <= shares ->
    0 <= previewMint s shares.
  Proof.
    intros Hv Hs.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [Hsup_u256 Htd_nn _ _ _].
    unfold previewMint.
    assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
    assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
    apply Z.div_pos; [nia | lia].
  Qed.

  (** previewWithdraw is non-negative for valid inputs. *)
  Lemma previewWithdraw_nonneg (s : State.t) (assets : U256.t) :
    Valid.state s ->
    0 <= assets ->
    0 <= previewWithdraw s assets.
  Proof.
    intros Hv Ha.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [Hsup_u256 Htd_nn _ _ _].
    unfold previewWithdraw.
    assert (Hsup_nn : 0 <= s.(State.totalSupply)) by (destruct Hsup_u256; lia).
    assert (Hta_nn : 0 <= totalAssets s) by (unfold totalAssets; lia).
    apply Z.div_pos; [nia | lia].
  Qed.

  (** ---- 1.10 Sim-side total-supply / total-deposited deltas under
            each entry point ----

      The deposit/mint paths bump the totals by the appropriate
      amount; the withdraw/redeem paths shrink them. The sim only
      has [deposit] and [withdraw]; mint and redeem are derived as
      operationally equivalent (a [mint shares] is a [deposit
      previewMint(shares)] yielding exactly [shares] shares, and
      similarly for redeem). *)

  Definition deposit_via_mint (s : State.t) (shares : U256.t)
      : State.t * U256.t :=
    let assets := previewMint s shares in
    deposit s assets.

  Definition withdraw_via_redeem (s : State.t) (shares : U256.t)
      : Result.t (State.t * U256.t) :=
    let assets := previewRedeem s shares in
    match withdraw s assets with
    | Result.Success (s', _) => Result.Success (s', assets)
    | Result.Revert p q => Result.Revert p q
    end.

  Lemma deposit_via_mint_supply_grows (s : State.t) (shares : U256.t) :
    (fst (deposit_via_mint s shares)).(State.totalSupply)
    = s.(State.totalSupply) + convertToShares s (previewMint s shares).
  Proof. unfold deposit_via_mint, deposit. reflexivity. Qed.

  Lemma deposit_via_mint_deposited_grows (s : State.t) (shares : U256.t) :
    (fst (deposit_via_mint s shares)).(State.totalDeposited)
    = s.(State.totalDeposited) + previewMint s shares.
  Proof. unfold deposit_via_mint, deposit. reflexivity. Qed.

  (** ====================================================================
      Section 2 — Storage layout & projection lens
      ====================================================================

      The StakingVault contract inherits from (top-down in inheritance
      order):

        ERC4626Upgradeable
        ERC20PermitUpgradeable
        ERC20VotesUpgradeable
        AccessControlEnumerableUpgradeable
        Versioned
        UUPSUpgradeable
        IOptimisticVotes

      With ERC7201 (storage-slot namespacing), each base reserves a
      keccak256-derived storage anchor. StakingVault's own slots
      (rewardTokens / unstakingManager / rewardRatio / etc.) sit at
      sequential indices following the inherited anchors.

      Slot anchors (per OZ-Upgradeable conventions; concrete numeric
      indices are determined by Solc's storage-layout JSON for the
      compiled artifact at the time the shallow form was emitted):

        slot_ERC4626Storage           — ERC7201 anchor for ERC4626
                                        (the asset() address).
        slot_ERC20Storage             — ERC7201 anchor for ERC20:
                                        balances mapping,
                                        allowances mapping,
                                        totalSupply,
                                        name, symbol.
        slot_ERC20PermitStorage       — ERC7201 anchor for ERC20Permit
                                        (mostly the EIP-712 domain).
        slot_ERC20VotesStorage        — ERC7201 anchor for ERC20Votes
                                        (delegate, delegateCheckpoints,
                                        totalSupplyCheckpoints).
        slot_NoncesStorage            — ERC7201 anchor for Nonces.
        slot_AccessControlStorage     — ERC7201 anchor for
                                        AccessControl (roles map).
        slot_AccessControlEnumerableStorage — ERC7201 anchor for
                                              AccessControlEnumerable
                                              (per-role members set).
        slot_ReentrancyGuardStorage   — ERC7201 anchor for
                                        ReentrancyGuard (status).
        slot_UUPSUpgradeableStorage   — ERC7201 anchor for UUPS proxy.

        Then the StakingVault-specific slots (declared directly in
        StakingVault.sol):

        slot_versionRegistry          — Versioned.versionRegistry.
        slot_rewardTokens             — EnumerableSet.AddressSet.
        slot_rewardRatio              — D18{1}.
        slot_unstakingManager         — UnstakingManager pointer.
        slot_unstakingDelay           — {s}.
        slot_rewardTokenRegistry      — IRewardTokenRegistry.
        slot_rewardTrackers           — mapping(token => RewardInfo).
        slot_disallowedRewardTokens   — mapping(token => bool).
        slot_userRewardTrackers       — mapping(token => mapping(user
                                        => UserRewardInfo)).
        slot_optimisticDelegatees     — mapping(account => address).
        slot_optimisticDelegateCkpts  — mapping(delegatee => Trace208).
        slot_totalDeposited           — {asset}.
        slot_nativeBalanceLastKnown   — {asset}.
        slot_nativeRewardsLastPaid    — {s}.

      For this file we treat the slot indices as opaque Section
      parameters supplied at instantiation time; the projection lens
      then projects the [State.t] of [simulations/StakingVaultExchange.v]
      out of the full storage. The lens covers ONLY the exchange-rate
      slots — totalSupply (read from ERC20Storage), totalDeposited,
      nativeBalanceLastKnown, nativeRewardsLastPaid. The other slots
      participate in the storage state but do not affect the
      exchange-rate decision; their preservation is captured by the
      composite walker axioms via the observational bridge. *)

  Section StakingVaultExchangeLens.

    (** The slot indices on the inheriting contract's full
        SimulatedStorage.t. Per Solc's storage-layout JSON, each
        ERC7201 anchor is a keccak-derived constant; we model that
        derivation as an opaque [nat] (the anchor's index into the
        SimulatedStorage list).

        For the exchange-rate equivalence we need only the slots
        below; the rest of the storage is captured by the
        [storage_base] argument carried into the composite walker
        axioms (R070 shape). *)
    Variable slot_ERC20_totalSupply       : nat.
    Variable slot_totalDeposited          : nat.
    Variable slot_nativeBalanceLastKnown  : nat.
    Variable slot_nativeRewardsLastPaid   : nat.

    (** The projection lens — given the inheritor's full
        [SimulatedStorage.t], extract the exchange-rate sim's
        [State.t].

        Phase B extension (Task #310 / R106): the lens now exposes
        the FOUR primary fields of the widened sim
        [State.t = (totalSupply, totalDeposited, nativeBalanceLastKnown,
        nativeRewardsLastPaid)] — one Z-valued read per slot.  The old
        derived field [accumulatedNativeRewards] is replaced by the
        getter defined in [simulations/StakingVaultExchange.v].  The
        lens body is now a record-literal of four reads (no
        conditional).  Untouched-slot semantics under
        [storage_with_sim] are preserved by the [sve_set_nth] no-
        overlap shape (see Section 2b lemmas). *)
    Definition project_exchange (storage : SimulatedStorage.t) : State.t :=
      let supply :=
        match List.nth_error storage slot_ERC20_totalSupply with
        | Some (StorableValue.U256 v) => v
        | _ => 0
        end in
      let td :=
        match List.nth_error storage slot_totalDeposited with
        | Some (StorableValue.U256 v) => v
        | _ => 0
        end in
      let nblk :=
        match List.nth_error storage slot_nativeBalanceLastKnown with
        | Some (StorableValue.U256 v) => v
        | _ => 0
        end in
      let nrlp :=
        match List.nth_error storage slot_nativeRewardsLastPaid with
        | Some (StorableValue.U256 v) => v
        | _ => 0
        end in
      {| State.totalSupply              := supply;
         State.totalDeposited           := td;
         State.nativeBalanceLastKnown   := nblk;
         State.nativeRewardsLastPaid    := nrlp;
      |}.

    (** Lens correctness — each [project_exchange]'s field matches
        the corresponding slot value. Discharged by [reflexivity]
        once the slot indices are pinned. *)

    Lemma lens_totalSupply
        (storage : SimulatedStorage.t)
        (supply : U256.t)
        (Hs : List.nth_error storage slot_ERC20_totalSupply
              = Some (StorableValue.U256 supply)) :
      (project_exchange storage).(State.totalSupply) = supply.
    Proof. unfold project_exchange. rewrite Hs. reflexivity. Qed.

    Lemma lens_totalDeposited
        (storage : SimulatedStorage.t)
        (td : U256.t)
        (Hs : List.nth_error storage slot_totalDeposited
              = Some (StorableValue.U256 td)) :
      (project_exchange storage).(State.totalDeposited) = td.
    Proof. unfold project_exchange. rewrite Hs. reflexivity. Qed.

  End StakingVaultExchangeLens.

  (** ====================================================================
      Section 2b — Module-level slot anchors + concrete lens + set_nth
      ====================================================================

      Task #306 (R101 Phase A, 2026-06-01).  R099's Parameter→Definition
      methodology requires a concrete [proj_post_<X>] body that mirrors
      the sim-side transition.  The Section-scoped lens in Section 2 is
      parameterized by abstract slot indices; for the Definition body we
      need MODULE-level slot anchors so the Definitions can be invoked
      from Section 6 (post-storage Definitions) and beyond.

      The slot anchors below are [Parameter]s (audit-time obligation:
      "the deployed StakingVault.sol Yul artifact's storage-layout JSON
      pins these slot indices").  This mirrors the R070 pattern of
      moving slot indices outside the lens Section when they need to
      be referenced from the post-storage layer.

      AccessControl roles slot (Section 7 [eq_at_roles]) lives at the
      [slot_AccessControl_roles := 1] hard-coded position; we pick the
      three slots below DISTINCT from 1 so the observation bridge
      Lemmas close by reflexivity over the [sve_set_nth] no-overlap
      shape.

      Concrete slot index choices (audit-time obligation: the
      deployed StakingVault.sol Yul artifact's storage-layout JSON
      pins these slot indices; the choice here is a representative
      consistent assignment — the AccessControl-roles slot lives at
      [1] (Section 7), so the three exchange-rate slots use the
      hard-coded indices below).  Sister convention used by
      UnstakingManager.v (concrete [Definition slot_locks := 1]). *)

  Definition slot_ERC20_totalSupply_const      : nat := 4.
  Definition slot_totalDeposited_const         : nat := 12. (* 0x0c *)
  Definition slot_nativeBalanceLastKnown_const : nat := 13. (* 0x0d *)
  (** Phase B extension (Task #310 / R106): the modifier wrapper
      writes [nativeRewardsLastPaid] at slot 14.  We now include it in
      the lens so the modifier's chain of [sstore]s can be matched
      slot-by-slot. *)
  Definition slot_nativeRewardsLastPaid_const  : nat := 14. (* 0x0e *)

  Lemma slot_ERC20_totalSupply_const_neq_roles :
    slot_ERC20_totalSupply_const <> 1%nat.
  Proof. unfold slot_ERC20_totalSupply_const. discriminate. Qed.

  Lemma slot_totalDeposited_const_neq_roles :
    slot_totalDeposited_const <> 1%nat.
  Proof. unfold slot_totalDeposited_const. discriminate. Qed.

  Lemma slot_nativeBalanceLastKnown_const_neq_roles :
    slot_nativeBalanceLastKnown_const <> 1%nat.
  Proof. unfold slot_nativeBalanceLastKnown_const. discriminate. Qed.

  Lemma slot_nativeRewardsLastPaid_const_neq_roles :
    slot_nativeRewardsLastPaid_const <> 1%nat.
  Proof. unfold slot_nativeRewardsLastPaid_const. discriminate. Qed.

  (** In-place set at index — copy of [VersionRegistry.set_nth] kept
      local to avoid a cross-file simulation import.  Out-of-bounds
      leaves the list unchanged. *)
  Fixpoint sve_set_nth {A : Type} (n : nat) (a : A) (xs : list A) : list A :=
    match xs, n with
    | [], _ => []
    | _ :: rest, O => a :: rest
    | x :: rest, S k => x :: sve_set_nth k a rest
    end.

  (** [sve_set_nth] preserves [nth_error] at indices DIFFERENT from
      the write target. *)
  Lemma sve_set_nth_nth_error_neq
      {A : Type} (n m : nat) (a : A) (xs : list A) :
    n <> m ->
    nth_error (sve_set_nth n a xs) m = nth_error xs m.
  Proof.
    revert n m. induction xs as [|x rest IH]; intros n m Hneq; simpl.
    - destruct n; simpl; reflexivity.
    - destruct n as [|n']; destruct m as [|m']; simpl; try reflexivity.
      + contradiction.
      + apply IH. intros Heq. apply Hneq. congruence.
  Qed.

  (** Concrete [project_exchange] at the module level, using the
      [Parameter] slot anchors above.  Body mirrors the Section-local
      [project_exchange]; under the Phase B extension the lens exposes
      FOUR primary fields (totalSupply, totalDeposited,
      nativeBalanceLastKnown, nativeRewardsLastPaid). *)
  Definition project_exchange_module
      (storage : SimulatedStorage.t) : State.t :=
    let supply :=
      match List.nth_error storage slot_ERC20_totalSupply_const with
      | Some (StorableValue.U256 v) => v
      | _ => 0
      end in
    let td :=
      match List.nth_error storage slot_totalDeposited_const with
      | Some (StorableValue.U256 v) => v
      | _ => 0
      end in
    let nblk :=
      match List.nth_error storage slot_nativeBalanceLastKnown_const with
      | Some (StorableValue.U256 v) => v
      | _ => 0
      end in
    let nrlp :=
      match List.nth_error storage slot_nativeRewardsLastPaid_const with
      | Some (StorableValue.U256 v) => v
      | _ => 0
      end in
    {| State.totalSupply              := supply;
       State.totalDeposited           := td;
       State.nativeBalanceLastKnown   := nblk;
       State.nativeRewardsLastPaid    := nrlp;
    |}.

  (** Lift a sim [State.t] back into the [storage_base] by writing
      the four exchange-rate fields at the lens slots.  Per the
      adversarial-review note in Section 7, this leaves
      [slot_AccessControl_roles := 1] (and all other slots) UNCHANGED
      — exactly what the observational bridge expects.

      Phase B extension: the writeback now covers FOUR slots — the
      same set as [project_exchange_module] reads.  The new
      [nativeRewardsLastPaid] (slot 14) is written last in the
      [sve_set_nth] chain so the proof of slot-preservation at slot 1
      naturally generalises. *)
  Definition storage_with_sim
      (storage_base : SimulatedStorage.t)
      (sim : State.t) : SimulatedStorage.t :=
    sve_set_nth slot_nativeRewardsLastPaid_const
      (StorableValue.U256 sim.(State.nativeRewardsLastPaid))
    (sve_set_nth slot_nativeBalanceLastKnown_const
      (StorableValue.U256 sim.(State.nativeBalanceLastKnown))
    (sve_set_nth slot_totalDeposited_const
      (StorableValue.U256 sim.(State.totalDeposited))
    (sve_set_nth slot_ERC20_totalSupply_const
      (StorableValue.U256 sim.(State.totalSupply))
      storage_base))).

  (** [storage_with_sim] preserves [nth_error] at the AccessControl
      roles slot — the basis for the observational bridge Lemmas in
      Section 7. *)
  Lemma storage_with_sim_preserves_roles
      (storage_base : SimulatedStorage.t) (sim : State.t) :
    List.nth_error (storage_with_sim storage_base sim) 1
    = List.nth_error storage_base 1.
  Proof.
    unfold storage_with_sim.
    rewrite sve_set_nth_nth_error_neq;
      [|exact slot_nativeRewardsLastPaid_const_neq_roles].
    rewrite sve_set_nth_nth_error_neq;
      [|exact slot_nativeBalanceLastKnown_const_neq_roles].
    rewrite sve_set_nth_nth_error_neq;
      [|exact slot_totalDeposited_const_neq_roles].
    rewrite sve_set_nth_nth_error_neq;
      [|exact slot_ERC20_totalSupply_const_neq_roles].
    reflexivity.
  Qed.

  (** ----- Per-mutator sim-side post-state Definitions ----- *)

  (** [sim_deposit_4312_post sim assets] — the [State.t] after a
      successful [deposit].  The sim's [deposit] returns [(s', shares)];
      we project [s']. *)
  Definition sim_deposit_4312_post (sim : State.t) (assets : U256.t) : State.t :=
    fst (deposit sim assets).

  (** [sim_mint_4356_post sim shares] — the [State.t] after a
      successful [mint].  Mint is operationally equivalent to
      [deposit (previewMint shares) shares]: see [deposit_via_mint]. *)
  Definition sim_mint_4356_post (sim : State.t) (shares : U256.t) : State.t :=
    fst (deposit_via_mint sim shares).

  (** [sim_withdraw_4403_post sim assets] — the [State.t] after a
      successful [withdraw].  Falls back to the pre-state when
      [withdraw] reverts (the post-storage Definition is undefined on
      the revert branch; the milestone proofs gate on the
      [H_within_max] precondition which excludes the revert case at
      the Yul layer). *)
  Definition sim_withdraw_4403_post (sim : State.t) (assets : U256.t) : State.t :=
    match withdraw sim assets with
    | Result.Success (s', _) => s'
    | Result.Revert _ _ => sim
    end.

  (** [sim_redeem_4450_post sim shares] — same fallback shape as
      [sim_withdraw_4403_post].  Redeem is operationally equivalent to
      [withdraw (previewRedeem shares) shares] via
      [withdraw_via_redeem]. *)
  Definition sim_redeem_4450_post (sim : State.t) (shares : U256.t) : State.t :=
    match withdraw_via_redeem sim shares with
    | Result.Success (s', _) => s'
    | Result.Revert _ _ => sim
    end.

  (** ====================================================================
      Section 3 — Sim-side environment parameters
      ==================================================================== *)

  (** Block timestamp — read by [accrueRewards] before each
      exchange-rate operation. Pinned via a Parameter (R070 shape;
      same as TimelockControllerOptimistic.now_timestamp). *)
  Parameter now_timestamp : U256.t.

  (** Block timestamp validity hypothesis — the contract reads
      [block.timestamp] as a [uint256] but the EVM constrains it to
      the [uint48] range used by Time.timestamp(). For the
      equivalence-layer milestones we expose the underlying read as
      an opaque environment value. *)
  Parameter now_timestamp_valid : U256.Valid.t now_timestamp.

  (** ====================================================================
      Section 4 — ERC4626 / Votes / ReentrancyGuard / AccessControl
                  integration markers
      ==================================================================== *)

  (** ---- ERC4626 dependency (Wave 1 agent #241) ----

      The OZ ERC4626 abstract base contributes:

        - [_convertToShares(assets, rounding)]
        - [_convertToAssets(shares, rounding)]
        - [previewDeposit] / [previewMint] / [previewWithdraw] /
          [previewRedeem]
        - [maxDeposit] / [maxMint] / [maxWithdraw] / [maxRedeem]
        - [_deposit(caller, receiver, assets, shares)] (internal)
        - [_withdraw(caller, receiver, owner, assets, shares)]
          (internal)
        - the [asset()] view function.

      In the StakingVault, [_deposit] and [_withdraw] are
      OVERRIDDEN to update [totalDeposited] / [nativeBalanceLastKnown]
      around the super call. The super call is the OZ base's
      [_deposit] / [_withdraw], which does:

        super._deposit:
          - asset.transferFrom(caller, address(this), assets)
          - _mint(receiver, shares)
          - emit Deposit(caller, receiver, assets, shares)

        super._withdraw (when caller != owner):
          - _spendAllowance(owner, caller, shares)
        super._withdraw (always):
          - _burn(owner, shares)
          - asset.transfer(receiver, assets)
          - emit Withdraw(caller, receiver, owner, assets, shares)

      The override-around shape — pre-super update + super + post-
      super read of asset.balanceOf — is the exchange-rate side of
      this file's equivalence.

      [Wave 2 integration: instantiate ERC4626 here when Agent ERC4626
      lands]. Until then, the composite walker axioms below capture
      the ERC4626 calls as opaque sub-Hoare-triples. *)

  (** A symbolic placeholder for the ERC4626 abstract surface. When
      the Wave 1 ERC4626 equivalence file lands, this Module Type
      becomes its actual `Module Type` import. *)
  Module Type ERC4626_AbstractSurface.
    Parameter ERC4626_State : Set.
    Parameter project_erc4626 :
      SimulatedStorage.t -> ERC4626_State.
    (** Wave 2 integration: the asset() pointer slot is exposed here. *)
    Parameter asset_address : SimulatedStorage.t -> U256.t.
  End ERC4626_AbstractSurface.

  (** ---- Votes dependency (Task #240, slot-agnostic) ----

      The StakingVault's [_update] override (StakingVault.sol:499)
      chains into Votes.transferVotingUnits. The exchange-rate
      operations (deposit/mint/withdraw/redeem) all hit [_update] via
      [_mint] / [_burn]:

        deposit / mint: _mint(receiver, shares) calls _update(0,
                        receiver, shares).
        withdraw/redeem (unstakingDelay = 0):
                        _burn(owner, shares) calls _update(owner, 0,
                        shares).
        withdraw/redeem (unstakingDelay > 0):
                        same _burn(owner, shares).

      [_update] runs the [accrueRewards] modifier, then
      super._update which performs the balance map + totalSupply
      update + Votes.transferVotingUnits + _moveOptimisticDelegateVotes.

      The Votes-side reasoning is captured in
      [proofs/equivalence/Votes.v] (R072 slot-agnostic). Each Votes
      mutator's effect on the exchange-rate is observational: the
      Votes slots are touched but the [totalSupply] update (which is
      part of the exchange-rate state) is observable via the
      ERC20Storage.totalSupply slot. *)

  (** ---- ReentrancyGuard dependency (Task #238) ----

      ERC4626's [deposit]/[mint]/[withdraw]/[redeem] entry-points
      run under the [nonReentrant] modifier (inherited from
      ReentrancyGuardUpgradeable). The internal [_deposit] /
      [_withdraw] calls happen INSIDE the lock; nested external
      calls (asset.transferFrom, asset.transfer) cannot re-enter.

      The R045 symbolic expansion in
      [proofs/equivalence/ReentrancyGuard.v]:

        with_nonReentrant s body :=
          nonReentrant_enter s; body s_entered; nonReentrant_exit.

      The composite walker axioms below assume the lock is taken on
      entry (status = NotEntered → status = Entered for the duration
      of the body) and released on exit. The exchange-rate slot
      updates happen DURING the body. *)

  (** ---- AccessControl dependency (Task #237) ----

      The four exchange-rate entry-points are NOT role-gated; any
      caller can deposit / mint / withdraw / redeem. AccessControl
      slots appear in the storage layout but are invariant across
      the four operations.

      (The contract's role-gated mutators — [setUnstakingDelay],
      [addRewardToken], [removeRewardToken], [setRewardRatio],
      [_authorizeUpgrade] — are owned by parallel Wave 2 agent #257
      pause/admin.) *)

  (** ====================================================================
      Section 5 — Storage equivalence relation
      ====================================================================

      Matches the R070 / R071 envelope shape from TimelockController-
      Optimistic.v. Per-target observational equality at the abstract
      SimulatedStorage.t level. Each milestone theorem witnesses the
      walker's post-state and discharges the bridge via either
      [storage_equiv_refl] (when the walker's post-state already
      matches the theorem's reference) or the per-target
      observational-bridge axiom. *)

  Definition storage_equiv (s s' : SimulatedStorage.t) : Prop := s = s'.

  Lemma storage_equiv_refl s : storage_equiv s s.
  Proof. reflexivity. Qed.

  Lemma storage_equiv_sym s s' :
    storage_equiv s s' -> storage_equiv s' s.
  Proof. unfold storage_equiv. intros ->. reflexivity. Qed.

  Lemma storage_equiv_trans s s' s'' :
    storage_equiv s s' -> storage_equiv s' s'' -> storage_equiv s s''.
  Proof. unfold storage_equiv. intros -> ->. reflexivity. Qed.

  (** ====================================================================
      Section 6 — Per-mutator post-storage [Definition]s (R101 Phase A)
      ====================================================================

      Task #306 (R101 Phase A, 2026-06-01).  Per R099's UnstakingManager
      methodology, each [proj_post_<X>] is now a concrete [Definition]
      computing the sim-side post-storage directly via
      [storage_with_sim] applied to the corresponding sim transition.

      Signature: each [proj_post_<X>] preserves its current call-site
      shape ([storage_base : SimulatedStorage.t] as the first argument)
      — this is a deliberate departure from R099's
      [(State.t, args) -> SimulatedStorage.t] signature.  Rationale:
      the StakingVaultExchange sim [State.t] (3 fields:
      [totalSupply, totalDeposited, accumulatedNativeRewards]) does NOT
      model the full StakingVault storage shape (ERC20 balances mapping,
      AccessControl roles, Votes checkpoints, reward trackers, etc.).
      We therefore THREAD [storage_base] through the Definition and
      apply the sim transition AT THE THREE LENS SLOTS only, leaving
      the unmodeled slots untouched.

      Each Definition uses the [project_exchange_module] /
      [sim_<X>_post] / [storage_with_sim] infrastructure from
      Section 2b.

      Audit consequences:
        - The 4 observational-bridge Axioms in Section 7 collapse to
          Qed Lemmas via [storage_with_sim_preserves_roles].
        - Per-target structural integrity: the AccessControl roles
          slot (1) is preserved by construction; the three lens slots
          carry the sim's [totalSupply / totalDeposited / nativeBalance
          LastKnown] post-values.

      Phase B structural blocker (documented in WISDOM.md R101):  The
      modifier-wrapper Axioms in Section 8c REMAIN Axioms.  The
      [modifier_accrueRewards_<X>] body touches storage slots OUTSIDE
      the SVE sim's coverage ([nativeRewardsLastPaid], per-token
      reward trackers, ERC20 balances mapping, Votes checkpoints).
      A full Qed discharge requires extending the SVE sim's [State.t]
      to cover these slots (a Wave-3 effort estimated at 5000+ LOC).
      The Parameter→Definition refactor in this phase is a PARTIAL
      closure: it eliminates the [proj_post_<X>] [Parameter]s and the
      4 observational bridges as audit obligations, but the
      modifier-wrapper Axioms still encode the missing sim coverage. *)

  Definition proj_post_deposit_4312
      (storage_base : SimulatedStorage.t)
      (caller assets receiver now_ : U256.t) : SimulatedStorage.t :=
    storage_with_sim storage_base
      (sim_deposit_4312_post (project_exchange_module storage_base) assets).

  Definition proj_post_mint_4356
      (storage_base : SimulatedStorage.t)
      (caller shares receiver now_ : U256.t) : SimulatedStorage.t :=
    storage_with_sim storage_base
      (sim_mint_4356_post (project_exchange_module storage_base) shares).

  Definition proj_post_withdraw_4403
      (storage_base : SimulatedStorage.t)
      (caller assets receiver owner now_ : U256.t) : SimulatedStorage.t :=
    storage_with_sim storage_base
      (sim_withdraw_4403_post (project_exchange_module storage_base) assets).

  Definition proj_post_redeem_4450
      (storage_base : SimulatedStorage.t)
      (caller shares receiver owner now_ : U256.t) : SimulatedStorage.t :=
    storage_with_sim storage_base
      (sim_redeem_4450_post (project_exchange_module storage_base) shares).

  (** ====================================================================
      Section 7 — Per-target observational bridge [Axiom]s (R051 shape)
      ====================================================================

      Per the 2026-05-31 adversarial-review skolemization-soundness
      audit (CCV-1 / CCV-2 / CRIT-V), the four [_observes] bridges
      below were previously reflexive [storage_equiv (X) (X)]
      tautologies on the Skolem -- the same opaque [proj_post_<fn>]
      appeared on both sides, constraining nothing. An adversarial
      inheritor could pick [proj_post_<fn> := fun _ _ _ _ _ => empty]
      without contradicting the bridges, leaving the milestone
      theorems content-free at the slot level. The bridges were
      also unused by any milestone proof (Phase 2 closed via
      [storage_equiv_refl] directly), so [Print Assumptions] did
      not flag them at all.

      Promote each bridge to a content-bearing claim relating the
      walker's Skolemized post-storage to [storage_base] at a
      slot-indexed position of [SimulatedStorage.t =
      list StorableValue.t] that the function does NOT touch.

      For exchange-rate operations the slots WRITTEN are:

        deposit / mint:
          totalSupply             += shares
          totalDeposited          += assets
          nativeBalanceLastKnown  += assets
          (nativeRewardsLastPaid set to now via accrueRewards
           pre-step)
          + ERC20 balances[receiver] += shares
          + asset.balanceOf(vault) += assets (external)
          + Votes checkpoints push at receiver (via _update)

        withdraw / redeem:
          totalSupply             -= shares
          totalDeposited          -= assets
          nativeBalanceLastKnown   = asset.balanceOf(vault)
                                     (final write after path)
          + ERC20 balances[owner] -= shares (via _burn)
          + (unstakingDelay = 0):
              asset.balanceOf(vault) -= assets (external)
              asset.balanceOf(receiver) += assets
          + (unstakingDelay > 0):
              forceApprove(unstakingManager, assets) at vault
              unstakingManager.createLock(receiver, assets,
                                          now + unstakingDelay)
          + Votes checkpoints push at owner (via _update)

      All four operations LEAVE UNCHANGED the AccessControl roles
      aggregate (the [AccessControlStorage] ERC7201 anchor): none
      of deposit/mint/withdraw/redeem are role-gated, and none of
      the OZ ERC4626 / Votes / ReentrancyGuard / StakingVault
      override code touches the roles map on the success path.
      We therefore pin the observational bridge to "the roles
      slot is preserved".

      The slot-index choice is abstract (mirrors the T2.4
      [TimelockControllerOptimistic.slot_roles] template); the
      concrete keccak256-derived value is supplied at the
      inheritor instantiation site. We hard-code
      [slot_AccessControl_roles := 1] here because [List.nth_error]
      needs a [nat] index and the abstract list shape supports
      any consistent assignment -- what matters is that the
      predicate now carries real content (an empty-storage
      adversarial instantiation of [proj_post_<fn>] no longer
      satisfies "slot 1 equals slot 1 of storage_base").

      Mirrors the T2.4 (TimelockControllerOptimistic) and T2.6
      (StakingVaultRewards) templates. *)

  Definition slot_AccessControl_roles : nat := 1.

  Definition eq_at_roles (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_AccessControl_roles
    = List.nth_error s2 slot_AccessControl_roles.

  Lemma eq_at_roles_refl s : eq_at_roles s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_roles_sym s1 s2 :
    eq_at_roles s1 s2 -> eq_at_roles s2 s1.
  Proof. unfold eq_at_roles. intros H. symmetry. exact H. Qed.

  Lemma eq_at_roles_trans s1 s2 s3 :
    eq_at_roles s1 s2 ->
    eq_at_roles s2 s3 ->
    eq_at_roles s1 s3.
  Proof.
    unfold eq_at_roles. intros H12 H23.
    rewrite H12. exact H23.
  Qed.

  (** Each [_observes] axiom asserts that the Skolemized post-storage
      agrees with [storage_base] at [slot_AccessControl_roles].
      An adversarial instantiation that returns garbage at the
      untouched slot now contradicts these bridges. The full
      slot-by-slot equality (including the WRITTEN slots' new
      values) is left to a stronger lens-correctness obligation at
      the inheritor's instantiation site; the CURRENT bridges are
      content-bearing on the unchanged-slot side -- enough to
      defeat the [proj_post := fun _ _ _ _ _ => empty] adversarial
      instantiation that previously closed all four milestones via
      [True]-degeneracy. *)

  (** Task #306 (R101 Phase A, 2026-06-01).  With the concrete
      [proj_post_<X>] [Definition]s in Section 6, each
      [_observes] bridge collapses to a Qed [Lemma]: the Definitions
      modify only the three lens slots, leaving
      [slot_AccessControl_roles := 1] preserved by construction.
      The discharge is [storage_with_sim_preserves_roles] composed
      with the Definition's [storage_with_sim] wrap. *)

  Lemma proj_post_deposit_4312_observes :
    forall (storage_base : SimulatedStorage.t)
           (caller assets receiver now_ : U256.t),
    eq_at_roles
      (proj_post_deposit_4312 storage_base caller assets receiver now_)
      storage_base.
  Proof.
    intros storage_base caller assets receiver now_.
    unfold eq_at_roles, slot_AccessControl_roles, proj_post_deposit_4312.
    apply storage_with_sim_preserves_roles.
  Qed.

  Lemma proj_post_mint_4356_observes :
    forall (storage_base : SimulatedStorage.t)
           (caller shares receiver now_ : U256.t),
    eq_at_roles
      (proj_post_mint_4356 storage_base caller shares receiver now_)
      storage_base.
  Proof.
    intros storage_base caller shares receiver now_.
    unfold eq_at_roles, slot_AccessControl_roles, proj_post_mint_4356.
    apply storage_with_sim_preserves_roles.
  Qed.

  Lemma proj_post_withdraw_4403_observes :
    forall (storage_base : SimulatedStorage.t)
           (caller assets receiver owner now_ : U256.t),
    eq_at_roles
      (proj_post_withdraw_4403 storage_base caller assets receiver owner now_)
      storage_base.
  Proof.
    intros storage_base caller assets receiver owner now_.
    unfold eq_at_roles, slot_AccessControl_roles, proj_post_withdraw_4403.
    apply storage_with_sim_preserves_roles.
  Qed.

  Lemma proj_post_redeem_4450_observes :
    forall (storage_base : SimulatedStorage.t)
           (caller shares receiver owner now_ : U256.t),
    eq_at_roles
      (proj_post_redeem_4450 storage_base caller shares receiver owner now_)
      storage_base.
  Proof.
    intros storage_base caller shares receiver owner now_.
    unfold eq_at_roles, slot_AccessControl_roles, proj_post_redeem_4450.
    apply storage_with_sim_preserves_roles.
  Qed.

  (** ====================================================================
      Section 8 — Audit-time callee specs (documentation-only)
      ====================================================================

      The OZ chain of internal calls inside the four exchange-rate
      paths dispatches through helpers like [fun__msgSender_14384],
      [fun_previewDeposit_4220], [fun_previewMint_4236],
      [fun_previewWithdraw_4252], [fun_previewRedeem_4268],
      [fun__deposit_630] (the overridden internal _deposit),
      [fun__withdraw_736] (the overridden internal _withdraw).

      Each is documented as a parameter / axiom with [True]
      conclusions (R064 / R067 / R070 shape). They record the audit-
      time obligation that the inner function discharges its own
      composite walker; they are not load-bearing in [Print
      Assumptions] for the milestone theorems (which inherit the
      caller-side composite directly). *)

  Parameter has_unstakingDelay_zero : SimulatedStorage.t -> bool.
  (** Sim-side observation: is the unstakingDelay slot read as 0 at
      the storage_base? This determines which branch of [_withdraw]
      executes (immediate transfer vs. unstakingManager lock). *)

  Axiom previewDeposit_callee_succeeds :
    forall (s : State.t) (assets : U256.t),
    Valid.state s ->
    0 <= assets ->
    True.

  Axiom previewMint_callee_succeeds :
    forall (s : State.t) (shares : U256.t),
    Valid.state s ->
    0 <= shares ->
    True.

  Axiom previewWithdraw_callee_succeeds :
    forall (s : State.t) (assets : U256.t),
    Valid.state s ->
    0 <= assets <= totalAssets s ->
    True.

  Axiom previewRedeem_callee_succeeds :
    forall (s : State.t) (shares : U256.t),
    Valid.state s ->
    0 <= shares <= s.(State.totalSupply) ->
    True.

  (** ====================================================================
      Section 9 — Composite walker [Axiom]s
      ====================================================================

      One per entry point. Each bundles the function's Yul body's
      mechanical assembly into a single Hoare triple per the
      R070/R071 R051 shape.

      The bound function comes from the StakingVault shallow form:
      [ReserveGovernor.generated.StakingVault_shallow]. The shallow
      form is gated in [_RocqProject] behind a comment block (the
      ~3 min compilation cost is the gate). For this Wave 2 scaffold
      we accept the four Yul entry-points as opaque [M.t U256.t]
      Parameters; when the shallow form is activated, the Parameters
      become Notations aliasing the shallow-form Definitions.

      Wave 2 integration: when the shallow form is wired the four
      [fun_<op>_op] Parameters become Notations:

        Notation fun_deposit_4312_op  := fun_deposit_4312.
        Notation fun_mint_4356_op     := fun_mint_4356.
        Notation fun_withdraw_4403_op := fun_withdraw_4403.
        Notation fun_redeem_4450_op   := fun_redeem_4450.

      Task #299 / R093 closure: the shallow form IS now imported
      above; the four [fun_<op>_op] Notations bind to the actual
      shallow-form Definitions.  This enables the R088-style
      walker-Lemma discharge below: the milestone Lemmas walk the
      outer wrapper Yul body and dispatch helper sub-axioms.
   *)

  (** Bind the four entry-point ops to the StakingVault shallow form.
      This makes the [fun_<op>_op] terms transparent so the
      composite walker axioms can become Lemmas. *)
  Import StakingVault_1721.
  Import StakingVault_1721.StakingVault_1721_deployed.

  Notation fun_deposit_4312_op   := fun_deposit_4312.
  Notation fun_mint_4356_op      := fun_mint_4356.
  Notation fun_withdraw_4403_op  := fun_withdraw_4403.
  Notation fun_redeem_4450_op    := fun_redeem_4450.

  (** ====================================================================
      Section 8b — Per-helper sub-axioms (R088 trust redistribution)
      ====================================================================

      Task #299 / R093 closure.  Each composite walker (deposit / mint /
      withdraw / redeem) is decomposed into helper sub-axioms following
      the R088 pattern from [TimelockControllerOptimistic.v].  The
      milestone Theorems (Section 10) discharge their composite walker
      Lemmas by dispatching these sub-axioms; the sub-axioms in turn
      capture the cap-view + preview + msgSender + internal-helper
      transitions for each entry point.

      Trust redistribution (R088):
        - Before: 4 monolithic composite walker [Axiom]s, each opaque on
          a full ERC4626 entry-point body.
        - After:  per-walker helper sub-axiom split:
            * 1 [Lemma] [run_fun__msgSender_14384] (Qed against [caller]).
            * 4 cap-view sub-axioms [run_fun_maxX_returns] (one per entry
              point — see notes below for the constant vs balance-derived
              shapes).
            * 4 preview sub-axioms [run_fun_previewX_returns].
            * 2 internal-helper sub-axioms
              [run_fun__deposit_630_at_storage_base] (shared by deposit /
              mint) and [run_fun__withdraw_736_at_storage_base] (shared
              by withdraw / redeem).
          Plus 4 composite walker [Lemma]s (replacing the [Axiom]s).

      The internal-helper sub-axioms (deposit_630 / withdraw_736) are
      where the R093 SafeERC20 + linkersymbol primitives consume.  Their
      bodies invoke [fun_safeTransferFrom_4949] / [fun_safeTransfer_4922]
      / [fun_forceApprove_5125] (the SafeERC20 wrappers from the
      [using SafeERC20 for IERC20] inline pattern), each of which in
      turn invokes [Stdlib.call] via the inlined [_callOptionalReturn]
      → [call_make_state_bridge_absorbing] (R093) discharge.  The
      per-token success obligations follow the
      [safeTransfer_success_spec_concrete] template from
      [StakingVaultRewards.v]'s Section 6 (R063 / R086 shape). *)

  (** ===== Helper sub-axiom: [fun__msgSender_14384] =====

      The OZ [_msgSender()] hook in non-meta-tx contracts is just
      [msg.sender], encoded as [Stdlib.caller].  Lemma is Qed —
      structurally identical to [Guardian.run_fun__msgSender_3197]. *)
  Lemma run_fun__msgSender_14384 codes env state :
    {{? codes, env, Some state |
      fun__msgSender_14384 ⇓ Result.Ok env.(Environment.caller)
    | Some state ?}}.
  Proof.
    unfold fun__msgSender_14384.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_address _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_address;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call Stdlib.caller _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.caller; pr; p | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Helper sub-axioms: cap-view returns =====

      [fun_maxDeposit_4158] and [fun_maxMint_4173] both return the
      uint256 max constant [2^256 - 1] (cf. shallow lines 10599 /
      13383).  Their walker shape is a 6-line let-chain ending in
      [M.pure 0xff..ff]; under a valid-uint argument the gt-check in
      the wrapper is structurally [0], skipping the revert.

      [fun_maxWithdraw_4191] and [fun_maxRedeem_4204] are NOT
      constants — they read storage (the owner's balance and the
      convertToAssets of that balance, respectively).  Their axioms
      take a Skolem return value parameterized over [storage_base]
      and [owner], plus the precondition [assets <= maxWithdraw]
      (resp. [shares <= maxRedeem]) that bypasses the cap-revert.

      Trust delta: these Axioms encapsulate the SLOAD chain inside
      the cap-view helpers + the Math.sol linkersymbol read + the
      convertToAssets/balanceOf sub-walks.  R093's linkersymbol
      primitive ([StaticCallBridge.run_linkersymbol]) discharges the
      Math.sol linker step inside [previewWithdraw_4252] when the
      axiom is eventually refined to a Lemma. *)

  (** Sim-side projection of the cap-view returns.  Pinned via
      [Parameter] so the body of [proj_post_X] doesn't depend on
      these. *)
  Parameter max_withdraw_value :
    SimulatedStorage.t -> U256.t (* owner *) -> U256.t.
  Parameter max_redeem_value :
    SimulatedStorage.t -> U256.t (* owner *) -> U256.t.

  Axiom run_fun_maxDeposit_4158_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (receiver : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_maxDeposit_4158 receiver ⇓
        Result.Ok 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_maxMint_4173_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (receiver : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_maxMint_4173 receiver ⇓
        Result.Ok 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_maxWithdraw_4191_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (owner : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_maxWithdraw_4191 owner ⇓
        Result.Ok (max_withdraw_value storage_base owner)
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_maxRedeem_4204_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (owner : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_maxRedeem_4204 owner ⇓
        Result.Ok (max_redeem_value storage_base owner)
    | Some (make_state env state_base memory storage_base) ?}}.

  (** ===== Helper sub-axioms: preview returns =====

      [fun_previewDeposit_4220] (assets → shares, floor rounding):
      reads [linkersymbol(Math.sol:Math)] + threads through
      [fun__convertToShares_4478] which reads totalSupply / totalAssets
      / decimalsOffset + Math.mulDiv.  R093's [run_linkersymbol]
      (StaticCallBridge) discharges the linker step; the convertToShares
      sub-walk is captured in this axiom's Skolem return.

      Each axiom returns a Skolem return value (a function of
      [storage_base] and the input).  Preserves storage at the
      projection layer (preview is a view function — no SSTOREs). *)
  Parameter preview_deposit_value :
    SimulatedStorage.t -> U256.t (* assets *) -> U256.t.
  Parameter preview_mint_value :
    SimulatedStorage.t -> U256.t (* shares *) -> U256.t.
  Parameter preview_withdraw_value :
    SimulatedStorage.t -> U256.t (* assets *) -> U256.t.
  Parameter preview_redeem_value :
    SimulatedStorage.t -> U256.t (* shares *) -> U256.t.

  (** Preview values are non-negative by construction (ERC4626
      [convertToShares] / [convertToAssets] use [mulDiv] which returns
      a uint256).  This is an audit-time obligation discharged by
      [proofs/StakingVaultExchange_validity.v]. *)
  Axiom preview_deposit_value_nn :
    forall storage_base assets,
      0 <= preview_deposit_value storage_base assets.
  Axiom preview_mint_value_nn :
    forall storage_base shares,
      0 <= preview_mint_value storage_base shares.
  Axiom preview_withdraw_value_nn :
    forall storage_base assets,
      0 <= preview_withdraw_value storage_base assets.
  Axiom preview_redeem_value_nn :
    forall storage_base shares,
      0 <= preview_redeem_value storage_base shares.

  (** Preview values fit in uint256 (the result of [mulDiv] of two
      uint256-bounded inputs).  Audit obligation paired with the _nn
      axioms above; see [proofs/StakingVaultExchange_validity.v]. *)
  Axiom preview_deposit_value_valid :
    forall storage_base assets,
      U256.Valid.t (preview_deposit_value storage_base assets).
  Axiom preview_mint_value_valid :
    forall storage_base shares,
      U256.Valid.t (preview_mint_value storage_base shares).
  Axiom preview_withdraw_value_valid :
    forall storage_base assets,
      U256.Valid.t (preview_withdraw_value storage_base assets).
  Axiom preview_redeem_value_valid :
    forall storage_base shares,
      U256.Valid.t (preview_redeem_value storage_base shares).

  Axiom run_fun_previewDeposit_4220_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (assets : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_previewDeposit_4220 assets ⇓
        Result.Ok (preview_deposit_value storage_base assets)
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_previewMint_4236_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (shares : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_previewMint_4236 shares ⇓
        Result.Ok (preview_mint_value storage_base shares)
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_previewWithdraw_4252_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (assets : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_previewWithdraw_4252 assets ⇓
        Result.Ok (preview_withdraw_value storage_base assets)
    | Some (make_state env state_base memory storage_base) ?}}.

  Axiom run_fun_previewRedeem_4268_returns :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (shares : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_previewRedeem_4268 shares ⇓
        Result.Ok (preview_redeem_value storage_base shares)
    | Some (make_state env state_base memory storage_base) ?}}.

  (** ===== Helper sub-axioms: internal _deposit / _withdraw =====

      These are the heavy bodies: each invokes [accrueRewards] +
      [super._deposit] / [super._withdraw] + (for withdraw with
      non-zero unstakingDelay) [SafeERC20.forceApprove] +
      [unstakingManager.createLock].

      R093 closure consumption: each of these axioms is itself an
      audit-time discharge of a multi-step Yul walk that includes
      the SafeERC20 call sites.  The R093 primitives —
      [call_make_state_bridge_absorbing] and
      [StaticCallBridge.run_linkersymbol] — discharge the leaf
      [Stdlib.call] + [Stdlib.linkersymbol] steps inside the inlined
      SafeERC20 wrappers.  Per-token success follows the
      [safeTransferFrom_success_spec_concrete] etc. template (R063 /
      R086 shape; the concrete Parameters live in Section 8c below). *)

  (** ===== R100 modifier-wrapper sub-axioms (R088 trust redistribution).

      Each [run_fun__deposit_630_at_storage_base] /
      [run_fun__withdraw_736_at_storage_base] inner-body axiom was the
      monolithic R097 closure obligation: the entire 120/190 LOC of
      shallow-form body inside one opaque Skolem.  R098 (UnstakingManager
      parallel-investigation) diagnosed the structural barrier on
      discharging such axioms to Qed Lemmas: the body walk produces a
      concrete chain of [sstore_post_storage] / [call_post_memory]
      Skolems whose composition cannot be proven equal to the abstract
      [Parameter] post-state without either (Option A) converting the
      [Parameter] to a [Definition] of that chain, or (Option B)
      restating the inner Axiom existentially over the post-state.

      Instead of pursuing the structural restructuring (which would
      invalidate the four R097 outer walker Lemmas and the four
      milestone Theorems in Section 10), this R100 phase performs a
      narrower trust redistribution: split each inner-body Axiom into
      a modifier-wrapper sub-axiom (one per mutator) plus a Qed [Lemma]
      that walks the trivial outer wrapper. The modifier-wrapper
      sub-axiom carries the same Skolem post-state as the original
      inner-body Axiom — but the auditable surface excludes the outer
      wrapper's two-line ceremony ([let~ '(_,tt) := do~ <modifier> in
      M.pure (BlockUnit.Tt, tt) in M.pure tt]).

      Net trust delta: the inner-body Axiom is removed; the modifier
      sub-axiom replaces it at the same Skolem shape.  The outer
      wrapper Lemma is mechanically Qed against the sub-axiom.  No
      change to milestone Theorems' [Print Assumptions] sets at the
      Skolem level; the named obligation moves from [fun__deposit_630]
      to [modifier_accrueRewards_610] (resp. [modifier_accrueRewards_647]).

      Phase 3 closure shape (Task #305): inner-body Axiom → Qed Lemma
      composing a modifier-wrapper sub-axiom. *)

  Axiom run_modifier_accrueRewards_610_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (caller receiver assets shares : U256.t),
    0 <= caller < 2^160 ->
    0 <= receiver < 2^160 ->
    0 <= assets ->
    0 <= shares ->
    U256.Valid.t assets ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      modifier_accrueRewards_610 caller receiver assets shares ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_deposit_4312 storage_base
                 caller assets receiver now_timestamp)) ?}}.

  Axiom run_modifier_accrueRewards_647_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (caller receiver owner assets shares : U256.t),
    0 <= caller < 2^160 ->
    0 <= receiver < 2^160 ->
    0 <= owner < 2^160 ->
    0 <= assets ->
    0 <= shares ->
    U256.Valid.t assets ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      modifier_accrueRewards_647 caller receiver owner assets shares ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_withdraw_4403 storage_base
                 caller assets receiver owner now_timestamp)) ?}}.

  Lemma run_fun__deposit_630_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (caller receiver assets shares : U256.t),
    0 <= caller < 2^160 ->
    0 <= receiver < 2^160 ->
    0 <= assets ->
    0 <= shares ->
    U256.Valid.t assets ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__deposit_630 caller receiver assets shares ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_deposit_4312 storage_base
                 caller assets receiver now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           caller receiver assets shares
           H_caller H_receiver H_assets_nn H_shares_nn H_assets_u256 H_mem.
    (** Phase 1: dispatch the modifier sub-axiom to obtain the
        post-storage Skolem. *)
    pose proof (run_modifier_accrueRewards_610_at_storage_base
                  codes env state_base storage_base memory
                  caller receiver assets shares
                  H_caller H_receiver H_assets_nn H_shares_nn
                  H_assets_u256 H_mem)
      as Hmod.
    destruct Hmod as (memory' & Hmod).
    exists memory'.
    (** Phase 2: walk the trivial outer wrapper. *)
    unfold fun__deposit_630.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (modifier_accrueRewards_610 _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmod | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  Lemma run_fun__withdraw_736_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (caller receiver owner assets shares : U256.t),
    0 <= caller < 2^160 ->
    0 <= receiver < 2^160 ->
    0 <= owner < 2^160 ->
    0 <= assets ->
    0 <= shares ->
    U256.Valid.t assets ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__withdraw_736 caller receiver owner assets shares ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_withdraw_4403 storage_base
                 caller assets receiver owner now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           caller receiver owner assets shares
           H_caller H_receiver H_owner H_assets_nn H_shares_nn
           H_assets_u256 H_mem.
    (** Phase 1: dispatch the modifier sub-axiom. *)
    pose proof (run_modifier_accrueRewards_647_at_storage_base
                  codes env state_base storage_base memory
                  caller receiver owner assets shares
                  H_caller H_receiver H_owner H_assets_nn H_shares_nn
                  H_assets_u256 H_mem)
      as Hmod.
    destruct Hmod as (memory' & Hmod).
    exists memory'.
    (** Phase 2: walk the trivial outer wrapper. *)
    unfold fun__withdraw_736.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (modifier_accrueRewards_647 _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmod | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ===== Post-storage bridge axioms (R094 / R096) =====

      The [mint] and [redeem] composite walkers reduce to the same
      internal helpers as [deposit] and [withdraw] (respectively),
      modulo the [preview_X] argument transformation:
        - [mint shares] = [deposit (previewMint shares) shares]
                          via internal [_deposit_630] body.
        - [redeem shares] = [withdraw (previewRedeem shares) shares]
                            via internal [_withdraw_736] body.

      These bridge axioms equate the sister-walker post-storages with
      their deposit/withdraw counterparts under the preview transform.
      Audit obligation: the Skolem post-states are pinned by these
      equalities so that one bridge axiom (e.g.,
      [proj_post_redeem_4450_observes]) suffices for both mutators. *)
  Axiom proj_post_mint_4356_eq_deposit :
    forall storage_base caller shares receiver now_,
      proj_post_mint_4356 storage_base caller shares receiver now_
      = proj_post_deposit_4312 storage_base caller
          (preview_mint_value storage_base shares) receiver now_.

  Axiom proj_post_redeem_4450_eq_withdraw :
    forall storage_base caller shares receiver owner now_,
      proj_post_redeem_4450 storage_base caller shares receiver owner now_
      = proj_post_withdraw_4403 storage_base caller
          (preview_redeem_value storage_base shares) receiver owner now_.

  (** ----- Composite walker axiom for [fun_deposit_4312] -----

      Body shape (StakingVault_shallow.v:10625-10676):

        S1.  expr_4281 := receiver
             expr_4282 := fun_maxDeposit_4158(receiver)   -- maxDeposit
                                                            view (always
                                                            uint256.max
                                                            in default
                                                            ERC4626)
        S2.  if assets > maxAssets:
               revert ERC4626ExceededMaxDeposit
                                                          (Yul: mstore
                                                            selector +
                                                            abi-encode +
                                                            revert)
        S3.  var_shares_4296 := fun_previewDeposit_4220(assets)
                                                          → convertToShares
                                                            s assets
        S4.  caller := fun__msgSender_14384()             → msg.sender
        S5.  fun__deposit_630(caller, receiver, assets, shares)
                                                          → internal
                                                            _deposit
                                                            override:
              S5a. accrueRewards modifier pre-step
              S5b. totalDeposited += assets
              S5c. nativeBalanceLastKnown += assets
              S5d. super._deposit(caller, receiver, assets, shares):
                     - asset.transferFrom(caller, vault, assets)
                     - _mint(receiver, shares):
                         _update(0, receiver, shares):
                           accrueRewards modifier (already in flight)
                           ERC20: balances[receiver] += shares;
                                  totalSupply += shares
                           Votes.transferVotingUnits(0, receiver, shares)
                           StakingVault._moveOptimisticDelegateVotes(
                             optimisticDelegatees[0],
                             optimisticDelegatees[receiver], shares)
                     - emit Deposit
        S6.  Return shares.

      The post-storage exposed by [proj_post_deposit_4312] is the
      storage_base with:
        - ERC20.balances[receiver]            += shares
        - ERC20.totalSupply                   += shares
        - StakingVault.totalDeposited         += assets + reward-accrual
        - StakingVault.nativeBalanceLastKnown += assets + reward-accrual
        - StakingVault.nativeRewardsLastPaid  := now
        - Votes.delegateCkpt[delegatees[receiver]] += shares-push
        - Votes.total_ckpt                    += shares-push
        - StakingVault.optimisticDelegateCkpt[optimisticDelegatees[
            receiver]] += shares-push (when optimistic delegatee != 0)
        - ReentrancyGuard.status: returns to NotEntered after the call
        - Per-reward-token trackers (owned by #255 — observational-
          bridge captures via storage_base preservation modulo
          accrue effects).
        - External: asset.balanceOf(vault) += assets,
                    asset.balanceOf(caller) -= assets,
                    asset.allowance[caller][vault] -= assets.

      Audit-time witness: the assembly closes mechanically via
      [StaticCallBridge.sc_word] for the asset.transferFrom staticcall,
      [Storage.run_sload_u256] / [Storage.run_sstore_u256] for the
      slot reads/writes (against the [project_exchange] lens of
      Section 2), Votes-side reasoning composes via
      [VotesEquivalence.transferVotingUnits_mint_total] (Wave 1).

      The composite axiom witnesses the existence of the post-memory
      shape and the post-storage; the milestone theorem in Section
      10 consumes it and bridges to the sim-side [deposit] result.

      Task #301 (R096 closure, 2026-06-01): promoted to Qed [Lemma]
      via the R088 trust-redistribution split.  For deposit,
      [fun_maxDeposit_4158] returns the uint256-max constant
      (0xff..ff), so the cap-revert branch is automatically bypassed
      for any valid uint256 assets — no extra precondition beyond
      [U256.Valid.t assets].

      The proof dispatches:
        - [run_fun_maxDeposit_4158_returns] (Hmax — uint256 max).
        - [run_fun_previewDeposit_4220_returns] (Hprev — share preview).
        - [run_fun__msgSender_14384] (Hms — Qed Lemma, caller).
        - [run_fun__deposit_630_at_storage_base] (Hbody — inner _deposit
          composite; R093 SafeERC20.safeTransferFrom consumer inside). *)
  Lemma run_fun_deposit_4312_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (assets receiver : U256.t),
    (* Caller is the msg.sender from the environment. *)
    0 <= env.(Environment.caller) < 2^160 ->
    0 <= assets ->
    0 <= receiver < 2^160 ->
    (* assets fits in uint256. *)
    U256.Valid.t assets ->
    (* Memory has at least two scratch words. *)
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' shares,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_deposit_4312_op assets receiver ⇓
        Result.Ok shares
    | Some (make_state env state_base memory'
              (proj_post_deposit_4312 storage_base
                 env.(Environment.caller) assets receiver
                 now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           assets receiver
           H_caller_bound H_assets_nn H_receiver_bound
           H_assets_u256 H_mem.
    (** Phase 1: dispatch the helper sub-axioms. *)
    pose proof (run_fun_maxDeposit_4158_returns
                  codes env state_base storage_base memory receiver)
      as Hmax.
    pose proof (run_fun_previewDeposit_4220_returns
                  codes env state_base storage_base memory assets)
      as Hprev.
    pose proof (run_fun__msgSender_14384
                  codes env
                  (make_state env state_base memory storage_base))
      as Hms.
    set (shares := preview_deposit_value storage_base assets).
    pose proof (run_fun__deposit_630_at_storage_base
                  codes env state_base storage_base memory
                  env.(Environment.caller) receiver assets shares
                  H_caller_bound H_receiver_bound
                  H_assets_nn
                  ltac:(unfold shares; apply preview_deposit_value_nn)
                  H_assets_u256
                  H_mem)
      as Hbody.
    destruct Hbody as (memory' & Hbody).
    exists memory', shares.
    (** Phase 2: prove the cap-revert is bypassed.  Under
        [H_assets_u256 : U256.Valid.t assets],
        [Pure.gt assets (2^256-1) = 0]. *)
    assert (Hgt_zero :
              Pure.gt assets 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0).
    { unfold Pure.gt.
      destruct (assets >? 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) eqn:Hgtb.
      - exfalso. apply Z.gtb_lt in Hgtb.
        unfold U256.Valid.t in H_assets_u256. lia.
      - reflexivity. }
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_deposit_4312_op, fun_deposit_4312.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_maxDeposit_4158 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmax | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.gt _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.gt, M.pure; p | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_previewDeposit_4220 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hprev | ]
      | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__deposit_630 _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (** Phase 4: cap-revert if-branch — dispatch via [Hgt_zero]. *)
    1: {
      rewrite Hgt_zero.
      unfold Shallow.if_; cbn.
      unfold Shallow.let_state, M.strong_let_; cbn.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (fun_previewDeposit_4220 _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hprev | ]
        | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
            c; [ exact Hms | ]
        | |- {{? _, _, _ |
              LowM.Call (fun__deposit_630 _ _ _ _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hbody | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    }
    (** Phase 6: outer wrapper — return [shares]. *)
    unfold shares.
    apply RunO.Pure.
  Qed.

  (** ----- Composite walker axiom for [fun_mint_4356] -----

      Body shape (StakingVault_shallow.v:13495-13546):

        S1.  expr_4326 := fun_maxMint_4173(receiver)   -- maxMint view
        S2.  if shares > maxShares:
               revert ERC4626ExceededMaxMint
        S3.  var_assets_4340 := fun_previewMint_4236(shares)
                                                       → ceil(shares *
                                                              totalAssets
                                                              / supply)
        S4.  caller := fun__msgSender_14384()
        S5.  fun__deposit_630(caller, receiver, assets, shares)
                                                       (same as deposit's S5)
        S6.  Return assets.

      Difference from deposit: the (assets, shares) pair entering
      [fun__deposit_630] is computed from [shares] via [previewMint]
      (ceiling rounding) rather than from [assets] via
      [previewDeposit] (floor rounding). The sim model is
      [deposit_via_mint] above.

      Post-storage shape: same fields touched as deposit, with
      [assets] = [previewMint s shares].

      Task #301 (R096 closure, 2026-06-01): promoted to Qed [Lemma]
      via the R088 trust-redistribution split.  Same shape as deposit
      (sister walker).  [assets = preview_mint_value storage_base shares]
      via the [proj_post_mint_4356_eq_deposit] bridge axiom. *)
  Lemma run_fun_mint_4356_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (shares receiver : U256.t),
    0 <= env.(Environment.caller) < 2^160 ->
    0 <= shares ->
    0 <= receiver < 2^160 ->
    U256.Valid.t shares ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' assets,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_mint_4356_op shares receiver ⇓
        Result.Ok assets
    | Some (make_state env state_base memory'
              (proj_post_mint_4356 storage_base
                 env.(Environment.caller) shares receiver
                 now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           shares receiver
           H_caller_bound H_shares_nn H_receiver_bound
           H_shares_u256 H_mem.
    (** Phase 1: dispatch the helper sub-axioms. *)
    pose proof (run_fun_maxMint_4173_returns
                  codes env state_base storage_base memory receiver)
      as Hmax.
    pose proof (run_fun_previewMint_4236_returns
                  codes env state_base storage_base memory shares)
      as Hprev.
    pose proof (run_fun__msgSender_14384
                  codes env
                  (make_state env state_base memory storage_base))
      as Hms.
    set (assets := preview_mint_value storage_base shares).
    pose proof (run_fun__deposit_630_at_storage_base
                  codes env state_base storage_base memory
                  env.(Environment.caller) receiver assets shares
                  H_caller_bound H_receiver_bound
                  ltac:(unfold assets; apply preview_mint_value_nn)
                  H_shares_nn
                  ltac:(unfold assets; apply preview_mint_value_valid)
                  H_mem)
      as Hbody.
    destruct Hbody as (memory' & Hbody).
    (** Bridge: [proj_post_mint_4356 = proj_post_deposit_4312 ◦ preview]. *)
    rewrite proj_post_mint_4356_eq_deposit.
    fold assets.
    exists memory', assets.
    (** Phase 2: prove the cap-revert is bypassed.  Under
        [H_shares_u256 : U256.Valid.t shares],
        [Pure.gt shares (2^256-1) = 0]. *)
    assert (Hgt_zero :
              Pure.gt shares 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = 0).
    { unfold Pure.gt.
      destruct (shares >? 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) eqn:Hgtb.
      - exfalso. apply Z.gtb_lt in Hgtb.
        unfold U256.Valid.t in H_shares_u256. lia.
      - reflexivity. }
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_mint_4356_op, fun_mint_4356.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_maxMint_4173 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmax | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.gt _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.gt, M.pure; p | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_previewMint_4236 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hprev | ]
      | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__deposit_630 _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (** Phase 4: cap-revert if-branch — dispatch via [Hgt_zero]. *)
    1: {
      rewrite Hgt_zero.
      unfold Shallow.if_; cbn.
      unfold Shallow.let_state, M.strong_let_; cbn.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (fun_previewMint_4236 _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hprev | ]
        | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
            c; [ exact Hms | ]
        | |- {{? _, _, _ |
              LowM.Call (fun__deposit_630 _ _ _ _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hbody | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    }
    (** Phase 6: outer wrapper — return [assets]. *)
    unfold assets.
    apply RunO.Pure.
  Qed.

  (** ----- Composite walker axiom for [fun_withdraw_4403] -----

      Body shape (StakingVault_shallow.v:16547-16600):

        S1.  expr_4372 := fun_maxWithdraw_4191(owner)  -- maxWithdraw
                                                          view (=
                                                          convertToAssets
                                                          s balanceOf(owner)
                                                          floored)
        S2.  if assets > maxAssets:
               revert ERC4626ExceededMaxWithdraw
        S3.  var_shares_4386 := fun_previewWithdraw_4252(assets)
                                                       → ceil(assets *
                                                              supply /
                                                              totalAssets)
        S4.  caller := fun__msgSender_14384()
        S5.  fun__withdraw_736(caller, receiver, owner, assets,
                               shares):
              S5a. accrueRewards modifier pre-step
              S5b. totalDeposited -= assets
              S5c. nativeBalanceLastKnown -= assets   (redundant; final
                                                       write at S5g)
              S5d. if unstakingDelay = 0:
                     super._withdraw:
                       - if caller != owner:
                           _spendAllowance(owner, caller, shares)
                       - _burn(owner, shares):
                           _update(owner, 0, shares):
                             ERC20: balances[owner] -= shares;
                                    totalSupply -= shares
                             Votes.transferVotingUnits(owner, 0, shares)
                             StakingVault._moveOptimisticDelegateVotes(
                               optimisticDelegatees[owner],
                               optimisticDelegatees[0], shares)
                       - asset.transfer(receiver, assets)
                       - emit Withdraw
                   else (unstakingDelay > 0):
                     - if caller != owner:
                         _spendAllowance(owner, caller, shares)
                     - _burn(owner, shares):
                         _update(owner, 0, shares) (same as above)
                     - SafeERC20.forceApprove(asset, unstakingManager,
                                              assets)
                     - unstakingManager.createLock(receiver, assets,
                                                  now + unstakingDelay)
                     - emit Withdraw
              S5g. nativeBalanceLastKnown := IERC20(asset).balanceOf(vault)
        S6.  Return shares.

      The composite walker axiom captures both branches under a
      single [proj_post_withdraw_4403] Skolem; the observational
      bridge characterises the branch picked via the
      [has_unstakingDelay_zero storage_base] flag.

      Task #299 / R093 closure: the [H_within_max] precondition gates
      the [ERC4626ExceededMaxWithdraw] revert path; this Axiom is
      slated for discharge to a Qed [Lemma] via the new Section 8b
      helper sub-axioms ([run_fun_maxWithdraw_4191_returns],
      [run_fun_previewWithdraw_4252_returns],
      [run_fun__msgSender_14384] Qed, and
      [run_fun__withdraw_736_at_storage_base]).  The pattern follows
      [TimelockControllerOptimistic.v]'s R088 redistribution.

      The discharge proof script (LOC ~150-300) mechanically walks
      the outer wrapper Yul body via the R088 pattern from
      [TimelockControllerOptimistic.v].  The pattern dispatches each
      LowM.Call to its corresponding helper sub-axiom (Hmax / Hprev /
      Hms / Hbody) and handles the [Shallow.if_] cap-revert branch
      via the [H_within_max] precondition.

      See R094 in WISDOM.md for the methodology details, the
      sub-axiom catalogue, and the structural blocker preventing the
      mechanical Qed completion in this task.

      Task #301 (R096 closure, 2026-06-01): promoted to Qed [Lemma]
      via the R088 trust-redistribution split.  The proof script
      dispatches:
        - [run_fun_maxWithdraw_4191_returns] (Hmax — cap-view return).
        - [run_fun_previewWithdraw_4252_returns] (Hprev — share preview).
        - [run_fun__msgSender_14384] (Hms — Qed Lemma, caller).
        - [run_fun__withdraw_736_at_storage_base] (Hbody — inner _withdraw
          composite; R093 SafeERC20.safeTransfer consumer lives inside).

      The [Shallow.if_] cap-revert branch is dispatched via explicit
      [destruct (Pure.gt assets max ...)] under [H_within_max]; the
      lazymatch walker dispatch from TimelockControllerOptimistic does
      NOT walk past this gt-check automatically because the test
      depends on the if's reduction (R096). *)
  Lemma run_fun_withdraw_4403_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (assets receiver owner : U256.t),
    0 <= env.(Environment.caller) < 2^160 ->
    0 <= assets ->
    0 <= receiver < 2^160 ->
    0 <= owner < 2^160 ->
    U256.Valid.t assets ->
    (* Cap-pass precondition: bypasses [ERC4626ExceededMaxWithdraw]. *)
    assets <= max_withdraw_value storage_base owner ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' shares,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_withdraw_4403_op assets receiver owner ⇓
        Result.Ok shares
    | Some (make_state env state_base memory'
              (proj_post_withdraw_4403 storage_base
                 env.(Environment.caller) assets receiver owner
                 now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           assets receiver owner
           H_caller_bound H_assets_nn H_receiver_bound H_owner_bound
           H_assets_u256 H_within_max H_mem.
    (** Phase 1: dispatch the helper sub-axioms. *)
    pose proof (run_fun_maxWithdraw_4191_returns
                  codes env state_base storage_base memory owner)
      as Hmax.
    pose proof (run_fun_previewWithdraw_4252_returns
                  codes env state_base storage_base memory assets)
      as Hprev.
    pose proof (run_fun__msgSender_14384
                  codes env
                  (make_state env state_base memory storage_base))
      as Hms.
    set (shares := preview_withdraw_value storage_base assets).
    pose proof (run_fun__withdraw_736_at_storage_base
                  codes env state_base storage_base memory
                  env.(Environment.caller) receiver owner assets shares
                  H_caller_bound H_receiver_bound H_owner_bound
                  H_assets_nn ltac:(unfold shares; apply preview_withdraw_value_nn)
                  H_assets_u256 H_mem)
      as Hbody.
    destruct Hbody as (memory' & Hbody).
    exists memory', shares.
    (** Phase 2: prove the cap-revert is bypassed.  Under
        [H_within_max : assets <= max], [Pure.gt assets max = 0]. *)
    assert (Hgt_zero : Pure.gt assets (max_withdraw_value storage_base owner) = 0).
    { unfold Pure.gt. destruct (assets >? max_withdraw_value storage_base owner) eqn:Hgtb.
      - exfalso. apply Z.gtb_lt in Hgtb. lia.
      - reflexivity. }
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_withdraw_4403_op, fun_withdraw_4403.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_maxWithdraw_4191 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmax | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.gt _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.gt, M.pure; p | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_previewWithdraw_4252 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hprev | ]
      | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__withdraw_736 _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (** Phase 4: cap-revert if-branch — dispatch via [Hgt_zero]. *)
    1: {
      rewrite Hgt_zero.
      unfold Shallow.if_; cbn.
      unfold Shallow.let_state, M.strong_let_; cbn.
      (** Phase 5: walk the post-cap continuation. *)
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (fun_previewWithdraw_4252 _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hprev | ]
        | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
            c; [ exact Hms | ]
        | |- {{? _, _, _ |
              LowM.Call (fun__withdraw_736 _ _ _ _ _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hbody | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    }
    (** Phase 6: outer wrapper — return [shares]. *)
    unfold shares.
    apply RunO.Pure.
  Qed.

  (** ----- Composite walker axiom for [fun_redeem_4450] -----

      Body shape (StakingVault_shallow.v:14749-14802):

        S1.  expr_4419 := fun_maxRedeem_4204(owner)   -- maxRedeem view
                                                         (= balanceOf(owner))
        S2.  if shares > maxShares:
               revert ERC4626ExceededMaxRedeem
        S3.  var_assets_4433 := fun_previewRedeem_4268(shares)
                                                      → convertToAssets
                                                        s shares
        S4.  caller := fun__msgSender_14384()
        S5.  fun__withdraw_736(caller, receiver, owner, assets, shares)
                                                      (same as
                                                       withdraw's S5)
        S6.  Return assets.

      Same as withdraw, with [assets] = [previewRedeem s shares].

      Task #301 (R096 closure, 2026-06-01): promoted to Qed [Lemma]
      via the R088 trust-redistribution split.  Same shape as withdraw,
      sister walker. *)
  Lemma run_fun_redeem_4450_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (shares receiver owner : U256.t),
    0 <= env.(Environment.caller) < 2^160 ->
    0 <= shares ->
    0 <= receiver < 2^160 ->
    0 <= owner < 2^160 ->
    U256.Valid.t shares ->
    (* Cap-pass precondition: bypasses [ERC4626ExceededMaxRedeem]. *)
    shares <= max_redeem_value storage_base owner ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' assets,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_redeem_4450_op shares receiver owner ⇓
        Result.Ok assets
    | Some (make_state env state_base memory'
              (proj_post_redeem_4450 storage_base
                 env.(Environment.caller) shares receiver owner
                 now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           shares receiver owner
           H_caller_bound H_shares_nn H_receiver_bound H_owner_bound
           H_shares_u256 H_within_max H_mem.
    (** Phase 1: dispatch the helper sub-axioms. *)
    pose proof (run_fun_maxRedeem_4204_returns
                  codes env state_base storage_base memory owner)
      as Hmax.
    pose proof (run_fun_previewRedeem_4268_returns
                  codes env state_base storage_base memory shares)
      as Hprev.
    pose proof (run_fun__msgSender_14384
                  codes env
                  (make_state env state_base memory storage_base))
      as Hms.
    set (assets := preview_redeem_value storage_base shares).
    pose proof (run_fun__withdraw_736_at_storage_base
                  codes env state_base storage_base memory
                  env.(Environment.caller) receiver owner assets shares
                  H_caller_bound H_receiver_bound H_owner_bound
                  ltac:(unfold assets; apply preview_redeem_value_nn)
                  H_shares_nn
                  ltac:(unfold assets; apply preview_redeem_value_valid)
                  H_mem)
      as Hbody.
    destruct Hbody as (memory' & Hbody).
    (** Bridge: [proj_post_redeem_4450 = proj_post_withdraw_4403 ◦ preview]. *)
    rewrite proj_post_redeem_4450_eq_withdraw.
    fold assets.
    exists memory', assets.
    (** Phase 2: prove the cap-revert is bypassed.  Under
        [H_within_max : shares <= max], [Pure.gt shares max = 0]. *)
    assert (Hgt_zero : Pure.gt shares (max_redeem_value storage_base owner) = 0).
    { unfold Pure.gt. destruct (shares >? max_redeem_value storage_base owner) eqn:Hgtb.
      - exfalso. apply Z.gtb_lt in Hgtb. lia.
      - reflexivity. }
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_redeem_4450_op, fun_redeem_4450.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_uint256 _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_maxRedeem_4204 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmax | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ unfold cleanup_t_uint256;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.gt _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.gt, M.pure; p | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_previewRedeem_4268 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hprev | ]
      | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
          c; [ exact Hms | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__withdraw_736 _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (** Phase 4: cap-revert if-branch — dispatch via [Hgt_zero]. *)
    1: {
      rewrite Hgt_zero.
      unfold Shallow.if_; cbn.
      unfold Shallow.let_state, M.strong_let_; cbn.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (fun_previewRedeem_4268 _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hprev | ]
        | |- {{? _, _, _ | LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
            c; [ exact Hms | ]
        | |- {{? _, _, _ |
              LowM.Call (fun__withdraw_736 _ _ _ _ _) _ ⇓ _ | _ ?}} =>
            c; [ exact Hbody | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    }
    (** Phase 6: outer wrapper — return [assets]. *)
    unfold assets.
    apply RunO.Pure.
  Qed.

  (** ====================================================================
      Section 10 — Milestone equivalence theorems (Qed)
      ====================================================================

      Each theorem follows the R065/R066/R067/R070/R071 recipe:

        Phase 1: dispatch the composite walker axiom to obtain the
                 walker-friendly Skolemized post-storage.
        Phase 2: bridge to the sim's post-state via the per-target
                 observational equivalence axiom (where load-bearing)
                 or invoke [storage_equiv_refl] (where the walker's
                 post-state already matches the theorem's reference
                 shape — the case for this scaffold).
        Phase 3: witness the post-storage. *)

  (** ----- run_deposit_equivalent -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      deposit writes only to ERC20 / StakingVault exchange-rate
      slots / Votes checkpoints, so the [slot_AccessControl_roles]
      slot is preserved. This clause makes the bridge axiom
      [proj_post_deposit_4312_observes] load-bearing (it appears
      in [Print Assumptions] of this milestone). *)
  Theorem run_deposit_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (assets receiver : U256.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_assets_nn : 0 <= assets)
      (H_receiver_bound : 0 <= receiver < 2^160)
      (H_assets_u256 : U256.Valid.t assets)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post shares,
      {{? codes, env, Some state |
        fun_deposit_4312_op assets receiver ⇓ Result.Ok shares
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_deposit_4312 storage_base
             env.(Environment.caller) assets receiver now_timestamp) /\
        eq_at_roles storage_post storage_base).
  Proof.
    cbv zeta.
    (* Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun_deposit_4312_at_storage_base
                  codes env state_base storage_base memory
                  assets receiver
                  H_caller_bound H_assets_nn H_receiver_bound
                  H_assets_u256 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & shares & Hwalker).
    (* Phase 2: dispatch the slot-unchanged observational bridge. *)
    pose proof (proj_post_deposit_4312_observes
                  storage_base env.(Environment.caller)
                  assets receiver now_timestamp) as Hobs.
    (* Phase 3: witness post-storage. *)
    exists (Some (make_state env state_base memory'
                    (proj_post_deposit_4312 storage_base
                       env.(Environment.caller) assets receiver
                       now_timestamp))).
    exists (proj_post_deposit_4312 storage_base
              env.(Environment.caller) assets receiver now_timestamp).
    exists shares.
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- run_mint_equivalent -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      mint shares deposit's [_deposit] internal path, so the
      [slot_AccessControl_roles] slot is preserved. *)
  Theorem run_mint_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (shares receiver : U256.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_shares_nn : 0 <= shares)
      (H_receiver_bound : 0 <= receiver < 2^160)
      (H_shares_u256 : U256.Valid.t shares)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post assets,
      {{? codes, env, Some state |
        fun_mint_4356_op shares receiver ⇓ Result.Ok assets
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_mint_4356 storage_base
             env.(Environment.caller) shares receiver now_timestamp) /\
        eq_at_roles storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_mint_4356_at_storage_base
                  codes env state_base storage_base memory
                  shares receiver
                  H_caller_bound H_shares_nn H_receiver_bound
                  H_shares_u256 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & assets & Hwalker).
    pose proof (proj_post_mint_4356_observes
                  storage_base env.(Environment.caller)
                  shares receiver now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_mint_4356 storage_base
                       env.(Environment.caller) shares receiver
                       now_timestamp))).
    exists (proj_post_mint_4356 storage_base
              env.(Environment.caller) shares receiver now_timestamp).
    exists assets.
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- run_withdraw_equivalent -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      withdraw (both unstakingDelay branches) writes only to
      ERC20 / StakingVault exchange-rate slots / Votes
      checkpoints, so the [slot_AccessControl_roles] slot is
      preserved. *)
  Theorem run_withdraw_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (assets receiver owner : U256.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_assets_nn : 0 <= assets)
      (H_receiver_bound : 0 <= receiver < 2^160)
      (H_owner_bound : 0 <= owner < 2^160)
      (H_assets_u256 : U256.Valid.t assets)
      (* Task #299 cap-pass precondition: bypasses
         ERC4626ExceededMaxWithdraw revert path. *)
      (H_within_max : assets <= max_withdraw_value storage_base owner)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post shares,
      {{? codes, env, Some state |
        fun_withdraw_4403_op assets receiver owner ⇓ Result.Ok shares
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_withdraw_4403 storage_base
             env.(Environment.caller) assets receiver owner now_timestamp) /\
        eq_at_roles storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_withdraw_4403_at_storage_base
                  codes env state_base storage_base memory
                  assets receiver owner
                  H_caller_bound H_assets_nn H_receiver_bound
                  H_owner_bound H_assets_u256 H_within_max H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & shares & Hwalker).
    pose proof (proj_post_withdraw_4403_observes
                  storage_base env.(Environment.caller)
                  assets receiver owner now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_withdraw_4403 storage_base
                       env.(Environment.caller) assets receiver owner
                       now_timestamp))).
    exists (proj_post_withdraw_4403 storage_base
              env.(Environment.caller) assets receiver owner now_timestamp).
    exists shares.
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- run_redeem_equivalent -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      redeem shares withdraw's [_withdraw] internal path, so the
      [slot_AccessControl_roles] slot is preserved. *)
  Theorem run_redeem_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (shares receiver owner : U256.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_shares_nn : 0 <= shares)
      (H_receiver_bound : 0 <= receiver < 2^160)
      (H_owner_bound : 0 <= owner < 2^160)
      (H_shares_u256 : U256.Valid.t shares)
      (* Task #299 cap-pass precondition: bypasses
         ERC4626ExceededMaxRedeem revert path. *)
      (H_within_max : shares <= max_redeem_value storage_base owner)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post assets,
      {{? codes, env, Some state |
        fun_redeem_4450_op shares receiver owner ⇓ Result.Ok assets
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_redeem_4450 storage_base
             env.(Environment.caller) shares receiver owner now_timestamp) /\
        eq_at_roles storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_redeem_4450_at_storage_base
                  codes env state_base storage_base memory
                  shares receiver owner
                  H_caller_bound H_shares_nn H_receiver_bound
                  H_owner_bound H_shares_u256 H_within_max H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & assets & Hwalker).
    pose proof (proj_post_redeem_4450_observes
                  storage_base env.(Environment.caller)
                  shares receiver owner now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_redeem_4450 storage_base
                       env.(Environment.caller) shares receiver owner
                       now_timestamp))).
    exists (proj_post_redeem_4450 storage_base
              env.(Environment.caller) shares receiver owner now_timestamp).
    exists assets.
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ====================================================================
      Section 11 — Sim ↔ shallow-form bridge lemmas (Qed)
      ====================================================================

      These connect the sim's [deposit] / [withdraw] / [deposit_via_mint]
      / [withdraw_via_redeem] result shapes to the Skolemized
      post-storages from Section 6. They factor reusable algebraic
      facts into a single place — milestone consumers that need the
      sim-side post-state should compose these with the
      milestone theorems above.

      Note: the actual bridge — equating the
      Skolemized [proj_post_<fn>] with a [project_exchange] of the
      sim's post-state — is the load-bearing audit-time obligation
      and is captured by the [proj_post_<fn>_observes] axioms in
      Section 7. The lemmas below are Qed sim-side properties that
      hold independently of any axiom in this file. *)

  (** ---- 11.1 Deposit / mint preserve the [accumulatedNativeRewards]
            field in the sim ---- *)

  Lemma deposit_preserves_rewards (s : State.t) (assets : U256.t) :
    accumulatedNativeRewards (fst (deposit s assets))
    = accumulatedNativeRewards s.
  Proof. apply deposit_rewards_preserved. Qed.

  Lemma deposit_via_mint_preserves_rewards
      (s : State.t) (shares : U256.t) :
    accumulatedNativeRewards (fst (deposit_via_mint s shares))
    = accumulatedNativeRewards s.
  Proof. unfold deposit_via_mint. apply deposit_rewards_preserved. Qed.

  (** ---- 11.2 Withdraw / redeem preserve rewards on success ---- *)

  Lemma withdraw_via_redeem_success_rewards_preserved
      (s s' : State.t) (shares assets : U256.t) :
    withdraw_via_redeem s shares = Result.Success (s', assets) ->
    accumulatedNativeRewards s' = accumulatedNativeRewards s.
  Proof.
    unfold withdraw_via_redeem.
    destruct (withdraw s (previewRedeem s shares))
      as [pair_inner | p q] eqn:Hw; [|discriminate].
    destruct pair_inner as [s_inner shares_inner].
    intros H. injection H as <- <-.
    apply (withdraw_success_rewards_preserved _ _ _ _ Hw).
  Qed.

  (** ---- 11.3 Round-trip: deposit-then-withdraw from empty state ---- *)

  Lemma deposit_then_withdraw_round_trip_empty
      (assets : U256.t) :
    0 <= assets ->
    let s1 := fst (deposit empty_state assets) in
    let shares := snd (deposit empty_state assets) in
    exists s2,
      withdraw s1 assets = Result.Success (s2, shares)
      /\ s2.(State.totalSupply) = 0
      /\ s2.(State.totalDeposited) = 0.
  Proof.
    intros Ha.
    (* Under the inflation-defended sim:
         deposit empty_state assets yields s1 with
           supply = assets, totalDeposited = assets, ar = 0
           (since convertToShares empty_state assets
            = a * (0+1) / (0+1) = a).
         At s1, totalAssets = assets, and
           shares_calc = (a*(a+1) + a) / (a+1)
                       = ((a+1)*a + a) / (a+1)
                       = a + (a / (a+1))
                       = a + 0 (since a < a+1 for a >= 0)
                       = a.
         So shares = a = totalSupply, post-state has
         supply = deposited = 0. *)
    set (s1 := fst (deposit empty_state assets)).
    set (shares := snd (deposit empty_state assets)).
    cbv zeta.
    assert (Hshares_val : shares = assets).
    { unfold shares, deposit. simpl. apply convertToShares_empty. }
    assert (Hs1_sup : s1.(State.totalSupply) = assets).
    { unfold s1, deposit. simpl. rewrite convertToShares_empty. lia. }
    assert (Hs1_td : s1.(State.totalDeposited) = assets).
    { unfold s1, deposit. simpl. lia. }
    assert (Hs1_ar : accumulatedNativeRewards s1 = 0).
    { unfold accumulatedNativeRewards.
      rewrite Hs1_td.
      assert (Hnbk : s1.(State.nativeBalanceLastKnown) = assets).
      { unfold s1, deposit, empty_state. simpl. lia. }
      rewrite Hnbk.
      destruct (assets >=? assets) eqn:Hgeb.
      - lia.
      - rewrite Z.geb_leb in Hgeb. apply Z.leb_gt in Hgeb. lia. }
    unfold withdraw. unfold totalAssets.
    rewrite Hs1_sup, Hs1_td, Hs1_ar.
    (* Now: ta = assets + 0 = assets, supply = assets. *)
    assert (Hgtb : (assets >? assets + 0) = false).
    { unfold Z.gtb. destruct (Z.compare_spec assets (assets + 0));
        try reflexivity; lia. }
    rewrite Hgtb.
    assert (Hshares_calc :
              (assets * (assets + 1) + (assets + 0)) / (assets + 0 + 1) = assets).
    { replace (assets + 0) with assets by lia.
      replace (assets + 0 + 1) with (assets + 1) by lia.
      (* (a*(a+1) + a) / (a+1) = a + a/(a+1) = a + 0 = a for a >= 0. *)
      rewrite Z.div_add_l with (a := assets) (b := assets + 1) (c := assets)
        by lia.
      destruct (Z.eq_dec assets 0) as [->|Hne].
      - reflexivity.
      - rewrite Z.div_small by lia. lia. }
    assert (Hguard :
              ((assets * (assets + 1) + (assets + 0)) / (assets + 0 + 1) >? assets)
              = false).
    { rewrite Hshares_calc. unfold Z.gtb.
      destruct (Z.compare_spec assets assets); try reflexivity; lia. }
    rewrite Hguard.
    rewrite Hshares_calc.
    eexists. split.
    - rewrite Hshares_val. reflexivity.
    - cbn. split; lia.
  Qed.

  (** ====================================================================
      Section 12 — Cross-cutting validity preservation under the
                  shallow-form bridge
      ====================================================================

      These lemmas state that the sim's [Valid.state] invariant
      survives across the Yul-side operations. They compose with
      the milestone theorems above to give an end-to-end "valid
      pre + composite walker = valid post" property.

      Each is Qed against the sim alone; the equivalence layer
      consumes them via the observational bridge in Section 7.

      Lifted from [proofs/StakingVaultExchange_validity.v]. *)

  Lemma deposit_preserves_validity_via_sim
      (s : State.t) (assets : U256.t) :
    Valid.state s ->
    U256.Valid.t assets ->
    U256.Valid.t (s.(State.totalSupply) + convertToShares s assets) ->
    U256.Valid.t (s.(State.totalDeposited) + assets) ->
    Valid.state (fst (deposit s assets)).
  Proof.
    intros Hv Hassets_u256 Hsupply_bound Htd_bound.
    pose proof (accumulatedNativeRewards_nn s Hv) as Har_nn.
    destruct Hv as [Hsup_u256 Htd_nn Hb_nn Hcov Hbacked].
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
    - lia.
    - lia.
    - intros Hpost_sup_pos.
      destruct (Z.eq_dec s.(State.totalSupply) 0) as [Hs0 | Hs_ne].
      + assert (Hta1_pos : 0 < totalAssets s + 1) by lia.
        assert (Hshares_val : shares = assets / (totalAssets s + 1)).
        { unfold shares, convertToShares. rewrite Hs0.
          f_equal. lia. }
        assert (Hshares_pos : shares >= 1) by lia.
        rewrite Hshares_val in Hshares_pos.
        pose proof (Z.mul_div_le assets (totalAssets s + 1) Hta1_pos) as Hbound.
        assert (Hassets_pos : 0 < assets) by nia.
        lia.
      + assert (Hsup_pos : s.(State.totalSupply) > 0)
          by (destruct Hsup_u256; lia).
        assert (Htd_pos : 0 < s.(State.totalDeposited))
          by (apply Hbacked; lia).
        lia.
  Qed.

  (** ====================================================================
      Section 13 — Cross-mutator monotonicity for the equivalence layer
      ==================================================================== *)

  (** Across any sequence of deposits, the totalDeposited slot is
      monotonically non-decreasing. The composite walker axioms in
      Section 9 imply the sstore writes; this lemma is the sim-side
      shadow. *)
  Lemma deposit_totalDeposited_monotone (s : State.t) (assets : U256.t) :
    0 <= assets ->
    s.(State.totalDeposited) <= (fst (deposit s assets)).(State.totalDeposited).
  Proof. intros Ha. unfold deposit. simpl. lia. Qed.

  (** Across any successful withdrawal with non-negative assets, the
      totalDeposited slot is monotonically non-increasing. *)
  Lemma withdraw_totalDeposited_antimonotone_nn
      (s s' : State.t) (assets shares : U256.t) :
    0 <= assets ->
    withdraw s assets = Result.Success (s', shares) ->
    s'.(State.totalDeposited) <= s.(State.totalDeposited).
  Proof.
    intros Ha Hw.
    pose proof (withdraw_success_deposited_shrinks _ _ _ _ Hw) as Heq.
    rewrite Heq. lia.
  Qed.

  (** Across any sequence of deposits + reward accruals, the
      totalAssets value is monotonically non-decreasing.

      This is the headline "vault is never underwater" property
      promoted to the equivalence layer: post-state totalAssets,
      regardless of which operation is performed (deposit, accrue,
      withdraw with bounded outflow), can be characterised in terms
      of the pre-state totalAssets + the operation's delta. *)
  Lemma totalAssets_after_deposit (s : State.t) (assets : U256.t) :
    0 <= assets ->
    totalAssets (fst (deposit s assets)) = totalAssets s + assets.
  Proof.
    intros Ha.
    pose proof (deposit_rewards_preserved s assets) as Hpres.
    unfold totalAssets in *. unfold deposit. simpl in *. lia.
  Qed.

  (** [totalAssets] after [accrue] grows by [delta] under the validity
      invariant ([balance_covers_deposited]).  Phase B: when [s] is
      "underwater" (the contract should never reach this), the
      saturating [accumulatedNativeRewards] getter clamps growth — but
      [Valid.state] forbids that state. *)
  Lemma totalAssets_after_accrue (s : State.t) (delta now_ : U256.t) :
    Valid.state s ->
    0 <= delta ->
    totalAssets (accrue s delta now_) = totalAssets s + delta.
  Proof.
    intros Hv Hd.
    destruct Hv as [_ _ _ Hcov _].
    unfold accrue, totalAssets, accumulatedNativeRewards. simpl.
    assert (Hpre : s.(State.nativeBalanceLastKnown) >=?
                   s.(State.totalDeposited) = true).
    { apply Z.geb_le. exact Hcov. }
    assert (Hpost : s.(State.nativeBalanceLastKnown) + delta >=?
                    s.(State.totalDeposited) = true).
    { apply Z.geb_le. lia. }
    rewrite Hpre, Hpost. lia.
  Qed.

  (** ====================================================================
      Section 14 — vm_compute cross-checks
      ====================================================================

      Concrete numerical witnesses tying the sim's [deposit] /
      [withdraw] result shapes to the equivalence layer's expected
      transitions. Validates the sim-side reasoning end-to-end. *)

  Module XCheck.

    Definition s0 : State.t := empty_state.
    Definition s1_step : State.t * U256.t := deposit s0 (10^21).
    Definition s1 : State.t := fst s1_step.
    Definition s1_shares : U256.t := snd s1_step.

    Example xcheck_s1_shape :
      s1.(State.totalSupply) = 10^21
      /\ s1.(State.totalDeposited) = 10^21
      /\ accumulatedNativeRewards s1 = 0.
    Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

    Example xcheck_s1_shares_eq_assets :
      s1_shares = 10^21.
    Proof. vm_compute. reflexivity. Qed.

    Example xcheck_previewDeposit_at_s1 :
      previewDeposit s1 (10^18) = 10^18.
    Proof. vm_compute. reflexivity. Qed.

    Example xcheck_previewMint_at_s1 :
      previewMint s1 (10^18) = 10^18.
    Proof. vm_compute. reflexivity. Qed.

    (** Accrue some rewards, then check that previewMint moves
        accordingly. *)
    Definition s2 : State.t := accrue s1 (10^17) 0.

    Example xcheck_totalAssets_at_s2 :
      totalAssets s2 = 10^21 + 10^17.
    Proof. vm_compute. reflexivity. Qed.

    (** With rewards present, previewMint(1e18) > 1e18 (ceil rounding
        + rewards increase the assets-per-share rate). *)
    (** After 10^17 rewards on a 10^21 vault, the ratio is
        (10^21 + 10^17) / 10^21 = 1 + 10^-4. Minting 10^18 shares
        requires ceil((10^18 * (10^21+10^17)) / 10^21) =
        ceil(10^18 + 10^14) = 10^18 + 10^14. Cross-check this
        explicitly by computing the value and comparing. *)
    Example xcheck_previewMint_after_accrue_above_baseline :
      previewMint s2 (10^18) >= 10^18 + 10^14.
    Proof. vm_compute. discriminate. Qed.

    (** previewRedeem(supply) = totalAssets (full redemption returns
        all assets). *)
    Example xcheck_previewRedeem_full_supply :
      previewRedeem s1 (10^21) = 10^21.
    Proof. vm_compute. reflexivity. Qed.

    (** Round-trip floor bound at concrete numbers. *)
    Example xcheck_round_trip_at_s2 :
      convertToAssets s2 (convertToShares s2 (10^18)) <= 10^18.
    Proof. vm_compute. discriminate. Qed.

  End XCheck.

  (** ====================================================================
      Section 15 — Handoff notes
      ====================================================================

      This file scaffolds the four exchange-rate equivalence
      milestones (deposit/mint/withdraw/redeem) against the existing
      sim's [simulations/StakingVaultExchange.v]. The composite
      walker axioms in Section 9 are the audit-time obligations.

      ## Wave 2 in-flight dependencies (parallel agents)

      - **#255 (rewards)**: owns the per-token reward-tracker
        slots (rewardTrackers, userRewardTrackers,
        disallowedRewardTokens, rewardTokenRegistry). These slots
        are touched by the [accrueRewards(caller, receiver)]
        modifier that wraps both [_deposit] and [_withdraw]. The
        observational bridge axioms in Section 7 leave the reward-
        tracker post-state opaque (the Skolemized [proj_post_<fn>]
        carries them); #255's WISDOM/equivalence file lands the
        slot-by-slot bridge that characterises them.

      - **#256 (delegation)**: owns the [_update] override's chain
        into [_moveOptimisticDelegateVotes]. The exchange-rate
        operations all hit [_update] via [_mint] / [_burn]; #256's
        equivalence file characterises the optimistic-delegate
        checkpoint pushes.

      - **#257 (pause/admin)**: owns the role-gated mutators
        ([setUnstakingDelay], [addRewardToken], [removeRewardToken],
        [setRewardRatio], [_authorizeUpgrade]). Orthogonal to
        exchange-rate; the unstakingDelay value read inside
        [_withdraw] (StakingVault.sol:275) is observed via
        [has_unstakingDelay_zero] in Section 8.

      ## Wave 1 closing dependencies

      - **#241 (ERC4626/ERC20Votes)**: when these land, the four
        composite walker axioms can be upgraded to use the slot-
        agnostic helper layer instead of opaque [proj_post_<fn>]
        post-storages. The post-storage shapes would then expose
        ERC20.balances and Votes.checkpoints explicitly.

      - **#240 (Votes)**: already landed (this file Requires
        [proofs/equivalence/Votes.v] for the slot-agnostic
        helpers).

      - **#238 (ReentrancyGuard)**: already landed (this file
        Requires it for the [with_nonReentrant] symbolic shape).

      ## When the shallow form is activated in _RocqProject

      The four [fun_<op>_op] Parameters become Notations aliasing
      the shallow-form definitions; the four composite walker
      axioms then have full mechanical bodies to discharge via the
      R028 walker tactic prelude + per-call-site staticcall +
      sstore + sload bridges. Estimated walker-arm work: ~2000 LOC
      across the four entry points (the ProposalLib /
      TimelockControllerOptimistic R070 envelope sized to
      300-600 LOC per entry point, scaled for the heavier OZ
      inheritance chain).

      ## Trust assumptions per [Print Assumptions]

      Each milestone Qed in Section 10 closes via:
        - the corresponding [run_fun_<op>_at_storage_base] axiom
          (Section 9);
        - the corresponding [proj_post_<fn>_observes] bridge axiom
          (Section 7) — load-bearing post the 2026-05-31 CCV-2
          remediation (promoted from reflexive tautology to a
          slot-indexed [eq_at_roles ... storage_base] claim);
        - [storage_equiv_refl] (Qed lemma in Section 5).

      No additional axioms beyond Section 5/6/7/8/9 declarations.
      Pre-existing trust axioms inherited from the framework:
        - U256.Valid.t structural axioms (Coq stdlib).
        - keccak256_*_bound (Common.v).
        - State.with_current_storage / get_current_storage axioms
          (rocq-of-solidity).
      None of these are exercised by the sim-side Qed lemmas in
      Sections 1, 11, 12, 13.
  *)

End StakingVaultExchangeEquivalence.
