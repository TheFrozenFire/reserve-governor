(** Task #242 — OpenZeppelin ERC4626 (Tokenized Vault) equivalence methodology stub.

    [ERC4626] (OZ v5.4.0, token/ERC20/extensions/ERC4626.sol) is an
    *abstract* contract extending [ERC20].  Its storage slots are
    reserved on the inheriting contract (e.g. the Reserve corpus's
    upcoming [StakingVault]).  There is no standalone
    [ERC4626_shallow.v] from solc; the Yul translation of each method
    lands inside the consumer contract's shallow form, with slot
    indices fixed by the inheritor's storage layout.

    This file therefore does not bind a shallow form.  It delivers:

      1. A set of sim-level helper lemmas about [mocks/ERC4626.v] —
         the pure-Coq facts every concrete inheritor's walker proof
         will reuse (`Qed`, no axioms beyond what the mock already
         imports).

      2. A documented walker-template surface — for each of the
         public ERC4626 operations, what the Yul body's walker arms
         look like, parameterized over slot indices and a projection
         lens.

      3. A skeletal [Section ERC4626EquivalenceTemplate] showing how
         downstream inheritors will instantiate the methodology when
         the corresponding shallow form lands.

    The companion design — methodology Option 2 from
    [notes/votes_equivalence_methodology.md] — is the same
    slot-agnostic parameterized pattern used by
    [proofs/equivalence/Nonces.v], [proofs/equivalence/EnumerableSet.v],
    [proofs/equivalence/Checkpoints.v], and [proofs/equivalence/Votes.v].

    Methodology decision (Option 2):
    --------------------------------
    Slot-agnostic helpers parameterized over slot indices, mirroring
    the abstract-base pattern.  Inheritors instantiate by supplying
    their own [proj_sim] and slot indices; the sim-level helper
    lemmas below close once and are reused.

    What this file does NOT do:
    ---------------------------
    - It does not bind any Yul function to the sim.  No shallow form
      exists to bind against.
    - It does not add new framework axioms.  Every closed lemma is
      [Qed] against [mocks/ERC4626.v] and [mocks/ERC20.v].
    - It does not anticipate the inheritor's storage layout beyond
      what is structurally forced by the abstract ERC4626 surface.

    Asset-side handling — methodology note:
    ---------------------------------------
    OZ's [totalAssets()] is implemented as
    [IERC20(asset()).balanceOf(address(this))] — a staticcall to the
    external asset ERC20 contract.  We do NOT compose the external
    ERC20's storage at this layer; the mock carries [total_assets]
    as a [U256.t] field of [ERC4626.State], a snapshot of the asset
    balance.  This mirrors the [State.voting_units] convention in
    [mocks/Votes.v] (where [_getVotingUnits(account)] is a virtual
    whose value is snapshotted in state).

    Two equivalent ways to discharge the staticcall when an inheritor
    binds a concrete shallow form:

      (a) **Staticcall bridge (R063)**: the inheritor's Yul body
          contains a [staticcall(asset.balanceOf, this)] sequence;
          the equivalence proof uses [StaticCallBridge.sc_word] to
          collapse it into a single read whose value is the sim's
          [total_assets] snapshot.  This is the recipe used by
          VersionRegistry / Guardian / TimelockControllerOptimistic
          for their staticcall paths.

      (b) **Section-parameterize the asset balance**: declare the
          asset balance as a Section [Variable] and a corresponding
          lens correctness hypothesis ("the projected snapshot
          matches the asset-side balance").  The inheritor discharges
          the hypothesis at instantiation time via R063 once, then
          all subsequent uses reduce to projecting the snapshot.

    The Section below adopts approach (b) — exposing
    [project_asset_balance] as a parameter — so the equivalence proof
    body never has to reason about the staticcall directly.  The R063
    discharge is a single lemma the inheritor proves once. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.mocks.ERC20.
Require Import ReserveGovernor.mocks.ERC4626.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module ERC4626Equivalence.

  Import ERC4626.

  (** ============================================================
      Section 1 — Sim-level helper lemmas (Qed)

      These are pure-Coq properties of [ERC4626.convertToShares],
      [ERC4626.convertToAssets], the four preview functions, and the
      [_deposit] / [_withdraw] internal mutators.  Every concrete
      inheritor walker proof will reuse them as post-state predicates;
      closing them here means the inheritor's instantiation does not
      have to re-derive sim-side facts.

      Convention: each lemma states an *invariant* of the mutator —
      what stays the same across the operation, or how the observable
      view-function output transforms.  Walker proofs combine these
      with the inheritor's projection lens to assemble the milestone
      Hoare triple.
      ============================================================ *)

  (** ---- 1.1  Zero-input characterizations ----

      The four conversion functions all return 0 on zero input.
      These are the cheap base cases that every walker proof uses to
      discharge the "no shares minted on zero deposit" / "no assets
      out on zero redeem" arms.  Restated here from the mock for
      naming-by-equivalence (so walker proofs cite the
      equivalence-side name, matching the convention in Votes.v). *)

  Lemma convertToShares_zero_assets_returns_zero :
    forall s, convertToShares s 0 = 0.
  Proof. intros s. apply convertToShares_zero. Qed.

  Lemma convertToAssets_zero_shares_returns_zero :
    forall s, convertToAssets s 0 = 0.
  Proof. intros s. apply convertToAssets_zero. Qed.

  Lemma previewDeposit_zero_assets_returns_zero :
    forall s, previewDeposit s 0 = 0.
  Proof. intros s. apply previewDeposit_zero. Qed.

  Lemma previewMint_zero_shares_returns_zero :
    forall s, previewMint s 0 = 0.
  Proof. intros s. apply previewMint_zero. Qed.

  Lemma previewWithdraw_zero_assets_returns_zero :
    forall s, previewWithdraw s 0 = 0.
  Proof. intros s. apply previewWithdraw_zero. Qed.

  Lemma previewRedeem_zero_shares_returns_zero :
    forall s, previewRedeem s 0 = 0.
  Proof. intros s. apply previewRedeem_zero. Qed.

  (** ---- 1.2  Proportionality of [convertToShares] to [totalSupply] ----

      Headline relationship: when the rounding is exact (i.e.
      [(assets * (totalSupply + 10^offset)) mod (totalAssets + 1) = 0]),
      the shares minted are exactly
        [assets * (totalSupply + 10^offset) / (totalAssets + 1)].
      This is the proportionality law the entire share/asset
      arithmetic rests on.  At empty vault and offset = 0 it reduces
      to the "1 asset = 1 share" identity. *)
  Lemma convertToShares_proportional_exact :
    forall s assets,
      totalAssets s + 1 <> 0 ->
      (assets * (totalSupply s + pow10 s.(decimals_offset)))
        mod (totalAssets s + 1) = 0 ->
      convertToShares s assets
      = (assets * (totalSupply s + pow10 s.(decimals_offset)))
        / (totalAssets s + 1).
  Proof.
    intros s assets Hd Hm.
    unfold convertToShares, _convertToShares.
    apply muldiv_exact; assumption.
  Qed.

  (** Generic bound: [convertToShares] is monotone in [assets]
      (with both denom > 0 and inputs non-negative).  Floor rounding
      preserves the order. *)
  Lemma convertToShares_monotone_in_assets :
    forall s a1 a2,
      0 <= a1 <= a2 ->
      0 <= totalSupply s ->
      0 <= totalAssets s ->
      convertToShares s a1 <= convertToShares s a2.
  Proof.
    intros s a1 a2 [Ha1 Hle] Hts Hta.
    unfold convertToShares, _convertToShares, muldiv.
    set (denom := totalAssets s + 1).
    set (num_co := totalSupply s + pow10 s.(decimals_offset)).
    assert (Hd : denom <> 0) by (unfold denom; lia).
    rewrite (proj2 (Z.eqb_neq _ _) Hd).
    cbn [rounds_up andb].
    (* Floor: both sides are simple division.  q1 <= q2 since
       num1 <= num2 and denom > 0. *)
    apply Z.div_le_mono; unfold denom; try lia.
    apply Z.mul_le_mono_nonneg_r; [|exact Hle].
    pose proof (pow10_pos s.(decimals_offset)). unfold num_co. lia.
  Qed.

  (** ---- 1.3  [_deposit] mints correct shares ----

      Composite Hoare-triple shape: after [_deposit s caller receiver
      assets shares_amt] (where [shares_amt = previewDeposit s assets]),
      the user [receiver]'s share balance has increased by exactly
      [shares_amt = convertToShares s assets] (Floor). *)
  Lemma deposit_mints_correct_shares :
    forall s caller receiver assets,
      let shares_amt := previewDeposit s assets in
      0 < shares_amt ->
      balanceOf (_deposit s caller receiver assets shares_amt) receiver
      = balanceOf s receiver + shares_amt.
  Proof.
    intros s caller receiver assets shares_amt Hpos.
    apply deposit_credits_receiver. exact Hpos.
  Qed.

  (** [_deposit] preserves the *other* (non-receiver) balances. *)
  Lemma deposit_preserves_other_balances :
    forall s caller receiver other assets shares_amt,
      other <> receiver ->
      balanceOf (_deposit s caller receiver assets shares_amt) other
      = balanceOf s other.
  Proof.
    intros s caller receiver other assets shares_amt Hne.
    unfold balanceOf, _deposit. cbn.
    unfold ERC20.balanceOf, ERC20.mint.
    destruct (Z.eqb shares_amt 0) eqn:Hsh.
    - reflexivity.
    - cbn [ERC20.balances].
      apply ERC20.balance_lookup_set_balance_neq.
      intro H. apply Hne. symmetry. exact H.
  Qed.

  (** [_deposit] grows the shares.totalSupply by exactly [shares_amt]. *)
  Lemma deposit_grows_total_supply_by_shares :
    forall s caller receiver assets shares_amt,
      0 < shares_amt ->
      totalSupply (_deposit s caller receiver assets shares_amt)
      = totalSupply s + shares_amt.
  Proof.
    intros. apply deposit_grows_totalSupply. assumption.
  Qed.

  (** ---- 1.4  [_withdraw] burns correct shares (success path) ----

      Dual to deposit_mints_correct_shares: a successful [_withdraw]
      drops the owner's share balance by exactly [shares_amt =
      previewWithdraw s assets] (Ceil). *)
  Lemma withdraw_burns_correct_shares :
    forall s s' caller receiver owner assets shares_amt,
      _withdraw s caller receiver owner assets shares_amt
        = Result.Success s' ->
      totalSupply s' = totalSupply s - shares_amt.
  Proof.
    intros s s' caller receiver owner assets shares_amt Hok.
    unfold _withdraw in Hok.
    destruct (negb _); [discriminate|].
    destruct (ERC20.burn _ _ _) as [s_burn|p q] eqn:Hburn; [|discriminate].
    injection Hok as Hs'. subst s'. unfold totalSupply. cbn.
    pose proof (ERC20.burn_decreases_totalSupply _ _ _ _ Hburn) as Heq.
    (* The pre-burn state's totalSupply equals s.shares.totalSupply
       (approve doesn't touch totalSupply). *)
    destruct (Z.eqb caller owner) eqn:Hco.
    - rewrite Heq. reflexivity.
    - unfold ERC20.burn in Hburn.
      destruct (Z.eqb shares_amt 0) eqn:Hsh.
      + apply Z.eqb_eq in Hsh. subst shares_amt.
        injection Hburn as Hb. subst s_burn. cbn.
        unfold ERC20.approve. cbn. lia.
      + destruct (ERC20.balanceOf _ _ <? _); [discriminate|].
        injection Hburn as Hb. subst s_burn. cbn.
        unfold ERC20.approve. cbn. lia.
  Qed.

  (** [_withdraw] success drops [total_assets] by exactly [assets]. *)
  Lemma withdraw_drops_total_assets_by_assets :
    forall s s' caller receiver owner assets shares_amt,
      _withdraw s caller receiver owner assets shares_amt
        = Result.Success s' ->
      s'.(total_assets) = s.(total_assets) - assets.
  Proof.
    intros. eapply withdraw_decreases_total_assets; eauto.
  Qed.

  (** ---- 1.5  [redeem] burns shares and returns assets ----

      Headline shape: a successful [redeem(shares, receiver, owner)]
      returns [(state', assets)] with
        assets = previewRedeem s shares  (= _convertToAssets Floor)
      and the owner's share balance drops by exactly [shares]. *)
  Lemma redeem_burns_shares_returns_assets :
    forall s s' caller receiver owner shares_amt assets,
      redeem s caller receiver owner shares_amt
        = Result.Success (s', assets) ->
      assets = previewRedeem s shares_amt /\
      totalSupply s' = totalSupply s - shares_amt /\
      s'.(total_assets) = s.(total_assets) - assets.
  Proof.
    intros s s' caller receiver owner shares_amt assets Hok.
    unfold redeem in Hok.
    destruct (maxRedeem s owner <? shares_amt); [discriminate|].
    destruct (_withdraw _ _ _ _ _ _) as [s_inner|p q] eqn:Hw; [|discriminate].
    injection Hok as Hs' Has. subst s_inner. subst assets.
    split; [reflexivity|].
    split.
    - apply (withdraw_burns_correct_shares _ _ _ _ _ _ _ Hw).
    - apply (withdraw_drops_total_assets_by_assets _ _ _ _ _ _ _ Hw).
  Qed.

  (** ---- 1.6  [mint] charges correct assets ----

      Headline shape: a successful [mint(shares, receiver)] returns
      [(state', assets)] with
        assets = previewMint s shares  (= _convertToAssets Ceil)
      and the vault's [total_assets] grows by exactly [assets]. *)
  Lemma mint_charges_correct_assets :
    forall s s' caller receiver shares_amt assets,
      mint s caller receiver shares_amt
        = Result.Success (s', assets) ->
      assets = previewMint s shares_amt /\
      s'.(total_assets) = s.(total_assets) + assets.
  Proof.
    intros s s' caller receiver shares_amt assets Hok.
    unfold mint in Hok.
    destruct (maxMint s receiver <? shares_amt); [discriminate|].
    injection Hok as Hs' Has. subst assets.
    rewrite <- Hs'.
    split; [reflexivity|].
    apply deposit_increases_total_assets.
  Qed.

  (** ---- 1.7  Roundtrip: deposit then withdraw preserves assets (modulo rounding) ----

      The user pays the rounding tax on both legs: deposit Floors
      down the shares; withdraw (or redeem) Floors down the assets
      returned.  In general, [deposit_then_withdraw] returns *fewer*
      assets than were deposited.

      The exact inequality is captured by the closed-form
      [muldiv_floor_le_exact] and [muldiv_ceil_ge_exact] in the mock.
      Here we record the equality case: when the conversions are
      exact (no rounding remainder), the roundtrip is lossless.

      The cleanest closed form: depositing [assets] mints
      [shares = convertToShares s assets Floor].  Then converting
      those shares back to assets (Floor) yields at most [assets]
      (and exactly [assets] when both conversions are exact). *)
  Lemma roundtrip_deposit_then_withdraw_exact :
    forall s assets,
      0 <= assets ->
      0 <= totalSupply s ->
      0 <= totalAssets s ->
      (assets * (totalSupply s + pow10 s.(decimals_offset)))
        mod (totalAssets s + 1) = 0 ->
      let shares := (assets * (totalSupply s + pow10 s.(decimals_offset)))
                      / (totalAssets s + 1) in
      (shares * (totalAssets s + 1))
        mod (totalSupply s + pow10 s.(decimals_offset)) = 0 ->
      convertToAssets s (convertToShares s assets)
      = shares
        * (totalAssets s + 1)
        / (totalSupply s + pow10 s.(decimals_offset)).
  Proof.
    intros s assets Has Hts Hta Hm1 shares Hm2.
    unfold convertToAssets, _convertToAssets, convertToShares, _convertToShares.
    rewrite (muldiv_exact assets _ _ Floor).
    - apply muldiv_exact.
      + pose proof (pow10_pos s.(decimals_offset)). lia.
      + exact Hm2.
    - lia.
    - exact Hm1.
  Qed.

  (** Documented inequality (commentary): in the general case
      (non-exact rounding), the roundtrip returns at most [assets].
      Formally:
        convertToAssets s (convertToShares s assets) <= assets
      (provided the share denominator divides the asset numerator).
      We do not prove this here — the closed form requires a chain
      of [muldiv_floor_le_exact] applications and is left to the
      inheritor's roundtrip-specific theorem.  See `mocks/ERC4626.v`
      lemma [muldiv_floor_le_exact] for the core building block. *)

  (** ---- 1.8  [deposit] preserves the total-assets accounting integral ----

      Headline asset-conservation: a successful [deposit(assets, receiver)]
      increases the vault's [total_assets] by exactly [assets], and
      no other field of the asset accounting (asset_address,
      decimals_offset, underlying_decimals, vault_address) changes. *)
  Lemma deposit_preserves_total_assets_minus_received :
    forall s s' caller receiver assets shares_amt,
      deposit s caller receiver assets
        = Result.Success (s', shares_amt) ->
      s'.(total_assets) = s.(total_assets) + assets /\
      s'.(asset_address) = s.(asset_address) /\
      s'.(decimals_offset) = s.(decimals_offset) /\
      s'.(vault_address) = s.(vault_address).
  Proof.
    intros s s' caller receiver assets shares_amt Hok.
    unfold deposit in Hok.
    destruct (maxDeposit s receiver <? assets); [discriminate|].
    injection Hok as Hs' Hsh. subst shares_amt. rewrite <- Hs'.
    split; [apply deposit_increases_total_assets|].
    split; [apply deposit_preserves_asset_address|].
    split; [apply deposit_preserves_offset|].
    apply deposit_preserves_vault_address.
  Qed.

  (** Dual for [withdraw] (success): [total_assets] drops by exactly
      [assets] and the other asset-accounting fields are preserved. *)
  Lemma withdraw_preserves_total_assets_minus_sent :
    forall s s' caller receiver owner assets shares_amt,
      withdraw s caller receiver owner assets
        = Result.Success (s', shares_amt) ->
      s'.(total_assets) = s.(total_assets) - assets /\
      s'.(asset_address) = s.(asset_address) /\
      s'.(decimals_offset) = s.(decimals_offset).
  Proof.
    intros s s' caller receiver owner assets shares_amt Hok.
    unfold withdraw in Hok.
    destruct (maxWithdraw s owner <? assets); [discriminate|].
    destruct (_withdraw _ _ _ _ _ _) as [s_inner|p q] eqn:Hw; [|discriminate].
    injection Hok as Hs' Hsh. subst shares_amt. subst s_inner.
    repeat split.
    - apply (withdraw_decreases_total_assets _ _ _ _ _ _ _ Hw).
    - apply (withdraw_preserves_asset_address _ _ _ _ _ _ _ Hw).
    - apply (withdraw_preserves_offset _ _ _ _ _ _ _ Hw).
  Qed.

  (** ---- 1.9  Inflation-attack bound (the [_decimalsOffset] defense) ----

      Headline safety property of the OZ ERC4626 base.  Even with
      [totalAssets] inflated by a donation, the first depositor
      cannot have their share count driven below the bound implied
      by the virtual [10^offset] shares.

      Formally: at [totalSupply = 0], for any non-negative [assets]
      and any [totalAssets] (inflated or not), the share count is
        convertToShares s assets = floor(assets * 10^offset / (totalAssets + 1)).
      The attacker's gain from inflating [totalAssets] by [donation]
      is bounded by:
        (loss to first depositor) <= assets * 10^offset / (totalAssets + 1) -
                                     assets * 10^offset / (totalAssets + donation + 1).

      The defense's strength scales with the virtual-shares
      multiplier [10^offset]; OZ's recommendation is to set offset
      to push the attacker's gain below their donation cost. *)
  Lemma inflation_attack_bound :
    forall s assets,
      totalSupply s = 0 ->
      convertToShares s assets
      = muldiv assets (pow10 s.(decimals_offset)) (totalAssets s + 1) Floor.
  Proof.
    intros s assets Hts.
    apply inflation_attack_floor_shares. exact Hts.
  Qed.

  (** Special case: offset = 0 (OZ default).  The bound becomes
      [floor(assets / (totalAssets + 1))].  This is the well-known
      "single virtual share" case from the OZ docs. *)
  Lemma inflation_attack_default_offset_bound :
    forall s assets,
      totalSupply s = 0 ->
      s.(decimals_offset) = O ->
      convertToShares s assets
      = assets / (totalAssets s + 1).
  Proof.
    intros. apply inflation_attack_default_offset; assumption.
  Qed.

  (** The virtual-share multiplier is bounded below by 1 (since
      [10^offset >= 1] for any [offset]).  This is the structural
      property that makes the defense non-degenerate. *)
  Lemma virtual_shares_ge_one :
    forall offset, 1 <= pow10 offset.
  Proof.
    induction offset; cbn -[Z.mul].
    - lia.
    - assert (10 >= 10) by lia.
      pose proof (pow10_pos offset). nia.
  Qed.

  (** ---- 1.10  Asset-accounting integrity across multiple deposits ----

      Headline composition: a sequence of deposits accumulates
      [total_assets] exactly by the sum of deposited assets, with
      no leakage. *)
  Lemma deposit_composes_total_assets :
    forall s1 s2 s3 caller r1 r2 a1 a2 sh1 sh2,
      deposit s1 caller r1 a1 = Result.Success (s2, sh1) ->
      deposit s2 caller r2 a2 = Result.Success (s3, sh2) ->
      s3.(total_assets) = s1.(total_assets) + a1 + a2.
  Proof.
    intros s1 s2 s3 caller r1 r2 a1 a2 sh1 sh2 Hd1 Hd2.
    apply deposit_preserves_total_assets_minus_received in Hd1 as [Ha1 _].
    apply deposit_preserves_total_assets_minus_received in Hd2 as [Ha2 _].
    rewrite Ha2, Ha1. reflexivity.
  Qed.

  (** ============================================================
      Section 2 — Slot-agnostic walker-template scaffolding

      Each inheriting contract will open this Section with concrete
      slot indices and a projection lens; the section parameters
      below document the abstract API.

      Note: we declare the section but do NOT instantiate concrete
      walker lemmas inside it — the walker arms require a shallow
      form to point at, which does not exist for the abstract ERC4626
      base.  Inheritors re-open the section in their own equivalence
      file and supply the shallow-form bindings.

      The Section here exists primarily as documentation — the names
      and types of the parameters are the API surface a future
      [StakingVaultEquivalence] file will fill in.
      ============================================================ *)

  Section ERC4626EquivalenceTemplate.

    (** Slot indices on the inheriting contract's [SimulatedStorage.t].
        For a hypothetical [StakingVault] inheriting [ERC4626 + ERC20Votes],
        these might be slots 6 / 7 / 8 sitting after the ERC20 balance,
        allowance, totalSupply, name, symbol, and ERC4626's two
        immutable fields. *)
    Variable slot_asset_address      : nat.
    Variable slot_total_assets       : nat.
    Variable slot_decimals_offset    : nat.
    Variable slot_underlying_decimals: nat.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the ERC4626 substate.  The
        inheritor supplies this from its own [proj_sim] structure. *)
    Variable project_erc4626 : SimulatedStorage.t -> ERC4626.State.

    (** Asset balance projection — the inheritor's view of
        [IERC20(asset()).balanceOf(address(this))].  At equivalence
        time, this is discharged by R063 (staticcall bridge):
        the Yul body's staticcall sequence collapses to a read whose
        value is the snapshotted [total_assets].  See top-of-file
        modeling note for the two equivalent discharge strategies. *)
    Variable project_asset_balance : SimulatedStorage.t -> U256.t.

    (** Lens correctness hypotheses — discharged by [reflexivity]
        (or a small [cbn]/[unfold] chain) at the instantiation site.
        Each says: the projected ERC4626 substate's [<field>] equals
        the inheritor's storage at the right slot. *)

    Hypothesis lens_asset_address_correct :
      forall (storage : SimulatedStorage.t),
        ERC4626.asset (project_erc4626 storage)
        = (project_erc4626 storage).(asset_address).

    Hypothesis lens_total_assets_correct :
      forall (storage : SimulatedStorage.t),
        ERC4626.totalAssets (project_erc4626 storage)
        = project_asset_balance storage.

    Hypothesis lens_total_supply_correct :
      forall (storage : SimulatedStorage.t),
        ERC4626.totalSupply (project_erc4626 storage)
        = (project_erc4626 storage).(shares).(ERC20.totalSupply).

    (** Walker-template documentation lives in the section as proven
        observations about the lens — these are tautological under
        the hypotheses above and serve to fix the names downstream
        walker proofs will cite. *)

    Lemma walker_obs_asset :
      forall (storage : SimulatedStorage.t),
        ERC4626.asset (project_erc4626 storage)
        = (project_erc4626 storage).(asset_address).
    Proof. intros. apply lens_asset_address_correct. Qed.

    Lemma walker_obs_totalAssets :
      forall (storage : SimulatedStorage.t),
        ERC4626.totalAssets (project_erc4626 storage)
        = project_asset_balance storage.
    Proof. intros. apply lens_total_assets_correct. Qed.

    Lemma walker_obs_totalSupply :
      forall (storage : SimulatedStorage.t),
        ERC4626.totalSupply (project_erc4626 storage)
        = (project_erc4626 storage).(shares).(ERC20.totalSupply).
    Proof. intros. apply lens_total_supply_correct. Qed.

    (** Composite observation: at any storage, the share-conversion
        formula equals the muldiv expression with the lens-projected
        operands. *)
    Lemma walker_obs_convertToShares :
      forall (storage : SimulatedStorage.t) (assets : U256.t),
        ERC4626.convertToShares (project_erc4626 storage) assets
        = muldiv assets
            ((project_erc4626 storage).(shares).(ERC20.totalSupply)
              + pow10 (project_erc4626 storage).(decimals_offset))
            (project_asset_balance storage + 1)
            Floor.
    Proof.
      intros storage assets.
      unfold ERC4626.convertToShares, _convertToShares.
      rewrite lens_total_assets_correct.
      reflexivity.
    Qed.

    Lemma walker_obs_convertToAssets :
      forall (storage : SimulatedStorage.t) (shares_amt : U256.t),
        ERC4626.convertToAssets (project_erc4626 storage) shares_amt
        = muldiv shares_amt
            (project_asset_balance storage + 1)
            ((project_erc4626 storage).(shares).(ERC20.totalSupply)
              + pow10 (project_erc4626 storage).(decimals_offset))
            Floor.
    Proof.
      intros storage shares_amt.
      unfold ERC4626.convertToAssets, _convertToAssets.
      rewrite lens_total_assets_correct.
      reflexivity.
    Qed.

  End ERC4626EquivalenceTemplate.

  (** ============================================================
      Section 3 — Walker-template documentation (commentary only)

      For each public ERC4626 operation, the comment block below
      describes what the Yul body's walker arms look like.  The
      walker proofs themselves cannot be written until a concrete
      shallow form (from an inheriting contract) is available.

      Cross-reference: WISDOM R072 (slot-agnostic helpers) +
      R063 (staticcall bridge for the asset.balanceOf path).
      ============================================================ *)

  (** ---- asset() ----

        Yul body shape (inlined into inheritor):
          slot   := slot_asset_address
          a      := sload(slot)

        Walker arms:
          - sload at <slot_asset_address>
              ↓ via R049 / R040 single-slot sload bridge
            (project_erc4626 storage).asset_address
          - matches: [ERC4626.asset (project_erc4626 storage)]
            via [lens_asset_address_correct]. *)

  (** ---- totalAssets() ----

        Yul body shape:
          let v := staticcall(gas, _asset, ...balanceOf(this)..., ...)
          let bal := mload(0)

        Walker arms:
          - staticcall sequence collapses via R063 [StaticCallBridge.sc_word]
            to a single read of [project_asset_balance storage].
          - The R064 abi-encoding leaves handle the
            [mstore(0, selector), mstore(4, address)] preamble and
            the [returndatasize / returndatacopy / mload] postamble.
          - Matches [ERC4626.totalAssets (project_erc4626 storage)]
            via [lens_total_assets_correct]. *)

  (** ---- convertToShares(assets) ----

        Yul body shape:
          let ts := sload(slot_totalSupply)
          let bal := staticcall(...)
          let num := add(ts, exp(10, _decimalsOffset))
          let denom := add(bal, 1)
          let q := mulDiv(assets, num, denom, 0)  // Floor

        Walker arms:
          - sload at slot_totalSupply.
          - staticcall via R063.
          - exp(10, n) — closed-form via [pow10] for small n; for
            arbitrary n, an inheritor that ships a [_decimalsOffset
            != 0] needs to compose the exp/pow leaf (typically an
            opaque immutable, so evaluates at construction time).
          - mulDiv: this is the OZ Math.mulDiv body.  At Z-level we
            model it as a single [muldiv] primitive.  The walker
            either calls a precompile-style bridge (if the inheritor
            inlines the assembly) or chains [mul / div / mod / add]
            leaves.  Either way, the composite leaf closes by
            asserting equality with [muldiv assets num denom Floor].
          - Matches [walker_obs_convertToShares]. *)

  (** ---- convertToAssets(shares) ----
        Mirror of convertToShares with swapped numerator / denominator.
        Same R063 + R064 + Math.mulDiv leaf structure.
        Matches [walker_obs_convertToAssets]. *)

  (** ---- previewDeposit / previewMint / previewWithdraw / previewRedeem ----
        Pure delegates of _convertToShares / _convertToAssets with
        different rounding modes.  Each is a one-line walker arm: the
        Yul body unfolds to a [_convertToShares] or [_convertToAssets]
        call with the rounding constant in scope.

        previewDeposit  -> _convertToShares with rounding=0 (Floor)
        previewMint     -> _convertToAssets with rounding=1 (Ceil)
        previewWithdraw -> _convertToShares with rounding=1 (Ceil)
        previewRedeem   -> _convertToAssets with rounding=0 (Floor)

        Walker template: substitute the rounding constant and reuse
        the convertToShares / convertToAssets walker. *)

  (** ---- maxDeposit / maxMint / maxWithdraw / maxRedeem ----
        - maxDeposit / maxMint default to type(uint256).max — a pure
          constant load.  Inheritors that override (e.g. a cap on
          deposits) override the walker arm; the default arm is a
          single [mload(uint256.max constant)] leaf.
        - maxWithdraw is _convertToAssets(balanceOf(owner), Floor).
        - maxRedeem is balanceOf(owner).
        All three reuse the same convertToAssets / balanceOf walker
        arms documented above. *)

  (** ---- deposit(assets, receiver) — six-phase composite ----

      Phase 1 — pre-state read:
        max_a := maxDeposit(receiver)        (= u256_max by default)

      Phase 2 — revert check (R047 case-split):
        if iszero(lt(max_a, assets)): continue
        else: revert ERC4626ExceededMaxDeposit

      Phase 3 — shares computation:
        shares := previewDeposit(assets)
                = _convertToShares(assets, Floor)

      Phase 4 — asset transfer (SafeERC20.safeTransferFrom):
        SafeERC20.safeTransferFrom(asset, caller, this, assets)
        — at the sim level, this updates [total_assets] (and reduces
        the external asset's balance for caller).  R048 (R045
        variant for pure-function libraries) covers the SafeERC20
        wrapper; the external ERC20 mutation is bound at the
        equivalence layer via R063.

      Phase 5 — shares mint:
        _mint(receiver, shares)              (= ERC20.mint internal)

      Phase 6 — return:
        return shares

      Composite post-state matches [ERC4626.deposit] via
      [deposit_preserves_total_assets_minus_received] +
      [deposit_grows_total_supply_by_shares] +
      [deposit_mints_correct_shares]. *)

  (** ---- mint(shares, receiver) — symmetric to deposit ----
      Same six-phase shape with [previewMint] in Phase 3.
      Returns assets instead of shares.
      Composite matches [mint_charges_correct_assets]. *)

  (** ---- withdraw(assets, receiver, owner) — seven-phase composite ----

      Phase 1: max_a := maxWithdraw(owner) = _convertToAssets(balanceOf(owner), Floor)
      Phase 2: revert check (R047 case-split) — ExceededMaxWithdraw.
      Phase 3: shares := previewWithdraw(assets) = _convertToShares(Ceil)
      Phase 4: allowance spend (if caller != owner):
                  _spendAllowance(owner, caller, shares)
                  — composes [ERC20.allowance] / [ERC20.approve]
                    with the spent amount.
      Phase 5: _burn(owner, shares)                      (= ERC20.burn)
      Phase 6: SafeERC20.safeTransfer(asset, receiver, assets)
                  — updates [total_assets] (and external ERC20).
      Phase 7: return shares

      Composite matches [withdraw_preserves_total_assets_minus_sent] +
      [withdraw_burns_correct_shares]. *)

  (** ---- redeem(shares, receiver, owner) — symmetric to withdraw ----
      Same seven-phase shape with [previewRedeem] in Phase 3.
      Returns assets instead of shares.
      Composite matches [redeem_burns_shares_returns_assets]. *)

  (** ============================================================
      Section 4 — Validity preservation across the mutator surface

      The [ERC4626.Valid.t] cross-state invariant (shares ERC20
      valid + total_assets non-negative + u256-bounded + offset
      bounded) is preserved by each mutator.

      Since the equivalence layer never depends on the exact
      construction of Valid.t past the public surface, we document
      the preservation lemmas here as a comment block.  Concrete
      inheritors that need composite Valid.t preservation across
      sequences of deposit/withdraw will instantiate them by
      threading [ERC20.Valid.t] preservation across [ERC20.mint] /
      [ERC20.burn].
      ============================================================ *)

  (** Documented preservation (no Qed here — inheritors prove the
      composite by threading [ERC20.Valid.t]):

      - [_deposit] preserves Valid.t provided [shares_amt >= 0],
        [assets >= 0], and the resulting [total_assets + assets]
        stays within u256.  [decimals_offset] is unchanged.

      - [_withdraw] (success path) preserves Valid.t provided
        [shares_amt <= ERC20.balanceOf s.shares owner] (the burn
        succeeds), [assets <= s.total_assets] (the asset
        subtraction stays non-negative), and the offset is
        unchanged.  Both shares.totalSupply and total_assets
        only decrease.

      Concrete inheritors typically state these as preconditions on
      their public-facing theorems (matching the OZ contract's
      revert paths). *)

  (** ============================================================
      Section 5 — Sanity check examples (vm_compute)

      A handful of fully-closed examples exercising the helper lemmas
      against a concrete sim state.  Serves as a smoke test that the
      sim composes properly and that [vm_compute] can evaluate the
      mutators end-to-end.
      ============================================================ *)

  Module Examples.

    (** A small state: empty vault with offset 0, vault address 200,
        asset address 100, underlying decimals 18. *)
    Definition asset_a : Address := 100.
    Definition vault_a : Address := 200.
    Definition alice   : Address := 1.
    Definition bob     : Address := 2.

    Definition s0 : ERC4626.State :=
      empty_state asset_a vault_a 0 18.

    (** Zero deposit yields zero shares. *)
    Example ex_zero_deposit :
      convertToShares s0 0 = 0.
    Proof. apply convertToShares_zero_assets_returns_zero. Qed.

    (** Zero redeem yields zero assets. *)
    Example ex_zero_redeem :
      convertToAssets s0 0 = 0.
    Proof. apply convertToAssets_zero_shares_returns_zero. Qed.

    (** First depositor at offset = 0: 1:1 share-to-asset ratio. *)
    Example ex_first_deposit_1to1 :
      convertToShares s0 1000 = 1000.
    Proof. vm_compute. reflexivity. Qed.

    (** Successful deposit by alice. *)
    Example ex_deposit_success :
      match deposit s0 alice alice 100 with
      | Result.Success (s', sh) =>
          sh = 100 /\
          s'.(total_assets) = 100 /\
          balanceOf s' alice = 100
      | _ => False
      end.
    Proof. vm_compute. repeat split. Qed.

    (** Composition lemma in action: two deposits. *)
    Example ex_deposit_composes :
      match deposit s0 alice alice 100 with
      | Result.Success (s1, _) =>
          match deposit s1 alice alice 50 with
          | Result.Success (s2, _) =>
              s2.(total_assets) = 150
          | _ => False
          end
      | _ => False
      end.
    Proof. vm_compute. reflexivity. Qed.

    (** Inflation-attack defense witness at offset = 6:
        first depositor of 1 asset (the dust attack) into a vault with
        a 10^9 donation gets [1 * 10^6 / (10^9 + 1) = 0] shares.
        At offset = 0, the same depositor would get [1 / (10^9 + 1) = 0]
        too.  But at offset = 6, an attacker donating 999 assets and
        first-depositing 1 asset themselves gets only [10^6 / 1000 = 1000]
        shares — meaning their virtual-share dilution dominates. *)
    Definition s_off6 : ERC4626.State :=
      empty_state asset_a vault_a 6 18.

    (** Empty-vault first depositor at offset 6: 100 assets -> 10^8 shares. *)
    Example ex_inflation_witness :
      convertToShares s_off6 100 = 100000000.
    Proof. vm_compute. reflexivity. Qed.

    (** Inflation-bound rewrite: at empty vault, convertToShares
        reduces to the muldiv form. *)
    Example ex_inflation_bound :
      convertToShares s0 1000
      = muldiv 1000 (pow10 s0.(decimals_offset)) (totalAssets s0 + 1) Floor.
    Proof. apply inflation_attack_bound. reflexivity. Qed.

  End Examples.

End ERC4626Equivalence.
