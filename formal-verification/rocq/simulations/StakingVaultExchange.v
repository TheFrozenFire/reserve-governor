(** StakingVault — ERC4626 exchange-rate surface.

    Mirrors contracts/staking/StakingVault.sol's `totalAssets`,
    `convertToShares`, `convertToAssets`, `deposit`, and `withdraw`
    paths. The native-rewards accrual computation
    [_currentAccountedNativeRewards] involves a discrete exponential
    that's painful to reason about in Rocq; here we abstract reward
    accrual as a non-negative delta the caller supplies. The actual
    decay model is validated separately in the CAS witness corpus
    (cas/staking_vault/exchange_rate.gp INV-1..INV-6).

    The headline theorems this file enables:

      1. Share-value monotonicity: totalAssets / supply is
         non-decreasing under any sequence of reward accruals.

      2. Round-trip rounding bound: convertToAssets(convertToShares(a))
         <= a for any (a, totalAssets, supply) with supply > 0.

      3. Deposit accounting: after deposit(assets, receiver) succeeds,
         totalDeposited' = totalDeposited + assets and the receiver's
         share balance increased by the conversion result.

    [block.timestamp] and reward decay are out of scope — see the
    integration proof for the coupling between this surface and the
    native-rewards accrual layer.

    ## Phase B extension (Task #310, R106)

    To unblock the modifier-wrapper Axiom discharge under R101 the
    sim's [State.t] is widened to model the additional storage slots
    that the [accrueRewards] modifier writes:

      - [nativeBalanceLastKnown]  (slot 13 / 0x0d) — the raw asset
        balance of the vault, written by the [_deposit] inner body and
        by [_accrueRewards] after iterating over reward tokens.  In
        OZ-base semantics this is [asset.balanceOf(vault)] frozen at
        the end of the previous operation.  The sim previously
        modelled this as a derived quantity
        ([totalDeposited + accumulatedNativeRewards]); the extension
        flips it to a PRIMARY field and demotes
        [accumulatedNativeRewards] to a derived getter
        [accumulatedNativeRewards s = nativeBalanceLastKnown s -
         totalDeposited s] (saturating at 0).
      - [nativeRewardsLastPaid]  (slot 14 / 0x0e) — the block
        timestamp at which the last reward accrual was performed.
        Written by [_accrueRewards] at the end of every modifier
        invocation.

    Mapping-style storage (per-token reward trackers, ERC20 balances,
    Votes delegate checkpoints, optimistic-delegate checkpoints) is
    NOT primary in the sim — those substates are carried opaquely
    through [storage_base] in the equivalence layer.  See
    [proofs/equivalence/StakingVaultExchange.v] Section 2b for the
    projection lens that pins these slots as untouched-by-construction
    at the lens slots.

    Backwards compatibility: the previous 3-field shape is preserved
    as the wave of headline audit theorems — [totalSupply],
    [totalDeposited], [accumulatedNativeRewards] all remain accessible
    via the same name.  [accumulatedNativeRewards] is now a Definition
    rather than a record projection. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module StakingVaultExchange.

Definition SCALAR : Z := 10 ^ 18.

(** Share supply, total deposited, raw asset balance snapshot, and
    last-paid timestamp.  Phase B extension widens this from the
    R101 3-field shape; see file docstring for the motivation. *)
Module State.
  Record t : Set := {
    totalSupply              : U256.t;
    totalDeposited           : U256.t;   (** {asset} *)
    nativeBalanceLastKnown   : U256.t;   (** {asset} — asset.balanceOf(vault)
                                             snapshot, slot 13 / 0x0d *)
    nativeRewardsLastPaid    : U256.t;   (** {s} — timestamp of last
                                             accrual, slot 14 / 0x0e *)
  }.
End State.

(** Lazily-accrued native rewards balance — DERIVED from the raw
    [nativeBalanceLastKnown] and [totalDeposited].  The contract
    computes this in [_currentAccountedNativeRewards] as
    [nativeBalanceLastKnown - totalDeposited] then applies the
    half-life decay factor.  The sim exposes the un-decayed gap:
    callers requiring the decayed value pair this with the CAS
    witness for the bound. *)
Definition accumulatedNativeRewards (s : State.t) : U256.t :=
  if s.(State.nativeBalanceLastKnown) >=? s.(State.totalDeposited)
  then s.(State.nativeBalanceLastKnown) - s.(State.totalDeposited)
  else 0.

Definition empty_state : State.t := {|
  State.totalSupply              := 0;
  State.totalDeposited           := 0;
  State.nativeBalanceLastKnown   := 0;
  State.nativeRewardsLastPaid    := 0;
|}.

Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** [totalAssets] override: totalDeposited plus any accrued native
    rewards. Source: StakingVault.sol#L235-L242 (`totalAssets() +
    _currentAccountedNativeRewards()`).

    Under the Phase B sim this is equivalently
    [max nativeBalanceLastKnown totalDeposited]: if the asset
    balance has dropped below [totalDeposited] (which shouldn't
    happen under honest operation), [totalAssets] floors at
    [totalDeposited] via the [accumulatedNativeRewards] cutoff. *)
Definition totalAssets (s : State.t) : U256.t :=
  s.(State.totalDeposited) + accumulatedNativeRewards s.

(** OZ ERC4626 conversion — inflation-defended form (floor rounding).

    OpenZeppelin v5.4 IERC4626 uses the "virtual shares / virtual
    assets" trick (ERC4626.sol L225-234):

      shares = mulDiv(assets,
                      totalSupply + 10^offset,
                      totalAssets + 1,
                      Floor)
      assets = mulDiv(shares,
                      totalAssets + 1,
                      totalSupply + 10^offset,
                      Floor)

    [StakingVault.sol] does NOT override [_decimalsOffset()], so the
    offset is 0 and [10^offset = 1]. Both denominators are therefore
    always >= 1 — no supply==0 special case is needed. The +1 on the
    asset side and +1 on the share side together defend against the
    classic "donate to inflate" first-depositor attack: the attacker
    cannot get an unbounded share-per-asset rate even by donating
    assets to a freshly initialized vault.

    Source: openzeppelin-contracts/contracts/token/ERC20/extensions/
    ERC4626.sol#L225-L234 (v5.4). *)
Definition convertToShares (s : State.t) (assets : U256.t) : U256.t :=
  let ta := totalAssets s in
  (assets * (s.(State.totalSupply) + 1)) / (ta + 1).

Definition convertToAssets (s : State.t) (shares : U256.t) : U256.t :=
  let ta := totalAssets s in
  (shares * (ta + 1)) / (s.(State.totalSupply) + 1).

(** [deposit(assets, _)] — increases [totalDeposited] and mints
    [convertToShares] shares.  Per the Solidity override
    (StakingVault.sol#L252-L261), [_deposit] also bumps
    [nativeBalanceLastKnown += assets] before delegating to the OZ
    base [super._deposit] (which performs the asset transferFrom and
    share mint).  The asset transfer at the EVM level reflects in
    [asset.balanceOf(vault)] which the contract re-snapshots in the
    accrueRewards modifier; under steady-state operation the post-
    deposit [nativeBalanceLastKnown] therefore equals
    [pre.nativeBalanceLastKnown + assets].

    [nativeRewardsLastPaid] is set by the modifier's accrual sweep to
    [now]; the [accrue] helper below models that path.  [deposit]
    leaves the timestamp untouched on the assumption it's invoked
    AFTER the accrual sweep within a single transaction; see
    [proofs/equivalence/StakingVaultExchange.v] Section 6 for the
    composed shape. *)
Definition deposit (s : State.t) (assets : U256.t) : State.t * U256.t :=
  let shares := convertToShares s assets in
  ({|
    State.totalSupply              := s.(State.totalSupply) + shares;
    State.totalDeposited           := s.(State.totalDeposited) + assets;
    State.nativeBalanceLastKnown   := s.(State.nativeBalanceLastKnown) + assets;
    State.nativeRewardsLastPaid    := s.(State.nativeRewardsLastPaid);
  |}, shares).

(** [withdraw(assets, _)] — decreases [totalDeposited] by [assets]
    and burns the equivalent shares. Reverts if [assets > totalAssets]
    (the OZ default) or if the share burn would exceed [totalSupply]
    (which would revert via ERC20 [_burn] in the contract).

    OZ [previewWithdraw] uses ceiling division of the inflation-defended
    form:

      shares = ceil(assets * (totalSupply + 1) / (totalAssets + 1))
             = (assets * (totalSupply + 1) + totalAssets) / (totalAssets + 1)

    With the +1 in the denominator, division is always well-defined —
    no supply==0 branch needed. The virtual-share offset is asymmetric
    under ceil rounding: trying to withdraw the *entire* totalAssets
    requires burning more than totalSupply, so even a single-holder
    fully-funded vault cannot drain to zero in one withdraw. This is
    the OZ inflation-attack defense surfacing as a guard, not a
    departure from spec.

    Per the Solidity override (StakingVault.sol#L266-L293):
    [nativeBalanceLastKnown -= assets] happens unconditionally
    pre-super-call, and the contract then re-snapshots
    [nativeBalanceLastKnown = asset.balanceOf(this)] at the end.
    Under steady-state operation the final balance equals
    [pre.nativeBalanceLastKnown - assets] (for the unstakingDelay = 0
    path) or [pre.nativeBalanceLastKnown - assets] also under
    unstakingDelay > 0 (the forceApprove + createLock pulls the same
    assets into the UnstakingManager).  We model the final write as
    [pre - assets]. *)
Definition withdraw (s : State.t) (assets : U256.t) : Result.t (State.t * U256.t) :=
  let ta := totalAssets s in
  if assets >? ta then
    Result.Revert 0 32
  else
    let supply := s.(State.totalSupply) in
    let shares := (assets * (supply + 1) + ta) / (ta + 1) in
    if shares >? supply then
      Result.Revert 0 32
    else
      Result.Success
        ({|
          State.totalSupply              := s.(State.totalSupply) - shares;
          State.totalDeposited           := s.(State.totalDeposited) - assets;
          State.nativeBalanceLastKnown   := s.(State.nativeBalanceLastKnown) - assets;
          State.nativeRewardsLastPaid    := s.(State.nativeRewardsLastPaid);
        |}, shares).

(** Reward accrual — an abstract non-negative delta added to the
    raw [nativeBalanceLastKnown] (the asset balance grew by [delta]
    via external donation / reward inflow).  Sets
    [nativeRewardsLastPaid := now_].  Since [accumulatedNativeRewards]
    is now derived from [nativeBalanceLastKnown - totalDeposited],
    this preserves the semantics of the old 3-field sim where
    [accumulatedNativeRewards] grew directly.

    The actual delta is computed by [_calculateHandout] in the
    contract; that computation's bounds are validated by the CAS
    witness corpus. *)
Definition accrue (s : State.t) (delta now_ : U256.t) : State.t :=
  {|
    State.totalSupply              := s.(State.totalSupply);
    State.totalDeposited           := s.(State.totalDeposited);
    State.nativeBalanceLastKnown   := s.(State.nativeBalanceLastKnown) + delta;
    State.nativeRewardsLastPaid    := now_;
  |}.

(** Convenience constructor: build a sim from the 3 headline fields
    (totalSupply / totalDeposited / accumulatedNativeRewards) while
    leaving [nativeRewardsLastPaid] at 0.  This mirrors the
    pre-Phase-B sim constructor used by the headline audit theorems
    in [proofs/StakingVaultExchange*.v]. *)
Definition make
    (totalSupply totalDeposited accumulatedNativeRewards : U256.t) : State.t :=
  {|
    State.totalSupply              := totalSupply;
    State.totalDeposited           := totalDeposited;
    State.nativeBalanceLastKnown   := totalDeposited + accumulatedNativeRewards;
    State.nativeRewardsLastPaid    := 0;
  |}.

(** Round-trip lemma: [make] inverts the derived getter. *)
Lemma accumulatedNativeRewards_make
    (sup td anr : U256.t) (Hanr : 0 <= anr) :
  accumulatedNativeRewards (make sup td anr) = anr.
Proof.
  unfold accumulatedNativeRewards, make. simpl.
  destruct (td + anr >=? td) eqn:Hgeb.
  - apply Z.geb_le in Hgeb. lia.
  - exfalso.
    rewrite Z.geb_leb in Hgeb. apply Z.leb_gt in Hgeb. lia.
Qed.

Module Valid.
  Record state (s : State.t) : Prop := {
    supply_u256  : U256.Valid.t s.(State.totalSupply);
    deposited_nn : 0 <= s.(State.totalDeposited);
    balance_nn   : 0 <= s.(State.nativeBalanceLastKnown);
    (** Asset-balance solvency: the asset balance is at least the
        sum of deposits.  Reward accrual only adds; legitimate
        operations never push [nativeBalanceLastKnown] below
        [totalDeposited]. *)
    balance_covers_deposited :
      s.(State.totalDeposited) <= s.(State.nativeBalanceLastKnown);
    (** When supply > 0, totalDeposited must be > 0 — there's at
        least one user's deposit backing the shares. *)
    backed       : s.(State.totalSupply) > 0 -> 0 < s.(State.totalDeposited);
  }.
End Valid.

(** Under [Valid.state], [accumulatedNativeRewards] is non-negative.
    Audit-bridge: existing claims about the old 3-field sim's
    [State.accumulatedNativeRewards] field non-negativity now follow
    from [Valid.state] + this Lemma. *)
Lemma accumulatedNativeRewards_nn (s : State.t) :
  Valid.state s ->
  0 <= accumulatedNativeRewards s.
Proof.
  intros Hv.
  destruct Hv as [_ _ _ Hcov _].
  unfold accumulatedNativeRewards.
  destruct (s.(State.nativeBalanceLastKnown) >=? s.(State.totalDeposited)) eqn:Hb.
  - apply Z.geb_le in Hb. lia.
  - lia.
Qed.

End StakingVaultExchange.
