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
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module StakingVaultExchange.

Definition SCALAR : Z := 10 ^ 18.

(** Share supply, total deposited, and the running accumulated reward
    balance that gets added into totalAssets via the override. *)
Module State.
  Record t : Set := {
    totalSupply              : U256.t;
    totalDeposited           : U256.t;   (** {asset} *)
    accumulatedNativeRewards : U256.t;   (** {asset}, lazily added *)
  }.
End State.

Definition empty_state : State.t := {|
  State.totalSupply              := 0;
  State.totalDeposited           := 0;
  State.accumulatedNativeRewards := 0;
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
    _currentAccountedNativeRewards()`). *)
Definition totalAssets (s : State.t) : U256.t :=
  s.(State.totalDeposited) + s.(State.accumulatedNativeRewards).

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
    [convertToShares] shares. The actual ERC20 transfer is modeled
    abstractly (storage-side only). *)
Definition deposit (s : State.t) (assets : U256.t) : State.t * U256.t :=
  let shares := convertToShares s assets in
  ({|
    State.totalSupply              := s.(State.totalSupply) + shares;
    State.totalDeposited           := s.(State.totalDeposited) + assets;
    State.accumulatedNativeRewards := s.(State.accumulatedNativeRewards);
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
    departure from spec. *)
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
          State.accumulatedNativeRewards := s.(State.accumulatedNativeRewards);
        |}, shares).

(** Reward accrual — an abstract non-negative delta added to the
    running [accumulatedNativeRewards]. The actual delta is computed
    by [_calculateHandout] in the contract; that computation's bounds
    are validated by the CAS witness corpus. *)
Definition accrue (s : State.t) (delta : U256.t) : State.t :=
  {|
    State.totalSupply              := s.(State.totalSupply);
    State.totalDeposited           := s.(State.totalDeposited);
    State.accumulatedNativeRewards := s.(State.accumulatedNativeRewards) + delta;
  |}.

Module Valid.
  Record state (s : State.t) : Prop := {
    supply_u256  : U256.Valid.t s.(State.totalSupply);
    deposited_nn : 0 <= s.(State.totalDeposited);
    rewards_nn   : 0 <= s.(State.accumulatedNativeRewards);
    (** When supply > 0, totalDeposited must be > 0 — there's at
        least one user's deposit backing the shares. *)
    backed       : s.(State.totalSupply) > 0 -> 0 < s.(State.totalDeposited);
  }.
End Valid.

End StakingVaultExchange.
