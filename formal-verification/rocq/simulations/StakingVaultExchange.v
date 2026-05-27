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

(** OZ ERC4626 conversion — floor everywhere. When supply is zero, the
    OZ shape uses a "virtual offset" via _decimalsOffset; for our
    purposes the supply==0 case is the initial-deposit edge and the
    result is exactly [assets] (1:1 share-to-asset exchange before any
    rewards have accrued). *)
Definition convertToShares (s : State.t) (assets : U256.t) : U256.t :=
  if s.(State.totalSupply) =? 0
  then assets
  else
    let ta := totalAssets s in
    (assets * s.(State.totalSupply)) / ta.

Definition convertToAssets (s : State.t) (shares : U256.t) : U256.t :=
  if s.(State.totalSupply) =? 0
  then shares
  else
    let ta := totalAssets s in
    (shares * ta) / s.(State.totalSupply).

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
    (the OZ default) — modeled here as a guard. *)
Definition withdraw (s : State.t) (assets : U256.t) : Result.t (State.t * U256.t) :=
  let ta := totalAssets s in
  if assets >? ta then
    Result.Revert 0 32
  else
    let supply := s.(State.totalSupply) in
    (* OZ ERC4626 previewWithdraw uses ceiling division. Modeled as
       (a*S + ta - 1) / ta when ta > 0. When ta = 0, supply = 0 by the
       no-rewards-before-deposit invariant — handled by the supply=0
       branch in convertToShares. *)
    let shares :=
      if supply =? 0 then assets
      else (assets * supply + ta - 1) / ta in
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
