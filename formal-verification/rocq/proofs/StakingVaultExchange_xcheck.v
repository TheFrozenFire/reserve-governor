(** StakingVaultExchange × CAS witness cross-check.

    Evaluates the [StakingVaultExchange] simulation on the same OZ
    conversion arithmetic the CAS witness corpus probes. Under the
    OZ v5.4 inflation-defended form the round-trip is no longer
    exact even at clean rates — the virtual +1 on both sides means
    each conversion loses a small constant offset, surfacing as the
    inflation-attack defense. The probe values below reflect the
    actual vm_compute output of the inflation-defended formula.

    The discrete-time exponential decay underpinning native rewards
    is validated separately in the CAS script (cas/staking_vault/
    exchange_rate.gp INV-1..INV-6); here we tie the round-trip
    rounding and conversion-zero behaviour to vm_compute values.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultExchange.

Module StakingVaultExchangeXCheck.

Import StakingVaultExchange.

(** CAS INV-4 probe values: supply, totalAssets, then [a] with rate > 1.
    Phase B sim shape: [nativeBalanceLastKnown] is the primary field;
    [accumulatedNativeRewards] is derived as [nbk - td].  Here we set
    [nbk = td] (no accrued rewards), [nrlp = 0] (never accrued). *)
Definition cal_state : State.t := {|
  State.totalSupply              := 10^18;       (** 1e18 = 1 share *)
  State.totalDeposited           := 10^18 * 8;   (** 8e18 totalAssets *)
  State.nativeBalanceLastKnown   := 10^18 * 8;   (** 0 accrued *)
  State.nativeRewardsLastPaid    := 0;
|}.

Lemma xcheck_totalAssets_8e18 :
  totalAssets cal_state = 8 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** convertToShares(4e18) = 4e18 * 1e18 / 8e18 = 0.5e18. *)
Lemma xcheck_convertToShares_half :
  convertToShares cal_state (4 * 10^18) = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** convertToAssets(0.5e18) under the inflation-defended form is
    [0.5e18 * (8e18 + 1) / (1e18 + 1) = 3999999999999999996], not
    the naive 4e18. The +1 virtuals shave 4 wei off the round-trip
    even at a rate that divides cleanly under the naive formula —
    this is the OZ inflation defense surfacing in concrete numbers.
    Critically: the round-trip is still floor-bounded (<= the
    original 4e18), as proved generally by [round_trip_floor_bound]. *)
Lemma xcheck_round_trip_inflation_defended :
  convertToAssets cal_state (convertToShares cal_state (4 * 10^18))
  = 3999999999999999996.
Proof. vm_compute. reflexivity. Qed.

(** Round-trip strictly loses 4 wei to the inflation defense at this
    calibration — concretely demonstrates that [round_trip_floor_bound]
    is a < (not =) bound under the OZ formula. *)
Lemma xcheck_round_trip_strictly_loses :
  convertToAssets cal_state (convertToShares cal_state (4 * 10^18))
  < 4 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** A round-trip that loses to floor on the share-side first:
    convertToShares(5) under the inflation-defended form is
    [5 * (1e18 + 1) / (8e18 + 1) = 0] (floors to zero, same as naive).
    convertToAssets(0) = 0. So round-trip yields 0, strictly < 5. *)
Lemma xcheck_round_trip_lossy_dust :
  convertToAssets cal_state (convertToShares cal_state 5) = 0.
Proof. vm_compute. reflexivity. Qed.

(** convertToShares on empty supply = identity (1:1 initial deposit). *)
Lemma xcheck_convert_initial_deposit :
  convertToShares empty_state (10^21) = 10^21.
Proof. vm_compute. reflexivity. Qed.

(** Deposit at empty state mints 1:1, sets totalDeposited and supply
    both to [assets]. *)
Lemma xcheck_initial_deposit_storage :
  let r := deposit empty_state (10^21) in
  (fst r).(State.totalSupply) = 10^21
  /\ (fst r).(State.totalDeposited) = 10^21
  /\ snd r = 10^21.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

(** Accrue bumps native rewards without changing supply or deposited.
    Phase B: the bump now happens on [nativeBalanceLastKnown] (the raw
    asset balance); the derived [accumulatedNativeRewards] getter
    returns the same value as before the refactor. *)
Lemma xcheck_accrue_native_only :
  let s := accrue cal_state (10^17) 0 in
  s.(State.totalSupply) = cal_state.(State.totalSupply)
  /\ s.(State.totalDeposited) = cal_state.(State.totalDeposited)
  /\ accumulatedNativeRewards s = 10^17.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

End StakingVaultExchangeXCheck.
