(** StakingVaultExchange × CAS witness cross-check.

    Evaluates the [StakingVaultExchange] simulation on the same OZ
    conversion arithmetic the CAS witness corpus probes.
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

(** CAS INV-4 probe values: supply, totalAssets, then [a] with rate > 1. *)
Definition cal_state : State.t := {|
  State.totalSupply              := 10^18;       (** 1e18 = 1 share *)
  State.totalDeposited           := 10^18 * 8;   (** 8e18 totalAssets *)
  State.accumulatedNativeRewards := 0;
|}.

Lemma xcheck_totalAssets_8e18 :
  totalAssets cal_state = 8 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** convertToShares(4e18) = 4e18 * 1e18 / 8e18 = 0.5e18. *)
Lemma xcheck_convertToShares_half :
  convertToShares cal_state (4 * 10^18) = 5 * 10^17.
Proof. vm_compute. reflexivity. Qed.

(** convertToAssets(0.5e18) = 0.5e18 * 8e18 / 1e18 = 4e18.
    So round-trip is exact at this calibration (rate divides cleanly). *)
Lemma xcheck_round_trip_exact :
  convertToAssets cal_state (convertToShares cal_state (4 * 10^18))
  = 4 * 10^18.
Proof. vm_compute. reflexivity. Qed.

(** A round-trip that loses to floor: ask for 5 wei with the rate above.
    convertToShares(5) = 5 * 1e18 / 8e18 = 0 (floors to zero).
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

(** Accrue bumps native rewards without changing supply or deposited. *)
Lemma xcheck_accrue_native_only :
  let s := accrue cal_state (10^17) in
  s.(State.totalSupply) = cal_state.(State.totalSupply)
  /\ s.(State.totalDeposited) = cal_state.(State.totalDeposited)
  /\ s.(State.accumulatedNativeRewards) = 10^17.
Proof. vm_compute. split; [reflexivity|]. split; reflexivity. Qed.

End StakingVaultExchangeXCheck.
