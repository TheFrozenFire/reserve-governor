(** ProposerThrottle simulation × CAS witness cross-check.

    Evaluates the [ProposerThrottle] simulation on the same probes
    used by [cas/proposer_throttle/charge_evolution.gp] and asserts
    identical outputs. Any divergence between the Rocq simulation and
    the CAS witness corpus fails the build.

    Calibration (matching the CAS script):
      PROPOSAL_THROTTLE_PERIOD = 43200 s (= 12 hours)
      FIX_ONE                   = 10^18
      capacity                  = 5  (CAS INV-5 probe)

    The CAS witness reports these specific equalities; the lemmas
    below verify the simulation produces the same numbers under
    [vm_compute].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposerThrottle.

Module ProposerThrottleXCheck.

Import ProposerThrottle.

(** ----- INV-4: refill from currentCharge = 0 reaches FIX_ONE in exactly
    PROPOSAL_THROTTLE_PERIOD seconds.
    CAS: "readCharge(0, 0, PERIOD) = 1000000000000000000". ----- *)
Lemma xcheck_full_recovery :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  readCharge t PROPOSAL_THROTTLE_PERIOD = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4 corollary: one second short stays strictly under FIX_ONE.
    CAS: probes [PERIOD - 1] and asserts < FIX_ONE. ----- *)
Lemma xcheck_short_of_recovery :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  readCharge t (PROPOSAL_THROTTLE_PERIOD - 1) < FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4 corollary: clipping at the ceiling.
    CAS: probes [PERIOD + 1] and asserts the result is exactly FIX_ONE. ----- *)
Lemma xcheck_over_recovery_clipped :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  readCharge t (PROPOSAL_THROTTLE_PERIOD + 1) = FIX_ONE.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-3: charge refill is linear in (now - lastUpdated) while
    uncapped. CAS reports per-quarter step = 0.25e18. ----- *)
Lemma xcheck_quarter_step :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  readCharge t (PROPOSAL_THROTTLE_PERIOD / 4) = FIX_ONE / 4.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-5: at exactly the threshold (charge = FIX_ONE / 5), one
    proposal is available — consume succeeds. CAS reports this probe. ----- *)
Definition cap5_at_threshold : Throttle.t := {|
  Throttle.currentCharge := FIX_ONE / 5;   (** 2 * 10^17 *)
  Throttle.lastUpdated   := 0;
|}.

Lemma xcheck_consume_at_threshold_succeeds :
  exists t', consume cap5_at_threshold 5 0 = Result.Success t'.
Proof. vm_compute. eexists. reflexivity. Qed.

(** ----- INV-5: one wei below threshold, consume reverts. ----- *)
Definition cap5_below_threshold : Throttle.t := {|
  Throttle.currentCharge := FIX_ONE / 5 - 1;
  Throttle.lastUpdated   := 0;
|}.

Lemma xcheck_consume_below_threshold_reverts :
  exists p s, consume cap5_below_threshold 5 0 = Result.Revert p s.
Proof. vm_compute. eexists. eexists. reflexivity. Qed.

(** ----- INV-2: consume's storage delta at full state is exactly
    [readCharge - FIX_ONE/cap], lastUpdated bumps to [now]. CAS confirms
    this across all probed capacities. ----- *)
Definition cap5_full : Throttle.t := {|
  Throttle.currentCharge := FIX_ONE;
  Throttle.lastUpdated   := 0;
|}.

Lemma xcheck_consume_storage_delta_full :
  match consume cap5_full 5 5000 with
  | Result.Success t' =>
      t'.(Throttle.currentCharge) = FIX_ONE - (FIX_ONE / 5) /\
      t'.(Throttle.lastUpdated)   = 5000
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** ----- INV-6: integer-division leak for capacity = 3.
    CAS reports leak/consume = 1 wei. ----- *)
Lemma xcheck_leak_cap3 :
  FIX_ONE - (FIX_ONE / 3) * 3 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: integer-division leak for capacity = 7.
    CAS reports leak/consume = 1 wei. ----- *)
Lemma xcheck_leak_cap7 :
  FIX_ONE - (FIX_ONE / 7) * 7 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: integer-division leak for capacity = 5 (exact divisor).
    CAS reports leak/consume = 0. ----- *)
Lemma xcheck_leak_cap5 :
  FIX_ONE - (FIX_ONE / 5) * 5 = 0.
Proof. vm_compute. reflexivity. Qed.

(** ----- proposalsAvailable monotonicity probe: from currentCharge = 0
    at lastUpdated = 0, the number of available proposals starts at 0
    and grows to [capacity] over PROPOSAL_THROTTLE_PERIOD seconds. CAS
    INV-1 sweep validates the cap. ----- *)
Lemma xcheck_proposalsAvailable_fresh_zero :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  proposalsAvailable t 5 0 = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_proposalsAvailable_fresh_full :
  let t := {| Throttle.currentCharge := 0; Throttle.lastUpdated := 0 |} in
  proposalsAvailable t 5 PROPOSAL_THROTTLE_PERIOD = 5.
Proof. vm_compute. reflexivity. Qed.

End ProposerThrottleXCheck.
