(** ProposerThrottle validity preservation.

    Headline lemma: [consume] preserves the [Valid.throttle] storage
    invariant.

    Three things have to fit:

      1. [currentCharge'] is in [0, FIX_ONE]. The new value is
         [readCharge t now - (FIX_ONE / capacity)]. The upper bound
         transfers from [readCharge <= FIX_ONE] (INV-1). The lower
         bound requires the consume to have succeeded, which means
         [(capacity * readCharge) / FIX_ONE >= 1], hence
         [readCharge >= FIX_ONE / capacity], hence the subtraction is
         non-negative.

      2. [currentCharge'] fits in uint256. Easy via the cap bound above.

      3. [lastUpdated'] = [now] fits in uint256, which holds whenever
         we feed a valid [now]. We take that as a precondition.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposerThrottle.
Require Import ReserveGovernor.proofs.ProposerThrottle.
Require Import Coq.Bool.Bool.

Module ProposerThrottleValidity.

Import ReserveGovernor.simulations.ProposerThrottle.
Import ReserveGovernor.proofs.ProposerThrottle.
Import ProposerThrottle.
Import ProposerThrottleProofs.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** Auxiliary: when consume succeeds, the post-state's currentCharge is
    non-negative. The success condition gives us
    [(capacity * readCharge) / FIX_ONE >= 1], from which we derive
    [readCharge >= FIX_ONE / capacity]. *)
Lemma consume_success_charge_nonneg
    (t t' : Throttle.t) (capacity : U256.t) (now : U256.t) :
  0 < capacity ->
  Valid.throttle t ->
  t.(Throttle.lastUpdated) <= now ->
  consume t capacity now = Result.Success t' ->
  0 <= t'.(Throttle.currentCharge).
Proof.
  intros Hcap Hv Hts Hok.
  destruct Hv as [Hcc_u256 Hcc_cap Hlu_u256].
  pose proof (consume_success_storage_delta _ _ _ _ Hok) as (Hlu_eq & Hcharge_eq).
  rewrite Hcharge_eq.
  set (r := readCharge t now) in *.
  (* From success we know (cap * r) / FIX_ONE >= 1, so cap * r >= FIX_ONE,
     so r >= FIX_ONE / cap (with cap > 0). *)
  assert (Havail_ge : 1 <= (capacity * r) / FIX_ONE).
  { unfold consume in Hok. fold r in Hok.
    destruct ((capacity * r) / FIX_ONE <? 1) eqn:Hb; [discriminate|].
    apply Z.ltb_ge in Hb. lia. }
  assert (HFO : 0 < FIX_ONE) by (unfold FIX_ONE; lia).
  assert (Hr_nn : 0 <= r).
  { unfold r. apply readCharge_nonneg.
    - exact (proj1 Hcc_u256).
    - exact Hts. }
  assert (Hcap_r : FIX_ONE <= capacity * r).
  { pose proof (Z.mul_div_le (capacity * r) FIX_ONE HFO) as Hle.
    nia. }
  assert (Hr_ge_slot : FIX_ONE / capacity <= r).
  { apply Z.div_le_upper_bound; [exact Hcap|]. nia. }
  lia.
Qed.

Lemma consume_preserves_validity
    (t t' : Throttle.t) (capacity : U256.t) (now : U256.t) :
  Valid.throttle t ->
  Valid.capacity capacity ->
  U256.Valid.t now ->
  t.(Throttle.lastUpdated) <= now ->
  consume t capacity now = Result.Success t' ->
  Valid.throttle t'.
Proof.
  intros Hv Hcapv Hnow_v Hts Hok.
  pose proof (consume_success_storage_delta _ _ _ _ Hok) as [Hlu_eq Hcharge_eq].
  pose proof (consume_success_charge_nonneg _ _ _ _ (proj1 Hcapv) Hv Hts Hok) as Hcharge_nn.
  pose proof (readCharge_le_fix_one t now) as Hr_le.
  assert (Hcharge_le : t'.(Throttle.currentCharge) <= FIX_ONE).
  { rewrite Hcharge_eq.
    (* readCharge - (FIX_ONE / capacity) <= FIX_ONE because
       FIX_ONE / capacity >= 0 and readCharge <= FIX_ONE. *)
    assert (0 <= FIX_ONE / capacity).
    { apply Z.div_pos; [unfold FIX_ONE; lia | exact (proj1 Hcapv)]. }
    lia. }
  constructor; simpl.
  - (* currentCharge fits in uint256: 0 <= cc' <= FIX_ONE < 2^256 *)
    unfold U256.Valid.t in *.
    split; [exact Hcharge_nn|].
    apply Z.le_lt_trans with FIX_ONE; [exact Hcharge_le|].
    unfold FIX_ONE. lia.
  - exact Hcharge_le.
  - rewrite Hlu_eq. exact Hnow_v.
Qed.

End ProposerThrottleValidity.
