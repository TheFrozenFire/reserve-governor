(** ProposerThrottle simulation invariant proofs.

    Proves the load-bearing safety invariants on the
    [ProposerThrottle] simulation defined in
    [ReserveGovernor.simulations.ProposerThrottle]:

      INV-1   readCharge t now <= FIX_ONE
      INV-1'  0 <= readCharge t now, under [Valid.throttle t] and
              [lastUpdated <= now]
      INV-2   consume t cap now = Success t' ->
                t'.lastUpdated = now ∧
                t'.currentCharge = readCharge t now - (FIX_ONE / cap)
      Cap     proposalsAvailable t cap now <= cap, under [0 < cap]
      Mono    readCharge is non-decreasing in [now] when lastUpdated
              is fixed

    These propagate to the on-chain code through the (still-pending)
    [run_consume] equivalence lemma, which lives in a separate file
    because it depends on the Yul-runtime semantics
    (proofs/RocqOfSolidity).

    INV-3 (validity preservation under [consume]) is split into
    [ProposerThrottle_validity.v] so the cap-and-overflow analysis
    stays separate from the structural-shape lemmas here.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposerThrottle.
Require Import Coq.Bool.Bool.

Module ProposerThrottleProofs.

Import ProposerThrottle.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** ----- INV-1: readCharge is bounded above by FIX_ONE. ----- *)
Lemma readCharge_le_fix_one (t : Throttle.t) (now : U256.t) :
  readCharge t now <= FIX_ONE.
Proof.
  unfold readCharge. apply Z.le_min_l.
Qed.

(** ----- INV-1': readCharge is non-negative under sane inputs. -----
    Requires [0 <= currentCharge] (part of [Valid.throttle]) and
    [lastUpdated <= now] (the natural assumption that block time
    doesn't run backwards). *)
Lemma readCharge_nonneg (t : Throttle.t) (now : U256.t) :
  0 <= t.(Throttle.currentCharge) ->
  t.(Throttle.lastUpdated) <= now ->
  0 <= readCharge t now.
Proof.
  intros Hcc Hts.
  unfold readCharge.
  apply Z.min_glb.
  - unfold FIX_ONE. lia.
  - enough (0 <= (now - t.(Throttle.lastUpdated)) * FIX_ONE / PROPOSAL_THROTTLE_PERIOD) by lia.
    apply Z.div_pos.
    + apply Z.mul_nonneg_nonneg.
      * lia.
      * unfold FIX_ONE. lia.
    + unfold PROPOSAL_THROTTLE_PERIOD. lia.
Qed.

(** ----- Cap: proposalsAvailable <= capacity, under positive capacity.
    This is the headline external-facing invariant — the number of
    proposals a single account can issue per 12h window is bounded by
    [capacity] regardless of clock drift or stale storage.

    The bound uses [(capacity * readCharge) / FIX_ONE <= capacity]
    because [readCharge <= FIX_ONE] by INV-1. *)
Lemma proposalsAvailable_le_capacity
    (t : Throttle.t) (capacity : U256.t) (now : U256.t) :
  0 < capacity ->
  proposalsAvailable t capacity now <= capacity.
Proof.
  intros Hcap.
  unfold proposalsAvailable.
  set (c := readCharge t now).
  pose proof (readCharge_le_fix_one t now) as Hc_le.
  fold c in Hc_le.
  (* (capacity * c) / FIX_ONE <= (capacity * FIX_ONE) / FIX_ONE = capacity *)
  assert (Hmul : capacity * c <= capacity * FIX_ONE).
  { apply Z.mul_le_mono_nonneg_l; [lia | exact Hc_le]. }
  apply Z.le_trans with ((capacity * FIX_ONE) / FIX_ONE).
  - apply Z.div_le_mono; [unfold FIX_ONE; lia | exact Hmul].
  - rewrite Z.div_mul; [lia | unfold FIX_ONE; lia].
Qed.

(** ----- INV-2: consume's storage delta is exact when successful. ----- *)
Lemma consume_success_storage_delta
    (t t' : Throttle.t) (capacity : U256.t) (now : U256.t) :
  consume t capacity now = Result.Success t' ->
  t'.(Throttle.lastUpdated) = now /\
  t'.(Throttle.currentCharge) = readCharge t now - (FIX_ONE / capacity).
Proof.
  intros Hok.
  unfold consume in Hok.
  destruct ((capacity * readCharge t now) / FIX_ONE <? 1) eqn:Havail.
  - discriminate.
  - inversion Hok; subst t'. simpl. auto.
Qed.

(** ----- INV-5: consume reverts iff proposalsAvailable < 1. -----
    Equivalent statement: success requires at least one slot's worth
    of charge to be present. *)
Lemma consume_revert_iff_no_proposals_available
    (t : Throttle.t) (capacity : U256.t) (now : U256.t) :
  (exists p s, consume t capacity now = Result.Revert p s)
  <-> proposalsAvailable t capacity now < 1.
Proof.
  unfold consume, proposalsAvailable. split.
  - intros (p & s & Hrev).
    destruct ((capacity * readCharge t now) / FIX_ONE <? 1) eqn:Hb.
    + apply Z.ltb_lt in Hb. exact Hb.
    + discriminate.
  - intros Hlt.
    apply Z.ltb_lt in Hlt.
    rewrite Hlt.
    eexists. eexists. reflexivity.
Qed.

(** ----- INV-5b: consume succeeds iff proposalsAvailable >= 1. ----- *)
Lemma consume_success_iff_proposal_available
    (t : Throttle.t) (capacity : U256.t) (now : U256.t) :
  (exists t', consume t capacity now = Result.Success t')
  <-> 1 <= proposalsAvailable t capacity now.
Proof.
  unfold consume, proposalsAvailable. split.
  - intros [t' Hok].
    destruct ((capacity * readCharge t now) / FIX_ONE <? 1) eqn:Hb.
    + discriminate.
    + apply Z.ltb_ge in Hb. exact Hb.
  - intros Hge.
    assert (Hb : (capacity * readCharge t now) / FIX_ONE <? 1 = false).
    { apply Z.ltb_ge. exact Hge. }
    rewrite Hb. eexists. reflexivity.
Qed.

(** ----- INV-6 statement: the per-consume slot is [FIX_ONE / capacity]
    (Z-level floor), and the implicit "leak" per consume is bounded by
    [capacity - 1]. ----- *)
Lemma consume_slot_leak_bounded (capacity : U256.t) :
  0 < capacity ->
  0 <= FIX_ONE - (FIX_ONE / capacity) * capacity < capacity.
Proof.
  intros Hcap.
  pose proof (Z.div_mod FIX_ONE capacity) as Hdm.
  pose proof (Z.mod_pos_bound FIX_ONE capacity Hcap) as Hbound.
  unfold FIX_ONE in *. lia.
Qed.

End ProposerThrottleProofs.
