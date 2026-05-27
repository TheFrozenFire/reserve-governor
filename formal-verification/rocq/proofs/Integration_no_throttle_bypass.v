(** Tier-5 adversarial/negative safety: per-proposer rate-limit
    enforcement.

    Headline claim:
      For any reachable sequence of [propose_optimistic] calls by a
      single proposer within a 12-hour window, the total D18 charge
      drained is bounded above by [2 * FIX_ONE], and (under the
      production-realistic [FIX_ONE mod capacity = 0] divisibility
      assumption) the number of successful calls is bounded above by
      [2 * capacity] — with the tighter [capacity] bound when the
      window starts at zero charge.

    Composition note:
      The Governor surface [propose_optimistic] reads a [throttleCharges]
      U256.t computed by [Integration_optimistic_propose] as
      [proposalsAvailable throttle capacity now]. The bridge there
      (theorem [propose_optimistic_implies_throttle_consumed_and_selectors_whitelisted])
      already shows that each successful [propose_optimistic] entails a
      successful [ProposerThrottle.consume]. This file does the bound:
      count successful [consume] calls in a 12-hour window.

    Argument shape (telescoping):
      Let [c_i] be [currentCharge] before consume [i]. Then
      [r_i = readCharge((c_i, lu_i), t_i)] and after consume
      [c_{i+1} = r_i - s], where [s = FIX_ONE / capacity]. Since
      [r_i <= c_i + (t_i - lu_i) * FIX_ONE / PERIOD] (the pre-clip
      refill expression bounds the post-clip value), summing over [n]
      consumes gives
        n * s <= c_1 - c_{n+1} + (t_n - lu_1) * FIX_ONE / PERIOD
              <= FIX_ONE + (t_n - lu_1) * FIX_ONE / PERIOD.
      Over a window of length [PERIOD], the second term is [FIX_ONE].
      So [n * s <= 2 * FIX_ONE], i.e. [n <= 2 * capacity] when
      [s * capacity = FIX_ONE] exactly (i.e. capacity divides FIX_ONE).

      The tighter [capacity] bound holds when [c_1 = 0] (the start
      is drained), since then only one period's worth of refill is
      available — see [successful_consumes_bounded_tight_start].

    Modeling decisions:
      - The window's [t0] is taken to be the [lastUpdated] of the
        initial throttle slot; the bound counts consumes whose
        timestamps fall in [t0, t0 + PROPOSAL_THROTTLE_PERIOD].
      - The drain bound [n * (FIX_ONE / capacity) <= 2 * FIX_ONE] holds
        unconditionally on capacity (as long as [Valid.capacity]).
      - The count bound [n <= 2 * capacity] requires
        [FIX_ONE mod capacity = 0]. Production calibrates capacity = 5,
        which divides 10^18 cleanly, so this is the practically
        relevant case.
      - We require monotone non-decreasing timestamps (block.timestamp
        never runs backwards) and a well-formed capacity.

    Honest gaps:
      1. The headline bound is [2 * capacity], NOT [capacity]. The
         factor-of-two slack comes from the throttle potentially
         carrying [FIX_ONE] of charge from before [t0] AND receiving a
         full [FIX_ONE] of refill across the 12h window. The tighter
         [capacity] bound only holds for a drained start (or a stricter
         window definition).
      2. The count bound requires [FIX_ONE mod capacity = 0]. Without
         divisibility, the floor-leak in [FIX_ONE / capacity] permits
         more successful consumes per [2 * FIX_ONE] of drain than
         [2 * capacity]. The drain-only theorem
         [no_throttle_bypass_drain] holds without this assumption.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposerThrottle.
Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import ReserveGovernor.proofs.ProposerThrottle.
Require Import ReserveGovernor.proofs.ProposerThrottle_validity.
Require Import ReserveGovernor.proofs.Integration_optimistic_propose.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationNoThrottleBypass.

Import ReserveGovernor.simulations.ProposerThrottle.
Import ProposerThrottle.
Import ProposerThrottleProofs.
Import ProposerThrottleValidity.
Import IntegrationOptimisticPropose.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** ======================================================================
    1. Reachable_throttle_sequence: an inductive recording the
       (charge, lastUpdated) trajectory under a sequence of consume
       calls by a single proposer.
    ====================================================================== *)

(** A reachable sequence of consumes from an initial throttle state.
    Each [Step] records: the consume succeeded at [now_after], and the
    timestamp is non-decreasing (block.timestamp never goes backwards).
    The result throttle is the new state to feed the next step. *)
Inductive Reachable_throttle_sequence
    (capacity : U256.t)
    : Throttle.t -> Throttle.t -> nat -> Prop :=
| Reachable_init :
    forall (t0 : Throttle.t),
      Valid.throttle t0 ->
      Reachable_throttle_sequence capacity t0 t0 0
| Reachable_step :
    forall (t_init t_mid t_next : Throttle.t) (now : U256.t) (n : nat),
      Reachable_throttle_sequence capacity t_init t_mid n ->
      (** Monotone block.timestamp from the prior step's lastUpdated. *)
      t_mid.(Throttle.lastUpdated) <= now ->
      U256.Valid.t now ->
      consume t_mid capacity now = Result.Success t_next ->
      Reachable_throttle_sequence capacity t_init t_next (S n).

(** ======================================================================
    2. Charge-budget invariant: along any reachable trajectory the
       running charge stays in [0, FIX_ONE].
    ====================================================================== *)

(** Validity preservation along the whole sequence: from a valid initial
    throttle, the final throttle is also valid. Built by induction over
    the sequence using [consume_preserves_validity]. *)
Lemma reachable_preserves_validity
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  Valid.throttle t_end.
Proof.
  intros Hcapv HR.
  induction HR as [t0 Hv0 | t_init t_mid t_next now n HR IH Hts Hnow_v Hok].
  - exact Hv0.
  - apply (consume_preserves_validity t_mid t_next capacity now); auto.
Qed.

(** Charge-budget bound: [currentCharge] of every reachable state is in
    [0, FIX_ONE]. Immediate from validity preservation. *)
Lemma reachable_charge_in_range
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  0 <= t_end.(Throttle.currentCharge) <= FIX_ONE.
Proof.
  intros Hcapv HR.
  pose proof (reachable_preserves_validity capacity t_init t_end n Hcapv HR) as Hv.
  destruct Hv as [Hu256 Hcap _].
  unfold U256.Valid.t in Hu256.
  split; [exact (proj1 Hu256) | exact Hcap].
Qed.

(** ======================================================================
    3. Counting bound: drain per consume is at least [FIX_ONE / capacity];
       refill across a window of length [PERIOD] is at most [FIX_ONE].
    ====================================================================== *)

(** The drain identity: post-consume, currentCharge equals readCharge
    minus the floor slot. Refactoring [consume_success_storage_delta]
    into the form we need for the telescoping bound. *)
Lemma consume_drain_identity
    (t t' : Throttle.t) (capacity : U256.t) (now : U256.t) :
  consume t capacity now = Result.Success t' ->
  t'.(Throttle.currentCharge) + (FIX_ONE / capacity) = readCharge t now.
Proof.
  intros Hok.
  pose proof (consume_success_storage_delta _ _ _ _ Hok) as [_ Hcc].
  rewrite Hcc. lia.
Qed.

(** Pre-clip refill bound: [readCharge t now <= currentCharge + drift],
    where drift is the linear refill [(now - lastUpdated) * FIX_ONE / PERIOD].
    This is the side of the min that uses the raw arithmetic. *)
Lemma readCharge_le_pre_clip
    (t : Throttle.t) (now : U256.t) :
  readCharge t now
    <= t.(Throttle.currentCharge)
       + (now - t.(Throttle.lastUpdated)) * FIX_ONE / PROPOSAL_THROTTLE_PERIOD.
Proof.
  unfold readCharge. apply Z.le_min_r.
Qed.

(** Counting bound: in a sequence of [n] successful consumes, the total
    drain [n * (FIX_ONE / capacity)] is bounded by the initial charge
    plus the elapsed refill, minus the final charge.

    The invariant we maintain in the induction:
      [n * s + currentCharge_end
        <= currentCharge_init
           + (lastUpdated_end - lastUpdated_init) * FIX_ONE / PERIOD]
    when n > 0, and the equality trivially for n = 0.

    Note: when n = 0, [lastUpdated_end = lastUpdated_init] and the
    drain is 0, so both sides are [currentCharge_init].
*)
Lemma reachable_drain_le_refill
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  0 < capacity ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  (** Telescoped form: drain <= initial charge + elapsed refill - final charge. *)
  Z.of_nat n * (FIX_ONE / capacity) + t_end.(Throttle.currentCharge)
    <= t_init.(Throttle.currentCharge)
       + (t_end.(Throttle.lastUpdated) - t_init.(Throttle.lastUpdated))
         * FIX_ONE / PROPOSAL_THROTTLE_PERIOD.
Proof.
  intros Hcap HR.
  induction HR as [t0 Hv0 | t_init t_mid t_next now n HR IH Hts Hnow_v Hok].
  - (* n = 0 *)
    simpl. replace (t0.(Throttle.lastUpdated) - t0.(Throttle.lastUpdated)) with 0 by lia.
    assert (Hzero : 0 * FIX_ONE / PROPOSAL_THROTTLE_PERIOD = 0).
    { rewrite Z.mul_0_l. apply Z.div_0_l.
      unfold PROPOSAL_THROTTLE_PERIOD. lia. }
    rewrite Hzero. lia.
  - (* successor *)
    rewrite Nat2Z.inj_succ.
    pose proof (consume_drain_identity _ _ _ _ Hok) as Hdrain.
    pose proof (consume_success_storage_delta _ _ _ _ Hok) as [Hlu_eq _].
    rewrite Hlu_eq.
    (* t_next.charge + s = readCharge t_mid now
        <= t_mid.charge + (now - t_mid.lu) * FO / PERIOD *)
    pose proof (readCharge_le_pre_clip t_mid now) as Hpre.
    (* From IH: n * s + t_mid.charge
                <= t_init.charge + (t_mid.lu - t_init.lu) * FO / PERIOD *)
    (* Goal: (n+1) * s + t_next.charge
            <= t_init.charge + (now - t_init.lu) * FO / PERIOD *)
    (* Strategy: add IH and (drain identity + pre-clip bound),
       then bound the sum of the two refill divisions by one division
       over the total elapsed window. *)
    set (S := FIX_ONE / capacity) in *.
    set (c_init := t_init.(Throttle.currentCharge)) in *.
    set (c_mid  := t_mid.(Throttle.currentCharge)) in *.
    set (c_next := t_next.(Throttle.currentCharge)) in *.
    set (lu_init := t_init.(Throttle.lastUpdated)) in *.
    set (lu_mid  := t_mid.(Throttle.lastUpdated)) in *.
    set (drift_old := (lu_mid - lu_init) * FIX_ONE / PROPOSAL_THROTTLE_PERIOD) in *.
    set (drift_new := (now - lu_mid) * FIX_ONE / PROPOSAL_THROTTLE_PERIOD) in *.
    set (drift_tot := (now - lu_init) * FIX_ONE / PROPOSAL_THROTTLE_PERIOD).
    (* IH:        n * S + c_mid  <= c_init + drift_old.
       Hdrain:    c_next + S      =  readCharge t_mid now.
       Hpre:      readCharge t_mid now <= c_mid + drift_new.
       Combine:   c_next + S <= c_mid + drift_new.
       Add IH:    (n+1)*S + c_next <= c_init + drift_old + drift_new.
       Need:      drift_old + drift_new <= drift_tot.
       That follows from div sub-additivity:
         (a*K)/D + (b*K)/D <= ((a+b)*K)/D when D > 0, K > 0, a,b >= 0,
         since a*K mod D + b*K mod D < 2*D and the floor of the sum
         is at least the sum of floors when carries are absorbed —
         actually the inequality is exactly the standard
         [Z.add_div_le_div] direction. *)
    assert (Hdiv_sub : drift_old + drift_new <= drift_tot).
    { unfold drift_old, drift_new, drift_tot.
      assert (HPER : 0 < PROPOSAL_THROTTLE_PERIOD)
        by (unfold PROPOSAL_THROTTLE_PERIOD; lia).
      assert (HFO : 0 < FIX_ONE)
        by (unfold FIX_ONE; lia).
      (* (now - lu_init) = (lu_mid - lu_init) + (now - lu_mid) *)
      assert (Hsplit : now - lu_init = (lu_mid - lu_init) + (now - lu_mid)) by lia.
      (* General fact: for D > 0, (a/D) + (b/D) <= (a + b)/D.
         Proof: a = D*(a/D) + a mod D, similarly b.
         a + b = D*((a/D)+(b/D)) + (a mod D + b mod D).
         (a + b)/D = (a/D) + (b/D) + (a mod D + b mod D) / D >= (a/D)+(b/D). *)
      set (A := (lu_mid - lu_init) * FIX_ONE).
      set (B := (now - lu_mid) * FIX_ONE).
      assert (HAB : (lu_mid - lu_init) * FIX_ONE + (now - lu_mid) * FIX_ONE
                    = (now - lu_init) * FIX_ONE).
      { rewrite Hsplit. rewrite Z.mul_add_distr_r. reflexivity. }
      rewrite <- HAB.
      fold A. fold B.
      pose proof (Z.div_mod A PROPOSAL_THROTTLE_PERIOD (Z.neq_sym _ _ (Z.lt_neq _ _ HPER))) as Hd_a.
      symmetry in Hd_a.
      pose proof (Z.div_mod B PROPOSAL_THROTTLE_PERIOD (Z.neq_sym _ _ (Z.lt_neq _ _ HPER))) as Hd_b.
      symmetry in Hd_b.
      pose proof (Z.mod_pos_bound A PROPOSAL_THROTTLE_PERIOD HPER) as Hma.
      pose proof (Z.mod_pos_bound B PROPOSAL_THROTTLE_PERIOD HPER) as Hmb.
      (* (A+B)/D = ((A/D)+(B/D))*D + (A mod D + B mod D) all over D, with carry. *)
      assert (Hsum_eq : A + B
              = PROPOSAL_THROTTLE_PERIOD * (A / PROPOSAL_THROTTLE_PERIOD)
                + A mod PROPOSAL_THROTTLE_PERIOD
                + (PROPOSAL_THROTTLE_PERIOD * (B / PROPOSAL_THROTTLE_PERIOD)
                   + B mod PROPOSAL_THROTTLE_PERIOD)).
      { (* Using Z.div_mod for A and B *)
        pose proof (Z.div_mod A PROPOSAL_THROTTLE_PERIOD (Z.neq_sym _ _ (Z.lt_neq _ _ HPER))) as HA.
        pose proof (Z.div_mod B PROPOSAL_THROTTLE_PERIOD (Z.neq_sym _ _ (Z.lt_neq _ _ HPER))) as HB.
        lia. }
      apply Z.div_le_lower_bound; [exact HPER|].
      lia.
    }
    lia.
Qed.

(** ======================================================================
    4. Headline bound: 2 * capacity over a PERIOD-length window.
    ====================================================================== *)

(** Successful consumes within a [PROPOSAL_THROTTLE_PERIOD]-length window
    drain at most [2 * FIX_ONE] of D18 charge from the throttle: the
    initial charge ([<= FIX_ONE]) plus a full window's worth of refill
    ([= FIX_ONE]).

    Preconditions:
      - [0 < capacity] (well-formed throttle).
      - Initial throttle is valid (charge in [0, FIX_ONE]).
      - The sequence stays within the 12h window: every recorded
        timestamp satisfies [now <= t_init.lastUpdated + PERIOD].

    This is the load-bearing arithmetic bound. Converting to a count
    bound [n <= 2 * capacity] requires a corollary that accounts for
    the floor-leak [FIX_ONE mod capacity]; see
    [successful_consumes_count_bounded] below. *)
Theorem successful_consumes_drain_bounded
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  Valid.throttle t_init ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n * (FIX_ONE / capacity) <= 2 * FIX_ONE)%Z.
Proof.
  intros Hcapv Hv_init HR Hwindow.
  destruct Hcapv as [Hcap_pos Hcap_le_max].
  pose proof (reachable_drain_le_refill capacity t_init t_end n Hcap_pos HR) as Hdrain.
  destruct Hv_init as [Hu256_init Hcap_init _].
  unfold U256.Valid.t in Hu256_init.
  destruct Hu256_init as [Hcc_init_nn _].
  assert (Hcapv : Valid.capacity capacity)
    by (split; [exact Hcap_pos | exact Hcap_le_max]).
  pose proof (reachable_charge_in_range capacity t_init t_end n Hcapv HR) as Hend_range.
  destruct Hend_range as [Hcc_end_nn _].
  assert (HFO : 0 < FIX_ONE) by (unfold FIX_ONE; lia).
  assert (HPER : 0 < PROPOSAL_THROTTLE_PERIOD)
    by (unfold PROPOSAL_THROTTLE_PERIOD; lia).
  assert (Hdrift_bound :
            (t_end.(Throttle.lastUpdated) - t_init.(Throttle.lastUpdated))
            * FIX_ONE / PROPOSAL_THROTTLE_PERIOD <= FIX_ONE).
  { apply Z.div_le_upper_bound; [exact HPER|].
    apply Z.mul_le_mono_nonneg_r; [lia | lia]. }
  lia.
Qed.

(** Headline count bound: [n <= 2 * capacity] when [capacity] divides
    [FIX_ONE] exactly (no per-slot floor leak). Production calibrates
    [capacity = 5] which divides [10^18] cleanly, so this is the
    relevant case.

    Without the divisibility assumption, the per-slot floor [S = FIX_ONE /
    capacity] can be much smaller than [FIX_ONE / capacity] in the
    rational sense (e.g. [capacity = FIX_ONE - 1] gives [S = 1]
    instead of [~1]). The drain bound [n * S <= 2 * FIX_ONE] then only
    gives [n <= 2 * FIX_ONE], not [n <= 2 * capacity]. This is a
    genuine slack from the floor-division, not a proof gap. *)
Theorem successful_consumes_count_bounded
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  capacity <= FIX_ONE ->
  FIX_ONE mod capacity = 0 ->
  Valid.throttle t_init ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n <= 2 * capacity)%Z.
Proof.
  intros Hcapv Hcap_le Hcap_div Hv_init HR Hwindow.
  pose proof (successful_consumes_drain_bounded capacity t_init t_end n
                Hcapv Hv_init HR Hwindow) as Hdrain.
  destruct Hcapv as [Hcap_pos _].
  (* When FIX_ONE mod capacity = 0, FIX_ONE = capacity * (FIX_ONE / capacity)
     exactly, so the drain bound gives n * (FIX_ONE/capacity) <= 2 * FIX_ONE
     = 2 * capacity * (FIX_ONE/capacity), hence n <= 2 * capacity. *)
  set (S := FIX_ONE / capacity) in *.
  assert (HS_eq : capacity * S = FIX_ONE).
  { unfold S.
    pose proof (Z.div_mod FIX_ONE capacity) as Hdm.
    rewrite Hcap_div in Hdm. lia. }
  assert (HS_pos : 0 < S).
  { unfold S. apply Z.div_str_pos. split; [exact Hcap_pos | exact Hcap_le]. }
  (* n * S <= 2 * FIX_ONE = 2 * capacity * S, hence n <= 2 * capacity (since S > 0). *)
  assert (Hn_nn : 0 <= Z.of_nat n) by lia.
  nia.
Qed.

(** Tight-start corollary: if the initial throttle starts at
    [currentCharge = 0] (drained or freshly initialized), then within a
    [PERIOD]-length window only one [capacity]'s worth of refill is
    available and the bound tightens to [capacity].

    This captures the realistic case where a proposer was already at
    their limit when the window started. *)
Corollary successful_consumes_bounded_tight_start
    (capacity : U256.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  capacity <= FIX_ONE ->
  FIX_ONE mod capacity = 0 ->
  Valid.throttle t_init ->
  t_init.(Throttle.currentCharge) = 0 ->
  Reachable_throttle_sequence capacity t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n <= capacity)%Z.
Proof.
  intros Hcapv Hcap_le Hcap_div Hv_init Hc0 HR Hwindow.
  destruct Hcapv as [Hcap_pos Hcap_le_max].
  pose proof (reachable_drain_le_refill capacity t_init t_end n Hcap_pos HR) as Hdrain.
  assert (Hcapv : Valid.capacity capacity)
    by (split; [exact Hcap_pos | exact Hcap_le_max]).
  pose proof (reachable_charge_in_range capacity t_init t_end n Hcapv HR) as Hend_range.
  destruct Hend_range as [Hcc_end_nn _].
  set (S := FIX_ONE / capacity) in *.
  assert (HFO : 0 < FIX_ONE) by (unfold FIX_ONE; lia).
  assert (HPER : 0 < PROPOSAL_THROTTLE_PERIOD)
    by (unfold PROPOSAL_THROTTLE_PERIOD; lia).
  assert (Hdrift_bound :
            (t_end.(Throttle.lastUpdated) - t_init.(Throttle.lastUpdated))
            * FIX_ONE / PROPOSAL_THROTTLE_PERIOD <= FIX_ONE).
  { apply Z.div_le_upper_bound; [exact HPER|].
    apply Z.mul_le_mono_nonneg_r; [lia | lia]. }
  rewrite Hc0 in Hdrain.
  assert (Hn_drain_bound : Z.of_nat n * S <= FIX_ONE) by lia.
  assert (HS_eq : capacity * S = FIX_ONE).
  { unfold S.
    pose proof (Z.div_mod FIX_ONE capacity) as Hdm.
    rewrite Hcap_div in Hdm. lia. }
  assert (HS_pos : 0 < S).
  { unfold S. apply Z.div_str_pos. split; [exact Hcap_pos | exact Hcap_le]. }
  assert (Hn_nn : 0 <= Z.of_nat n) by lia.
  nia.
Qed.

(** ======================================================================
    5. Headline composition: no_throttle_bypass via
       Integration_optimistic_propose.
    ====================================================================== *)

(** A reachable sequence of [propose_optimistic] calls under bridged
    oracles. Each successful propose_optimistic produces a fresh
    proposal AND entails a successful [ProposerThrottle.consume]
    (via [Integration_optimistic_propose]). We record only the
    throttle/timestamp trajectory; the proposal-id, target/selector
    lists, etc. are immaterial to the count bound. *)
Inductive Reachable_propose_optimistic_sequence
    (proposer : Governor.Address)
    (capacity : U256.t)
    (reg : SelectorRegistry.State.t)
    : Throttle.t -> Throttle.t -> nat -> Prop :=
| RPO_init :
    forall (t0 : Throttle.t),
      Valid.throttle t0 ->
      Reachable_propose_optimistic_sequence proposer capacity reg t0 t0 0
| RPO_step :
    forall (t_init t_mid t_next : Throttle.t)
           (pid : U256.t)
           (vetoDelay vetoPeriod vetoThresholdD18 pastSupply now : U256.t)
           (targets : list Governor.Address)
           (selectors : list Governor.Selector)
           (p' : Governor.Proposal.t)
           (n : nat),
      Reachable_propose_optimistic_sequence proposer capacity reg t_init t_mid n ->
      t_mid.(Throttle.lastUpdated) <= now ->
      U256.Valid.t now ->
      SelectorRegistry.cross_invariant reg ->
      Governor.propose_optimistic
        pid proposer vetoDelay vetoPeriod vetoThresholdD18 pastSupply
        (throttle_charges_for_governor t_mid capacity now)
        targets selectors
        (selector_registry_allowlist_bridge reg)
        now
      = Governor.Result.Success p' ->
      consume t_mid capacity now = Result.Success t_next ->
      Reachable_propose_optimistic_sequence
        proposer capacity reg t_init t_next (S n).

(** A propose-optimistic sequence projects down to a consume sequence.
    Built by induction over the propose sequence. *)
Lemma propose_sequence_projects_to_consume_sequence
    (proposer : Governor.Address)
    (capacity : U256.t)
    (reg : SelectorRegistry.State.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Reachable_propose_optimistic_sequence proposer capacity reg t_init t_end n ->
  Reachable_throttle_sequence capacity t_init t_end n.
Proof.
  intros HR.
  induction HR as [t0 Hv0 |
                   t_init t_mid t_next pid vd vp vt ps now ts ss p' n HR IH Hts Hnow_v Hcross Hok Hconsume].
  - apply Reachable_init. exact Hv0.
  - eapply Reachable_step; eauto.
Qed.

(** Headline theorem: in any reachable sequence of propose_optimistic
    calls by a single proposer within a 12h window, the count of
    successes is bounded by [2 * capacity].

    Note: the [consume] success premise on each step of
    [Reachable_propose_optimistic_sequence] is morally implied by the
    [propose_optimistic] success premise (via
    [propose_optimistic_implies_throttle_consumed_and_selectors_whitelisted])
    — we carry it explicitly in the inductive so the projection lemma
    above is a one-liner. The integration with the bridge ensures
    consistency. *)
Theorem no_throttle_bypass
    (proposer : Governor.Address)
    (capacity : U256.t)
    (reg : SelectorRegistry.State.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  capacity <= FIX_ONE ->
  FIX_ONE mod capacity = 0 ->
  Valid.throttle t_init ->
  Reachable_propose_optimistic_sequence proposer capacity reg t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n <= 2 * capacity)%Z.
Proof.
  intros Hcapv Hcap_le Hcap_div Hv_init HR Hwindow.
  apply (successful_consumes_count_bounded capacity t_init t_end n); auto.
  apply (propose_sequence_projects_to_consume_sequence proposer capacity reg).
  exact HR.
Qed.

(** Drain-side variant of [no_throttle_bypass]: holds unconditionally
    on capacity divisibility, bounds the total D18 drain. *)
Theorem no_throttle_bypass_drain
    (proposer : Governor.Address)
    (capacity : U256.t)
    (reg : SelectorRegistry.State.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  Valid.throttle t_init ->
  Reachable_propose_optimistic_sequence proposer capacity reg t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n * (FIX_ONE / capacity) <= 2 * FIX_ONE)%Z.
Proof.
  intros Hcapv Hv_init HR Hwindow.
  apply (successful_consumes_drain_bounded capacity t_init t_end n); auto.
  apply (propose_sequence_projects_to_consume_sequence proposer capacity reg).
  exact HR.
Qed.

(** Tight-start corollary at the propose-optimistic surface. *)
Corollary no_throttle_bypass_tight_start
    (proposer : Governor.Address)
    (capacity : U256.t)
    (reg : SelectorRegistry.State.t)
    (t_init t_end : Throttle.t) (n : nat) :
  Valid.capacity capacity ->
  capacity <= FIX_ONE ->
  FIX_ONE mod capacity = 0 ->
  Valid.throttle t_init ->
  t_init.(Throttle.currentCharge) = 0 ->
  Reachable_propose_optimistic_sequence proposer capacity reg t_init t_end n ->
  t_end.(Throttle.lastUpdated)
    <= t_init.(Throttle.lastUpdated) + PROPOSAL_THROTTLE_PERIOD ->
  (Z.of_nat n <= capacity)%Z.
Proof.
  intros Hcapv Hcap_le Hcap_div Hv_init Hc0 HR Hwindow.
  apply (successful_consumes_bounded_tight_start capacity t_init t_end n); auto.
  apply (propose_sequence_projects_to_consume_sequence proposer capacity reg).
  exact HR.
Qed.

(** ======================================================================
    6. vm_compute cross-checks.
    ====================================================================== *)

(** Cross-check 1: capacity = 5, fresh full throttle, 5 consumes succeed
    in lock-step at the same instant; the 6th reverts.

    This is the classic "batch flood" sanity check: a proposer with a
    fully charged throttle (1e18 D18 charge) can submit 5 proposals
    back-to-back at the same block (no refill), and the 6th fails.

    Per-slot drain = FIX_ONE / 5 = 2e17. 5 slots drains exactly FIX_ONE
    (capacity = 5 divides FIX_ONE so no leak).
*)

Definition full_throttle_cap5 : Throttle.t := {|
  Throttle.currentCharge := FIX_ONE;
  Throttle.lastUpdated   := 0;
|}.

(** After 1 consume at now=0: charge = FIX_ONE - FIX_ONE/5 = 4e17. *)
Definition step1_cap5 : Throttle.t :=
  match consume full_throttle_cap5 5 0 with
  | Result.Success t => t
  | _ => full_throttle_cap5
  end.

Definition step2_cap5 : Throttle.t :=
  match consume step1_cap5 5 0 with
  | Result.Success t => t
  | _ => step1_cap5
  end.

Definition step3_cap5 : Throttle.t :=
  match consume step2_cap5 5 0 with
  | Result.Success t => t
  | _ => step2_cap5
  end.

Definition step4_cap5 : Throttle.t :=
  match consume step3_cap5 5 0 with
  | Result.Success t => t
  | _ => step3_cap5
  end.

Definition step5_cap5 : Throttle.t :=
  match consume step4_cap5 5 0 with
  | Result.Success t => t
  | _ => step4_cap5
  end.

Lemma xcheck_five_consumes_succeed_at_full :
  (exists t1, consume full_throttle_cap5 5 0 = Result.Success t1)
  /\ (exists t2, consume step1_cap5 5 0 = Result.Success t2)
  /\ (exists t3, consume step2_cap5 5 0 = Result.Success t3)
  /\ (exists t4, consume step3_cap5 5 0 = Result.Success t4)
  /\ (exists t5, consume step4_cap5 5 0 = Result.Success t5).
Proof.
  repeat split.
  - vm_compute. eexists. reflexivity.
  - vm_compute. eexists. reflexivity.
  - vm_compute. eexists. reflexivity.
  - vm_compute. eexists. reflexivity.
  - vm_compute. eexists. reflexivity.
Qed.

Lemma xcheck_sixth_consume_reverts :
  exists p s, consume step5_cap5 5 0 = Result.Revert p s.
Proof. vm_compute. eexists. eexists. reflexivity. Qed.

(** Cross-check 2: a 24h window (= 2 * PERIOD), capacity = 5. From
    [currentCharge = 0] start, refill arrives linearly. After 24h the
    charge has been clipped at FIX_ONE so total drain across 10
    successful consumes equals one full capacity refill (5) plus the
    second refill (5) — exactly 10. The 11th reverts.

    Since the 24h window exceeds [PROPOSAL_THROTTLE_PERIOD], the
    [no_throttle_bypass] bound theorem above doesn't directly apply,
    but the headline arithmetic is the same: 10 consumes <= 2*5.

    We sequence the consumes at well-spaced times so each readCharge
    re-fills before consumption. With capacity=5 and 5 consumes
    per PERIOD, spacing them by PERIOD/5 keeps the charge available.
*)

Definition fresh_drained : Throttle.t := {|
  Throttle.currentCharge := 0;
  Throttle.lastUpdated   := 0;
|}.

(** A trace of 10 consumes spaced PERIOD/5 apart starting at
    PROPOSAL_THROTTLE_PERIOD/5 (so the first consume sees one slot of
    refill). The 11th attempt happens at time = 10 * PERIOD/5 = 2 *
    PERIOD, at which point the charge has just been drained to zero by
    the 10th consume and no further refill has accumulated. *)

Definition tick : Z := PROPOSAL_THROTTLE_PERIOD / 5.

Definition s24_1 : Throttle.t :=
  match consume fresh_drained 5 tick with
  | Result.Success t => t
  | _ => fresh_drained
  end.

Definition s24_2 : Throttle.t :=
  match consume s24_1 5 (2 * tick) with
  | Result.Success t => t
  | _ => s24_1
  end.

Definition s24_3 : Throttle.t :=
  match consume s24_2 5 (3 * tick) with
  | Result.Success t => t
  | _ => s24_2
  end.

Definition s24_4 : Throttle.t :=
  match consume s24_3 5 (4 * tick) with
  | Result.Success t => t
  | _ => s24_3
  end.

Definition s24_5 : Throttle.t :=
  match consume s24_4 5 (5 * tick) with
  | Result.Success t => t
  | _ => s24_4
  end.

Definition s24_6 : Throttle.t :=
  match consume s24_5 5 (6 * tick) with
  | Result.Success t => t
  | _ => s24_5
  end.

Definition s24_7 : Throttle.t :=
  match consume s24_6 5 (7 * tick) with
  | Result.Success t => t
  | _ => s24_6
  end.

Definition s24_8 : Throttle.t :=
  match consume s24_7 5 (8 * tick) with
  | Result.Success t => t
  | _ => s24_7
  end.

Definition s24_9 : Throttle.t :=
  match consume s24_8 5 (9 * tick) with
  | Result.Success t => t
  | _ => s24_8
  end.

Definition s24_10 : Throttle.t :=
  match consume s24_9 5 (10 * tick) with
  | Result.Success t => t
  | _ => s24_9
  end.

Lemma xcheck_ten_consumes_succeed_over_24h :
  (exists t, consume fresh_drained 5 tick = Result.Success t)
  /\ (exists t, consume s24_1 5 (2 * tick) = Result.Success t)
  /\ (exists t, consume s24_2 5 (3 * tick) = Result.Success t)
  /\ (exists t, consume s24_3 5 (4 * tick) = Result.Success t)
  /\ (exists t, consume s24_4 5 (5 * tick) = Result.Success t)
  /\ (exists t, consume s24_5 5 (6 * tick) = Result.Success t)
  /\ (exists t, consume s24_6 5 (7 * tick) = Result.Success t)
  /\ (exists t, consume s24_7 5 (8 * tick) = Result.Success t)
  /\ (exists t, consume s24_8 5 (9 * tick) = Result.Success t)
  /\ (exists t, consume s24_9 5 (10 * tick) = Result.Success t).
Proof.
  repeat split;
    (vm_compute; eexists; reflexivity).
Qed.

Lemma xcheck_eleventh_consume_reverts_over_24h :
  exists p s, consume s24_10 5 (10 * tick) = Result.Revert p s.
Proof. vm_compute. eexists. eexists. reflexivity. Qed.

End IntegrationNoThrottleBypass.
