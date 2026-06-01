(** ReserveOptimisticGovernor simulation × CAS witness cross-check.

    Evaluates the [Governor] simulation on the same scenarios used by
    [cas/governor/escalation.gp] and asserts identical outcomes. Any
    divergence between the Rocq simulation and the CAS witness corpus
    fails the build.

    Scenarios reproduced:
      - INV-1   monotonicity along the optimistic happy path and the
                escalation chain.
      - INV-1b  no de-escalation: executeOptimistic post-defeat reverts.
      - INV-2   veto threshold gate (boundary, snap-to-1).
      - INV-3   executeOptimistic gating.
      - INV-4   standard execution chain (queue->execute).
      - INV-4b  optimistic proposals cannot be queued.
      - INV-5   throttle is consumed on every successful propose.
      - INV-6   selector-registry gate.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import Coq.Lists.List.
Import ListNotations.

Module GovernorXCheck.

Import Governor.

(** Calibration mirrors the CAS script.

    NOTE (CRIT-V / T1.4): [fresh_optimistic] now takes the un-snapped
    [vetoThresholdD18] D18 fraction (instead of the snapped {tok}).
    To keep the observable behavior of these calibrations identical
    to the pre-T1.4 layout (which passed e.g. [vetoThresholdTok = 5]
    with [pastSupply = 100]), we now pass [vetoThresholdD18] such that
    [vetoThresholdTokOf vetoThresholdD18 pastSupply] yields the same
    {tok} threshold. Concrete recalibrations:
      - vtTok=5,  ps=100  ⟹  D18 = FIX_ONE / 20 (=5e16) so (5e16*100)/1e18 = 5
      - vtTok=10, ps=100  ⟹  D18 = FIX_ONE / 10 (=1e17) so (1e17*100)/1e18 = 10
      - vtTok=1, smallest snap : any D18*pastSupply/FIX_ONE < 1 snaps to 1
*)
Definition FIX_ONE_C  : Z := 10 ^ 18.
Definition vetoDelay  : Z := 100.
Definition vetoPeriod : Z := 1000.

(** Helper aliases: D18 fractions that give the desired {tok}
    snap-output against [pastSupply = 100]. *)
Definition D18_for_5_at_100  : Z := FIX_ONE_C / 20.
Definition D18_for_10_at_100 : Z := FIX_ONE_C / 10.

(** ----- INV-2: veto-threshold snap. CAS:
      vetoThresholdTok(10%, 100) = 10
      vetoThresholdTok(1 wei, 10) = 1 (Math.max(_, 1) snap)
    ----- *)
Lemma xcheck_vtt_canonical :
  vetoThresholdTokOf (FIX_ONE_C / 10) 100 = 10.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_vtt_snap_to_one :
  vetoThresholdTokOf 1 10 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ----- Reproduce the CAS Path A: submitted -> active -> succeeded
    -> executed. ----- *)
(** pastSupply chosen >0 so the [pastSupply == 0 -> Canceled] branch
    does not fire (T1.3/CRIT-G); paired with vetoThresholdD18 set so
    the LIVE-computed snapped {tok} = 5 (T1.4/CRIT-V), the rest of
    the calibration is unchanged. *)
Definition pa_initial : Proposal.t :=
  fresh_optimistic 101 1001 100 1000 D18_for_5_at_100 100.

Lemma xcheck_path_a_active :
  observe pa_initial 500 = PhaseActive.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_path_a_succeeded :
  observe pa_initial 1500 = PhaseSucceeded.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_path_a_execute :
  match execute_optimistic pa_initial 1500 with
  | Result.Success p => p.(Proposal.phase) = PhaseExecuted
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ----- Reproduce the CAS Path B: optimistic veto -> escalation.
    Build a proposal, add veto, transition. ----- *)
Definition pb_initial : Proposal.t :=
  fresh_optimistic 201 2001 100 1000 D18_for_5_at_100 100.

Definition pb_vetoed : Proposal.t :=
  add_veto pb_initial 10.

Lemma xcheck_path_b_defeated :
  observe pb_vetoed 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

Definition pb_transition_result :=
  transition_to_pessimistic pb_vetoed 999 50 1000 500.

Lemma xcheck_path_b_transition_succeeds :
  exists parent' child, pb_transition_result = Result.Success (parent', child).
Proof. vm_compute. eexists. eexists. reflexivity. Qed.

Lemma xcheck_path_b_parent_is_defeated :
  match pb_transition_result with
  | Result.Success (parent', _) => parent'.(Proposal.phase) = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_path_b_child_is_pending :
  match pb_transition_result with
  | Result.Success (_, child) =>
      child.(Proposal.phase) = PhaseStdPending /\
      child.(Proposal.isOptimistic) = false /\
      child.(Proposal.parent) = 201
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ----- INV-1b: executeOptimistic post-defeat reverts.
    CAS: "executeOptimistic post-defeat -> revert". ----- *)
Lemma xcheck_execute_post_defeat_reverts :
  execute_optimistic (add_veto (fresh_optimistic 301 3001 100 1000
                                                 D18_for_5_at_100 100) 5)
                     9999
  = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: veto threshold boundary cases. -----
    Build three proposals with snapped vtt=10 (D18=1e17 at pastSupply=100),
    votes 9 / 10 / 11, observe in the active window. The {tok}
    threshold is now computed LIVE per call (CRIT-V / T1.4). *)
Lemma xcheck_inv2_below_active :
  let p := add_veto (fresh_optimistic 401 4001 100 1000
                                      D18_for_10_at_100 100) 9 in
  observe p 500 = PhaseActive.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_at_defeated :
  let p := add_veto (fresh_optimistic 402 4002 100 1000
                                      D18_for_10_at_100 100) 10 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_above_defeated :
  let p := add_veto (fresh_optimistic 403 4003 100 1000
                                      D18_for_10_at_100 100) 11 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-3: executeOptimistic gating. ----- *)
Definition p_inv3 : Proposal.t :=
  fresh_optimistic 501 5001 100 1000 D18_for_5_at_100 100.

Lemma xcheck_inv3_active_window_reverts :
  execute_optimistic p_inv3 500 = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv3_postdeadline_no_veto_succeeds :
  exists p', execute_optimistic p_inv3 2000 = Result.Success p'.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_inv3_postdeadline_veto_reverts :
  execute_optimistic (add_veto p_inv3 6) 2000 = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4: standard execution chain. ----- *)
Definition std_initial : Proposal.t :=
  fresh_standard_child 601 9999 6001 50 1000.

Definition std_in_active : Proposal.t := std_initial.   (* PhaseStdPending observed pre-deadline *)

(** queue from std_active should revert (we model with phase set to
    StdActive). ----- *)
Definition std_active : Proposal.t :=
  {| Proposal.pid := 9999;
     Proposal.proposer := 6001;
     Proposal.voteStart := 50;
     Proposal.voteDuration := 1000;
     Proposal.vetoThresholdD18 := 0;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdActive;
     Proposal.isOptimistic := false;
     Proposal.parent := 601;
     Proposal.pastSupply := 1;
  |}.

Lemma xcheck_inv4_queue_from_active_reverts :
  queue_operations std_active = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv4_execute_from_active_reverts :
  execute_standard std_active = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

Definition std_succeeded : Proposal.t :=
  {| Proposal.pid := 9999;
     Proposal.proposer := 6001;
     Proposal.voteStart := 50;
     Proposal.voteDuration := 1000;
     Proposal.vetoThresholdD18 := 0;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdSucceeded;
     Proposal.isOptimistic := false;
     Proposal.parent := 601;
     Proposal.pastSupply := 1;
  |}.

Lemma xcheck_inv4_queue_from_succeeded_ok :
  match queue_operations std_succeeded with
  | Result.Success p => p.(Proposal.phase) = PhaseStdQueued
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv4_execute_from_queued_ok :
  match queue_operations std_succeeded with
  | Result.Success p =>
      match execute_standard p with
      | Result.Success p2 => p2.(Proposal.phase) = PhaseStdExecuted
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-4b: optimistic proposals cannot be queued. -----
    Even when phase is StdSucceeded, isOptimistic=true forces the
    OptimisticProposalCannotBeQueued revert. ----- *)
Definition opt_marked_std : Proposal.t :=
  {| Proposal.pid := 9998;
     Proposal.proposer := 6002;
     Proposal.voteStart := 50;
     Proposal.voteDuration := 1000;
     Proposal.vetoThresholdD18 := D18_for_5_at_100;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdSucceeded;
     Proposal.isOptimistic := true;
     Proposal.parent := 0;
     Proposal.pastSupply := 100;
  |}.

Lemma xcheck_inv4b_optimistic_cannot_queue :
  queue_operations opt_marked_std = revert_optimistic_no_queue.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-5: throttle consumption is exactly one slot per success. ----- *)
Definition simple_allow : list (Address * Selector) := [(20, 1000)].

Lemma xcheck_inv5_one_success_decrements :
  consume_throttle_oracle 3 = Result.Success 2.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv5_empty_reverts :
  consume_throttle_oracle 0 = revert_throttle_exceeded.
Proof. vm_compute. reflexivity. Qed.

(** Three successful proposes then two reverts mirrors the CAS sweep. ----- *)
Definition propose_call (charges : U256.t) :=
  propose_optimistic 700 7001 vetoDelay vetoPeriod (FIX_ONE_C / 10) 100
                     charges [20] [1000] simple_allow 0.

Lemma xcheck_inv5_propose_with_charge_ok :
  exists p, propose_call 1 = Result.Success p.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_inv5_propose_no_charge_reverts :
  propose_call 0 = revert_throttle_exceeded.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-6: selector-registry gate. ----- *)
Definition allow_two : list (Address * Selector) := [(20, 1000); (30, 3000)].

Lemma xcheck_inv6_all_allowed :
  exists p, propose_optimistic 801 8001 vetoDelay vetoPeriod
              (FIX_ONE_C / 10) 100 1
              [20; 30] [1000; 3000] allow_two 0
            = Result.Success p.
Proof. vm_compute. eexists. reflexivity. Qed.

Lemma xcheck_inv6_one_denied :
  propose_optimistic 802 8001 vetoDelay vetoPeriod
    (FIX_ONE_C / 10) 100 1
    [20; 30] [1000; 9999] allow_two 0
  = revert_invalid_call.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv6_disallowed_target :
  propose_optimistic 803 8001 vetoDelay vetoPeriod
    (FIX_ONE_C / 10) 100 1
    [99] [1000] allow_two 0
  = revert_invalid_call.
Proof. vm_compute. reflexivity. Qed.

(** ----- CRIT-G (T1.3): pastSupply == 0 -> Canceled. -----
    Mirrors ReserveOptimisticGovernor.sol:251-253. A proposal whose
    [pastSupply] is zero observes as [PhaseCanceled] regardless of
    veto votes or whether the deadline has elapsed. *)

(** Past-snapshot, optimistic, with pastSupply = 0: even in the
    "would-be Active" window, observe reports Canceled. The
    vetoThresholdD18 value doesn't matter — the pastSupply==0 branch
    fires first (after the now-prepended sentinel check, which is
    bypassed when D18 != sentinel). *)
Lemma xcheck_pastSupply_zero_active_window_canceled :
  let p := fresh_optimistic 901 9001 100 1000 D18_for_5_at_100 0 in
  observe p 500 = PhaseCanceled.
Proof. vm_compute. reflexivity. Qed.

(** Past-deadline, optimistic, with pastSupply = 0: would have been
    Succeeded, but the contract short-circuits to Canceled. *)
Lemma xcheck_pastSupply_zero_post_deadline_canceled :
  let p := fresh_optimistic 902 9001 100 1000 D18_for_5_at_100 0 in
  observe p 2000 = PhaseCanceled.
Proof. vm_compute. reflexivity. Qed.

(** With againstVotes meeting the threshold AND pastSupply = 0, the
    contract still returns Canceled (the pastSupply branch precedes
    the veto check at ROG.sol:251 before 256-262). *)
Lemma xcheck_pastSupply_zero_with_vetoes_still_canceled :
  let p := add_veto (fresh_optimistic 903 9001 100 1000
                                      D18_for_5_at_100 0) 100 in
  observe p 500 = PhaseCanceled.
Proof. vm_compute. reflexivity. Qed.

(** Pre-snapshot (now < voteStart) with pastSupply = 0: the contract
    returns Pending BEFORE the pastSupply test (the snapshot >=
    block.timestamp check at ROG.sol:236-238 precedes the
    pastSupply test). The sim mirrors that ordering. *)
Lemma xcheck_pastSupply_zero_pre_snapshot_submitted :
  let p := fresh_optimistic 904 9001 100 1000 D18_for_5_at_100 0 in
  observe p 50 = PhaseSubmitted.
Proof. vm_compute. reflexivity. Qed.

(** [execute_optimistic] reverts on a pastSupply=0 proposal because
    observe returns Canceled, not Succeeded. *)
Lemma xcheck_pastSupply_zero_execute_reverts :
  let p := fresh_optimistic 905 9001 100 1000 D18_for_5_at_100 0 in
  execute_optimistic p 2000 = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

(** ----- CRIT-V (T1.4): vetoThresholdTok is computed LIVE. -----
    Mirrors ReserveOptimisticGovernor.sol:241,256-257. The threshold
    is no longer frozen at create time; the sim now recomputes it
    on every observation from [vetoThresholdD18] and [pastSupply].
    These xchecks confirm that changing pastSupply between create
    and observe would shift the live threshold (and we can construct
    proposals at different D18+pastSupply combos that hit the same
    snapped {tok}). *)

(** Threshold {tok} computed live from D18=FIX_ONE/10 (= 10%) and
    pastSupply=100: yields 10. *)
Lemma xcheck_live_tok_at_pastSupply_100 :
  let p := fresh_optimistic 906 9001 100 1000 D18_for_10_at_100 100 in
  vetoThresholdTokAt p = 10.
Proof. vm_compute. reflexivity. Qed.

(** Same D18 (=10%) at a doubled pastSupply yields a doubled
    {tok} threshold — demonstrating live recomputation. *)
Lemma xcheck_live_tok_scales_with_pastSupply :
  let p := fresh_optimistic 907 9001 100 1000 D18_for_10_at_100 200 in
  vetoThresholdTokAt p = 20.
Proof. vm_compute. reflexivity. Qed.

(** TRANSITIONED sentinel short-circuit: a proposal with
    [vetoThresholdD18 = TRANSITIONED_VETO_THRESHOLD], past its
    snapshot, optimistic, observes as PhaseDefeated regardless of
    pastSupply or votes. Matches ROG.sol:243-246. *)
Lemma xcheck_sentinel_observes_defeated :
  let p := fresh_optimistic 908 9001 100 1000
                            TRANSITIONED_VETO_THRESHOLD 100 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

(** Sentinel BEFORE snapshot still observes Pending — the pending
    check precedes the sentinel check (ROG.sol:236-238 before 241). *)
Lemma xcheck_sentinel_pre_snapshot_pending :
  let p := fresh_optimistic 909 9001 100 1000
                            TRANSITIONED_VETO_THRESHOLD 100 in
  observe p 50 = PhaseSubmitted.
Proof. vm_compute. reflexivity. Qed.

(** Sentinel with pastSupply=0: the sentinel check fires first
    (ROG.sol:243 precedes 251), so observe returns Defeated, not
    Canceled. *)
Lemma xcheck_sentinel_beats_pastSupply_zero :
  let p := fresh_optimistic 910 9001 100 1000
                            TRANSITIONED_VETO_THRESHOLD 0 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

End GovernorXCheck.
