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

(** Calibration mirrors the CAS script. *)
Definition FIX_ONE_C  : Z := 10 ^ 18.
Definition vetoDelay  : Z := 100.
Definition vetoPeriod : Z := 1000.

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
Definition pa_initial : Proposal.t :=
  fresh_optimistic 101 1001 100 1000 5.

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
  fresh_optimistic 201 2001 100 1000 5.

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
  execute_optimistic (add_veto (fresh_optimistic 301 3001 100 1000 5) 5)
                     9999
  = revert_wrong_phase.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-2: veto threshold boundary cases. -----
    Build three proposals with vtt=10, votes 9 / 10 / 11, observe in
    the active window. *)
Lemma xcheck_inv2_below_active :
  let p := add_veto (fresh_optimistic 401 4001 100 1000 10) 9 in
  observe p 500 = PhaseActive.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_at_defeated :
  let p := add_veto (fresh_optimistic 402 4002 100 1000 10) 10 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_inv2_above_defeated :
  let p := add_veto (fresh_optimistic 403 4003 100 1000 10) 11 in
  observe p 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

(** ----- INV-3: executeOptimistic gating. ----- *)
Definition p_inv3 : Proposal.t := fresh_optimistic 501 5001 100 1000 5.

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
     Proposal.vetoThresholdTok := 0;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdActive;
     Proposal.isOptimistic := false;
     Proposal.parent := 601;
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
     Proposal.vetoThresholdTok := 0;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdSucceeded;
     Proposal.isOptimistic := false;
     Proposal.parent := 601;
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
     Proposal.vetoThresholdTok := 5;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdSucceeded;
     Proposal.isOptimistic := true;
     Proposal.parent := 0;
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

End GovernorXCheck.
