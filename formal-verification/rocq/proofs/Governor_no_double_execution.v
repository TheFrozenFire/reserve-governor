(** ReserveOptimisticGovernor - no double execution (path exclusivity).

    Audit context. The Reserve Optimistic Governor exposes two terminal
    execution phases:

      - [PhaseExecuted]    : reached only via [execute_optimistic] on an
                             optimistic proposal whose [observe] is
                             [PhaseSucceeded] (past deadline, no veto
                             threshold met).
      - [PhaseStdExecuted] : reached only via [execute_standard] on the
                             corresponding standard child proposal,
                             after [queue_operations] writes
                             [PhaseStdQueued].

    Because the contract spawns a fresh standard child (a different
    [ProposalCore] with a different [proposalId]) inside
    [transitionToPessimistic], a parent that escalates is pinned to
    [PhaseDefeated] (see Governor_no_de_escalation.v) and the child runs
    on its own [ProposalCore]. Within any one [ProposalCore] (modeled
    here as one [Proposal.t]), at most one terminal-execution phase is
    ever reachable.

    This file delivers:

      1. Path-exclusivity lemmas. After [execute_optimistic] succeeds,
         any subsequent [execute_standard] or [queue_operations] on the
         resulting proposal reverts. Symmetrically, after
         [execute_standard] succeeds, any subsequent [execute_optimistic]
         reverts.

      2. Sticky-phase support lemmas. [PhaseExecuted] and [PhaseStdExecuted]
         are observation-sticky in [observe] - i.e. [observe p now] returns
         the stored terminal phase regardless of [now]. Each of these
         terminal phases is reachable only when the stored phase is
         already that exact value (no other branch of [observe] can produce
         these tags).

      3. Headline [terminal_phase_exclusivity]. For any single proposal
         [p], no pair of observation timestamps [now1, now2] can
         simultaneously yield [observe p now1 = PhaseExecuted] and
         [observe p now2 = PhaseStdExecuted]. The phases are by-value
         exclusive on the stored field, and observation is sticky for
         both.

      4. Reachability headline [no_double_execution]. A [Reachable]
         inductive captures any proposal reachable from a fresh
         [fresh_optimistic] or [fresh_standard_child] seed through a
         finite sequence of valid Governor transitions
         ([add_veto], [mark_std_succeeded], [queue_operations],
         [execute_standard], [execute_optimistic], [cancel],
         [transition_to_pessimistic] (parent-side or child-side)).
         The headline shows that for any [Reachable p], no pair of
         timestamps observes both terminal-execution phases on [p].

      5. [vm_compute] cross-check of the negative scenario: a proposal
         is optimistic-executed, then a second [execute_standard] is
         attempted and reverts with [revert_wrong_phase].

    Modeling notes.

      - Time abstraction. The Governor's [observe] takes a [now]
         argument; the terminal-phase observations are independent of
         [now] (the sticky cases in [observe] short-circuit before any
         time-dependent branch). The Reachable inductive does not carry
         a global clock - each transition that consumes a timestamp
         takes its own [now] - so we frame the path-ordering claim as
         "in any sequence, the first execute that succeeded fixes the
         terminal phase, and subsequent attempts of the other kind
         revert."
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module GovernorNoDoubleExecution.

Import Governor.

(** ===== Section 1: stored-phase characterizations ===== *)

(** [execute_optimistic] outputs a proposal whose stored phase is
    exactly [PhaseExecuted], and whose [isOptimistic] flag is preserved
    (and therefore [true], by [execute_optimistic]'s gate). *)
Lemma execute_optimistic_postcondition
    (p p' : Proposal.t) (now : U256.t) :
  execute_optimistic p now = Result.Success p' ->
  p'.(Proposal.phase) = PhaseExecuted /\
  p'.(Proposal.isOptimistic) = true.
Proof.
  intros Hok. unfold execute_optimistic in Hok.
  destruct (negb p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  apply negb_false_iff in Hopt.
  destruct (observe p now) eqn:Hobs; try discriminate.
  injection Hok as Hp'.
  rewrite <- Hp'. cbn. split; [reflexivity|exact Hopt].
Qed.

(** [execute_standard] outputs a proposal whose stored phase is exactly
    [PhaseStdExecuted], and whose [isOptimistic] flag is preserved
    (and therefore [false], by [execute_standard]'s gate). *)
Lemma execute_standard_postcondition
    (p p' : Proposal.t) :
  execute_standard p = Result.Success p' ->
  p'.(Proposal.phase) = PhaseStdExecuted /\
  p'.(Proposal.isOptimistic) = false.
Proof.
  intros Hok. unfold execute_standard in Hok.
  destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|].
  destruct (phase_eq p.(Proposal.phase) PhaseStdQueued) eqn:Hph;
    [|discriminate].
  injection Hok as Hp'.
  rewrite <- Hp'. cbn. split; reflexivity.
Qed.

(** ===== Section 2: path-exclusivity lemmas ===== *)

(** Headline path-exclusivity 1. After [execute_optimistic] succeeds,
    [execute_standard] on the resulting proposal reverts. The proof
    pivots on [isOptimistic] being preserved by [execute_optimistic]
    (and therefore [true] in the output), which trips
    [execute_standard]'s first gate. *)
Lemma execute_optimistic_then_execute_standard_reverts
    (p p' : Proposal.t) (now : U256.t) :
  execute_optimistic p now = Result.Success p' ->
  execute_standard p' = revert_wrong_phase.
Proof.
  intros Hok.
  pose proof (execute_optimistic_postcondition p p' now Hok)
    as (_ & Hopt').
  unfold execute_standard. rewrite Hopt'. reflexivity.
Qed.

(** Headline path-exclusivity 2. After [execute_optimistic] succeeds,
    [queue_operations] on the resulting proposal reverts. Same
    [isOptimistic = true] gate. *)
Lemma execute_optimistic_then_queue_reverts
    (p p' : Proposal.t) (now : U256.t) :
  execute_optimistic p now = Result.Success p' ->
  queue_operations p' = revert_optimistic_no_queue.
Proof.
  intros Hok.
  pose proof (execute_optimistic_postcondition p p' now Hok)
    as (_ & Hopt').
  unfold queue_operations. rewrite Hopt'. reflexivity.
Qed.

(** Symmetric path-exclusivity: after [execute_standard] succeeds, any
    subsequent [execute_optimistic] reverts. The proof pivots on
    [isOptimistic = false] being preserved, which trips
    [execute_optimistic]'s [revert_not_optimistic] gate. *)
Lemma execute_standard_then_execute_optimistic_reverts
    (p p' : Proposal.t) (now : U256.t) :
  execute_standard p = Result.Success p' ->
  execute_optimistic p' now = revert_not_optimistic.
Proof.
  intros Hok.
  pose proof (execute_standard_postcondition p p' Hok)
    as (_ & Hopt').
  unfold execute_optimistic. rewrite Hopt'. cbn. reflexivity.
Qed.

(** ===== Section 3: observation tags pin stored phase ===== *)

(** [observe] returns [PhaseExecuted] only if the stored phase is
    [PhaseExecuted]. The forward direction is sticky (already in
    [GovernorProofs.observe_executed_sticky]); here we prove the reverse:
    no other branch of [observe] can produce [PhaseExecuted]. *)
Lemma observe_eq_executed_pins_stored
    (p : Proposal.t) (now : U256.t) :
  observe p now = PhaseExecuted ->
  p.(Proposal.phase) = PhaseExecuted.
Proof.
  intros Hobs. unfold observe in Hobs.
  destruct (p.(Proposal.phase)) eqn:Hph; try reflexivity;
    try discriminate.
  - (* phase = PhaseSubmitted: only pre-deadline or active/succeeded/defeated
       can appear; none equal PhaseExecuted. *)
    destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
Qed.

(** Same reverse direction for [PhaseStdExecuted]. *)
Lemma observe_eq_std_executed_pins_stored
    (p : Proposal.t) (now : U256.t) :
  observe p now = PhaseStdExecuted ->
  p.(Proposal.phase) = PhaseStdExecuted.
Proof.
  intros Hobs. unfold observe in Hobs.
  destruct (p.(Proposal.phase)) eqn:Hph; try reflexivity;
    try discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
  - destruct (now <? p.(Proposal.voteStart)).
    + destruct (p.(Proposal.isOptimistic)); discriminate.
    + destruct (p.(Proposal.isOptimistic)).
      * destruct (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)); [discriminate|].
        destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
      * destruct (now <? p.(Proposal.voteStart) +
                           p.(Proposal.voteDuration)); discriminate.
Qed.

(** ===== Section 4: headline terminal_phase_exclusivity ===== *)

(** Headline: no proposal is ever observable as both [PhaseExecuted]
    and [PhaseStdExecuted], regardless of when the observation is
    taken. This is the audit-facing form: paths are exclusive at the
    [observe] surface, not just on the underlying transitions. *)
Theorem terminal_phase_exclusivity
    (p : Proposal.t) (now1 now2 : U256.t) :
  observe p now1 = PhaseExecuted ->
  observe p now2 = PhaseStdExecuted ->
  False.
Proof.
  intros H1 H2.
  apply observe_eq_executed_pins_stored in H1.
  apply observe_eq_std_executed_pins_stored in H2.
  rewrite H1 in H2. discriminate.
Qed.

(** Symmetric phrasing - useful when the proof site already has the
    StdExecuted observation in hand. *)
Theorem terminal_phase_exclusivity_sym
    (p : Proposal.t) (now1 now2 : U256.t) :
  observe p now1 = PhaseStdExecuted ->
  observe p now2 = PhaseExecuted ->
  False.
Proof.
  intros H1 H2.
  apply (terminal_phase_exclusivity p now2 now1); assumption.
Qed.

(** ===== Section 5: Reachable inductive ===== *)

(** A proposal is [Reachable] if it can be produced from a fresh
    optimistic or standard-child seed by a finite sequence of valid
    Governor transitions. Each constructor reflects exactly one
    successful transition; reverts are not in the picture (they don't
    update state).

    [now] arguments per transition are existentially handled - the
    Reachable inductive records that *some* valid [now] was chosen, but
    does not enforce a global clock across transitions. This matches
    the contract's behavior: each call reads [block.timestamp] fresh.
*)
Inductive Reachable : Proposal.t -> Prop :=
| reach_fresh_opt :
    forall pid proposer voteStart voteDuration vetoThresholdTok,
    Reachable (fresh_optimistic pid proposer voteStart voteDuration
                                vetoThresholdTok)
| reach_fresh_std :
    forall parent_pid new_pid proposer voteStart voteDuration,
    Reachable (fresh_standard_child parent_pid new_pid proposer
                                    voteStart voteDuration)
| reach_add_veto :
    forall p delta,
    Reachable p ->
    Reachable (add_veto p delta)
| reach_mark_std_succeeded :
    forall p p' now,
    Reachable p ->
    mark_std_succeeded p now = Result.Success p' ->
    Reachable p'
| reach_queue :
    forall p p',
    Reachable p ->
    queue_operations p = Result.Success p' ->
    Reachable p'
| reach_execute_standard :
    forall p p',
    Reachable p ->
    execute_standard p = Result.Success p' ->
    Reachable p'
| reach_execute_optimistic :
    forall p p' now,
    Reachable p ->
    execute_optimistic p now = Result.Success p' ->
    Reachable p'
| reach_cancel :
    forall p p',
    Reachable p ->
    cancel p = Result.Success p' ->
    Reachable p'
| reach_transition_parent :
    forall parent parent' child new_pid votingDelay votingPeriod now,
    Reachable parent ->
    transition_to_pessimistic parent new_pid votingDelay votingPeriod now
      = Result.Success (parent', child) ->
    Reachable parent'
| reach_transition_child :
    forall parent parent' child new_pid votingDelay votingPeriod now,
    Reachable parent ->
    transition_to_pessimistic parent new_pid votingDelay votingPeriod now
      = Result.Success (parent', child) ->
    Reachable child.

(** ===== Section 6: Reachable preserves at most one terminal tag ===== *)

(** Helper: for any reachable proposal, at most one of
    [phase = PhaseExecuted] or [phase = PhaseStdExecuted] holds.
    Trivial by exclusivity on the [Phase] enum, since they are
    distinct constructors. *)
Lemma stored_terminal_phases_distinct (p : Proposal.t) :
  p.(Proposal.phase) = PhaseExecuted ->
  p.(Proposal.phase) = PhaseStdExecuted ->
  False.
Proof.
  intros H1 H2. rewrite H1 in H2. discriminate.
Qed.

(** Reachability headline. Any reachable proposal has at most one
    terminal-execution observation across all timestamps. Stated as:
    no pair of timestamps can observe both [PhaseExecuted] and
    [PhaseStdExecuted] on a reachable proposal. *)
Theorem no_double_execution
    (p : Proposal.t) (now1 now2 : U256.t) :
  Reachable p ->
  observe p now1 = PhaseExecuted ->
  observe p now2 = PhaseStdExecuted ->
  False.
Proof.
  intros _ H1 H2.
  exact (terminal_phase_exclusivity p now1 now2 H1 H2).
Qed.

(** The reachability hypothesis is not used in the proof above - the
    pin-to-stored lemmas are pointwise on any proposal. We keep the
    [Reachable p] hypothesis in the statement because it is the
    audit-relevant framing: the claim is "for any proposal that the
    Governor's state machine can produce, no double execution is ever
    observable." *)

(** Convenient reformulation: any reachable proposal whose [observe]
    yields [PhaseExecuted] at some time will never yield
    [PhaseStdExecuted] at any other time. *)
Corollary no_double_execution_directed
    (p : Proposal.t) (now1 : U256.t) :
  Reachable p ->
  observe p now1 = PhaseExecuted ->
  forall now2, observe p now2 <> PhaseStdExecuted.
Proof.
  intros Hr H1 now2 H2.
  exact (no_double_execution p now1 now2 Hr H1 H2).
Qed.

Corollary no_double_execution_directed_sym
    (p : Proposal.t) (now1 : U256.t) :
  Reachable p ->
  observe p now1 = PhaseStdExecuted ->
  forall now2, observe p now2 <> PhaseExecuted.
Proof.
  intros Hr H1 now2 H2.
  exact (no_double_execution p now2 now1 Hr H2 H1).
Qed.

(** ===== Section 7: vm_compute cross-checks ===== *)

(** Concrete scenario: an optimistic proposal succeeds past its
    deadline; we execute it optimistically, then attempt to
    [execute_standard] on the result. The second attempt must revert. *)

Definition xc_initial : Proposal.t :=
  fresh_optimistic 1101 1001 100 1000 5.

(** Past-deadline observation is [PhaseSucceeded]. *)
Lemma xcheck_xc_initial_succeeded :
  observe xc_initial 1500 = PhaseSucceeded.
Proof. vm_compute. reflexivity. Qed.

(** [execute_optimistic] succeeds and pins phase to [PhaseExecuted]. *)
Lemma xcheck_xc_initial_optimistic_executes :
  match execute_optimistic xc_initial 1500 with
  | Result.Success p => p.(Proposal.phase) = PhaseExecuted /\
                        p.(Proposal.isOptimistic) = true
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** Subsequent [execute_standard] on the executed proposal reverts. *)
Lemma xcheck_xc_no_double_execute_standard :
  match execute_optimistic xc_initial 1500 with
  | Result.Success p => execute_standard p = revert_wrong_phase
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Subsequent [queue_operations] on the executed proposal reverts. *)
Lemma xcheck_xc_no_double_queue :
  match execute_optimistic xc_initial 1500 with
  | Result.Success p =>
      queue_operations p = revert_optimistic_no_queue
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Symmetric scenario: a standard proposal in [PhaseStdQueued] is
    standard-executed; the resulting [PhaseStdExecuted] proposal cannot
    be optimistic-executed. *)
Definition xc_std_queued : Proposal.t :=
  {| Proposal.pid := 2202;
     Proposal.proposer := 2002;
     Proposal.voteStart := 50;
     Proposal.voteDuration := 1000;
     Proposal.vetoThresholdTok := 0;
     Proposal.againstVotes := 0;
     Proposal.phase := PhaseStdQueued;
     Proposal.isOptimistic := false;
     Proposal.parent := 1101;
  |}.

Lemma xcheck_xc_std_executes :
  match execute_standard xc_std_queued with
  | Result.Success p => p.(Proposal.phase) = PhaseStdExecuted /\
                        p.(Proposal.isOptimistic) = false
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Lemma xcheck_xc_no_double_execute_optimistic :
  match execute_standard xc_std_queued with
  | Result.Success p => execute_optimistic p 9999 = revert_not_optimistic
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Headline observable: at no two timestamps can the
    optimistic-executed proposal observe [PhaseStdExecuted]. *)
Lemma xcheck_xc_no_observed_std_exec :
  match execute_optimistic xc_initial 1500 with
  | Result.Success p => observe p 9999 = PhaseExecuted
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_xc_no_observed_exec_after_std :
  match execute_standard xc_std_queued with
  | Result.Success p => observe p 9999 = PhaseStdExecuted
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End GovernorNoDoubleExecution.
