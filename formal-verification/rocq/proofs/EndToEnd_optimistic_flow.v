(** End-to-end positive lifecycle: the optimistic-execution flow.

    ============================================================
    ADVERSARIAL-REVIEW DISCLOSURE (SV1, Caveat-10 in Audit.v)
    ============================================================

    Read the parallel disclosure in
    [proofs/EndToEnd_standard_flow.v] for the long form. The
    short summary for the optimistic flow:

      - The 3-step witness ([propose -> wait -> execute]) sets
        [vetoThreshold = 1e17] against [pastSupply = 100], for a
        veto threshold of 10 tokens. Numeric constants picked for
        [vm_compute], not production realism (realistic supplies
        are 10^24+).

      - Witness uses [reach_fresh_opt] in the [Reachable p2] step,
        which bypasses [propose_optimistic]. The throttle/registry/
        length gates are validated separately by
        [step1_propose_optimistic_succeeds] but are NOT part of the
        [Reachable] claim.

      - The [_Hmono] time-monotonicity hypothesis is discarded in
        the proof body — the numeric constants make the witness
        work regardless.

      - The witness exercises ONLY the trivial pass-through. No
        vetoed proposal (no [add_veto] transition), no guardian
        cancel, no throttle exhaustion, no selector-registry
        update between propose and execute. The "lifecycle is
        realizable" claim is realized only along the silent path.

      - Not referenced from [Audit.v]. Zero audit_* notations.

    Read this file as: "happy path types-check coherently." NOT as
    "the system works under contention."
    ============================================================

    The negative theorems in [Governor_no_double_execution.v] and the
    single-step composition theorems in [Integration_optimistic_propose.v]
    and [Integration_governor_timelock.v] cover "bad things cannot
    happen" and "this single step composes correctly." This file lands
    the audit-facing positive complement: starting from a sane initial
    world (full throttle charge, registry with a whitelisted call,
    fresh governor), *there exists* a Reachable sequence of operations
    that drives a proposal through the full optimistic-execution
    lifecycle and lands it in [PhaseExecuted].

    Lifecycle modeled:
      Step 1.  [propose_optimistic] succeeds at [t0]. The throttle has
               charge (proposalsAvailable >= 1), every (target, selector)
               is whitelisted, the call payload is non-empty and
               length-matched. The output is a fresh
               [Proposal.t] in [PhaseSubmitted] (the stored phase), with
               [isOptimistic = true], [againstVotes = 0], and
               [voteStart = t0 + vetoDelay].

      Step 2.  Time advances to [now_executable] with
               [now_executable >= t0 + vetoDelay + vetoPeriod]. No
               veto is added, so [againstVotes = 0] which is strictly
               below [vetoThresholdTok] (vetoThresholdTok >= 1 by the
               [Math.max(_, 1)] snap proved in
               [GovernorProofs.vetoThresholdTok_ge_1]). Therefore
               [observe p1 now_executable = PhaseSucceeded].

      Step 3.  [execute_optimistic p1 now_executable] succeeds and
               produces a proposal [p2] with [phase = PhaseExecuted].

    The execution chain is encoded as the [Reachable] inductive from
    [Governor_no_double_execution.v]: [reach_fresh_opt] constructs
    [fresh_optimistic ...], which is exactly the value
    [propose_optimistic] returns on success;
    [reach_execute_optimistic] threads through [execute_optimistic].

    Calibration choices:
      - capacity = 5 proposals / 12 hours.
          The production governor calibrates capacity at 5 (FIX_ONE / 5
          divides cleanly into 10^18 with no rounding leak, so each
          consume removes exactly one slot's worth of charge).
      - throttle: currentCharge = FIX_ONE (full), lastUpdated = 0
          → proposalsAvailable at any [now >= 0] is 5.
      - registry: one whitelisted (target=20, selector=1000).
      - vetoDelay = 100, vetoPeriod = 1000.
          → voteStart = 0 + 100 = 100, deadline = 100 + 1000 = 1100.
      - vetoThresholdD18 = FIX_ONE / 10, pastSupply = 100
          → vetoThresholdTok = (10^17 * 100) / 10^18 = 10. With
            againstVotes = 0, the [>= vtt] check fails, no veto.
      - t0 = 0, now_executable = 1101 (one second past deadline).

    Bridge to ProposerThrottle + SelectorRegistry: we reuse the
    bridging functions from [Integration_optimistic_propose.v] (the
    [throttle_charges_for_governor] feed and
    [selector_registry_allowlist_bridge] flattener). The witness
    sequence carries those bridges through into the propose_optimistic
    call site, so the lifecycle theorem is anchored on the concrete
    component states, not just on the Governor's oracle abstractions.

    The required precondition [t0 <= now_executable] is the EVM-level
    timestamp monotonicity guarantee — [block.timestamp] only advances
    forward. Here it is stated as a numeric inequality
    [0 <= 1101] (trivially true) and surfaced explicitly so the
    audit reader can see what assumption the lifecycle theorem rests
    on.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.simulations.ProposerThrottle.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import ReserveGovernor.proofs.Governor.
Require Import ReserveGovernor.proofs.Governor_no_double_execution.
Require Import ReserveGovernor.proofs.Integration_optimistic_propose.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module EndToEndOptimisticFlow.

Import IntegrationOptimisticPropose.

(** ======================================================================
    1. Initial world: throttle + registry + (no proposals yet)
    ====================================================================== *)

(** Capacity of 5 proposals per 12-hour window. Divides FIX_ONE cleanly
    so the per-consume slot is exact (no rounding leak). *)
Definition init_capacity : U256.t := 5.

(** Throttle at full charge, last updated at time 0. proposalsAvailable
    at any [now >= 0] computes to 5. *)
Definition init_throttle : ProposerThrottle.Throttle.t :=
  {| ProposerThrottle.Throttle.currentCharge := ProposerThrottle.FIX_ONE;
     ProposerThrottle.Throttle.lastUpdated   := 0 |}.

(** Registry seeded with one whitelisted (target=20, selector=1000)
    on top of [empty_state]. No forbidden targets. *)
Definition init_registry : SelectorRegistry.State.t :=
  match SelectorRegistry.addSelector
          SelectorRegistry.empty_state [] 20 1000 with
  | SelectorRegistry.Result.Success s => s
  | _ => SelectorRegistry.empty_state
  end.

(** Call payload: one (target, selector) pair, both in the registry. *)
Definition init_targets   : list Governor.Address  := [20].
Definition init_selectors : list Governor.Selector := [1000].

(** Timing calibration. *)
Definition init_t0             : U256.t := 0.
Definition init_vetoDelay      : U256.t := 100.
Definition init_vetoPeriod     : U256.t := 1000.
Definition init_vetoThresholdD18 : U256.t := Governor.FIX_ONE / 10.
Definition init_pastSupply     : U256.t := 100.
Definition init_pid            : U256.t := 4242.
Definition init_proposer       : Governor.Address := 7777.

(** Wall-clock at which [execute_optimistic] is invoked: one second
    past the optimistic deadline. *)
Definition init_now_executable : U256.t :=
  init_t0 + init_vetoDelay + init_vetoPeriod + 1.

(** The slot of charge consumed per successful propose, at this
    calibration. With capacity = 5, slot = FIX_ONE / 5. *)
Definition init_slot : U256.t :=
  ProposerThrottle.FIX_ONE / init_capacity.

(** ======================================================================
    2. Concrete witness: the three-step lifecycle
    ====================================================================== *)

(** Step 1: the proposal that [propose_optimistic] would return at
    the initial calibration. *)
Definition witness_p1 : Governor.Proposal.t :=
  Governor.fresh_optimistic init_pid init_proposer
                   (init_t0 + init_vetoDelay)
                   init_vetoPeriod
                   (Governor.vetoThresholdTokOf init_vetoThresholdD18
                                                init_pastSupply).

(** Step 3: the proposal after [execute_optimistic]. Same record as
    [witness_p1] but with [phase] flipped to [PhaseExecuted]. *)
Definition witness_p2 : Governor.Proposal.t :=
  {| Governor.Proposal.pid              := witness_p1.(Governor.Proposal.pid);
     Governor.Proposal.proposer         := witness_p1.(Governor.Proposal.proposer);
     Governor.Proposal.voteStart        := witness_p1.(Governor.Proposal.voteStart);
     Governor.Proposal.voteDuration     := witness_p1.(Governor.Proposal.voteDuration);
     Governor.Proposal.vetoThresholdTok := witness_p1.(Governor.Proposal.vetoThresholdTok);
     Governor.Proposal.againstVotes     := witness_p1.(Governor.Proposal.againstVotes);
     Governor.Proposal.phase            := Governor.PhaseExecuted;
     Governor.Proposal.isOptimistic     := witness_p1.(Governor.Proposal.isOptimistic);
     Governor.Proposal.parent           := witness_p1.(Governor.Proposal.parent);
  |}.

(** The throttle after one successful consume. *)
Definition witness_throttle_after : ProposerThrottle.Throttle.t :=
  match ProposerThrottle.consume init_throttle init_capacity init_t0 with
  | ProposerThrottle.Result.Success t' => t'
  | _ => init_throttle
  end.

(** ======================================================================
    3. Step-1 facts: propose_optimistic succeeds, returns witness_p1
    ====================================================================== *)

(** The bridged throttle feed at [init_t0] is 5 (full charge, no time
    elapsed). *)
Lemma init_throttle_charges_eq_5 :
  throttle_charges_for_governor init_throttle init_capacity init_t0 = 5.
Proof. vm_compute. reflexivity. Qed.

(** Selector (20, 1000) is whitelisted by the registry. *)
Lemma init_registry_whitelists_call :
  SelectorRegistry.isAllowed init_registry 20 1000 = true.
Proof. vm_compute. reflexivity. Qed.

(** The Governor's bridged-allowlist surface agrees. *)
Lemma init_bridged_allowlist_contains_call :
  Governor.allowed_tuple
    (selector_registry_allowlist_bridge init_registry) 20 1000 = true.
Proof. vm_compute. reflexivity. Qed.

(** [propose_optimistic] succeeds at [init_t0] and returns exactly
    [witness_p1]. *)
Lemma step1_propose_optimistic_succeeds :
  Governor.propose_optimistic
    init_pid init_proposer init_vetoDelay init_vetoPeriod
    init_vetoThresholdD18 init_pastSupply
    (throttle_charges_for_governor init_throttle init_capacity init_t0)
    init_targets init_selectors
    (selector_registry_allowlist_bridge init_registry)
    init_t0
  = Governor.Result.Success witness_p1.
Proof. vm_compute. reflexivity. Qed.

(** [ProposerThrottle.consume] succeeds in parallel — the throttle
    really had charge to spend. *)
Lemma step1_throttle_consume_succeeds :
  ProposerThrottle.consume init_throttle init_capacity init_t0
  = ProposerThrottle.Result.Success witness_throttle_after.
Proof. vm_compute. reflexivity. Qed.

(** The throttle's currentCharge decreases by exactly one slot
    (FIX_ONE / capacity) after the consume. This is the
    "side-effect" claim of the lifecycle theorem. *)
Lemma step1_throttle_charge_decreases_by_one_slot :
  witness_throttle_after.(ProposerThrottle.Throttle.currentCharge)
  = init_throttle.(ProposerThrottle.Throttle.currentCharge) - init_slot.
Proof. vm_compute. reflexivity. Qed.

(** ======================================================================
    4. Step-2 facts: the veto window elapses with no veto raised
    ====================================================================== *)

(** [witness_p1] starts in [PhaseSubmitted] (the [fresh_optimistic]
    constructor sets it). *)
Lemma witness_p1_stored_phase :
  witness_p1.(Governor.Proposal.phase) = Governor.PhaseSubmitted.
Proof. reflexivity. Qed.

(** [witness_p1] has [isOptimistic = true]. *)
Lemma witness_p1_isOptimistic :
  witness_p1.(Governor.Proposal.isOptimistic) = true.
Proof. reflexivity. Qed.

(** [witness_p1] has [againstVotes = 0] — no vetoes have been added. *)
Lemma witness_p1_no_veto :
  witness_p1.(Governor.Proposal.againstVotes) = 0.
Proof. reflexivity. Qed.

(** Time-monotonicity precondition: the wall-clock at execution
    [init_now_executable = 1101] is past the initial time [init_t0 = 0].
    This is the EVM-level [block.timestamp] monotonicity guarantee,
    stated explicitly as a numeric inequality so the audit reader can
    see what assumption the lifecycle rests on. *)
Lemma time_monotonicity_precondition :
  init_t0 <= init_now_executable.
Proof. vm_compute. discriminate. Qed.

(** At [init_now_executable], [observe witness_p1] returns
    [PhaseSucceeded]: past the deadline, no veto threshold met. *)
Lemma step2_observe_succeeded :
  Governor.observe witness_p1 init_now_executable = Governor.PhaseSucceeded.
Proof. vm_compute. reflexivity. Qed.

(** ======================================================================
    5. Step-3 facts: execute_optimistic succeeds, witness_p2 produced
    ====================================================================== *)

(** [execute_optimistic] succeeds and returns exactly [witness_p2]. *)
Lemma step3_execute_optimistic_succeeds :
  Governor.execute_optimistic witness_p1 init_now_executable
  = Governor.Result.Success witness_p2.
Proof. vm_compute. reflexivity. Qed.

(** [witness_p2] is in [PhaseExecuted]. *)
Lemma witness_p2_phase_executed :
  witness_p2.(Governor.Proposal.phase) = Governor.PhaseExecuted.
Proof. reflexivity. Qed.

(** ======================================================================
    6. Reachability bridge: witness_p1, witness_p2 are Reachable
    ====================================================================== *)

(** [witness_p1] is reachable — it is exactly the value of
    [fresh_optimistic init_pid init_proposer (init_t0 + init_vetoDelay)
                      init_vetoPeriod (vetoThresholdTokOf ...)],
    which is the [reach_fresh_opt] base case. *)
Lemma witness_p1_reachable : GovernorNoDoubleExecution.Reachable witness_p1.
Proof.
  unfold witness_p1.
  apply GovernorNoDoubleExecution.reach_fresh_opt.
Qed.

(** [witness_p2] is reachable via [reach_execute_optimistic] applied
    to [witness_p1] using [step3_execute_optimistic_succeeds]. *)
Lemma witness_p2_reachable : GovernorNoDoubleExecution.Reachable witness_p2.
Proof.
  eapply GovernorNoDoubleExecution.reach_execute_optimistic.
  - apply witness_p1_reachable.
  - exact step3_execute_optimistic_succeeds.
Qed.

(** ======================================================================
    7. Headline existence theorem: the optimistic lifecycle is realizable
    ====================================================================== *)

(** [optimistic_lifecycle_exists].

    Starting from the initial world (full-charge throttle, registry
    with a whitelisted call, fresh governor), THERE EXISTS a Reachable
    proposal [p2] whose phase is [PhaseExecuted] and a post-throttle
    state whose currentCharge has decreased by exactly one slot
    (FIX_ONE / capacity), provided the wall-clock advances enough to
    cross the veto deadline.

    The bundled conjunction reflects the audit claim:
      - the lifecycle is realized as a Reachable derivation chain
        ([reach_fresh_opt] → [reach_execute_optimistic]),
      - the call payload was non-empty and length-matched (otherwise
        propose would have reverted),
      - the call payload was whitelisted (otherwise propose would have
        reverted),
      - the throttle had charge (otherwise propose would have reverted),
      - [execute_optimistic] succeeded (the proposal observed
        [PhaseSucceeded] at the chosen execution time),
      - the final phase is [PhaseExecuted],
      - the throttle's currentCharge dropped by exactly one slot.

    The bridging functions [throttle_charges_for_governor] and
    [selector_registry_allowlist_bridge] are reused verbatim from
    [Integration_optimistic_propose.v]: the lifecycle is anchored on
    the concrete component states (Throttle.t and State.t), not just
    the Governor's oracle abstractions. *)
Theorem optimistic_lifecycle_exists :
  init_t0 <= init_now_executable ->
  exists (p1 p2 : Governor.Proposal.t)
         (throttle_after : ProposerThrottle.Throttle.t),
    (* Step 1: propose succeeds under the bridged oracles. *)
    Governor.propose_optimistic
      init_pid init_proposer init_vetoDelay init_vetoPeriod
      init_vetoThresholdD18 init_pastSupply
      (throttle_charges_for_governor init_throttle init_capacity init_t0)
      init_targets init_selectors
      (selector_registry_allowlist_bridge init_registry)
      init_t0
    = Governor.Result.Success p1
    /\ (* Step 1 side-effect: the concrete throttle consume succeeded
          and drained exactly one slot. *)
       ProposerThrottle.consume init_throttle init_capacity init_t0
       = ProposerThrottle.Result.Success throttle_after
    /\ throttle_after.(ProposerThrottle.Throttle.currentCharge)
       = init_throttle.(ProposerThrottle.Throttle.currentCharge) - init_slot
    /\ (* Step 2: observation at the execution time is PhaseSucceeded. *)
       Governor.observe p1 init_now_executable = Governor.PhaseSucceeded
    /\ (* Step 3: execute_optimistic succeeds, output is p2. *)
       Governor.execute_optimistic p1 init_now_executable
       = Governor.Result.Success p2
    /\ (* Reachability chain. *)
       GovernorNoDoubleExecution.Reachable p1
    /\ GovernorNoDoubleExecution.Reachable p2
    /\ (* The headline lifecycle outcome. *)
       p2.(Governor.Proposal.phase) = Governor.PhaseExecuted.
Proof.
  intros _Hmono.
  exists witness_p1, witness_p2, witness_throttle_after.
  split; [exact step1_propose_optimistic_succeeds|].
  split; [exact step1_throttle_consume_succeeds|].
  split; [exact step1_throttle_charge_decreases_by_one_slot|].
  split; [exact step2_observe_succeeded|].
  split; [exact step3_execute_optimistic_succeeds|].
  split; [exact witness_p1_reachable|].
  split; [exact witness_p2_reachable|].
  exact witness_p2_phase_executed.
Qed.

(** ======================================================================
    8. vm_compute cross-check at the concrete witness values
    ====================================================================== *)

(** A single bundled [vm_compute] reduction that evaluates all three
    steps at the concrete numerics, confirming the post-state matches
    [witness_p2] with phase [PhaseExecuted], the throttle drained by
    exactly [FIX_ONE / 5 = 2*10^17] D18, and proposalsAvailable in the
    post-throttle equal to 4 (one slot consumed from a 5-slot capacity).

    This is the audit-facing concrete witness: every numeric in the
    lifecycle is reduced to a closed value, so an auditor can read off
    "5 → 4 charges available, currentCharge 10^18 → 8*10^17, phase
    PhaseSubmitted → PhaseExecuted" without re-running a proof
    assistant. *)
Lemma xcheck_lifecycle_post_state :
  (* Pre-state: 5 proposal slots, full charge. *)
  throttle_charges_for_governor init_throttle init_capacity init_t0 = 5
  /\ init_throttle.(ProposerThrottle.Throttle.currentCharge)
     = ProposerThrottle.FIX_ONE
  (* Step 1: propose returns witness_p1. *)
  /\ Governor.propose_optimistic
       init_pid init_proposer init_vetoDelay init_vetoPeriod
       init_vetoThresholdD18 init_pastSupply
       (throttle_charges_for_governor init_throttle init_capacity init_t0)
       init_targets init_selectors
       (selector_registry_allowlist_bridge init_registry)
       init_t0
     = Governor.Result.Success witness_p1
  (* Step 1 side-effect: throttle drained by FIX_ONE/5. *)
  /\ ProposerThrottle.consume init_throttle init_capacity init_t0
     = ProposerThrottle.Result.Success witness_throttle_after
  /\ witness_throttle_after.(ProposerThrottle.Throttle.currentCharge)
     = 8 * 10 ^ 17
  /\ ProposerThrottle.proposalsAvailable witness_throttle_after
       init_capacity init_now_executable
     = 4
     (* After consume currentCharge = 8*10^17 (4 slots). Across the
        veto window [0, 1101] only ~2.5% of FIX_ONE is refilled
        (1101 / 43200 of a period), insufficient to bring the
        available slot count back up to 5. So at execution time the
        proposer would have exactly 4 slots — one slot of capacity
        consumed by the lifecycle, as expected. *)
  (* Step 2: observation at execution time = PhaseSucceeded. *)
  /\ Governor.observe witness_p1 init_now_executable = Governor.PhaseSucceeded
  (* Step 3: execute_optimistic returns witness_p2 in PhaseExecuted. *)
  /\ Governor.execute_optimistic witness_p1 init_now_executable
     = Governor.Result.Success witness_p2
  /\ witness_p2.(Governor.Proposal.phase) = Governor.PhaseExecuted.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

End EndToEndOptimisticFlow.
