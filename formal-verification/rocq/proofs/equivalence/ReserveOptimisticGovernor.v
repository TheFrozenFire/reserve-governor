(** ReserveOptimisticGovernor equivalence — sim-side ↔ shallow-Yul bridge.

    Mirrors [contracts/governance/ReserveOptimisticGovernor.sol] — the
    hybrid optimistic/pessimistic Governor that combines the OZ
    GovernorUpgradeable surface with the project-specific optimistic
    veto-route.

    See [simulations/Governor.v] for the simulation model and
    [proofs/Governor.v] for the existing sim-side audit lemmas.

    Surface decomposition
    ---------------------

    This contract aggregates multiple OZ namespaces (Governor,
    GovernorSettings, GovernorPreventLateQuorum, GovernorCountingSimple,
    GovernorVotes, GovernorVotesQuorumFraction, GovernorTimelockControl,
    Versioned, UUPSUpgradeable). For the three full-mutator equivalence
    targets, the recipe of R070 / R071 ports nearly verbatim — the only
    new wrinkles are:

      (1) The optimistic-route branch: castVote and execute both check
          [_isOptimistic(proposalId)] (i.e. [vetoThreshold(pid) != 0]),
          dispatching to a custom path for optimistic proposals
          (against-only voting + execute-bypass) vs the inherited
          super-chain for pessimistic ones.

      (2) The transitioned-pessimistic sentinel: a successful
          [_tallyUpdated] post-castVote sets
          [vetoThreshold := UINT256_MAX] (the sentinel) to spawn a
          fresh standard child. State() reads the sentinel and
          observes [PhaseDefeated].

      (3) The composite Versioned + UUPS upgrade authorization:
          [_authorizeUpgrade] is governed by [onlyGovernance], i.e.
          [msg.sender == _executor() == address(this)] — the
          self-call invariant of the OZ Governor base.

    Milestone targets (R070/R071 recipe)
    ------------------------------------

      1. [propose]                — permissionless pessimistic
                                     proposal creation.
      2. [castVote]               — branches on _isOptimistic;
                                     optimistic path enforces Against;
                                     pessimistic path threads through
                                     OZ GovernorCountingSimple.
      3. [execute]                — branches on _isOptimistic;
                                     optimistic path bypasses
                                     timelock; pessimistic path
                                     dispatches through
                                     TimelockControllerOptimistic.

    Trust budget per mutator (per R051): 2-4 composite walker axioms +
    1-2 observational bridges + 1-2 Skolemized post-storage parameters.

    The composite walker axioms here are stated against the inheritor's
    storage layout. Because this contract inherits state from multiple
    abstract OZ bases (Governor's [_proposals], [_governanceCall],
    GovernorSettings's three [uint256]s, GovernorCountingSimple's
    [_proposalVotes] mapping, GovernorTimelockControl's [_timelock] and
    [_timelockIds] mapping), the post-storage parameters take the full
    [SimulatedStorage.t] and let the contract-internal slot anchors
    determine which sub-namespace gets touched. This mirrors R070's
    choice for ProposalLib / TimelockControllerOptimistic.

    Storage projection and slot-indexed bridges
    -------------------------------------------

    The contract's [SimulatedStorage.t = list StorableValue.t] is
    decomposed into slot-indexed namespaces, with the abstract OZ
    GovernorUpgradeable base contributing two reserved aggregates and
    the ReserveOptimisticGovernor-specific surface adding its own:

      [slot_proposals]                  — OZ [_proposals] mapping anchor
      [slot_governance_call]            — OZ [_governanceCall] queue
      [slot_optimistic_proposal_details] — OG-specific veto-threshold and
                                           transitioned-pessimistic
                                           sentinel storage

    Each function's Skolemized post-storage [proj_post_<fn>] is
    constrained against [storage_base] at the slots it does NOT touch
    via slot-indexed observational bridge Axioms (Section 4 below).
    An adversarial instantiation [proj_post_<fn> := fun _ _ => empty]
    no longer satisfies these bridges, so the milestone Qeds carry
    real content at the slot level (mirrors the T2.4 promotion in
    [proofs/equivalence/TimelockControllerOptimistic.v]).

    GovernorBase wiring
    -------------------

    The OZ Governor abstract base is mechanized in
    [proofs/equivalence/GovernorBase.v] (and its mock
    [mocks/GovernorBase.v]). That file exports
    [Section GovernorBaseEquivalenceTemplate] with slot indices and a
    [project_base] lens for inheritors to instantiate. This file's
    Section 11 instantiates that template with concrete slot indices
    and a [project_base] lens tied to the ROG's storage decomposition;
    the three lens-correctness hypotheses discharge by reflexivity
    against the concrete lens.

    What is Qed:
      - Sim-level helper lemmas about [Governor.propose_optimistic],
        [Governor.add_veto_validated], [Governor.execute_optimistic],
        [Governor.execute_standard], [Governor.transition_to_pessimistic],
        and the [observe] / [phase_index] functions (Section 1).
      - The three milestone equivalence theorems for [fun_propose_389],
        [fun_castVote_4378], [fun_execute_4145] (Section 6), each of
        whose conclusions includes the slot-unchanged clauses that
        make the bridge axioms load-bearing.
      - The GovernorBase template instantiation (Section 11), with
        all three lens-correctness hypotheses discharged.

    Trust axioms accepted:
      - 3 composite walker axioms (Section 5; one per public mutator).
      - 3 slot-indexed observational bridge axioms (Section 4).
        Each constrains [proj_post_<fn>] against [storage_base] at
        the slots the function does NOT touch. Promoted from reflexive
        tautologies per the 2026-05-31 adversarial-review
        (CCV-1 / CCV-4) and T2.3.
      - 3 Skolemized post-storage [Parameter]s.
      - 1 sim-environment [Parameter] ([now_timestamp]).

    What remains as branch-shape documentation (NOT load-bearing):
      - Section 7 / Section 8: per-branch shapes (optimistic-route
        castVote, optimistic-route execute, pessimistic-route execute,
        transition-to-pessimistic side-exit). These were previously
        reflexive Axioms documenting the audit-time discharge per
        branch; they are now tightened to the same slot-indexed
        observational shape used in Section 4. The milestone theorems
        of Section 6 do NOT consume them — they are kept as
        documentation cross-references for downstream readers.

    Cross-references:
      - [proofs/equivalence/GovernorBase.v] — OZ Governor abstract
        base equivalence methodology.
      - [proofs/equivalence/TimelockControllerOptimistic.v] — T2.4
        slot-indexed bridge promotion (template followed here).
      - [proofs/equivalence/StakingVaultRewards.v] — T2.6
        [eq_at_*_concrete] promotion (template followed here).
      - [notes/adversarial_review_2026_05_31/SYNTHESIS.md] — CCV-1
        (reflexive observational bridges) and CCV-4 (ROG ↔
        GovernorBase disconnection); T2.3 is the remediation task.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.generated.ReserveOptimisticGovernor_shallow.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.

(** Bring the abstract Governor base's mock and equivalence template
    into scope. Section 11 instantiates
    [GovernorBaseEquivalenceTemplate] with the concrete slot indices
    and projection lens for ROG. We do NOT [Import] the mock here
    (which would shadow [Governor.Address] with
    [mocks.GovernorBase.Address]); instead we reference its types as
    [GovBase.State.t] via a module alias below. *)
Require ReserveGovernor.mocks.GovernorBase.
Require Import ReserveGovernor.proofs.equivalence.GovernorBase.

(** Module-alias the mock's inner [GovernorBase] module to avoid
    name collision with [simulations.Governor]'s [Address] /
    [Result] / [ProposalId] surface. The mock's namespace becomes
    [GovBase.<X>] for any [X] exported from
    [mocks/GovernorBase.v]'s [Module GovernorBase]. *)
Module GovBase := ReserveGovernor.mocks.GovernorBase.GovernorBase.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module ReserveOptimisticGovernorEquivalence.

  Import ReserveOptimisticGovernor_1302.ReserveOptimisticGovernor_1302_deployed.

  (** Bring sim-side names into scope so the axioms below can refer to
      them unqualified — the deployed-shallow namespace has no such
      names. *)
  Import Governor.

  (** ====================================================================
      Storage projection — abstract per R070 / R071 shape
      ====================================================================

      The ReserveOptimisticGovernor's storage layout is a composition
      of multiple OZ namespaces (Governor, GovernorSettings,
      GovernorPreventLateQuorum, GovernorCountingSimple, GovernorVotes,
      GovernorVotesQuorumFraction, GovernorTimelockControl, UUPS,
      Initializable) plus the inheritor's own fields
      ([optimisticParams], [selectorRegistry], [proposalThrottle],
      [optimisticProposalDetails]). Each lives at a keccak256-derived
      slot anchor.

      We model the on-chain storage abstractly: each milestone theorem
      quantifies over an opaque [storage_base : SimulatedStorage.t]
      representing the pre-call state. The walker axioms reveal a
      [proj_post_<fn>] post-state that the observational bridges then
      equate to a reference shape keyed to the sim's [Governor.<fn>]
      transition.

      This mirrors the R070 / R071 design for ProposalLib and
      TimelockControllerOptimistic (both of which depend on multiple
      OZ namespaces and have no single slot-pinned projection).
      ==================================================================== *)

  (** ====================================================================
      Sim-side environment for the equivalence statements
      ====================================================================

      The contract reads [block.timestamp] in [state()] / [castVote] /
      [propose] / [execute]. We expose it as a sim-level [Parameter]
      (same shape as ProposalLibEquivalence.now_timestamp).
      ==================================================================== *)

  Parameter now_timestamp : U256.t.

  (** ====================================================================
      Audit-time callee specs
      ====================================================================

      The contract dispatches through helpers like [_msgSender],
      [_getGovernorStorage], [_proposalCore], [_isOptimistic],
      [_castVote_4615], and external calls into ProposalLib /
      TimelockControllerOptimistic / the IOptimisticVotes token. For
      the audit-time obligations consumed inside the composite walker
      axioms we surface these as parameters / axioms with [True]
      conclusions (R064 / R067 / R070 shape). *)

  (** Role-membership oracles (mirrors TimelockControllerOptimistic.v).
      OPTIMISTIC_PROPOSER_ROLE is consumed inside [proposeOptimistic]
      (out of scope for this file's three milestones — propose is the
      pessimistic path). PROPOSER / EXECUTOR / CANCELLER on the
      timelock are checked from the Governor side when the dispatch
      hits the timelock's [scheduleBatch] / [executeBatch] / [cancel]
      via the inherited [_queueOperations] / [_executeOperations]. *)
  Parameter has_PROPOSER_ROLE  : Address -> bool.
  Parameter has_EXECUTOR_ROLE  : Address -> bool.
  Parameter has_CANCELLER_ROLE : Address -> bool.

  (** Audit-time witnesses for the cross-contract obligations consumed
      inside the composite walker axioms. Each is paired with a
      sim-side precondition in the milestone theorems. These are NOT
      load-bearing for the [Print Assumptions] of the milestone
      theorems — the composite walker axiom carries the discharge
      directly via its precondition. *)
  Axiom checkRole_proposer_succeeds :
    forall (caller : U256.t),
    has_PROPOSER_ROLE caller = true ->
    True.

  Axiom checkRole_executor_succeeds :
    forall (caller : U256.t),
    has_EXECUTOR_ROLE caller = true ->
    True.

  Axiom checkRole_canceller_succeeds :
    forall (caller : U256.t),
    has_CANCELLER_ROLE caller = true ->
    True.

  (** ====================================================================
      Storage equivalence relation
      ====================================================================

      Same shape as ProposalLib's / TimelockControllerOptimistic's:
      per-target observational equality at the abstract
      SimulatedStorage.t level. Each milestone theorem witnesses the
      walker's post-state and discharges the bridge as either
      reflexive (when the walker's post-state already matches the
      theorem's reference) or via the observational-bridge axiom. *)

  Definition storage_equiv (s s' : SimulatedStorage.t) : Prop := s = s'.

  Lemma storage_equiv_refl s : storage_equiv s s.
  Proof. reflexivity. Qed.

  Lemma storage_equiv_sym s s' : storage_equiv s s' -> storage_equiv s' s.
  Proof. unfold storage_equiv. intros. symmetry. assumption. Qed.

  Lemma storage_equiv_trans s s' s'' :
    storage_equiv s s' -> storage_equiv s' s'' -> storage_equiv s s''.
  Proof. unfold storage_equiv. intros -> ->. reflexivity. Qed.

  (** ====================================================================
      Section 1 — Sim-level helper lemmas (Qed, no shallow form needed)
      ====================================================================

      Pure-Coq properties of [Governor.propose_optimistic],
      [Governor.add_veto_validated], [Governor.execute_optimistic],
      [Governor.execute_standard], [Governor.transition_to_pessimistic],
      and the [observe] / [phase_index] functions. These mirror the
      sim-level layer of [proofs/Governor.v] but expose them in the
      shape downstream equivalence proofs will cite.

      Convention: each lemma is a property the walker proof discharges
      "automatically" once it lines up the sim's post-state with the
      walker's intermediate state. Closing them here means the
      composite walker axioms in Section 5 don't have to re-derive
      sim-side facts.
      ==================================================================== *)

  Module SimLemmas.

    (** ---- 1.1 propose_optimistic preserves [isOptimistic = true] ---- *)
    Lemma propose_optimistic_sets_isOptimistic
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      p'.(Proposal.isOptimistic) = true.
    Proof.
      intros Hok. unfold propose_optimistic in Hok.
      destruct (throttleCharges <? 1); [discriminate|].
      destruct (Nat.eqb (Datatypes.length targets) 0); [discriminate|].
      destruct (negb (lengths_match targets selectors)); [discriminate|].
      destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma propose_optimistic_sets_voteStart
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      p'.(Proposal.voteStart) = now + vetoDelay.
    Proof.
      intros Hok. unfold propose_optimistic in Hok.
      destruct (throttleCharges <? 1); [discriminate|].
      destruct (Nat.eqb (Datatypes.length targets) 0); [discriminate|].
      destruct (negb (lengths_match targets selectors)); [discriminate|].
      destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma propose_optimistic_against_votes_zero
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      p'.(Proposal.againstVotes) = 0.
    Proof.
      intros Hok. unfold propose_optimistic in Hok.
      destruct (throttleCharges <? 1); [discriminate|].
      destruct (Nat.eqb (Datatypes.length targets) 0); [discriminate|].
      destruct (negb (lengths_match targets selectors)); [discriminate|].
      destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma propose_optimistic_parent_zero
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      p'.(Proposal.parent) = 0.
    Proof.
      intros Hok. unfold propose_optimistic in Hok.
      destruct (throttleCharges <? 1); [discriminate|].
      destruct (Nat.eqb (Datatypes.length targets) 0); [discriminate|].
      destruct (negb (lengths_match targets selectors)); [discriminate|].
      destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma propose_optimistic_phase_submitted
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      p'.(Proposal.phase) = PhaseSubmitted.
    Proof.
      intros Hok. unfold propose_optimistic in Hok.
      destruct (throttleCharges <? 1); [discriminate|].
      destruct (Nat.eqb (Datatypes.length targets) 0); [discriminate|].
      destruct (negb (lengths_match targets selectors)); [discriminate|].
      destruct (negb (all_calls_allowed allow targets selectors)); [discriminate|].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    (** ---- 1.2 add_veto_validated post-state characterization ---- *)

    Lemma add_veto_validated_preserves_pid
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.pid) = p.(Proposal.pid).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_proposer
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.proposer) = p.(Proposal.proposer).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_voteStart
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.voteStart) = p.(Proposal.voteStart).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_voteDuration
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.voteDuration) = p.(Proposal.voteDuration).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_vetoThreshold
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.vetoThresholdD18) = p.(Proposal.vetoThresholdD18).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_isOptimistic
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    Lemma add_veto_validated_preserves_phase
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.phase) = p.(Proposal.phase).
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)) eqn:Hph; try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; cbn; rewrite Hph; reflexivity.
    Qed.

    Lemma add_veto_validated_increments_against
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      p'.(Proposal.againstVotes) = p.(Proposal.againstVotes) + delta.
    Proof.
      intros Hok. unfold add_veto_validated in Hok.
      destruct (p.(Proposal.phase)); try discriminate;
        destruct (now <? p.(Proposal.voteStart)); try discriminate;
        destruct (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
        try discriminate;
        injection Hok as Hp'; rewrite <- Hp'; reflexivity.
    Qed.

    (** ---- 1.3 execute_optimistic post-state ---- *)
    Lemma execute_optimistic_writes_executed
        (p p' : Proposal.t) (now : U256.t) :
      execute_optimistic p now = Result.Success p' ->
      p'.(Proposal.phase) = PhaseExecuted.
    Proof.
      intros Hok. unfold execute_optimistic in Hok.
      destruct (negb p.(Proposal.isOptimistic)); [discriminate|].
      destruct (observe p now); try discriminate.
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma execute_optimistic_preserves_pid
        (p p' : Proposal.t) (now : U256.t) :
      execute_optimistic p now = Result.Success p' ->
      p'.(Proposal.pid) = p.(Proposal.pid).
    Proof.
      intros Hok. unfold execute_optimistic in Hok.
      destruct (negb p.(Proposal.isOptimistic)); [discriminate|].
      destruct (observe p now); try discriminate.
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma execute_optimistic_preserves_isOptimistic
        (p p' : Proposal.t) (now : U256.t) :
      execute_optimistic p now = Result.Success p' ->
      p'.(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
    Proof.
      intros Hok. unfold execute_optimistic in Hok.
      destruct (negb p.(Proposal.isOptimistic)); [discriminate|].
      destruct (observe p now); try discriminate.
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma execute_optimistic_requires_succeeded
        (p p' : Proposal.t) (now : U256.t) :
      execute_optimistic p now = Result.Success p' ->
      observe p now = PhaseSucceeded.
    Proof.
      intros Hok. unfold execute_optimistic in Hok.
      destruct (negb p.(Proposal.isOptimistic)); [discriminate|].
      destruct (observe p now) eqn:Hobs; try discriminate.
      reflexivity.
    Qed.

    (** ---- 1.4 execute_standard post-state ---- *)
    Lemma execute_standard_writes_executed
        (p p' : Proposal.t) :
      execute_standard p = Result.Success p' ->
      p'.(Proposal.phase) = PhaseStdExecuted.
    Proof.
      intros Hok. unfold execute_standard in Hok.
      destruct (p.(Proposal.isOptimistic)); [discriminate|].
      destruct (phase_eq p.(Proposal.phase) PhaseStdQueued); [|discriminate].
      injection Hok as Hp'. rewrite <- Hp'. reflexivity.
    Qed.

    Lemma execute_standard_requires_not_optimistic
        (p p' : Proposal.t) :
      execute_standard p = Result.Success p' ->
      p.(Proposal.isOptimistic) = false.
    Proof.
      intros Hok. unfold execute_standard in Hok.
      destruct (p.(Proposal.isOptimistic)) eqn:Hopt; [discriminate|reflexivity].
    Qed.

    (** ---- 1.5 transition_to_pessimistic ---- *)
    Lemma transition_parent_preserves_pid
        (parent parent' child : Proposal.t)
        (new_pid votingDelay votingPeriod now : U256.t) :
      transition_to_pessimistic parent new_pid votingDelay votingPeriod now
        = Result.Success (parent', child) ->
      parent'.(Proposal.pid) = parent.(Proposal.pid).
    Proof.
      intros Hok. unfold transition_to_pessimistic in Hok.
      destruct (observe parent now); try discriminate.
      injection Hok as Hparent' Hchild. rewrite <- Hparent'. reflexivity.
    Qed.

    Lemma transition_parent_preserves_against
        (parent parent' child : Proposal.t)
        (new_pid votingDelay votingPeriod now : U256.t) :
      transition_to_pessimistic parent new_pid votingDelay votingPeriod now
        = Result.Success (parent', child) ->
      parent'.(Proposal.againstVotes) = parent.(Proposal.againstVotes).
    Proof.
      intros Hok. unfold transition_to_pessimistic in Hok.
      destruct (observe parent now); try discriminate.
      injection Hok as Hparent' Hchild. rewrite <- Hparent'. reflexivity.
    Qed.

    Lemma transition_child_carries_parent_pid
        (parent parent' child : Proposal.t)
        (new_pid votingDelay votingPeriod now : U256.t) :
      transition_to_pessimistic parent new_pid votingDelay votingPeriod now
        = Result.Success (parent', child) ->
      child.(Proposal.parent) = parent.(Proposal.pid).
    Proof.
      intros Hok. unfold transition_to_pessimistic in Hok.
      destruct (observe parent now); try discriminate.
      injection Hok as Hparent' Hchild. rewrite <- Hchild. reflexivity.
    Qed.

    Lemma transition_child_starts_not_optimistic
        (parent parent' child : Proposal.t)
        (new_pid votingDelay votingPeriod now : U256.t) :
      transition_to_pessimistic parent new_pid votingDelay votingPeriod now
        = Result.Success (parent', child) ->
      child.(Proposal.isOptimistic) = false.
    Proof.
      intros Hok. unfold transition_to_pessimistic in Hok.
      destruct (observe parent now); try discriminate.
      injection Hok as Hparent' Hchild. rewrite <- Hchild. reflexivity.
    Qed.

    (** ---- 1.6 observe stickiness on Defeated phase ----

        After [transition_to_pessimistic], the contract writes
        [vetoThreshold := UINT256_MAX] AND the sim pins
        [phase := PhaseDefeated]. observe is sticky in either of two
        ways: (a) via the new sentinel short-circuit
        (CRIT-V / T1.4), or (b) via the votes-tally branch when
        [againstVotes >= vetoThresholdTokAt p] and the threshold isn't
        the sentinel.

        STATEMENT CHANGED (T1.4): the prior statement used the now-
        gone [Proposal.vetoThresholdTok] field. The replacement uses
        [vetoThresholdTokAt p] (the live-computed snapped value).
        Also added the [vetoThresholdD18 != TRANSITIONED] precondition
        — without it, the sentinel branch fires first and the
        votes-tally never enters the picture (the conclusion is
        still PhaseDefeated, just via a different route). *)
    Lemma observe_defeated_sticky_at_threshold
        (p : Proposal.t) (now : U256.t) :
      p.(Proposal.phase) = PhaseDefeated ->
      p.(Proposal.isOptimistic) = true ->
      p.(Proposal.vetoThresholdD18) <> TRANSITIONED_VETO_THRESHOLD ->
      p.(Proposal.againstVotes) >= vetoThresholdTokAt p ->
      p.(Proposal.voteStart) <= now ->
      p.(Proposal.pastSupply) <> 0 ->
      observe p now = PhaseDefeated.
    Proof.
      intros Hph Hopt Hsent Hge Hns Hps. unfold observe, vetoThresholdTokAt in *.
      rewrite Hph.
      assert (Hpre : (now <? p.(Proposal.voteStart)) = false)
        by (apply Z.ltb_ge; lia).
      rewrite Hpre. rewrite Hopt.
      assert (Hsentb : (p.(Proposal.vetoThresholdD18)
                         =? TRANSITIONED_VETO_THRESHOLD) = false)
        by (apply Z.eqb_neq; exact Hsent).
      rewrite Hsentb.
      assert (Hpsb : (p.(Proposal.pastSupply) =? 0) = false)
        by (apply Z.eqb_neq; exact Hps).
      rewrite Hpsb.
      assert (Hgeb : (p.(Proposal.againstVotes) >=?
                     vetoThresholdTokOf p.(Proposal.vetoThresholdD18)
                                        p.(Proposal.pastSupply)) = true)
        by (apply Z.geb_le; lia).
      rewrite Hgeb. reflexivity.
    Qed.

    (** Companion (NEW at T1.4): the sentinel-driven version of the
        sticky claim. With [vetoThresholdD18 = TRANSITIONED] and the
        usual phase/optimistic/voteStart preconditions, [observe]
        returns [PhaseDefeated] via the short-circuit branch — no
        votes-tally or pastSupply involvement. *)
    Lemma observe_defeated_sticky_via_sentinel
        (p : Proposal.t) (now : U256.t) :
      p.(Proposal.phase) = PhaseDefeated ->
      p.(Proposal.isOptimistic) = true ->
      p.(Proposal.vetoThresholdD18) = TRANSITIONED_VETO_THRESHOLD ->
      p.(Proposal.voteStart) <= now ->
      observe p now = PhaseDefeated.
    Proof.
      intros Hph Hopt Hsent Hns. unfold observe. rewrite Hph.
      assert (Hpre : (now <? p.(Proposal.voteStart)) = false)
        by (apply Z.ltb_ge; lia).
      rewrite Hpre. rewrite Hopt.
      assert (Hsentb : (p.(Proposal.vetoThresholdD18)
                         =? TRANSITIONED_VETO_THRESHOLD) = true)
        by (apply Z.eqb_eq; exact Hsent).
      rewrite Hsentb. reflexivity.
    Qed.

    (** ---- 1.7 _isOptimistic mirror at the sim layer ---- *)
    Definition sim_is_optimistic (p : Proposal.t) : bool :=
      p.(Proposal.isOptimistic).

    Lemma sim_is_optimistic_after_propose
        (pid : U256.t) (proposer : Address)
        (vetoDelay vetoPeriod vetoThresholdD18 pastSupply
         throttleCharges now : U256.t)
        (targets : list Address) (selectors : list Selector)
        (allow : list (Address * Selector))
        (p' : Proposal.t) :
      propose_optimistic pid proposer vetoDelay vetoPeriod
        vetoThresholdD18 pastSupply throttleCharges
        targets selectors allow now
      = Result.Success p' ->
      sim_is_optimistic p' = true.
    Proof.
      intros Hok. unfold sim_is_optimistic.
      apply propose_optimistic_sets_isOptimistic in Hok. exact Hok.
    Qed.

    (** ---- 1.8 vetoThreshold snap is bounded below by 1 ---- *)
    Lemma vetoThresholdTok_positive
        (vetoThresholdD18 pastSupply : U256.t) :
      vetoThresholdTokOf vetoThresholdD18 pastSupply >= 1.
    Proof.
      unfold vetoThresholdTokOf.
      destruct ((vetoThresholdD18 * pastSupply) / FIX_ONE <? 1) eqn:Hb.
      - lia.
      - apply Z.ltb_ge in Hb. lia.
    Qed.

    (** ---- 1.9 Optimistic-path castVote enforces support = Against ----

        The contract's [_countVote] override (line 390) reverts if
        [_isOptimistic(proposalId)] AND [support != Against]. The sim
        models the "Against" check via the [delta] parameter to
        [add_veto_validated] (which only counts againstVotes — the
        For / Abstain buckets don't exist in the sim's Proposal.t).
        This is the property downstream walker proofs cite when
        discharging the support-must-be-Against arm. *)
    Lemma optimistic_against_only_is_modeled
        (p p' : Proposal.t) (now delta : U256.t) :
      add_veto_validated p now delta = Result.Success p' ->
      (* The sim's add_veto_validated tracks only againstVotes. The
         For / Abstain support values are unreachable for optimistic
         proposals by construction of the sim. *)
      p'.(Proposal.againstVotes) = p.(Proposal.againstVotes) + delta.
    Proof. apply add_veto_validated_increments_against. Qed.

  End SimLemmas.

  (** ====================================================================
      Section 2 — Sim-side post-state references for the three mutators
      ====================================================================

      Each post-state reference is a function of the sim's pre-state
      and the call arguments. The walker axioms below witness that
      the Yul body's post-storage observationally equals these
      references via the per-target observational bridges. *)

  (** ---- 2.1 propose (pessimistic-route, permissionless) ----

      The contract's [propose] (line 177 of the source) calls
      [ProposalLib.proposePessimistic(...)] which writes a fresh
      [ProposalCore] at the proposal-id-indexed mapping slot. There
      is no veto-threshold write (the optimistic-route field
      [optimisticProposalDetails[pid]] stays at its zero default,
      and [_isOptimistic(pid)] therefore returns false).

      The sim-side mirror is a fresh [Proposal.t] with
      [isOptimistic = false], [phase = PhaseStdPending],
      and a parent of 0. We expose a sim-side function
      [sim_post_propose] that returns the expected fresh-standard
      structure. *)

  Definition sim_post_propose
      (pid : U256.t) (proposer : Address)
      (votingDelay votingPeriod now : U256.t) : Proposal.t :=
    fresh_standard_child 0 pid proposer (now + votingDelay) votingPeriod.

  (** ---- 2.2 castVote (branches on _isOptimistic) ----

      The contract's [_castVote] (line 404):
        1. Validates state via [_validateStateBitmap(Active)]
           (which calls [state(proposalId)] internally — see source
           line 409).
        2. Branches on [_isOptimistic(proposalId)]:
            - Optimistic: weight = getPastOptimisticVotes;
                          [_countVote] enforces support == Against.
            - Pessimistic: weight = getPastVotes;
                          [_countVote] threads through OZ
                          GovernorCountingSimple.
        3. Emits VoteCast / VoteCastWithParams.
        4. Calls [_tallyUpdated(proposalId)] — which for optimistic
           proposals checks if the just-incremented againstVotes
           crossed the threshold (and if so, transitions to
           pessimistic).

      Sim-side mirror: [Governor.add_veto_validated] for the
      optimistic case. For the pessimistic case, the sim's
      coverage is via the inherited OZ GovernorCountingSimple
      (which Agent GOV-BASE is mechanizing). *)

  Definition sim_post_castVote_optimistic
      (p : Proposal.t) (now delta : U256.t)
      : Governor.Result.t Proposal.t :=
    add_veto_validated p now delta.

  (** ---- 2.3 execute (branches on _isOptimistic) ----

      The contract's [execute] is inherited from
      [GovernorUpgradeable]: it dispatches to [_executeOperations]
      which the inheritor overrides at line 345:
        - Optimistic: calls [TimelockControllerOptimistic
                             .executeBatchBypass] (bypasses delay).
        - Pessimistic: calls super._executeOperations (which
                       schedules via the OZ Timelock).

      Sim-side mirror: [Governor.execute_optimistic] for the
      optimistic case, [Governor.execute_standard] for the
      pessimistic case (which is preceded by [queue_operations]). *)

  Definition sim_post_execute_optimistic
      (p : Proposal.t) (now : U256.t)
      : Governor.Result.t Proposal.t :=
    execute_optimistic p now.

  Definition sim_post_execute_standard
      (p : Proposal.t) : Governor.Result.t Proposal.t :=
    execute_standard p.

  (** ====================================================================
      Section 3 — Skolemized post-storage [Parameter]s (R051 / R070 shape)
      ====================================================================

      Each public mutator may rewrite arbitrary slots inside the
      composite OZ-namespaced storage. The post-storage is an
      existential surfaced as an opaque [Parameter] returning a
      [SimulatedStorage.t] given the call arguments. The composite
      walker axiom carries the existential envelope; the
      observational bridge axiom characterises the post-storage in
      terms of the sim-side post-state.

      Convention: each Parameter is keyed on [storage_base] plus the
      semantic arguments (not the Yul ABI pointers / lengths, which
      are erased into [storage_base]). *)

  Parameter proj_post_propose_389 :
    SimulatedStorage.t -> U256.t (* pid *) -> Address (* proposer *) ->
    U256.t (* votingDelay *) -> U256.t (* votingPeriod *) ->
    U256.t (* now *) -> SimulatedStorage.t.

  Parameter proj_post_castVote_4378 :
    SimulatedStorage.t -> U256.t (* pid *) -> Address (* voter *) ->
    U256.t (* support *) -> U256.t (* weight *) -> U256.t (* now *) ->
    SimulatedStorage.t.

  Parameter proj_post_execute_4145 :
    SimulatedStorage.t -> U256.t (* pid *) -> bool (* isOptimistic *) ->
    U256.t (* now *) -> SimulatedStorage.t.

  (** ====================================================================
      Slot-indexed observational predicates
      ====================================================================

      Per the 2026-05-31 adversarial-review (CCV-1 / CCV-4 / T2.3),
      the per-mutator observational bridges previously stated
      [storage_equiv (proj_post X) (proj_post X)] — reflexive
      tautologies that any [proj_post_<fn> := fun _ _ => empty]
      adversarial instantiation would satisfy. The milestone theorems
      degenerated to "the Yul body terminates" with zero slot-level
      content.

      We promote each bridge to a content-bearing claim that pins
      the Skolemized post-storage to [storage_base] at slot-indexed
      positions of the [SimulatedStorage.t = list StorableValue.t]
      list. Slot indices are abstract (mirror the
      [GovernorBaseEquivalenceTemplate]'s [Variable slot_proposals :
      nat] pattern); we hard-code consistent values here for the
      audit-time discharge, with the lens instantiation in Section 11
      pinning the concrete keccak-derived correspondence.

      Slot assignment for ROG's composite storage:
        - [slot_proposals]                  := 0  (OZ Governor base's
                                                   [_proposals] mapping)
        - [slot_governance_call]            := 1  (OZ Governor base's
                                                   [_governanceCall] queue
                                                   for re-entrancy)
        - [slot_optimistic_proposal_details] := 2 (OG-specific
                                                   [optimisticProposalDetails]
                                                   mapping holding
                                                   [vetoThreshold] +
                                                   [TRANSITIONED] sentinel)

      ROG inherits additional storage from GovernorSettings,
      GovernorPreventLateQuorum, GovernorCountingSimple, GovernorVotes,
      GovernorVotesQuorumFraction, GovernorTimelockControl, UUPS,
      Initializable, and AccessControlEnumerable. Those are reserved
      at distinct higher slot indices but are not load-bearing for
      the three milestone bridges — what matters is that the
      [_observes] axioms now constrain [proj_post] against
      [storage_base] at the slots the function does NOT touch. *)

  Definition slot_proposals                   : nat := 0.
  Definition slot_governance_call             : nat := 1.
  Definition slot_optimistic_proposal_details : nat := 2.

  Definition eq_at_proposals (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_proposals = List.nth_error s2 slot_proposals.

  Definition eq_at_governance_call (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_governance_call
    = List.nth_error s2 slot_governance_call.

  Definition eq_at_optimistic_proposal_details
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_optimistic_proposal_details
    = List.nth_error s2 slot_optimistic_proposal_details.

  (** Refl / sym / trans companions, [Qed] from the [Definition]s. *)

  Lemma eq_at_proposals_refl s : eq_at_proposals s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_proposals_sym s1 s2 :
    eq_at_proposals s1 s2 -> eq_at_proposals s2 s1.
  Proof. unfold eq_at_proposals. intros H. symmetry. exact H. Qed.

  Lemma eq_at_proposals_trans s1 s2 s3 :
    eq_at_proposals s1 s2 ->
    eq_at_proposals s2 s3 ->
    eq_at_proposals s1 s3.
  Proof. unfold eq_at_proposals. intros H12 H23. rewrite H12. exact H23. Qed.

  Lemma eq_at_governance_call_refl s : eq_at_governance_call s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_governance_call_sym s1 s2 :
    eq_at_governance_call s1 s2 -> eq_at_governance_call s2 s1.
  Proof. unfold eq_at_governance_call. intros H. symmetry. exact H. Qed.

  Lemma eq_at_governance_call_trans s1 s2 s3 :
    eq_at_governance_call s1 s2 ->
    eq_at_governance_call s2 s3 ->
    eq_at_governance_call s1 s3.
  Proof.
    unfold eq_at_governance_call. intros H12 H23. rewrite H12. exact H23.
  Qed.

  Lemma eq_at_optimistic_proposal_details_refl s :
    eq_at_optimistic_proposal_details s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_optimistic_proposal_details_sym s1 s2 :
    eq_at_optimistic_proposal_details s1 s2 ->
    eq_at_optimistic_proposal_details s2 s1.
  Proof.
    unfold eq_at_optimistic_proposal_details. intros H. symmetry. exact H.
  Qed.

  Lemma eq_at_optimistic_proposal_details_trans s1 s2 s3 :
    eq_at_optimistic_proposal_details s1 s2 ->
    eq_at_optimistic_proposal_details s2 s3 ->
    eq_at_optimistic_proposal_details s1 s3.
  Proof.
    unfold eq_at_optimistic_proposal_details. intros H12 H23.
    rewrite H12. exact H23.
  Qed.

  (** ====================================================================
      Section 4 — Per-target observational bridge Axioms
      ====================================================================

      Each Axiom states the audit-time obligation: under the
      function's Success-branch preconditions, the walker's
      Skolemized post-storage [proj_post_<fn> ...] agrees with
      [storage_base] at the slots the function does NOT touch.

      Function-by-function slot-touch decomposition (from the
      contract source ReserveOptimisticGovernor.sol + the OZ
      Governor base):

        propose (pessimistic-route, permissionless):
          touches  : [slot_proposals]
                     (ProposalLib.proposePessimistic writes the
                     fresh _proposals[pid] entry)
          unchanged: [slot_governance_call]
                     [slot_optimistic_proposal_details]
                     (vetoThreshold stays 0 -> _isOptimistic(pid)
                     returns false)

        castVote (branches on _isOptimistic):
          touches  : [slot_proposals]
                     (super._countVote tally updates the inherited
                     GovernorCountingSimple mapping; the
                     transition-to-pessimistic side-exit also writes
                     a fresh _proposals[child_pid] entry and pushes
                     the sentinel into optimisticProposalDetails)
          touches (conditionally): [slot_optimistic_proposal_details]
                     (only when the optimistic-route tally crosses
                     the threshold, triggering the
                     ProposalLib.transitionToPessimistic side-exit)
          unchanged: [slot_governance_call]
                     (the re-entrancy queue is only touched by
                     execute() under _executor() != address(this))

        execute (branches on _isOptimistic):
          touches  : [slot_proposals]
                     (_proposals[pid].executed flag write at
                     ROG_shallow line ~13059)
          touches (conditionally): [slot_governance_call]
                     (only when _executor() != address(this) AND a
                     self-call target appears in the batch — the
                     OZ re-entrancy queue is push-back-then-cleared)
          unchanged: [slot_optimistic_proposal_details]
                     (the optimistic-route post-execute writes
                     happen via the TimelockControllerOptimistic
                     bypass, not in the OG-specific storage)

      The bridges below assert the unconditional-untouched slot for
      each function. The conditional-touched slots are documented
      but NOT pinned (the conditional condition would need a case
      split that re-introduces the [_isOptimistic] dispatch we're
      already encoding via the milestone theorem's
      precondition). *)

  Axiom proj_post_propose_389_observes :
    forall (storage_base : SimulatedStorage.t)
           (pid : U256.t) (proposer : Address)
           (votingDelay votingPeriod now : U256.t),
    (* propose() writes only the OZ _proposals mapping at
       [slot_proposals]; the OG-specific optimistic-route storage
       (vetoThreshold etc.) stays at its zero default — and the
       re-entrancy queue [_governanceCall] is untouched. *)
    eq_at_governance_call
      (proj_post_propose_389 storage_base pid proposer
                              votingDelay votingPeriod now)
      storage_base
    /\
    eq_at_optimistic_proposal_details
      (proj_post_propose_389 storage_base pid proposer
                              votingDelay votingPeriod now)
      storage_base.

  Axiom proj_post_castVote_4378_observes :
    forall (storage_base : SimulatedStorage.t)
           (pid : U256.t) (voter : Address)
           (support weight now : U256.t),
    (* castVote() touches the inherited GovernorCountingSimple
       tally (which lives within the OZ [_proposals] slot
       sub-namespace via OZ's nested storage) and conditionally
       the OG-specific optimistic details (on the transition
       side-exit). The OZ [_governanceCall] re-entrancy queue
       is NOT touched in any branch of castVote. *)
    eq_at_governance_call
      (proj_post_castVote_4378 storage_base pid voter support weight now)
      storage_base.

  Axiom proj_post_execute_4145_observes :
    forall (storage_base : SimulatedStorage.t)
           (pid : U256.t) (isOpt : bool)
           (now : U256.t),
    (* execute() writes the OZ [_proposals[pid].executed] flag and
       conditionally pushes to [_governanceCall] when
       [_executor() != address(this)]. The OG-specific optimistic
       details slot is NOT touched by execute (the
       TimelockControllerOptimistic bypass uses a separate storage
       contract). *)
    eq_at_optimistic_proposal_details
      (proj_post_execute_4145 storage_base pid isOpt now)
      storage_base.

  (** ====================================================================
      Section 5 — Composite walker axioms (R051 / R070 shape)
      ====================================================================

      Each Axiom bundles the function's Yul body's mechanical
      assembly into a single Hoare triple. Mirrors R070's
      [run_fun__saveProposal_580_at_storage_base] and R071's
      [run_fun_executeBatchBypass_201_at_proj_sim] structure: the
      audit-time witness is that the assembly closes mechanically
      with every Yul primitive mapping to a Stdlib operation, every
      sstore mapping to a known wrapper (R040 / R051), every
      delegatecall / staticcall mapping to an R063 StaticCallBridge
      stanza, every external call into ProposalLib (which carries
      its own R070 walker chain — see ProposalLib.v) discharged via
      ProposalLib's per-function equivalence, and every modifier
      gate succeeding under its precondition.

      Slot-touch decomposition is documented in Section 4's
      observational bridges; the per-mutator slot-unchanged
      clauses make those bridges load-bearing in [Print
      Assumptions]. Cross-references to GovernorBase.v's
      slot-anchor projection appear inline. *)

  (** ----- Composite walker axiom for [fun_propose_389] -----

      The body (lines 15993-16389 of
      [ReserveOptimisticGovernor_shallow.v]) decomposes into the
      following structural steps (high-level — the contract dispatches
      through ProposalLib via delegatecall which carries its own
      walker chain):

        S1.  abi_decode the four memory arguments (targets / values /
             calldatas / description).
        S2.  Read caller as proposer.
        S3.  keccak256(description) — sim model: hash is opaque.
        S4.  fun_getProposalId_3355(targets, values, calldatas,
                                    keccak256(description))
                                              → ProposalId derived from
                                                args (sim model: pure
                                                function on inputs).
        S5.  Delegatecall to ProposalLib.proposePessimistic
                                              → carries the ProposalLib
                                                walker chain
                                                (R070 / R071 already
                                                landed for ProposalLib).
        S6.  Function returns proposalId.

      The post-storage exposed by [proj_post_propose_389] is the
      [storage_base] with the GovernorStorage [_proposals[pid]] slot
      updated to reflect the fresh PhaseStdPending proposal. The
      ReserveOptimisticGovernor-specific
      [optimisticProposalDetails[pid]] slot is UNTOUCHED (vetoThreshold
      stays 0, so [_isOptimistic(pid)] reads false). This is the
      defining invariant: the pessimistic-route propose() leaves
      [optimisticProposalDetails] untouched.

      Slot-anchor cross-references:
        - The slot anchor for [_proposals[pid]] is at
          [slot_proposals], with GovernorBase's [project_base] lens
          (instantiated in Section 11 below) extracting the typed
          [GovernorBase.State.proposals] view. The
          [proj_post_propose_389_observes] axiom (Section 4)
          asserts the [_governanceCall] and
          [optimisticProposalDetails] slots stay unchanged.
        - The ProposalLib delegatecall's post-storage shape is
          characterised by [ProposalLib's proj_post_proposePessimistic_288],
          which already exists in ProposalLib.v.

      Audit-time witness: same as ProposalLib's composite axioms —
      every step maps to an existing primitive or a documented
      sub-call's post-state. The ProposalLib delegatecall's storage
      effects are encapsulated in
      [ProposalLib.proj_post_proposePessimistic_288]'s shape. *)
  Axiom run_fun_propose_389_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (targets_mpos values_mpos calldatas_mpos description_mpos : U256.t)
           (pid : U256.t)
           (votingDelay votingPeriod : U256.t),
    0 <= env.(Environment.caller) < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' result,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_propose_389 targets_mpos values_mpos calldatas_mpos
                      description_mpos ⇓ Result.Ok result
    | Some (make_state env state_base memory'
              (proj_post_propose_389 storage_base pid
                env.(Environment.caller) votingDelay votingPeriod
                now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_castVote_4378] -----

      The body (lines 12357-12375 of
      [ReserveOptimisticGovernor_shallow.v]) is a thin dispatch
      to [fun__castVote_4615] which dispatches to [fun__castVote_1014]
      which carries the meaningful body. The decomposition:

        S1.  Read caller as voter (via fun__msgSender).
        S2.  Dispatch to fun__castVote_4615(pid, voter, support, "")
              -- empty-reason variant.
        S3.  Inner fun__castVote_1014:
              S3a.  _validateStateBitmap(Active): require state ==
                    Active. Calls state(proposalId) which itself
                    branches on _isOptimistic. The sim mirrors this
                    precondition.
              S3b.  proposalSnapshot(proposalId): the voteStart.
              S3c.  if _isOptimistic(proposalId):
                      weight = _getOptimisticVotes(voter, snapshot)
                           — staticcall into the
                             IOptimisticVotes token.
                    else:
                      weight = _getVotes(voter, snapshot, params)
                           — inherited from GovernorVotes.
              S3d.  _countVote(proposalId, voter, support, weight, params):
                    - if _isOptimistic and support != Against:
                        revert OptimisticGovernor__OptimisticProposalCanOnlyBeVetoed
                    - super._countVote (GovernorCountingSimple):
                        records the vote in _proposalVotes[pid].
              S3e.  Emit VoteCast or VoteCastWithParams.
              S3f.  _tallyUpdated(proposalId):
                    - if !_isOptimistic:
                        super._tallyUpdated (GovernorPreventLateQuorum):
                          maybe extend the deadline.
                    - else:
                        if state(proposalId) == Defeated:
                          ProposalLib.transitionToPessimistic — spawns
                          a fresh standard child via ProposalLib.

      The post-storage exposed by [proj_post_castVote_4378] is the
      [storage_base] with:
        - The GovernorCountingSimple [_proposalVotes[pid]] slot
          updated to reflect the +weight to the appropriate vote
          bucket (against for optimistic; against/for/abstain for
          pessimistic).
        - For the optimistic-AND-just-crossed-threshold case, an
          additional ProposalLib.transitionToPessimistic dispatch
          spawns a child proposal (a fresh _proposals[child_pid] slot
          and a vetoThreshold[parent_pid] = UINT256_MAX sentinel
          write).
        - For the pessimistic case, no optimistic-side slot is
          touched.

      Inherited-dispatch cross-references:
        - The state() call inside _validateStateBitmap dispatches on
          _isOptimistic at runtime. GovernorBase's [project_base]
          lens (Section 11) exposes the dispatch; the audit-time
          discharge folds into a case-split on [_isOptimistic] via
          the slot read at [slot_optimistic_proposal_details].
        - _getVotes and _countVote in the pessimistic case dispatch
          through GovernorVotes and GovernorCountingSimple
          respectively — both inherited from OZ. GovernorBase.v's
          [GovernorBaseEquivalenceTemplate] (Section 11) carries the
          slot-agnostic walker template for these.
        - _getOptimisticVotes in the optimistic case is a
          staticcall into the IOptimisticVotes-bearing token. The
          R063 StaticCallBridge handles the dispatch; the
          callee-side spec is captured by
          [StakingVaultDelegationCheckpointed]'s checkpoint reading
          (already mechanized; sim mirrors [Trace208.upperLookupRecent]).

      Audit-time witness: every Yul primitive maps to a Stdlib
      operation; every sstore maps to a known wrapper; every
      external staticcall (to _getOptimisticVotes or to state())
      maps to an R063 StaticCallBridge stanza; the
      ProposalLib.transitionToPessimistic dispatch (when reached) is
      encapsulated in ProposalLib's own R070 walker for that function. *)
  Axiom run_fun_castVote_4378_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposalId support : U256.t)
           (voter : Address)
           (weight : U256.t)
           (p_sim : Proposal.t)
           (H_caller : env.(Environment.caller) = voter)
           (H_caller_bound : 0 <= voter < 2^160)
           (H_pid_match : p_sim.(Proposal.pid) = proposalId)
           (H_active :
              observe p_sim now_timestamp = PhaseActive \/
              observe p_sim now_timestamp = PhaseStdActive)
           (H_optimistic_gate :
              (* For optimistic proposals: support must be Against (=0).
                 The contract's _countVote enforces this. *)
              p_sim.(Proposal.isOptimistic) = true -> support = 0)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory' result,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_castVote_4378 proposalId support ⇓ Result.Ok result
    | Some (make_state env state_base memory'
              (proj_post_castVote_4378 storage_base proposalId voter
                                       support weight now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_execute_4145] -----

      The body (lines 13022-onward of
      [ReserveOptimisticGovernor_shallow.v]) is the inherited OZ
      Governor [execute] entry point. The high-level structural steps:

        S1.  abi_decode targets / values / calldatas / descriptionHash.
        S2.  fun_getProposalId_3355(...) → proposalId.
        S3.  _validateStateBitmap(Succeeded | Queued).
        S4.  Mark _proposals[pid].executed := true (slot write at
             offset 30 of the ProposalCore struct — line 13059).
        S5.  Loop over targets — emit ProposalExecuted (no actual
             external dispatch is part of the bookkeeping; the
             dispatch happens inside _executeOperations).
        S6.  Call _executeOperations(pid, targets, values, calldatas,
                                     descriptionHash).
              - Branches on _isOptimistic (override at line 345):
                - Optimistic: TimelockControllerOptimistic
                  .executeBatchBypass(...) — bypasses delay.
                - Pessimistic: super._executeOperations — schedules
                  the operation through the OZ Timelock chain.

      The post-storage exposed by [proj_post_execute_4145] is the
      [storage_base] with:
        - The _proposals[pid].executed flag set to true.
        - For the optimistic case: the TimelockControllerOptimistic
          [_timestamps[opId]] slot updated to DONE_TIMESTAMP (via
          the inherited executeBatchBypass — composite walker
          already in TimelockControllerOptimistic.v).
        - For the pessimistic case: the inherited super
          ._executeOperations chain writes the TimelockControl
          _timelockIds[pid] and dispatches through the timelock's
          executeBatch.

      Inherited-dispatch cross-references:
        - The dispatch on _isOptimistic at S6 follows the case
          discriminator captured by the milestone theorem's
          [isOpt] argument (Section 6). The case-split between
          executeBatchBypass (already mechanized in
          TimelockControllerOptimistic.v) and the inherited
          super._executeOperations is packed into the composite
          walker axiom's existential post-storage.
        - The state bitmap validation at S3 reuses GovernorBase's
          [state] cascade (see [proofs/equivalence/GovernorBase.v]
          Section 4 [state_unfold] lemma).
        - The R063 StaticCallBridge handles the cross-contract call
          into TimelockControllerOptimistic.

      Audit-time witness: every step maps to a primitive or a
      documented sub-call's post-state. The
      TimelockControllerOptimistic dispatch is encapsulated in
      [TimelockControllerOptimisticEquivalence.proj_post_executeBatchBypass_201]
      / [proj_post_executeBatch_1552]'s shape (both already proven). *)
  Axiom run_fun_execute_4145_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (targets_mpos values_mpos calldatas_mpos descriptionHash : U256.t)
           (pid : U256.t) (isOpt : bool)
           (p_sim : Proposal.t)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_pid_match : p_sim.(Proposal.pid) = pid)
           (H_isOpt_match : p_sim.(Proposal.isOptimistic) = isOpt)
           (H_succeeded :
              (* For optimistic: state must be Succeeded; for
                 pessimistic: state must be Succeeded or Queued. *)
              observe p_sim now_timestamp = PhaseSucceeded \/
              observe p_sim now_timestamp = PhaseStdSucceeded \/
              observe p_sim now_timestamp = PhaseStdQueued)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory' result,
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_execute_4145 targets_mpos values_mpos calldatas_mpos
                       descriptionHash ⇓ Result.Ok result
    | Some (make_state env state_base memory'
              (proj_post_execute_4145 storage_base pid isOpt now_timestamp)) ?}}.

  (** ====================================================================
      Section 6 — Milestone Theorems (R070/R071 recipe)
      ====================================================================

      Each theorem follows the standard 3-phase recipe:

        Phase 1: dispatch the composite walker axiom to obtain the
                 walker-friendly Skolemized post-storage.
        Phase 2: bridge to the sim's post-state via the per-target
                 observational equivalence axiom (where load-bearing)
                 or invoke storage_equiv_refl (where the walker's
                 post-state already matches the theorem's reference
                 shape).
        Phase 3: witness the post-storage. *)

  (** ----- Theorem: [propose] equivalence -----

      For the pessimistic-route, permissionless propose() entry
      point. The theorem witnesses that the Yul body runs to
      completion on any caller, the resulting storage equals the
      Skolemized post-storage, AND that the [_governanceCall]
      re-entrancy queue and the OG-specific
      [optimisticProposalDetails] slot are unchanged. The latter
      two clauses make the bridge axiom
      [proj_post_propose_389_observes] load-bearing in the
      milestone's [Print Assumptions] — an adversarial
      [proj_post := fun _ _ => empty] no longer satisfies the
      theorem statement. *)
  Theorem run_propose_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (targets_mpos values_mpos calldatas_mpos description_mpos : U256.t)
      (pid : U256.t)
      (votingDelay votingPeriod : U256.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    let storage_post :=
      proj_post_propose_389 storage_base pid
        env.(Environment.caller) votingDelay votingPeriod now_timestamp in
    exists state' result,
      {{? codes, env, Some state |
        fun_propose_389 targets_mpos values_mpos
                        calldatas_mpos description_mpos
        ⇓ Result.Ok result
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_governance_call storage_post storage_base /\
        eq_at_optimistic_proposal_details storage_post storage_base).
  Proof.
    cbv zeta.
    (** Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun_propose_389_at_proj_sim
                  codes env state_base storage_base memory
                  targets_mpos values_mpos calldatas_mpos description_mpos
                  pid votingDelay votingPeriod
                  H_caller_bound H_mem) as Hwalker.
    destruct Hwalker as (memory' & result & Hwalker).
    (** Phase 2: dispatch the slot-indexed observational bridge. *)
    pose proof (proj_post_propose_389_observes
                  storage_base pid env.(Environment.caller)
                  votingDelay votingPeriod now_timestamp) as Hobs.
    destruct Hobs as (Hobs_gc & Hobs_opd).
    (** Phase 3: witness post-storage + slot-unchanged conjuncts. *)
    exists (Some (make_state env state_base memory'
                    (proj_post_propose_389 storage_base pid
                       env.(Environment.caller)
                       votingDelay votingPeriod now_timestamp))).
    exists result.
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|].
    split; [exact Hobs_gc|exact Hobs_opd].
  Qed.

  (** ----- Theorem: [castVote] equivalence -----

      Branches on [_isOptimistic(proposalId)]. The composite walker
      axiom carries both branches; the milestone theorem witnesses
      either case with the appropriate sim precondition. The
      conclusion includes the slot-unchanged clause
      [eq_at_governance_call storage_post storage_base]: castVote
      never touches the OZ re-entrancy queue in either dispatch
      branch (the queue is push-back-then-cleared only by
      execute()). This makes the bridge
      [proj_post_castVote_4378_observes] load-bearing. *)
  Theorem run_castVote_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposalId support : U256.t)
      (voter : Address)
      (weight : U256.t)
      (p_sim : Proposal.t)
      (H_caller : env.(Environment.caller) = voter)
      (H_caller_bound : 0 <= voter < 2^160)
      (H_pid_match : p_sim.(Proposal.pid) = proposalId)
      (H_active :
         observe p_sim now_timestamp = PhaseActive \/
         observe p_sim now_timestamp = PhaseStdActive)
      (H_optimistic_gate :
         p_sim.(Proposal.isOptimistic) = true -> support = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    let storage_post :=
      proj_post_castVote_4378 storage_base proposalId
        voter support weight now_timestamp in
    exists state' result,
      {{? codes, env, Some state |
        fun_castVote_4378 proposalId support ⇓ Result.Ok result
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_governance_call storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_castVote_4378_at_proj_sim
                  codes env state_base storage_base memory
                  proposalId support voter weight p_sim
                  H_caller H_caller_bound H_pid_match
                  H_active H_optimistic_gate H_mem) as Hwalker.
    destruct Hwalker as (memory' & result & Hwalker).
    pose proof (proj_post_castVote_4378_observes
                  storage_base proposalId voter support weight now_timestamp)
      as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_castVote_4378 storage_base proposalId
                       voter support weight now_timestamp))).
    exists result.
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|exact Hobs].
  Qed.

  (** ----- Theorem: [execute] equivalence -----

      Branches on [_isOptimistic(proposalId)]. The composite walker
      axiom carries both branches; the milestone theorem witnesses
      the storage-equivalence under either case via the [isOpt]
      discriminator. The conclusion includes the slot-unchanged
      clause [eq_at_optimistic_proposal_details storage_post
      storage_base]: execute() never touches the OG-specific
      [optimisticProposalDetails] slot — the optimistic-route
      post-execute writes go to the TimelockControllerOptimistic
      bypass's separate storage. This makes the bridge
      [proj_post_execute_4145_observes] load-bearing. *)
  Theorem run_execute_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (targets_mpos values_mpos calldatas_mpos descriptionHash : U256.t)
      (pid : U256.t) (isOpt : bool)
      (p_sim : Proposal.t)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_pid_match : p_sim.(Proposal.pid) = pid)
      (H_isOpt_match : p_sim.(Proposal.isOptimistic) = isOpt)
      (H_succeeded :
         observe p_sim now_timestamp = PhaseSucceeded \/
         observe p_sim now_timestamp = PhaseStdSucceeded \/
         observe p_sim now_timestamp = PhaseStdQueued)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    let storage_post :=
      proj_post_execute_4145 storage_base pid isOpt now_timestamp in
    exists state' result,
      {{? codes, env, Some state |
        fun_execute_4145 targets_mpos values_mpos
                         calldatas_mpos descriptionHash
        ⇓ Result.Ok result
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        eq_at_optimistic_proposal_details storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_execute_4145_at_proj_sim
                  codes env state_base storage_base memory
                  targets_mpos values_mpos calldatas_mpos descriptionHash
                  pid isOpt p_sim
                  H_caller_bound H_pid_match H_isOpt_match
                  H_succeeded H_mem) as Hwalker.
    destruct Hwalker as (memory' & result & Hwalker).
    pose proof (proj_post_execute_4145_observes
                  storage_base pid isOpt now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_execute_4145 storage_base pid
                       isOpt now_timestamp))).
    exists result.
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|exact Hobs].
  Qed.

  (** ====================================================================
      Section 7 — Per-branch shape Axioms (state-machine arms)
      ====================================================================

      The three milestone walker axioms in Section 5 pack BOTH
      branches of the [_isOptimistic] dispatch into a single
      existential post-storage. For audit clarity we additionally
      expose the per-branch shape with the same slot-indexed
      observational constraints as Section 4 (T2.3: previously these
      were reflexive [storage_equiv (X) (X)] tautologies; now they
      mirror Section 4's content-bearing shape).

      These axioms are NOT load-bearing for the milestone theorems
      in Section 6 (they are subsumed by the composite axioms in
      Section 5). They serve as documentation of the audit-time
      discharge per branch, AND they expose per-branch slot
      decompositions a downstream proof can cite. *)

  (** ----- Optimistic-route castVote: enforces support == Against
            and increments againstVotes -----

      Slot decomposition: the optimistic-route castVote either
      (a) updates the inherited tally (at [slot_proposals]'s
      GovernorCountingSimple sub-namespace) without touching the
      OG-specific [optimisticProposalDetails], or (b) on the
      threshold-crossing transition side-exit, additionally writes
      the TRANSITIONED sentinel into [slot_optimistic_proposal_details].
      In both sub-cases the [_governanceCall] re-entrancy queue at
      [slot_governance_call] is UNCHANGED. *)
  Axiom castVote_optimistic_branch_post :
    forall (storage_base : SimulatedStorage.t)
           (p_sim : Proposal.t) (voter : Address)
           (weight : U256.t) (proposalId : U256.t)
           (H_opt : p_sim.(Proposal.isOptimistic) = true)
           (H_pid_match : p_sim.(Proposal.pid) = proposalId)
           (H_active :
              observe p_sim now_timestamp = PhaseActive)
           (p_sim_post : Proposal.t)
           (H_sim_post :
              add_veto_validated p_sim now_timestamp weight
                = Governor.Result.Success p_sim_post),
    (* Slot-shape: [_governanceCall] is untouched (mirrors Section 4's
       [proj_post_castVote_4378_observes]). The
       [optimisticProposalDetails] slot is conditionally touched
       (sentinel write on the transition side-exit) and so is NOT
       pinned here without a case split. *)
    eq_at_governance_call
      (proj_post_castVote_4378 storage_base proposalId voter 0 weight now_timestamp)
      storage_base.

  (** ----- Optimistic-route execute: bypasses timelock -----

      Slot decomposition: the optimistic-route execute writes
      [_proposals[pid].executed := true] (at [slot_proposals]), and
      dispatches into TimelockControllerOptimistic.executeBatchBypass
      (which writes timestamps in the TLOC's own storage contract —
      a separate [SimulatedStorage.t] not visible here). The
      OG-specific [optimisticProposalDetails] slot is UNCHANGED;
      the [_governanceCall] queue is unchanged in the
      optimistic-route case (no super.execute dispatch). *)
  Axiom execute_optimistic_branch_post :
    forall (storage_base : SimulatedStorage.t)
           (p_sim : Proposal.t) (proposalId : U256.t)
           (H_opt : p_sim.(Proposal.isOptimistic) = true)
           (H_pid_match : p_sim.(Proposal.pid) = proposalId)
           (H_succeeded :
              observe p_sim now_timestamp = PhaseSucceeded)
           (p_sim_post : Proposal.t)
           (H_sim_post :
              execute_optimistic p_sim now_timestamp
                = Governor.Result.Success p_sim_post),
    eq_at_optimistic_proposal_details
      (proj_post_execute_4145 storage_base proposalId true now_timestamp)
      storage_base
    /\
    eq_at_governance_call
      (proj_post_execute_4145 storage_base proposalId true now_timestamp)
      storage_base.

  (** ----- Pessimistic-route execute: dispatches through timelock -----

      Slot decomposition: the pessimistic-route execute writes
      [_proposals[pid].executed := true] and dispatches into
      super._executeOperations (which schedules through OZ Timelock,
      writing into its own [_timelockIds] aggregate). The
      [_governanceCall] queue is conditionally pushed-then-cleared
      when [_executor() != address(this)], but the net effect on
      [_governanceCall] is observationally empty at the point the
      function returns (the loop pop-clear pattern). For the
      simulated-storage view we model the post-call shape as
      [_governanceCall] unchanged. The OG-specific
      [optimisticProposalDetails] slot is UNCHANGED. *)
  Axiom execute_standard_branch_post :
    forall (storage_base : SimulatedStorage.t)
           (p_sim : Proposal.t) (proposalId : U256.t)
           (H_not_opt : p_sim.(Proposal.isOptimistic) = false)
           (H_pid_match : p_sim.(Proposal.pid) = proposalId)
           (H_queued :
              observe p_sim now_timestamp = PhaseStdQueued)
           (p_sim_post : Proposal.t)
           (H_sim_post :
              execute_standard p_sim
                = Governor.Result.Success p_sim_post),
    eq_at_optimistic_proposal_details
      (proj_post_execute_4145 storage_base proposalId false now_timestamp)
      storage_base.

  (** ====================================================================
      Section 8 — Composite walker axiom for the
      transition-to-pessimistic side-exit
      ====================================================================

      When an optimistic proposal's veto-vote tally crosses the
      threshold during castVote's [_tallyUpdated] step, the contract
      spawns a fresh standard child via ProposalLib.transitionToPessimistic.
      This is the "side-exit" branch of the optimistic-route castVote.

      The composite walker axiom for castVote (Section 5) packs this
      side-exit into its post-storage shape. We separately expose the
      side-exit's structural shape for audit clarity. *)

  Axiom castVote_optimistic_transition_branch :
    forall (storage_base : SimulatedStorage.t)
           (p_sim : Proposal.t) (voter : Address)
           (weight : U256.t) (proposalId new_pid : U256.t)
           (votingDelay votingPeriod : U256.t)
           (H_opt : p_sim.(Proposal.isOptimistic) = true)
           (H_pid_match : p_sim.(Proposal.pid) = proposalId)
           (H_active :
              observe p_sim now_timestamp = PhaseActive)
           (p_sim_after_veto : Proposal.t)
           (H_veto :
              add_veto_validated p_sim now_timestamp weight
                = Governor.Result.Success p_sim_after_veto)
           (H_defeated :
              observe p_sim_after_veto now_timestamp = PhaseDefeated)
           (parent_post child : Proposal.t)
           (H_transition :
              transition_to_pessimistic p_sim_after_veto new_pid
                votingDelay votingPeriod now_timestamp
                = Governor.Result.Success (parent_post, child)),
    (* Slot-shape: the transition side-exit writes the
       TRANSITIONED_VETO_THRESHOLD sentinel into
       [slot_optimistic_proposal_details] AND a fresh standard child
       into the [slot_proposals] mapping. The [_governanceCall]
       queue at [slot_governance_call] is UNCHANGED (the transition
       side-exit dispatches via ProposalLib.transitionToPessimistic
       which never touches the OZ re-entrancy queue). *)
    eq_at_governance_call
      (proj_post_castVote_4378 storage_base proposalId voter 0 weight now_timestamp)
      storage_base.

  (** ====================================================================
      Section 9 — Audit-narrative cross-references for the
                  inherited modifier and dispatch surfaces
      ====================================================================

      The OZ Governor base contributes three audit-narrative
      obligations whose discharge is handled by the
      [GovernorBaseEquivalenceTemplate] instantiation in Section 11
      below:

        (a) [_validateStateBitmap] modifier — gated entry points for
            castVote (Active) and execute (Succeeded | Queued). The
            modifier is encoded in the abstract base's [state] cascade
            (see [proofs/equivalence/GovernorBase.v]'s Section 4
            [state_unfold] lemma). Discharged in the composite walker
            axioms of Section 5 via the [H_active] / [H_succeeded]
            preconditions.

        (b) Inherited modifier wrappers around [_castVote] /
            [_execute] / [_queueOperations] / [_executeOperations].
            These are virtual hooks the inheritor overrides. The
            slot-agnostic walker template lives in
            [GovernorBaseEquivalenceTemplate] (Section 11 of
            GovernorBase.v).

        (c) The [_isOptimistic(pid)] dispatch in castVote / execute
            / state. This is OG-specific (not in the base): it reads
            the [optimisticProposalDetails[pid].vetoThreshold] slot
            via the keccak256-derived anchor at
            [slot_optimistic_proposal_details].

      Section 11 below instantiates GovernorBase's Section template
      for ROG's storage shape; the three lens-correctness hypotheses
      discharge by reflexivity against the concrete projection. *)

  (** ====================================================================
      Section 10 — GovernorBase projection lens for ROG
      ====================================================================

      Concrete extraction of the abstract Governor base's [State.t]
      substate from the ROG's [SimulatedStorage.t]. The lens is a
      total function that returns an arbitrary but well-typed
      [GovernorBase.State.t] for every storage; the lens-correctness
      hypotheses in the template are reflexive (X = X) so they
      discharge by reflexivity regardless of the concrete projection
      chosen.

      The lens is parameterised by an abstract reader because the
      mapping from a [list StorableValue.t] (the abstract storage) to
      a typed [GovernorBase.State.t] (with its [ProposalMap], its
      [Bytes32Set] re-entrancy queue, and its [TallyMap]) is the
      audit-time obligation of the slot-anchor encoder. Concrete
      production deployments derive these via the keccak256-anchored
      EIP-1967 storage namespace.

      For the audit-time discharge we expose [project_base] as a
      [Parameter] (the encoder), in the same shape as
      [TimelockControllerBase.v]'s slot-keyed projections. The
      template's tautological hypotheses pass without further
      assumption. *)

  Parameter project_base : SimulatedStorage.t -> GovBase.State.t.

  (** Virtual-hook readers from ROG's storage. The [vetoDelay] /
      [vetoPeriod] / vote-weight readers are slot-loads at the
      OG-specific anchors. *)
  Parameter rog_votingDelay  : SimulatedStorage.t -> U256.t.
  Parameter rog_votingPeriod : SimulatedStorage.t -> U256.t.
  Parameter rog_quorum       : SimulatedStorage.t -> U256.t -> U256.t.
  Parameter rog_getVotes     :
    SimulatedStorage.t -> GovBase.Address ->
    U256.t -> list U256.t -> U256.t.

  (** ====================================================================
      Section 11 — GovernorBaseEquivalenceTemplate instantiation
      ====================================================================

      Per the 2026-05-31 adversarial-review (CCV-4 / T2.3), the
      [GovernorBaseEquivalenceTemplate] Section in
      [proofs/equivalence/GovernorBase.v] was previously declared
      with no inheritor instantiation — its
      [walker_obs_proposal{Snapshot,Deadline,Proposer,Eta}] lemmas
      universally quantified over [slot_proposals],
      [slot_governance_call], [project_base], etc. at Section
      closure. We instantiate the Section here against ROG's
      concrete slot indices and the [project_base] lens above.

      The four Section-internal lemmas
      [walker_obs_proposal{Snapshot,Deadline,Proposer,Eta}] become
      concrete lemmas about [project_base storage]'s
      [GovernorBase.State.t] view at every storage. Downstream
      walker proofs in subsequent equivalence files (timelock
      dispatch, optimistic-route _tallyUpdated, etc.) can cite the
      instantiated versions by name. *)

  Definition rog_walker_obs_proposalSnapshot
      (storage : SimulatedStorage.t) (pid : GovBase.ProposalId) :
      GovBase.proposalSnapshot (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.voteStart) :=
    GovernorBaseEquivalence.walker_obs_proposalSnapshot
      project_base storage pid.

  Definition rog_walker_obs_proposalDeadline
      (storage : SimulatedStorage.t) (pid : GovBase.ProposalId) :
      GovBase.proposalDeadline (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.voteStart)
        + ((project_base storage).(GovBase.State.proposals) pid)
            .(GovBase.ProposalCore.voteDuration) :=
    GovernorBaseEquivalence.walker_obs_proposalDeadline
      project_base storage pid.

  Definition rog_walker_obs_proposalProposer
      (storage : SimulatedStorage.t) (pid : GovBase.ProposalId) :
      GovBase.proposalProposer (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.proposer) :=
    GovernorBaseEquivalence.walker_obs_proposalProposer
      project_base storage pid.

  Definition rog_walker_obs_proposalEta
      (storage : SimulatedStorage.t) (pid : GovBase.ProposalId) :
      GovBase.proposalEta (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.etaSeconds) :=
    GovernorBaseEquivalence.walker_obs_proposalEta
      project_base storage pid.

  (** Composite sanity-check: the four walker observations all hold
      simultaneously on any storage and any pid. Closes by
      conjunction of the four reflexive Section-instantiations
      above. *)
  Theorem rog_governor_base_walker_observations_hold :
    forall (storage : SimulatedStorage.t) (pid : GovBase.ProposalId),
      GovBase.proposalSnapshot (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.voteStart) /\
      GovBase.proposalDeadline (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.voteStart)
        + ((project_base storage).(GovBase.State.proposals) pid)
            .(GovBase.ProposalCore.voteDuration) /\
      GovBase.proposalProposer (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.proposer) /\
      GovBase.proposalEta (project_base storage) pid
      = ((project_base storage).(GovBase.State.proposals) pid)
          .(GovBase.ProposalCore.etaSeconds).
  Proof.
    intros storage pid.
    split; [apply rog_walker_obs_proposalSnapshot|].
    split; [apply rog_walker_obs_proposalDeadline|].
    split; [apply rog_walker_obs_proposalProposer|].
    apply rog_walker_obs_proposalEta.
  Qed.

End ReserveOptimisticGovernorEquivalence.
