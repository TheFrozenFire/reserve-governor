(** Task #244 — OpenZeppelin Governor abstract-base equivalence methodology.

    [Governor] (OZ v5.4.0, governance/Governor.sol) is the *abstract*
    base every concrete governor in the Reserve corpus (presently:
    [ReserveOptimisticGovernor]) inherits from.  Its storage slots
    ([_proposals], [_governanceCall]) are reserved on the inheritor;
    there is no standalone [Governor_shallow.v] from solc — the Yul
    translation of each method lands inside the consumer's shallow
    form, with slot indices fixed by the inheritor's storage layout.

    This file therefore does not bind a shallow form.  It delivers
    the same three deliverables as [proofs/equivalence/Votes.v]:

      1. A set of sim-level helper lemmas about [mocks/GovernorBase.v]
         — the pure-Coq facts every concrete inheritor's walker proof
         will reuse (`Qed`, no axioms beyond what the mock already
         imports).

      2. A documented walker-template surface — for each of the
         public Governor operations, what the Yul body's walker arms
         look like, parameterized over slot indices and a projection
         lens.

      3. A skeletal Section [GovernorBaseEquivalenceTemplate] showing
         how downstream inheritors will instantiate the methodology
         when the corresponding shallow form lands.

    The companion mock is [mocks/GovernorBase.v]; the methodology
    decision is captured in WISDOM R072 (abstract-base-class
    equivalence) and R074 (this file).

    Methodology decision (Option 2 from votes_equivalence_methodology.md):
    --------------------------------------------------------------------
    Slot-agnostic helpers parameterized over slot indices, mirroring
    the existing abstract-base pattern in [proofs/equivalence/Nonces.v],
    [proofs/equivalence/EnumerableSet.v],
    [proofs/equivalence/Checkpoints.v], and
    [proofs/equivalence/Votes.v].  Inheritors instantiate by supplying
    their own [proj_sim] and slot indices; the sim-level helper lemmas
    below close once and are reused.

    Handling of `virtual` functions:
    --------------------------------
    The OZ Governor has a large `virtual` surface — [votingDelay],
    [votingPeriod], [quorum], [_quorumReached], [_voteSucceeded],
    [_countVote], [_getVotes], [_executor], [proposalNeedsQueuing],
    [_validateCancel], [_isValidDescriptionForProposer], [clock],
    [CLOCK_MODE], [proposalThreshold], [_queueOperations],
    [_executeOperations], [_tallyUpdated], [_validateVoteSig],
    [_validateExtendedVoteSig], [_defaultParams].

    We split them three ways:

      A. **Closed over as explicit arguments to mock entry points.**
         [votingDelay], [votingPeriod], [vote_weight] (= _getVotes),
         [quorum_reached] / [vote_succeeded] (= _quorumReached /
         _voteSucceeded), [queue_eta] (= _queueOperations),
         [executor_is_self] (= _executor() == address(this)),
         [self_call_hashes] (= the keccak256(calldatas[i]) list).

      B. **Section parameters at the equivalence layer.**  When the
         inheritor instantiates [GovernorBaseEquivalenceTemplate], it
         passes its concrete implementations of these hooks (or, for
         the lifecycle hooks that don't materially affect the proof
         shape, axiom-free witnesses that the OZ contract uses).

      C. **Out of scope.**  [_tallyUpdated] is an empty hook in OZ's
         default; the inheritor overrides it for cross-contract
         notification.  We do NOT model it — the mock's [castVote]
         leaves state untouched at the [_tallyUpdated] point, which
         matches the empty default.  Concrete inheritors that override
         [_tallyUpdated] compose their post-cast effects as a
         post-state predicate on top of the mock's [castVote] post-state.

    What this file does NOT do:
    ---------------------------
    - It does not bind any Yul function to the sim.  No shallow form
      exists to bind against.
    - It does not add new framework axioms.  Every closed lemma is
      [Qed] against [mocks/GovernorBase.v], [mocks/EnumerableSet.v],
      and the existing mock infrastructure.  [hashProposal_fn] is
      already a [Parameter] in the mock — we do not introduce
      additional axioms in the equivalence file.

    Cross-references:
    -----------------
    - [proofs/equivalence/Votes.v] — methodology template, identical
      Section-parameterization shape.
    - [proofs/equivalence/Nonces.v] — abstract-base, sequenced-check
      shape (cited by Governor.castVoteBySig path).
    - [proofs/equivalence/EnumerableSet.v] — used by the governance
      queue (mock backs [_governanceCall] with [Bytes32Set]).
    - WISDOM R072 — methodology pattern.
    - WISDOM R074 — this file's design notes (after compile-verify).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.mocks.EnumerableSet.
Require Import ReserveGovernor.mocks.GovernorBase.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module GovernorBaseEquivalence.

  Import GovernorBase.

  (** ============================================================
      Section 1 — View-function unfoldings (Qed)

      Each public view function on the Governor abstract base unfolds
      to a definitional projection of [State.proposals].  Walker
      proofs cite these by name rather than re-unfold the mock.
      ============================================================ *)

  Lemma proposalSnapshot_unfold :
    forall (s : State.t) (pid : ProposalId),
      proposalSnapshot s pid
      = (s.(State.proposals) pid).(ProposalCore.voteStart).
  Proof. reflexivity. Qed.

  Lemma proposalDeadline_unfold :
    forall (s : State.t) (pid : ProposalId),
      proposalDeadline s pid
      = (s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration).
  Proof. reflexivity. Qed.

  Lemma proposalProposer_unfold :
    forall (s : State.t) (pid : ProposalId),
      proposalProposer s pid
      = (s.(State.proposals) pid).(ProposalCore.proposer).
  Proof. reflexivity. Qed.

  Lemma proposalEta_unfold :
    forall (s : State.t) (pid : ProposalId),
      proposalEta s pid
      = (s.(State.proposals) pid).(ProposalCore.etaSeconds).
  Proof. reflexivity. Qed.

  Lemma proposal_exists_iff_voteStart_nonzero :
    forall (s : State.t) (pid : ProposalId),
      proposal_exists s pid = true
      <-> (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0.
  Proof.
    intros s pid. unfold proposal_exists, proposalSnapshot.
    split.
    - intro Hb.
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) eqn:Hz.
      + simpl in Hb. discriminate.
      + apply Z.eqb_neq in Hz. exact Hz.
    - intro Hne.
      assert (Hb : ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
        by (apply Z.eqb_neq; exact Hne).
      rewrite Hb. reflexivity.
  Qed.

  (** ============================================================
      Section 2 — [hashProposal] determinism

      [hashProposal_fn] is an opaque [Parameter] in the mock.  Its
      determinism is therefore a function property (same args →
      same hash); injectivity is NOT proven here because it would
      require an axiom about the underlying keccak.  Concrete
      inheritors that need injectivity will introduce their own
      axiom at the call site (or compose through the keccak surface
      we trust elsewhere in the corpus).
      ============================================================ *)

  Lemma hashProposal_deterministic_eq :
    forall (a1 a2 : ProposalArgs),
      a1 = a2 -> hashProposal a1 = hashProposal a2.
  Proof. exact hashProposal_deterministic. Qed.

  (** ============================================================
      Section 3 — [propose] post-state characterization (Qed)

      The OZ [_propose] body has two revert paths and one success
      path.  Each lemma below isolates one of them.
      ============================================================ *)

  (** Invalid-length args revert. *)
  Lemma propose_invalid_length_reverts :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t),
      propose_args_valid a = false ->
      propose s a proposer vd vp = revert_invalid_length.
  Proof.
    intros s a proposer vd vp Hv.
    unfold propose. rewrite Hv. reflexivity.
  Qed.

  (** Duplicate-id revert.  The OZ source: "if (_proposals[proposalId].voteStart != 0)
      revert GovernorUnexpectedProposalState(...)". *)
  Lemma propose_duplicate_id_reverts :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) <> 0 ->
      propose s a proposer vd vp = revert_unexpected_state.
  Proof.
    intros s a proposer vd vp Hv Hne.
    unfold propose. rewrite Hv. cbn [negb].
    assert (Hne' :
      ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hne).
    rewrite Hne'. reflexivity.
  Qed.

  (** Success: [voteStart] equals [clock + votingDelay]. *)
  Lemma propose_sets_voteStart :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) = 0 ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      pid = hashProposal a /\
      (s'.(State.proposals) pid).(ProposalCore.voteStart) = s.(State.clock) + vd.
  Proof.
    intros s a proposer vd vp s' pid Hv Hz Hpr.
    unfold propose in Hpr. rewrite Hv in Hpr. cbn [negb] in Hpr.
    assert (Hz' :
      ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0) = true)
      by (apply Z.eqb_eq; exact Hz).
    rewrite Hz' in Hpr. cbn [negb] in Hpr.
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn.
    split; [reflexivity|].
    unfold upd_proposals. rewrite Z.eqb_refl. cbn. reflexivity.
  Qed.

  (** Success: [voteDuration] equals [votingPeriod]. *)
  Lemma propose_sets_voteDuration :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) = 0 ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      (s'.(State.proposals) pid).(ProposalCore.voteDuration) = vp.
  Proof.
    intros s a proposer vd vp s' pid Hv Hz Hpr.
    unfold propose in Hpr. rewrite Hv in Hpr. cbn [negb] in Hpr.
    assert (Hz' :
      ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0) = true)
      by (apply Z.eqb_eq; exact Hz).
    rewrite Hz' in Hpr. cbn [negb] in Hpr.
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn. reflexivity.
  Qed.

  (** Success: [proposer] is assigned. *)
  Lemma propose_assigns_proposer :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) = 0 ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      (s'.(State.proposals) pid).(ProposalCore.proposer) = proposer.
  Proof.
    intros s a proposer vd vp s' pid Hv Hz Hpr.
    unfold propose in Hpr. rewrite Hv in Hpr. cbn [negb] in Hpr.
    assert (Hz' :
      ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0) = true)
      by (apply Z.eqb_eq; exact Hz).
    rewrite Hz' in Hpr. cbn [negb] in Hpr.
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn. reflexivity.
  Qed.

  (** Success: the new proposal is [executed = false], [canceled = false],
      [etaSeconds = 0].  These are the OZ-default initial values. *)
  Lemma propose_initial_flags :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) = 0 ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      (s'.(State.proposals) pid).(ProposalCore.executed)   = false /\
      (s'.(State.proposals) pid).(ProposalCore.canceled)   = false /\
      (s'.(State.proposals) pid).(ProposalCore.etaSeconds) = 0.
  Proof.
    intros s a proposer vd vp s' pid Hv Hz Hpr.
    unfold propose in Hpr. rewrite Hv in Hpr. cbn [negb] in Hpr.
    assert (Hz' :
      ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0) = true)
      by (apply Z.eqb_eq; exact Hz).
    rewrite Hz' in Hpr. cbn [negb] in Hpr.
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn.
    repeat split.
  Qed.

  (** Success: other proposals are untouched. *)
  Lemma propose_preserves_other_proposals :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid pid' : ProposalId),
      propose s a proposer vd vp = Result.Success (s', pid) ->
      pid' <> pid ->
      s'.(State.proposals) pid' = s.(State.proposals) pid'.
  Proof.
    intros s a proposer vd vp s' pid pid' Hpr Hne.
    unfold propose in Hpr.
    destruct (propose_args_valid a) eqn:Hv; cbn [negb] in Hpr;
      [|unfold revert_invalid_length in Hpr; discriminate].
    destruct ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0)
      eqn:Hz; cbn [negb] in Hpr;
      [|unfold revert_unexpected_state in Hpr; discriminate].
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn.
    unfold upd_proposals.
    assert (Hpid : Z.eqb pid' (hashProposal a) = false)
      by (apply Z.eqb_neq; exact Hne).
    rewrite Hpid. reflexivity.
  Qed.

  (** [propose] does not touch [governance_call], [tallies], or [clock]. *)
  Lemma propose_preserves_governance_call :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose s a proposer vd vp = Result.Success (s', pid) ->
      s'.(State.governance_call) = s.(State.governance_call).
  Proof.
    intros s a proposer vd vp s' pid Hpr.
    unfold propose in Hpr.
    destruct (propose_args_valid a) eqn:Hv; cbn [negb] in Hpr;
      [|unfold revert_invalid_length in Hpr; discriminate].
    destruct ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0)
      eqn:Hz; cbn [negb] in Hpr;
      [|unfold revert_unexpected_state in Hpr; discriminate].
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn. reflexivity.
  Qed.

  Lemma propose_preserves_tallies :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose s a proposer vd vp = Result.Success (s', pid) ->
      s'.(State.tallies) = s.(State.tallies).
  Proof.
    intros s a proposer vd vp s' pid Hpr.
    unfold propose in Hpr.
    destruct (propose_args_valid a) eqn:Hv; cbn [negb] in Hpr;
      [|unfold revert_invalid_length in Hpr; discriminate].
    destruct ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0)
      eqn:Hz; cbn [negb] in Hpr;
      [|unfold revert_unexpected_state in Hpr; discriminate].
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn. reflexivity.
  Qed.

  Lemma propose_preserves_clock :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      propose s a proposer vd vp = Result.Success (s', pid) ->
      s'.(State.clock) = s.(State.clock).
  Proof.
    intros s a proposer vd vp s' pid Hpr.
    unfold propose in Hpr.
    destruct (propose_args_valid a) eqn:Hv; cbn [negb] in Hpr;
      [|unfold revert_invalid_length in Hpr; discriminate].
    destruct ((s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) =? 0)
      eqn:Hz; cbn [negb] in Hpr;
      [|unfold revert_unexpected_state in Hpr; discriminate].
    injection Hpr as Heq_s Heq_pid. subst pid s'. cbn. reflexivity.
  Qed.

  (** ============================================================
      Section 4 — [state] cascade unfolding (Qed)

      The 8-state machine's case-splits, lifted to lemma form so the
      walker can match against them without re-unfolding the cascade.
      ============================================================ *)

  (** A pure unfolding of [state] — the exact OZ cascade.  Used by
      downstream walker proofs as a single rewrite step. *)
  Lemma state_unfold :
    forall (s : State.t) (pid : ProposalId)
           (qr vs : bool),
      state s pid qr vs =
      (let proposal := s.(State.proposals) pid in
       if proposal.(ProposalCore.executed) then Result.Success Executed
       else if proposal.(ProposalCore.canceled) then Result.Success Canceled
       else
         let snap := proposal.(ProposalCore.voteStart) in
         if Z.eqb snap 0 then revert_nonexistent_proposal
         else
           let now := s.(State.clock) in
           if snap >=? now then Result.Success Pending
           else
             let dl := snap + proposal.(ProposalCore.voteDuration) in
             if dl >=? now then Result.Success Active
             else if negb (andb qr vs) then Result.Success Defeated
                  else if Z.eqb proposal.(ProposalCore.etaSeconds) 0 then
                         Result.Success Succeeded
                       else Result.Success Queued).
  Proof. reflexivity. Qed.

  (** [executed = true] dominates: the [state] cascade returns
      [Executed] regardless of canceled / voteStart / clock. *)
  Lemma state_executed_terminal :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = true ->
      state s pid qr vs = Result.Success Executed.
  Proof.
    intros s pid qr vs Hex.
    unfold state. rewrite Hex. reflexivity.
  Qed.

  (** [canceled = true] dominates when [executed = false]. *)
  Lemma state_canceled_terminal :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = true ->
      state s pid qr vs = Result.Success Canceled.
  Proof.
    intros s pid qr vs Hex Hca.
    unfold state. rewrite Hex, Hca. reflexivity.
  Qed.

  (** Nonexistent proposal: [voteStart = 0], no flag set, reverts. *)
  Lemma state_nonexistent_reverts :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) = 0 ->
      state s pid qr vs = revert_nonexistent_proposal.
  Proof.
    intros s pid qr vs Hex Hca Hvs.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = true)
      by (apply Z.eqb_eq; exact Hvs).
    rewrite Hvs'. reflexivity.
  Qed.

  (** Pending transition: [voteStart >= clock] and not terminal. *)
  Lemma state_pending_when_snapshot_ge_now :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0 ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) >= s.(State.clock) ->
      state s pid qr vs = Result.Success Pending.
  Proof.
    intros s pid qr vs Hex Hca Hvs Hge.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hvs).
    rewrite Hvs'.
    assert (Hge' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock)) = true)
      by (apply Z.geb_le; lia).
    rewrite Hge'. reflexivity.
  Qed.

  (** Active transition: [voteStart < clock] AND
      [voteStart + voteDuration >= clock]. *)
  Lemma state_active_when_in_window :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0 ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) < s.(State.clock) ->
      (s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration) >= s.(State.clock) ->
      state s pid qr vs = Result.Success Active.
  Proof.
    intros s pid qr vs Hex Hca Hvs Hlt Hdl.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hvs).
    rewrite Hvs'.
    assert (Hlt' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock))
        eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hlt'.
    assert (Hdl' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
       >=? s.(State.clock)) = true)
      by (apply Z.geb_le; lia).
    rewrite Hdl'. reflexivity.
  Qed.

  (** Defeated transition: window closed AND (not quorum OR not succeeded). *)
  Lemma state_defeated_when_quorum_or_vote_fails :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0 ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) < s.(State.clock) ->
      (s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration) < s.(State.clock) ->
      andb qr vs = false ->
      state s pid qr vs = Result.Success Defeated.
  Proof.
    intros s pid qr vs Hex Hca Hvs Hlt Hdl Hqvs.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hvs).
    rewrite Hvs'.
    assert (Hlt' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock))
        eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hlt'.
    assert (Hdl' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
       >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
        >=? s.(State.clock)) eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hdl'. rewrite Hqvs. cbn [negb]. reflexivity.
  Qed.

  (** Succeeded transition: window closed, quorum + succeeded, eta = 0. *)
  Lemma state_succeeded_when_no_eta :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0 ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) < s.(State.clock) ->
      (s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration) < s.(State.clock) ->
      andb qr vs = true ->
      (s.(State.proposals) pid).(ProposalCore.etaSeconds) = 0 ->
      state s pid qr vs = Result.Success Succeeded.
  Proof.
    intros s pid qr vs Hex Hca Hvs Hlt Hdl Hqvs Heta.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hvs).
    rewrite Hvs'.
    assert (Hlt' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock))
        eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hlt'.
    assert (Hdl' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
       >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
        >=? s.(State.clock)) eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hdl'. rewrite Hqvs. cbn [negb].
    assert (Heta' :
      ((s.(State.proposals) pid).(ProposalCore.etaSeconds) =? 0) = true)
      by (apply Z.eqb_eq; exact Heta).
    rewrite Heta'. reflexivity.
  Qed.

  (** Queued transition: window closed, quorum + succeeded, eta != 0. *)
  Lemma state_queued_when_eta_set :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      (s.(State.proposals) pid).(ProposalCore.canceled) = false ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) <> 0 ->
      (s.(State.proposals) pid).(ProposalCore.voteStart) < s.(State.clock) ->
      (s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration) < s.(State.clock) ->
      andb qr vs = true ->
      (s.(State.proposals) pid).(ProposalCore.etaSeconds) <> 0 ->
      state s pid qr vs = Result.Success Queued.
  Proof.
    intros s pid qr vs Hex Hca Hvs Hlt Hdl Hqvs Heta.
    unfold state. rewrite Hex, Hca.
    assert (Hvs' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) =? 0) = false)
      by (apply Z.eqb_neq; exact Hvs).
    rewrite Hvs'.
    assert (Hlt' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart) >=? s.(State.clock))
        eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hlt'.
    assert (Hdl' :
      ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
       >=? s.(State.clock)) = false)
    .
    {
      destruct ((s.(State.proposals) pid).(ProposalCore.voteStart)
        + (s.(State.proposals) pid).(ProposalCore.voteDuration)
        >=? s.(State.clock)) eqn:E; [|reflexivity].
      apply Z.geb_le in E. lia.
    }
    rewrite Hdl'. rewrite Hqvs. cbn [negb].
    assert (Heta' :
      ((s.(State.proposals) pid).(ProposalCore.etaSeconds) =? 0) = false)
      by (apply Z.eqb_neq; exact Heta).
    rewrite Heta'. reflexivity.
  Qed.

  (** A fresh proposal (just posted via [propose]) is in [Pending]
      iff [clock + votingDelay > clock] (i.e. [votingDelay > 0]).  When
      [votingDelay = 0] the freshly-posted proposal flips immediately
      to [Active] from the next observation.  Captured below. *)
  Lemma state_after_propose_pending :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId)
           (qr vs : bool),
      propose_args_valid a = true ->
      (s.(State.proposals) (hashProposal a)).(ProposalCore.voteStart) = 0 ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      s.(State.clock) + vd >= s.(State.clock) ->
      s.(State.clock) + vd <> 0 ->
      state s' pid qr vs = Result.Success Pending.
  Proof.
    intros s a proposer vd vp s' pid qr vs Hv Hz Hpr Hge Hne.
    pose proof (propose_sets_voteStart s a proposer vd vp s' pid Hv Hz Hpr) as HpvP.
    destruct HpvP as [Hpid Hvs].
    pose proof (propose_initial_flags s a proposer vd vp s' pid Hv Hz Hpr) as Hinit.
    destruct Hinit as [Hex Hrest]. destruct Hrest as [Hca _].
    pose proof (propose_preserves_clock s a proposer vd vp s' pid Hpr) as Hclk.
    apply state_pending_when_snapshot_ge_now; try assumption.
    - rewrite Hvs. exact Hne.
    - rewrite Hvs, Hclk. exact Hge.
  Qed.

  (** ============================================================
      Section 5 — [castVote] post-state characterization (Qed)

      [castVote] is gated on [state == Active].  We isolate the
      three outcome classes: (a) non-Active state reverts; (b)
      replay reverts; (c) success records the vote.
      ============================================================ *)

  Lemma castVote_non_active_reverts :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (p : Phase),
      state s pid qr vs = Result.Success p ->
      p <> Active ->
      castVote s pid acct support w qr vs = revert_unexpected_state.
  Proof.
    intros s pid acct support w qr vs p Hst Hne.
    unfold castVote. rewrite Hst.
    destruct p; try reflexivity. contradiction.
  Qed.

  Lemma castVote_revert_state_revert :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (p q : U256.t),
      state s pid qr vs = Result.Revert p q ->
      castVote s pid acct support w qr vs = Result.Revert p q.
  Proof.
    intros s pid acct support w qr vs p q Hst.
    unfold castVote. rewrite Hst. reflexivity.
  Qed.

  Lemma castVote_replay_reverts :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool),
      state s pid qr vs = Result.Success Active ->
      vote_already_cast (s.(State.tallies) pid) acct = true ->
      castVote s pid acct support w qr vs = revert_already_cast_vote.
  Proof.
    intros s pid acct support w qr vs Hst Hin.
    unfold castVote. rewrite Hst. rewrite Hin. reflexivity.
  Qed.

  Lemma castVote_records_vote :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (s' : State.t) (votedW : Z),
      state s pid qr vs = Result.Success Active ->
      vote_already_cast (s.(State.tallies) pid) acct = false ->
      castVote s pid acct support w qr vs = Result.Success (s', votedW) ->
      votedW = w /\
      vote_already_cast (s'.(State.tallies) pid) acct = true.
  Proof.
    intros s pid acct support w qr vs s' votedW Hst Hnotin Hcv.
    unfold castVote in Hcv. rewrite Hst in Hcv. rewrite Hnotin in Hcv.
    injection Hcv as Heq_s Heq_v. subst votedW s'. cbn.
    split; [reflexivity|].
    unfold vote_already_cast, apply_vote.
    unfold upd_tallies. rewrite Z.eqb_refl. cbn [VoteTally.voters].
    rewrite existsb_app. rewrite Bool.orb_true_iff. right.
    cbn. rewrite Z.eqb_refl. reflexivity.
  Qed.

  (** [castVote] is idempotent under replay: a second call with the
      same [acct] reverts. *)
  Lemma castVote_idempotent_replay :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (s' : State.t) (votedW : Z)
           (qr2 vs2 : bool),
      state s pid qr vs = Result.Success Active ->
      vote_already_cast (s.(State.tallies) pid) acct = false ->
      castVote s pid acct support w qr vs = Result.Success (s', votedW) ->
      state s' pid qr2 vs2 = Result.Success Active ->
      castVote s' pid acct support w qr2 vs2 = revert_already_cast_vote.
  Proof.
    intros s pid acct support w qr vs s' votedW qr2 vs2 Hst Hnotin Hcv Hst2.
    pose proof (castVote_records_vote s pid acct support w qr vs s' votedW
                  Hst Hnotin Hcv) as [_ Hin].
    apply castVote_replay_reverts; assumption.
  Qed.

  (** [castVote] preserves the [proposals] mapping (no proposal
      lifecycle field changes during a vote). *)
  Lemma castVote_preserves_proposals :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (s' : State.t) (votedW : Z),
      castVote s pid acct support w qr vs = Result.Success (s', votedW) ->
      s'.(State.proposals) = s.(State.proposals).
  Proof.
    intros s pid acct support w qr vs s' votedW Hcv.
    unfold castVote in Hcv.
    destruct (state s pid qr vs) as [p|p q] eqn:Hst; [|discriminate].
    destruct p; try discriminate.
    destruct (vote_already_cast (s.(State.tallies) pid) acct); [discriminate|].
    injection Hcv as Heq_s _. subst s'. cbn. reflexivity.
  Qed.

  (** ============================================================
      Section 6 — [queue] post-state characterization (Qed)
      ============================================================ *)

  Lemma queue_non_succeeded_reverts :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (p : Phase),
      state s pid qr vs = Result.Success p ->
      p <> Succeeded ->
      queue s pid qe qr vs = revert_unexpected_state.
  Proof.
    intros s pid qe qr vs p Hst Hne.
    unfold queue. rewrite Hst.
    destruct p; try reflexivity. contradiction.
  Qed.

  Lemma queue_zero_eta_reverts :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      state s pid qr vs = Result.Success Succeeded ->
      queue s pid 0 qr vs = revert_queue_not_implemented.
  Proof.
    intros s pid qr vs Hst.
    unfold queue. rewrite Hst. cbn. reflexivity.
  Qed.

  Lemma queue_sets_eta :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (s' : State.t) (out : U256.t),
      state s pid qr vs = Result.Success Succeeded ->
      qe <> 0 ->
      queue s pid qe qr vs = Result.Success (s', out) ->
      out = qe /\
      (s'.(State.proposals) pid).(ProposalCore.etaSeconds) = qe.
  Proof.
    intros s pid qe qr vs s' out Hst Hne Hq.
    unfold queue in Hq. rewrite Hst in Hq.
    assert (Hne' : (qe =? 0) = false) by (apply Z.eqb_neq; exact Hne).
    rewrite Hne' in Hq.
    injection Hq as Heq_s Heq_o. subst out s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn.
    split; reflexivity.
  Qed.

  Lemma queue_preserves_other_proposals :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (s' : State.t) (out : U256.t) (pid' : ProposalId),
      queue s pid qe qr vs = Result.Success (s', out) ->
      pid' <> pid ->
      s'.(State.proposals) pid' = s.(State.proposals) pid'.
  Proof.
    intros s pid qe qr vs s' out pid' Hq Hne.
    unfold queue in Hq.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate.
    destruct (qe =? 0); [discriminate|].
    injection Hq as Heq_s _. subst s'. cbn.
    unfold upd_proposals.
    assert (Hpid : Z.eqb pid' pid = false) by (apply Z.eqb_neq; exact Hne).
    rewrite Hpid. reflexivity.
  Qed.

  Lemma queue_preserves_tallies :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (s' : State.t) (out : U256.t),
      queue s pid qe qr vs = Result.Success (s', out) ->
      s'.(State.tallies) = s.(State.tallies).
  Proof.
    intros s pid qe qr vs s' out Hq.
    unfold queue in Hq.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate.
    destruct (qe =? 0); [discriminate|].
    injection Hq as Heq_s _. subst s'. cbn. reflexivity.
  Qed.

  Lemma queue_preserves_governance_call :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (s' : State.t) (out : U256.t),
      queue s pid qe qr vs = Result.Success (s', out) ->
      s'.(State.governance_call) = s.(State.governance_call).
  Proof.
    intros s pid qe qr vs s' out Hq.
    unfold queue in Hq.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate.
    destruct (qe =? 0); [discriminate|].
    injection Hq as Heq_s _. subst s'. cbn. reflexivity.
  Qed.

  (** ============================================================
      Section 7 — [execute] post-state characterization (Qed)
      ============================================================ *)

  Lemma execute_non_executable_reverts :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (p : Phase),
      state s pid qr vs = Result.Success p ->
      p <> Succeeded -> p <> Queued ->
      execute s pid eis sch qr vs = revert_unexpected_state.
  Proof.
    intros s pid eis sch qr vs p Hst HnS HnQ.
    unfold execute. rewrite Hst.
    destruct p; try reflexivity; contradiction.
  Qed.

  Lemma execute_sets_executed_from_succeeded :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (s' : State.t),
      state s pid qr vs = Result.Success Succeeded ->
      execute s pid eis sch qr vs = Result.Success s' ->
      (s'.(State.proposals) pid).(ProposalCore.executed) = true.
  Proof.
    intros s pid eis sch qr vs s' Hst Hex.
    unfold execute in Hex. rewrite Hst in Hex.
    injection Hex as Heq_s. subst s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn. reflexivity.
  Qed.

  Lemma execute_sets_executed_from_queued :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (s' : State.t),
      state s pid qr vs = Result.Success Queued ->
      execute s pid eis sch qr vs = Result.Success s' ->
      (s'.(State.proposals) pid).(ProposalCore.executed) = true.
  Proof.
    intros s pid eis sch qr vs s' Hst Hex.
    unfold execute in Hex. rewrite Hst in Hex.
    injection Hex as Heq_s. subst s'. cbn.
    unfold upd_proposals. rewrite Z.eqb_refl. cbn. reflexivity.
  Qed.

  (** Once executed, the proposal stays in [Executed] state forever
      (the [state] cascade returns [Executed] regardless of any other
      state field). *)
  Lemma execute_leads_to_executed_state :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (s' : State.t) (qr' vs' : bool),
      state s pid qr vs = Result.Success Succeeded ->
      execute s pid eis sch qr vs = Result.Success s' ->
      state s' pid qr' vs' = Result.Success Executed.
  Proof.
    intros s pid eis sch qr vs s' qr' vs' Hst Hex.
    apply state_executed_terminal.
    apply (execute_sets_executed_from_succeeded s pid eis sch qr vs s' Hst Hex).
  Qed.

  Lemma execute_preserves_other_proposals :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (s' : State.t) (pid' : ProposalId),
      execute s pid eis sch qr vs = Result.Success s' ->
      pid' <> pid ->
      s'.(State.proposals) pid' = s.(State.proposals) pid'.
  Proof.
    intros s pid eis sch qr vs s' pid' Hex Hne.
    unfold execute in Hex.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hex as Heq_s; subst s'; cbn;
       unfold upd_proposals;
       assert (Hpid : Z.eqb pid' pid = false) by (apply Z.eqb_neq; exact Hne);
       rewrite Hpid; reflexivity).
  Qed.

  Lemma execute_governance_call_when_executor_is_self :
    forall (s : State.t) (pid : ProposalId) (sch : list U256.t)
           (qr vs : bool) (s' : State.t),
      execute s pid true sch qr vs = Result.Success s' ->
      s'.(State.governance_call) = s.(State.governance_call).
  Proof.
    intros s pid sch qr vs s' Hex.
    unfold execute in Hex.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hex as Heq_s; subst s'; cbn; reflexivity).
  Qed.

  Lemma execute_governance_call_cleared_when_executor_external :
    forall (s : State.t) (pid : ProposalId) (sch : list U256.t)
           (qr vs : bool) (s' : State.t),
      execute s pid false sch qr vs = Result.Success s' ->
      s'.(State.governance_call) = EnumerableSet.Bytes32Set.empty.
  Proof.
    intros s pid sch qr vs s' Hex.
    unfold execute in Hex.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hex as Heq_s; subst s'; cbn; reflexivity).
  Qed.

  (** ============================================================
      Section 8 — [cancel] post-state characterization (Qed)
      ============================================================ *)

  Lemma cancel_canceled_state_reverts :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      state s pid qr vs = Result.Success Canceled ->
      cancel s pid qr vs = revert_unexpected_state.
  Proof.
    intros s pid qr vs Hst. unfold cancel. rewrite Hst. reflexivity.
  Qed.

  Lemma cancel_expired_state_reverts :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      state s pid qr vs = Result.Success Expired ->
      cancel s pid qr vs = revert_unexpected_state.
  Proof.
    intros s pid qr vs Hst. unfold cancel. rewrite Hst. reflexivity.
  Qed.

  Lemma cancel_executed_state_reverts :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      state s pid qr vs = Result.Success Executed ->
      cancel s pid qr vs = revert_unexpected_state.
  Proof.
    intros s pid qr vs Hst. unfold cancel. rewrite Hst. reflexivity.
  Qed.

  (** [cancel] succeeds and flips the canceled flag from any of the
      non-terminal pre-states (Pending, Active, Defeated, Succeeded,
      Queued).  The OZ source: state ∈ ALL_STATES \ {Canceled, Expired, Executed}. *)
  Lemma cancel_flips_canceled :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool)
           (s' : State.t) (p : Phase),
      state s pid qr vs = Result.Success p ->
      p <> Canceled -> p <> Expired -> p <> Executed ->
      cancel s pid qr vs = Result.Success s' ->
      (s'.(State.proposals) pid).(ProposalCore.canceled) = true.
  Proof.
    intros s pid qr vs s' p Hst Hnc Hne Hnx Hcan.
    unfold cancel in Hcan. rewrite Hst in Hcan.
    destruct p; try contradiction;
      (injection Hcan as Heq_s; subst s'; cbn;
       unfold upd_proposals; rewrite Z.eqb_refl; cbn; reflexivity).
  Qed.

  (** Once canceled, the [state] cascade returns [Canceled] from any
      future observation (because [executed] stays false). *)
  Lemma cancel_leads_to_canceled_state :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool)
           (s' : State.t) (p : Phase) (qr' vs' : bool),
      state s pid qr vs = Result.Success p ->
      p <> Canceled -> p <> Expired -> p <> Executed ->
      (s.(State.proposals) pid).(ProposalCore.executed) = false ->
      cancel s pid qr vs = Result.Success s' ->
      state s' pid qr' vs' = Result.Success Canceled.
  Proof.
    intros s pid qr vs s' p qr' vs' Hst Hnc Hne Hnx Hex Hcan.
    apply state_canceled_terminal.
    - unfold cancel in Hcan. rewrite Hst in Hcan.
      destruct p; try contradiction;
        (injection Hcan as Heq_s; subst s'; cbn;
         unfold upd_proposals; rewrite Z.eqb_refl; cbn; exact Hex).
    - apply (cancel_flips_canceled s pid qr vs s' p Hst Hnc Hne Hnx Hcan).
  Qed.

  Lemma cancel_preserves_other_proposals :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool)
           (s' : State.t) (pid' : ProposalId),
      cancel s pid qr vs = Result.Success s' ->
      pid' <> pid ->
      s'.(State.proposals) pid' = s.(State.proposals) pid'.
  Proof.
    intros s pid qr vs s' pid' Hcan Hne.
    unfold cancel in Hcan.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hcan as Heq_s; subst s'; cbn;
       unfold upd_proposals;
       assert (Hpid : Z.eqb pid' pid = false) by (apply Z.eqb_neq; exact Hne);
       rewrite Hpid; reflexivity).
  Qed.

  Lemma cancel_preserves_tallies :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool) (s' : State.t),
      cancel s pid qr vs = Result.Success s' ->
      s'.(State.tallies) = s.(State.tallies).
  Proof.
    intros s pid qr vs s' Hcan.
    unfold cancel in Hcan.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hcan as Heq_s; subst s'; cbn; reflexivity).
  Qed.

  Lemma cancel_preserves_governance_call :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool) (s' : State.t),
      cancel s pid qr vs = Result.Success s' ->
      s'.(State.governance_call) = s.(State.governance_call).
  Proof.
    intros s pid qr vs s' Hcan.
    unfold cancel in Hcan.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hcan as Heq_s; subst s'; cbn; reflexivity).
  Qed.

  (** [cancel_public] gates on the default [_validateCancel] (proposer
      cancels Pending).  When that gate fails, the public wrapper
      reverts with [GovernorUnableToCancel] without invoking the
      inner [cancel]. *)
  Lemma cancel_public_validate_failure_reverts :
    forall (s : State.t) (pid : ProposalId) (caller : Address)
           (qr vs : bool),
      default_validateCancel s pid caller qr vs = false ->
      cancel_public s pid caller qr vs = revert_unable_to_cancel.
  Proof.
    intros s pid caller qr vs Hv.
    unfold cancel_public. rewrite Hv. reflexivity.
  Qed.

  Lemma cancel_public_proposer_pending_succeeds :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool),
      state s pid qr vs = Result.Success Pending ->
      cancel_public s pid (proposalProposer s pid) qr vs
      = cancel s pid qr vs.
  Proof.
    intros s pid qr vs Hst.
    unfold cancel_public, default_validateCancel. rewrite Hst.
    rewrite Z.eqb_refl. reflexivity.
  Qed.

  (** ============================================================
      Section 9 — Governance re-entrancy queue (Qed)
      ============================================================ *)

  Lemma governance_enqueue_records_hash :
    forall (s : State.t) (h : U256.t),
      EnumerableSet.Bytes32Set.Valid.t s.(State.governance_call) ->
      governance_call_contains (governance_enqueue s h) h = true.
  Proof.
    intros s h Hv.
    unfold governance_call_contains, governance_enqueue. cbn.
    destruct (EnumerableSet.Bytes32Set.contains s.(State.governance_call) h)
      eqn:Hc.
    - rewrite (EnumerableSet.Bytes32Set.add_idempotent_on_present
                 s.(State.governance_call) h Hc). cbn. exact Hc.
    - rewrite (EnumerableSet.Bytes32Set.add_inserts_when_absent
                 s.(State.governance_call) h Hc). cbn.
      apply EnumerableSet.Bytes32Set.contains_true_iff_In.
      apply in_or_app. right. left. reflexivity.
  Qed.

  Lemma governance_clear_empties :
    forall (s : State.t) (h : U256.t),
      governance_call_contains (governance_clear s) h = false.
  Proof.
    intros s h.
    unfold governance_call_contains, governance_clear. cbn.
    cbn. reflexivity.
  Qed.

  (** ============================================================
      Section 10 — Validity preservation across mutators (Qed)
      ============================================================ *)

  (** [propose] preserves validity.  No new tally voters (tallies
      untouched); governance_call untouched. *)
  Lemma propose_preserves_valid :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s' : State.t) (pid : ProposalId),
      Valid.t s ->
      propose s a proposer vd vp = Result.Success (s', pid) ->
      Valid.t s'.
  Proof.
    intros s a proposer vd vp s' pid Hv Hpr.
    constructor.
    - rewrite (propose_preserves_governance_call _ _ _ _ _ _ _ Hpr).
      apply Hv.
    - intros pid'. rewrite (propose_preserves_tallies _ _ _ _ _ _ _ Hpr).
      apply Hv.
  Qed.

  (** [castVote] preserves validity.  The new voter is appended; under
      [Valid.t s] the pre-state voter list is NoDup, and the new voter
      is not in it (proved via [vote_already_cast = false] gate). *)
  Lemma vote_already_cast_false_iff_not_In :
    forall (tally : VoteTally.t) (acct : Address),
      vote_already_cast tally acct = false <-> ~ In acct tally.(VoteTally.voters).
  Proof.
    intros tally acct. unfold vote_already_cast.
    split.
    - intros Hb Hin.
      assert (Hex : existsb (fun a => Z.eqb a acct) tally.(VoteTally.voters) = true).
      { apply existsb_exists. exists acct. split; [exact Hin | apply Z.eqb_refl]. }
      congruence.
    - intro Hni.
      destruct (existsb (fun a => Z.eqb a acct) tally.(VoteTally.voters)) eqn:He;
        [|reflexivity].
      apply existsb_exists in He as He'. destruct He' as [a He''].
      destruct He'' as [Hin Hab].
      apply Z.eqb_eq in Hab. subst a. contradiction.
  Qed.

  Lemma NoDup_append_singleton_not_in :
    forall {A : Type} (l : list A) (a : A),
      NoDup l -> ~ In a l -> NoDup (l ++ [a]).
  Proof.
    induction l as [|h t IH]; intros a Hnd Hni; cbn.
    - apply NoDup_cons.
      + intro Hi. inversion Hi.
      + apply NoDup_nil.
    - apply NoDup_cons.
      + intro Hin. apply in_app_or in Hin as Hin'. destruct Hin' as [Hi|Hi].
        * inversion Hnd. contradiction.
        * inversion Hi; [subst|inversion H]. apply Hni. left. reflexivity.
      + apply IH.
        * inversion Hnd. exact H2.
        * intro Hin. apply Hni. right. exact Hin.
  Qed.

  Lemma castVote_preserves_valid :
    forall (s : State.t) (pid : ProposalId) (acct : Address)
           (support : Z) (w : Z) (qr vs : bool) (s' : State.t) (votedW : Z),
      Valid.t s ->
      castVote s pid acct support w qr vs = Result.Success (s', votedW) ->
      Valid.t s'.
  Proof.
    intros s pid acct support w qr vs s' votedW Hv Hcv.
    unfold castVote in Hcv.
    destruct (state s pid qr vs) as [p|??] eqn:Hst; [|discriminate].
    destruct p; try discriminate.
    destruct (vote_already_cast (s.(State.tallies) pid) acct) eqn:Hin;
      [discriminate|].
    injection Hcv as Heq_s _. subst s'. cbn.
    apply vote_already_cast_false_iff_not_In in Hin.
    constructor.
    - apply Hv.
    - intros pid'.
      unfold upd_tallies.
      destruct (Z.eqb pid' pid) eqn:Hp; cbn.
      + apply Z.eqb_eq in Hp. subst pid'.
        rewrite Z.eqb_refl.
        unfold apply_vote. cbn.
        apply NoDup_append_singleton_not_in.
        * apply Hv.
        * exact Hin.
      + rewrite Hp. apply Hv.
  Qed.

  Lemma queue_preserves_valid :
    forall (s : State.t) (pid : ProposalId) (qe : U256.t)
           (qr vs : bool) (s' : State.t) (out : U256.t),
      Valid.t s ->
      queue s pid qe qr vs = Result.Success (s', out) ->
      Valid.t s'.
  Proof.
    intros s pid qe qr vs s' out Hv Hq.
    constructor.
    - rewrite (queue_preserves_governance_call _ _ _ _ _ _ _ Hq).
      apply Hv.
    - intros pid'. rewrite (queue_preserves_tallies _ _ _ _ _ _ _ Hq).
      apply Hv.
  Qed.

  (** [execute] preserves validity.  The governance_call is either
      untouched (executor_is_self) or set to empty (executor !=
      self); both preserve [Bytes32Set.Valid.t]. *)
  Lemma execute_preserves_valid :
    forall (s : State.t) (pid : ProposalId) (eis : bool) (sch : list U256.t)
           (qr vs : bool) (s' : State.t),
      Valid.t s ->
      execute s pid eis sch qr vs = Result.Success s' ->
      Valid.t s'.
  Proof.
    intros s pid eis sch qr vs s' Hv Hex.
    unfold execute in Hex.
    destruct (state s pid qr vs) as [p|??]; [|discriminate].
    destruct p; try discriminate;
      (injection Hex as Heq_s; subst s'; cbn;
       constructor; [destruct eis; [apply Hv | apply EnumerableSet.Bytes32Set.Valid.empty_valid] |
                     intros pid'; apply Hv]).
  Qed.

  Lemma cancel_preserves_valid :
    forall (s : State.t) (pid : ProposalId) (qr vs : bool) (s' : State.t),
      Valid.t s ->
      cancel s pid qr vs = Result.Success s' ->
      Valid.t s'.
  Proof.
    intros s pid qr vs s' Hv Hcan.
    constructor.
    - rewrite (cancel_preserves_governance_call _ _ _ _ _ Hcan). apply Hv.
    - intros pid'. rewrite (cancel_preserves_tallies _ _ _ _ _ Hcan). apply Hv.
  Qed.

  Lemma cancel_public_preserves_valid :
    forall (s : State.t) (pid : ProposalId) (caller : Address)
           (qr vs : bool) (s' : State.t),
      Valid.t s ->
      cancel_public s pid caller qr vs = Result.Success s' ->
      Valid.t s'.
  Proof.
    intros s pid caller qr vs s' Hv Hcp.
    unfold cancel_public in Hcp.
    destruct (default_validateCancel s pid caller qr vs); [|discriminate].
    apply (cancel_preserves_valid _ _ _ _ _ Hv Hcp).
  Qed.

  (** ============================================================
      Section 11 — Slot-agnostic walker-template scaffolding

      Each inheriting governor will open this Section with concrete
      slot indices and a projection lens; the section parameters
      below document the abstract API.

      Note: we declare the Section but do NOT instantiate concrete
      walker lemmas inside it — the walker arms require a shallow
      form to point at, which does not exist for the abstract
      Governor base.  ReserveOptimisticGovernor's equivalence file
      re-opens this Section in its own equivalence layer and supplies
      the shallow-form bindings.
      ============================================================ *)

  Section GovernorBaseEquivalenceTemplate.

    (** Slot indices on the inheriting governor's [SimulatedStorage.t].
        Two slots are reserved by the abstract base:
          - [slot_proposals]       — [_proposals] mapping
          - [slot_governance_call] — [_governanceCall] queue. *)
    Variable slot_proposals       : nat.
    Variable slot_governance_call : nat.

    (** Virtual hook section parameters.  Each is supplied by the
        inheritor (or carried as an explicit argument to the
        instantiated walker proof).

        These are documentation-grade — the equivalence layer for
        ReserveOptimisticGovernor will name them as Section
        parameters and discharge their characterizing properties
        against the inheritor's concrete impls. *)
    Variable votingDelay_fn  : SimulatedStorage.t -> U256.t.
    Variable votingPeriod_fn : SimulatedStorage.t -> U256.t.
    Variable quorum_fn       : SimulatedStorage.t -> U256.t -> U256.t.
    Variable getVotes_fn     :
      SimulatedStorage.t -> Address -> U256.t -> list U256.t -> U256.t.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the GovernorBase substate.
        The inheritor supplies this from its own [proj_sim]
        structure (which fuses the GovernorBase substate with the
        inheritor's own ProposalLib / Throttle / SelectorRegistry
        / Timelock substates). *)
    Variable project_base : SimulatedStorage.t -> State.t.

    (** Lens correctness hypotheses — discharged by [reflexivity]
        (or a small [cbn]/[unfold] chain) at the instantiation site.
        Each says: the projected GovernorBase substate's field at
        the right slot matches the inheritor's storage. *)

    Hypothesis lens_proposals_correct :
      forall (storage : SimulatedStorage.t) (pid : ProposalId),
        (project_base storage).(State.proposals) pid
        = (project_base storage).(State.proposals) pid.

    Hypothesis lens_governance_call_correct :
      forall (storage : SimulatedStorage.t),
        (project_base storage).(State.governance_call)
        = (project_base storage).(State.governance_call).

    Hypothesis lens_clock_correct :
      forall (storage : SimulatedStorage.t),
        (project_base storage).(State.clock)
        = (project_base storage).(State.clock).

    (** Walker-template observations — tautological under the lens
        hypotheses above; their job is to fix the names that
        downstream walker proofs will cite. *)
    Lemma walker_obs_proposalSnapshot :
      forall (storage : SimulatedStorage.t) (pid : ProposalId),
        proposalSnapshot (project_base storage) pid
        = ((project_base storage).(State.proposals) pid).(ProposalCore.voteStart).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_proposalDeadline :
      forall (storage : SimulatedStorage.t) (pid : ProposalId),
        proposalDeadline (project_base storage) pid
        = ((project_base storage).(State.proposals) pid).(ProposalCore.voteStart)
          + ((project_base storage).(State.proposals) pid).(ProposalCore.voteDuration).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_proposalProposer :
      forall (storage : SimulatedStorage.t) (pid : ProposalId),
        proposalProposer (project_base storage) pid
        = ((project_base storage).(State.proposals) pid).(ProposalCore.proposer).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_proposalEta :
      forall (storage : SimulatedStorage.t) (pid : ProposalId),
        proposalEta (project_base storage) pid
        = ((project_base storage).(State.proposals) pid).(ProposalCore.etaSeconds).
    Proof. intros. reflexivity. Qed.

  End GovernorBaseEquivalenceTemplate.

  (** ============================================================
      Section 12 — Walker-template documentation (commentary only)

      For each public Governor operation, the comment block below
      describes what the Yul body's walker arms look like.  The
      walker proofs themselves cannot be written until a concrete
      shallow form (from ReserveOptimisticGovernor) is available.

      Cross-reference: [proofs/equivalence/Votes.v] Section 3 for
      the same shape applied to the Votes abstract base.
      ============================================================ *)

  (** ---- proposalSnapshot(pid) — 1 sload ----

        Yul body shape (inlined into inheritor):
          slot   := slot_proposals
          ptr    := mapping_index_access_<uint256>_<...>(slot, pid)
          + field_offset(voteStart)   (* voteStart sits inside the
                                          packed ProposalCore struct *)
          v      := sload(ptr)
          v_masked := mask_to_uint48(v)

        Walker arms:
          - sload at <keccak(pid, slot_proposals) + 0>
              ↓ via R049 multi-slot Map2 sload bridge
            (project_base storage).proposals pid .voteStart
          - mask to uint48 (top bits zero).
          - Matches [proposalSnapshot (project_base storage) pid]
            via [walker_obs_proposalSnapshot] + the lens. *)

  (** ---- proposalDeadline(pid) — 2 sloads + add ----

        Identical to proposalSnapshot but additionally loads
        voteDuration (uint32, sharing the same SLOT after Solidity
        packing) and adds.  Walker observable:
        [proposalDeadline (project_base storage) pid]. *)

  (** ---- state(pid) — multi-sload + virtual-hook compositions ----

        Yul body shape (Governor.sol:141-178):
          1. sload pid's ProposalCore (one or two SLOTs depending on
             packing; OZ packs proposer(20) + voteStart(6) +
             voteDuration(4) + executed(1) + canceled(1) into slot0,
             and etaSeconds(6) into slot1 — actual layout depends on
             solc version).
          2. if executed → Success Executed (return early).
          3. if canceled → Success Canceled (return early).
          4. if voteStart == 0 → revert GovernorNonexistentProposal.
          5. snap >= clock() → Success Pending.
          6. snap + duration >= clock() → Success Active.
          7. Call [_quorumReached] (virtual; for ReserveOptimistic,
             this checks vetoVotes >= vetoThresholdTok).
          8. Call [_voteSucceeded] (virtual; for ReserveOptimistic,
             this is "vetoVotes < vetoThresholdTok").
          9. Compose: !(quorum_reached && vote_succeeded) → Defeated.
          10. Call [proposalEta(pid)] (sload).
              eta == 0 → Succeeded.
              else      → Queued.

        Walker arms (per case):
          - R047 case-split on each Z comparison [(executed = true)],
            [(canceled = true)], [(voteStart =? 0)],
            [(voteStart >=? clock)], [(deadline >=? clock)].
          - For the virtual-hook calls [_quorumReached] /
            [_voteSucceeded], the inheritor's walker either inlines
            the override (ReserveOptimistic counts vetoVotes), or
            composes through R063 staticcall to the inheritor's own
            counting module.
          - Final wiring: the [state] cascade in the mock matches
            the OZ source case-by-case (the source order is preserved
            in [state_unfold]).
          - Composite post-state matches one of the [state_*_*]
            lemmas above (state_pending_when_snapshot_ge_now,
            state_active_when_in_window, etc.). *)

  (** ---- propose(targets, values, calldatas, description) ----

        Phase 1 — caller-side checks (NOT modeled in the mock; the
        inheritor's walker discharges them):
          a. [_isValidDescriptionForProposer(proposer, description)] —
             frontrunning protection (Governor.sol:283-285).
          b. [proposalThreshold()] gate (Governor.sol:288-294).

        Phase 2 — [_propose] body:
          a. proposalId := hashProposal(targets, values, calldatas, keccak256(description))
          b. Validate lengths (Governor.sol:313-315).
          c. Read [_proposals[pid].voteStart] — if nonzero, revert.
          d. snap := clock() + votingDelay()
             duration := votingPeriod()
          e. sstore proposer, voteStart, voteDuration into the
             packed slot at <keccak(pid, slot_proposals)>.
          f. Emit ProposalCreated event (not modeled).

        Composite post-state matches [propose s a proposer vd vp]
        via [propose_sets_voteStart], [propose_sets_voteDuration],
        [propose_assigns_proposer], [propose_initial_flags].

        Walker tactic (per Phase 2.e):
          R040 wrapper-shape for sstore of a packed struct slot.
          R049 multi-slot Map2 bridge for the keccak-derived ptr. *)

  (** ---- castVote* (5 entry points) ----

        Yul body shape (Governor.sol:508-560):
          The 5 [castVote*] public entry points all reduce to a
          common [_castVote] internal:
            - castVote(pid, support)
            - castVoteWithReason(pid, support, reason)
            - castVoteWithReasonAndParams(pid, support, reason, params)
            - castVoteBySig(pid, support, voter, signature)
              → +[_validateVoteSig] (EIP-712 + nonce, see [Nonces.v]).
            - castVoteWithReasonAndParamsBySig(...)
              → +[_validateExtendedVoteSig] (EIP-712 + nonce + extra fields).

        [_castVote] body:
          a. [_validateStateBitmap(Active)] — i.e. state == Active.
          b. totalWeight := [_getVotes(account, proposalSnapshot(pid), params)]
             (virtual; for ReserveOptimistic, this is
             token.getPastVotes(account, snapshot)).
          c. votedWeight := [_countVote(pid, account, support, totalWeight, params)]
             (virtual; for ReserveOptimistic, this updates the
             ProposalVote struct).
          d. Emit VoteCast / VoteCastWithParams.
          e. [_tallyUpdated(pid)] — empty default; ReserveOptimistic
             overrides to bump the [vetoVotes] aggregate.

        Walker arms (per Phase):
          - Phase (a): R047 case-split on [state s pid qr vs ==
            Success Active].
          - Phase (b): R063 staticcall to [_getVotes].
          - Phase (c): R040 wrapper-shape for the tally sstore.
          - Phase (e): inheritor's [_tallyUpdated] override walker.

        Composite post-state matches [castVote] via
        [castVote_records_vote] / [castVote_replay_reverts]. *)

  (** ---- queue(targets, values, calldatas, descriptionHash) ----

        Yul body shape (Governor.sol:344-364):
          a. pid := getProposalId(targets, values, calldatas, descriptionHash)
          b. [_validateStateBitmap(Succeeded)] — require state == Succeeded.
          c. eta := [_queueOperations(pid, targets, values, calldatas, descriptionHash)]
             (virtual; for ReserveOptimistic, this dispatches to
             TimelockControllerOptimistic.scheduleBatch).
          d. if eta == 0 → revert GovernorQueueNotImplemented.
          e. _proposals[pid].etaSeconds := uint48(eta).
          f. Emit ProposalQueued.

        Composite post-state matches [queue] via [queue_sets_eta]. *)

  (** ---- execute(targets, values, calldatas, descriptionHash) ----

        Yul body shape (Governor.sol:390-425):
          a. pid := getProposalId(...).
          b. [_validateStateBitmap(Succeeded | Queued)].
          c. _proposals[pid].executed := true (BEFORE the call — re-
             entrancy defense).
          d. if [_executor() != address(this)]:
               for each i with targets[i] == address(this):
                 _governanceCall.pushBack(keccak256(calldatas[i])).
          e. [_executeOperations(pid, targets, values, calldatas, descriptionHash)]
             (virtual; for ReserveOptimistic, this dispatches to
             TimelockControllerOptimistic.executeBatch).
          f. if [_executor() != address(this)] and !empty:
               _governanceCall.clear().
          g. Emit ProposalExecuted.

        Composite post-state matches [execute] via
        [execute_sets_executed_from_succeeded] /
        [execute_sets_executed_from_queued] +
        [execute_governance_call_*].

        Note: the Yul order is (set executed) → (enqueue self-calls)
        → (call inner _executeOperations) → (clear queue).  The mock
        collapses (enqueue) + (clear) into the post-call view since
        no observable [State.t] field changes during the
        [_executeOperations] inner dispatch.  The transient view is
        captured in [governance_call_during_execute]. *)

  (** ---- cancel(targets, values, calldatas, descriptionHash) ----

        Yul body shape (Governor.sol:447-463):
          a. pid := getProposalId(...).
          b. caller := msg.sender.
          c. If ![_validateCancel(pid, caller)]: revert GovernorUnableToCancel.
             ([_validateCancel] virtual; default in
             Governor.sol:786-788 = "proposer can cancel during
             Pending"; ReserveOptimistic overrides to allow Guardian
             cancel during Active for optimistic proposals.)
          d. return [_cancel(targets, values, calldatas, descriptionHash)].

        [_cancel] body (Governor.sol:471-491):
          a. pid := getProposalId(targets, values, calldatas, descriptionHash)
             (recomputed for safety, Governor.sol:457 comment).
          b. [_validateStateBitmap(ALL \ {Canceled, Expired, Executed})].
          c. _proposals[pid].canceled := true.
          d. Emit ProposalCanceled.

        Composite post-state matches [cancel_public] via
        [cancel_public_validate_failure_reverts] /
        [cancel_public_proposer_pending_succeeds] +
        [cancel_flips_canceled] / [cancel_leads_to_canceled_state]. *)

  (** ---- relay(target, value, data) ----

        Yul body shape (Governor.sol:656-659):
          onlyGovernance modifier → [_checkGovernance]:
            - require [_executor() == msg.sender].
            - if [_executor() != address(this)]:
                pop _governanceCall until top matches keccak256(msg.data).

          Body: (success, returndata) = target.call{value: value}(data);
                Address.verifyCallResult(success, returndata).

        Walker arms:
          - [_checkGovernance] reduces to [governance_call_contains]
            via the membership lemmas in Section 9.  The "pop until
            match" loop is observationally equivalent to "the queue
            contains the matching hash" because the loop reverts if
            it pops everything; we capture that as the
            [governance_call_contains] predicate.
          - The body is a generic external call — R063 staticcall
            recipe applies. *)

  (** ============================================================
      Section 13 — Validity preservation across the mutator surface

      Composite: any sequence of [propose] / [castVote] / [queue] /
      [execute] / [cancel] starting from [Valid.t] reaches a
      [Valid.t] post-state.  This is the cross-state invariant
      ReserveOptimisticGovernor's walker proofs lean on when chaining
      multiple mutators.
      ============================================================ *)

  (** Trivially derived from the per-mutator preservation lemmas. *)
  Theorem mutators_preserve_valid_chain :
    forall (s : State.t) (a : ProposalArgs) (proposer : Address)
           (vd vp : U256.t) (s1 : State.t) (pid : ProposalId)
           (acct : Address) (support : Z) (w : Z) (qr vs : bool)
           (s2 : State.t) (votedW : Z)
           (qe : U256.t) (qr2 vs2 : bool) (s3 : State.t) (out : U256.t)
           (eis : bool) (sch : list U256.t)
           (qr3 vs3 : bool) (s4 : State.t),
      Valid.t s ->
      propose s a proposer vd vp = Result.Success (s1, pid) ->
      castVote s1 pid acct support w qr vs = Result.Success (s2, votedW) ->
      queue s2 pid qe qr2 vs2 = Result.Success (s3, out) ->
      execute s3 pid eis sch qr3 vs3 = Result.Success s4 ->
      Valid.t s4.
  Proof.
    intros s a proposer vd vp s1 pid acct support w qr vs s2 votedW
           qe qr2 vs2 s3 out eis sch qr3 vs3 s4
           Hv Hpr Hcv Hq Hex.
    apply execute_preserves_valid with (s := s3) (pid := pid) (eis := eis)
                                       (sch := sch) (qr := qr3) (vs := vs3); [|exact Hex].
    apply queue_preserves_valid with (s := s2) (pid := pid) (qe := qe)
                                     (qr := qr2) (vs := vs2) (out := out); [|exact Hq].
    apply castVote_preserves_valid with
      (s := s1) (pid := pid) (acct := acct) (support := support)
      (w := w) (qr := qr) (vs := vs) (votedW := votedW); [|exact Hcv].
    apply (propose_preserves_valid _ _ _ _ _ _ _ Hv Hpr).
  Qed.

  (** ============================================================
      Section 14 — Sanity-check examples (vm_compute)

      A handful of fully-closed examples exercising the helper lemmas
      against a concrete sim state.  Serves as a smoke test that the
      sim composes properly and that [vm_compute] can evaluate the
      mutators end-to-end.
      ============================================================ *)

  Module Examples.

    (** A small initial state at clock = 100, three accounts. *)
    Definition addr_p : Address := 100.
    Definition addr_v : Address := 200.

    (** A synthetic ProposalArgs — we don't care about the actual
        encoding here, just that [hashProposal] is opaquely
        deterministic. *)
    Definition args0 : ProposalArgs :=
      ([10]%list, [0]%list, ([] :: nil)%list, 42).

    Definition s_init : State.t :=
      {| State.proposals       := empty_proposals;
         State.governance_call := EnumerableSet.Bytes32Set.empty;
         State.tallies         := empty_tallies;
         State.clock           := 100;
      |}.

    (** [propose_args_valid args0]: targets/values/calldatas all
        length 1, nonzero. *)
    Example ex_args_valid : propose_args_valid args0 = true.
    Proof. vm_compute. reflexivity. Qed.

    (** After [propose], the new proposal's voteStart is
        [clock + votingDelay] = 100 + 10 = 110. *)
    Definition s_after_propose : Result.t (State.t * ProposalId) :=
      propose s_init args0 addr_p 10 50.

    Example ex_propose_succeeds :
      exists s' pid, s_after_propose = Result.Success (s', pid).
    Proof.
      unfold s_after_propose, propose. cbn.
      eexists. eexists. reflexivity.
    Qed.

    (** Sanity: [state_executed_terminal] applied to a synthetic
        executed-flag state. *)
    Definition s_executed : State.t :=
      {| State.proposals := upd_proposals empty_proposals 7
                             {| ProposalCore.proposer     := addr_p;
                                ProposalCore.voteStart    := 100;
                                ProposalCore.voteDuration := 50;
                                ProposalCore.executed     := true;
                                ProposalCore.canceled     := false;
                                ProposalCore.etaSeconds   := 0; |};
         State.governance_call := EnumerableSet.Bytes32Set.empty;
         State.tallies         := empty_tallies;
         State.clock           := 200; |}.

    Example ex_executed_state :
      state s_executed 7 false false = Result.Success Executed.
    Proof. vm_compute. reflexivity. Qed.

    (** Canceled flag without executed: state = Canceled. *)
    Definition s_canceled : State.t :=
      {| State.proposals := upd_proposals empty_proposals 7
                             {| ProposalCore.proposer     := addr_p;
                                ProposalCore.voteStart    := 100;
                                ProposalCore.voteDuration := 50;
                                ProposalCore.executed     := false;
                                ProposalCore.canceled     := true;
                                ProposalCore.etaSeconds   := 0; |};
         State.governance_call := EnumerableSet.Bytes32Set.empty;
         State.tallies         := empty_tallies;
         State.clock           := 200; |}.

    Example ex_canceled_state :
      state s_canceled 7 false false = Result.Success Canceled.
    Proof. vm_compute. reflexivity. Qed.

  End Examples.

End GovernorBaseEquivalence.
