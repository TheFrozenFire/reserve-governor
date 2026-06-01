(** ReserveOptimisticGovernor — escalation state machine simulation.

    Mirrors contracts/governance/ReserveOptimisticGovernor.sol — a
    hybrid governor that unifies the optimistic and pessimistic
    governance flows. The defining property is the fast-to-slow
    *escalation*: an optimistic proposal under veto transitions to a
    standard confirmation vote (a fresh ProposalCore with a different
    proposalId, sharing the calls), or it reaches its optimistic
    deadline and becomes executable directly.

    This simulation models the proposal-state machine only — the
    actual ERC20 transfers, the timelock dispatch, and the OZ Governor
    storage layout are abstracted away. The contract delegates to:

      - ProposerThrottle.consume — modeled as an oracle that returns
        a residual charges-remaining count.
      - OptimisticSelectorRegistry.isAllowed(target, selector) —
        modeled as a list of allowed [Address * Selector] tuples.
      - token.getPastTotalSupply / getPastVotes — supplied per-call as
        explicit [U256.t] arguments.
      - TimelockControllerOptimistic.scheduleBatch / executeBatch /
        executeBatchBypass — modeled as a phase bump.

    Phase encoding (matches state() in the source):

      PhaseSubmitted    voteStart in future (pending), optimistic
      PhaseActive       in optimistic veto window
      PhaseDefeated     vetoVotes >= vetoThresholdTok within window
                        side-exit: spawns a new standard proposal
      PhaseSucceeded    optimistic deadline elapsed, !defeated
      PhaseExecuted     terminal — optimistic execute-bypass path
      PhaseCanceled     terminal cancellation

    Standard / confirmation phase (different proposalId):
      PhaseStdPending     voteStart > now
      PhaseStdActive      in voting window
      PhaseStdSucceeded   forVotes pass + quorum + deadline elapsed
      PhaseStdQueued      timelock.scheduleBatch called
      PhaseStdExecuted    timelock.executeBatch called

    [block.timestamp] is read on-chain; here it is passed explicitly as
    [now : U256.t] so the simulation is pure.

    Revert coverage:
      - revert_throttle_exceeded     proposeOptimistic with no charge.
      - revert_invalid_proposal      empty or length-mismatched batch.
      - revert_invalid_call          (target, selector) not in registry.
      - revert_wrong_phase           operation issued from a phase that
                                     does not permit it.
      - revert_optimistic_no_queue   queueOperations on an optimistic
                                     proposal.
      - revert_not_optimistic        executeOptimistic on a standard
                                     proposal.
      - revert_already_terminal      cancel after execute.

    Not modeled (deliberately):
      - The proposer-threshold check on the pessimistic propose() path
        (covered by ProposalLib / StakingVault delegation surfaces).
      - The "ConfirmationPrefix not allowed" check on the description
        string (string-content concern, not state-machine).
      - The transitionedVetoThreshold sentinel (UINT256_MAX): the
        state-machine view here treats the parent as Defeated once a
        child has been spawned, which is the observable contract
        outcome.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module Governor.

Definition Address  : Set := U256.t.
Definition Selector : Set := U256.t.
Definition FIX_ONE  : Z := 10 ^ 18.

(** ===== Phase ===== *)
Inductive Phase : Set :=
| PhaseSubmitted
| PhaseActive
| PhaseDefeated
| PhaseSucceeded
| PhaseExecuted
| PhaseCanceled
| PhaseStdPending
| PhaseStdActive
| PhaseStdSucceeded
| PhaseStdQueued
| PhaseStdExecuted.

(** Total ordering used for monotonicity proofs. The two tracks
    (optimistic and standard) are merged onto a single index so a
    parent's Defeated and a child's StdPending sit at consecutive
    indices; once the child reaches StdExecuted the parent is
    considered terminal too. *)
Definition phase_index (p : Phase) : Z :=
  match p with
  | PhaseSubmitted    => 0
  | PhaseActive       => 1
  | PhaseSucceeded    => 2
  | PhaseDefeated     => 2
  | PhaseStdPending   => 3
  | PhaseStdActive    => 4
  | PhaseStdSucceeded => 5
  | PhaseStdQueued    => 6
  | PhaseStdExecuted  => 7
  | PhaseExecuted     => 7
  | PhaseCanceled     => 7
  end.

(** ===== TRANSITIONED_VETO_THRESHOLD sentinel =====

    Mirrors [ProposalLib.TRANSITIONED_VETO_THRESHOLD = type(uint256).max]
    (ProposalLib.sol:20). The contract overwrites a proposal's stored
    [optimisticProposalDetails[proposalId].vetoThreshold] with this
    value inside [transitionToPessimistic] (ProposalLib.sol:122). The
    [state()] view short-circuits to [Defeated] when it observes the
    sentinel (ReserveOptimisticGovernor.sol:243-246), BEFORE the
    [pastSupply] read or the threshold-tok multiplication — both of
    which would otherwise mishandle the sentinel value (the multiply
    would either overflow on-chain or, in the sim's unbounded Z,
    produce a value that the snap-to-1 cannot bring back into range).

    Defined here (rather than imported from [ProposalLib]) so that
    the [Governor] sim's [observe] can refer to it without a forward
    import; the equivalence to [ProposalLib.ProposalLib.TRANSITIONED_VETO_THRESHOLD]
    is checked by reflexivity in [Governor_no_de_escalation.v]. *)
Definition TRANSITIONED_VETO_THRESHOLD : U256.t := 2 ^ 256 - 1.

(** ===== Proposal record =====

    The simulation tracks the minimal fields needed for the state
    machine: when voting opens, how long it lasts, the threshold
    fraction (in D18, i.e. the un-snapped [vetoThreshold(proposalId)]
    value), the running tally of veto votes, the current phase, and
    whether this is an optimistic or a standard proposal. [parent] is
    0 for fresh proposals and equals the parent proposalId for
    confirmation children.

    [vetoThresholdD18] is the live, mutable per-proposal threshold
    fraction. The contract's [state()] reads
    [optimisticProposalDetails[proposalId].vetoThreshold] at every
    observation (ReserveOptimisticGovernor.sol:241), so this field is
    written:
      - at create time to the global [optimisticParams.vetoThreshold]
        value, AND
      - re-written to [TRANSITIONED_VETO_THRESHOLD] by
        [transition_to_pessimistic] when the parent escalates.
    The snapped {tok} threshold used to gate Defeated is computed on
    the fly in [observe] via [vetoThresholdTokOf vetoThresholdD18
    pastSupply], matching the contract's
    [(_vetoThreshold * pastSupply) / 1e18] re-evaluation per call
    (ROG.sol:256-257). This closes CRIT-V / T1.4 from the adversarial
    review (see notes/adversarial_review_2026_05_31/SYNTHESIS.md);
    previously the sim froze the snapped value at create time.

    [pastSupply] is [token().getPastTotalSupply(voteStart)] — the
    historical token supply at the proposal's snapshot block. The
    contract re-reads this on every call to [state()] (see
    ReserveOptimisticGovernor.sol:249), but since [getPastTotalSupply]
    is a historical query keyed by the immutable [voteStart], the
    value is constant once the snapshot block is mined. Storing it
    once in the simulation is observably equivalent to the contract's
    live read AT THE pastSupply LEVEL.

    [pastSupply] is required by [observe] to model the contract's
    [pastSupply == 0 -> Canceled] short-circuit branch
    (ReserveOptimisticGovernor.sol:251-253) — the CRIT-G branch
    closed by adversarial review T1.3. For standard-track children
    the field is set to 1 (a non-zero placeholder) since the standard
    track does not consult this branch. *)
Module Proposal.
  Record t : Set := {
    pid               : U256.t;
    proposer          : Address;
    voteStart         : U256.t;   (** {seconds} *)
    voteDuration      : U256.t;   (** {seconds} *)
    vetoThresholdD18  : U256.t;   (** D18{1}, un-snapped threshold fraction *)
    againstVotes      : U256.t;   (** {tok} *)
    phase             : Phase;
    isOptimistic      : bool;
    parent            : U256.t;   (** 0 = no parent *)
    pastSupply        : U256.t;   (** {tok}, getPastTotalSupply(voteStart) *)
  }.
End Proposal.

(** [vetoThresholdD18] is the live, mutable per-proposal threshold
    fraction (initialized to [optimisticParams.vetoThreshold] at
    create); [pastSupply] is the snapshot-time
    [getPastTotalSupply(voteStart)]. [observe] computes the snapped
    {tok} threshold from these on demand. *)
Definition fresh_optimistic
    (pid : U256.t) (proposer : Address)
    (voteStart voteDuration vetoThresholdD18 pastSupply : U256.t)
    : Proposal.t :=
  {|
    Proposal.pid               := pid;
    Proposal.proposer          := proposer;
    Proposal.voteStart         := voteStart;
    Proposal.voteDuration      := voteDuration;
    Proposal.vetoThresholdD18  := vetoThresholdD18;
    Proposal.againstVotes      := 0;
    Proposal.phase             := PhaseSubmitted;
    Proposal.isOptimistic      := true;
    Proposal.parent            := 0;
    Proposal.pastSupply        := pastSupply;
  |}.

(** Standard-track children do not consult the threshold-tok
    computation (the optimistic-only [_isOptimistic] arm of [state()]
    is where vetoThresholdD18, pastSupply and the snap-Math.max all
    live in the contract); we set [vetoThresholdD18] to [0] and
    [pastSupply] to [1] (non-zero placeholder) so the "fresh standard
    children never appear as Canceled via the pastSupply branch"
    invariant is trivial. *)
Definition fresh_standard_child
    (parent_pid new_pid : U256.t) (proposer : Address)
    (voteStart voteDuration : U256.t)
    : Proposal.t :=
  {|
    Proposal.pid               := new_pid;
    Proposal.proposer          := proposer;
    Proposal.voteStart         := voteStart;
    Proposal.voteDuration      := voteDuration;
    Proposal.vetoThresholdD18  := 0;
    Proposal.againstVotes      := 0;
    Proposal.phase             := PhaseStdPending;
    Proposal.isOptimistic      := false;
    Proposal.parent            := parent_pid;
    Proposal.pastSupply        := 1;
  |}.

(** ===== Result ===== *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert  {_}.
End Result.

Definition revert_throttle_exceeded    {A : Set} : Result.t A := Result.Revert 0   32.
Definition revert_invalid_proposal     {A : Set} : Result.t A := Result.Revert 32  32.
Definition revert_invalid_call         {A : Set} : Result.t A := Result.Revert 64  32.
Definition revert_wrong_phase          {A : Set} : Result.t A := Result.Revert 96  32.
Definition revert_optimistic_no_queue  {A : Set} : Result.t A := Result.Revert 128 32.
Definition revert_not_optimistic       {A : Set} : Result.t A := Result.Revert 160 32.
Definition revert_already_terminal     {A : Set} : Result.t A := Result.Revert 192 32.
Definition revert_inactive_phase       {A : Set} : Result.t A := Result.Revert 224 32.
Definition revert_invalid_state        {A : Set} : Result.t A := Result.Revert 256 32.

(** ===== Veto-threshold snap (Math.max(_, 1)) ===== *)
Definition vetoThresholdTokOf (vetoThresholdD18 pastSupply : U256.t) : U256.t :=
  let raw := (vetoThresholdD18 * pastSupply) / FIX_ONE in
  if raw <? 1 then 1 else raw.

(** ===== state() — observable proposal phase at [now] =====

    Mirrors ReserveOptimisticGovernor.state() for optimistic and
    standard tracks. The pre-deadline cases are derived from the
    stored fields; the post-deadline outcomes (executed, canceled,
    succeeded, queued, std_succeeded) are reflected by the [phase]
    field after they are written.

    The contract's optimistic arm at ROG.sol:222-273 evaluates a
    cascade with these branches, in order:

      (a) executed?  Executed (sticky)
      (b) canceled?  Canceled (sticky)
      (c) snapshot >= block.timestamp?  Pending
      (d) _vetoThreshold == TRANSITIONED_VETO_THRESHOLD?  Defeated
      (e) pastSupply == 0?  Canceled                          [CRIT-G, T1.3]
      (f) vetoThresholdTok := max(1, _vetoThreshold * pastSupply / 1e18)
          (computed LIVE per call; both _vetoThreshold and pastSupply
          are reads from storage / historical query)            [CRIT-V, T1.4]
      (g) againstVotes >= vetoThresholdTok?  Defeated
      (h) deadline >= block.timestamp?  Active
      (i) otherwise  Succeeded

    CRIT-V (T1.4): step (f) is computed LIVE from [vetoThresholdD18]
    (the stored, mutable per-proposal threshold fraction) and
    [pastSupply] at each call to [observe]. The previous sim froze
    the snapped {tok} value at create time, which would mis-track any
    threshold change between create and observe. With [vetoThresholdD18]
    now stored as a mutable field and snapped on demand via
    [vetoThresholdTokOf], the sim re-evaluates the threshold every
    time [observe] is called — matching the contract.

    The TRANSITIONED-sentinel short-circuit (step d) must come BEFORE
    the snap-and-compare (step f), because the contract's check
    matches the sentinel value exactly, while the sim's
    [vetoThresholdTokOf] applied to the sentinel would produce a
    value larger than any realistic [againstVotes] — the votes
    comparison would always fail, returning Active/Succeeded instead
    of Defeated. The on-chain branch at ROG.sol:243-246 exists
    precisely for this reason.

    Subtle ordering: the pending-test (step c) precedes the
    TRANSITIONED test (step d) and the pastSupply test (step e), so a
    pre-snapshot proposal with sentinel threshold or zero pastSupply
    observes as [Pending], not [Defeated]/[Canceled]. The sim mirrors
    that ordering: the [now <? voteStart] guard is checked first. *)
Definition observe (p : Proposal.t) (now : U256.t) : Phase :=
  match p.(Proposal.phase) with
  | PhaseExecuted    => PhaseExecuted
  | PhaseCanceled    => PhaseCanceled
  | PhaseStdQueued   => PhaseStdQueued
  | PhaseStdExecuted => PhaseStdExecuted
  | _ =>
      if now <? p.(Proposal.voteStart) then
        if p.(Proposal.isOptimistic) then PhaseSubmitted else PhaseStdPending
      else
        let deadline := p.(Proposal.voteStart) + p.(Proposal.voteDuration) in
        if p.(Proposal.isOptimistic) then
          (* CRIT-V / T1.4: TRANSITIONED-sentinel short-circuit
             precedes the live tok computation. Matches
             ReserveOptimisticGovernor.sol:243-246. *)
          if p.(Proposal.vetoThresholdD18) =? TRANSITIONED_VETO_THRESHOLD
          then PhaseDefeated
          (* CRIT-G / T1.3: pastSupply == 0 -> Canceled, precedes the
             veto-threshold tok computation. Matches
             ReserveOptimisticGovernor.sol:251-253. *)
          else if p.(Proposal.pastSupply) =? 0 then PhaseCanceled
          else
            (* CRIT-V / T1.4: tok threshold computed LIVE per call
               from vetoThresholdD18 and pastSupply. Matches
               ReserveOptimisticGovernor.sol:256-257. *)
            let vtt := vetoThresholdTokOf p.(Proposal.vetoThresholdD18)
                                          p.(Proposal.pastSupply) in
            if p.(Proposal.againstVotes) >=? vtt then PhaseDefeated
            else if now <? deadline then PhaseActive
            else PhaseSucceeded
        else
          if now <? deadline then PhaseStdActive
          else p.(Proposal.phase)  (* post-deadline outcome is stored *)
  end.

(** [vetoThresholdTokAt]: the snapped {tok} threshold a proposal
    currently observes, computed from its [vetoThresholdD18] and
    [pastSupply]. For audit citation when downstream proofs need the
    snapped value without spelling out the [vetoThresholdTokOf]
    application. *)
Definition vetoThresholdTokAt (p : Proposal.t) : U256.t :=
  vetoThresholdTokOf p.(Proposal.vetoThresholdD18) p.(Proposal.pastSupply).

(** ===== Helpers ===== *)

(** Tuple-membership check on the selector-registry allowlist. *)
Fixpoint allowed_tuple
    (allow : list (Address * Selector))
    (target : Address) (sel : Selector) : bool :=
  match allow with
  | []                 => false
  | (a, s) :: rest =>
      if andb (a =? target) (s =? sel)
      then true
      else allowed_tuple rest target sel
  end.

(** Walk a parallel pair of lists [targets] [selectors] and check that
    every (t_i, s_i) is in the allowlist. Returns [false] on length
    mismatch or empty input. *)
Fixpoint all_calls_allowed
    (allow : list (Address * Selector))
    (targets : list Address) (selectors : list Selector) : bool :=
  match targets, selectors with
  | [], [] => true
  | t :: ts, s :: ss =>
      if allowed_tuple allow t s then all_calls_allowed allow ts ss
      else false
  | _, _ => false
  end.

Definition lengths_match (targets : list Address) (selectors : list Selector)
    : bool :=
  Nat.eqb (length targets) (length selectors).

(** ===== Transitions =====

    Each transition is a [Phase -> Result.t Phase] or
    [Proposal.t -> Result.t Proposal.t] function.

    [propose_optimistic] — gated on throttle, length-validity, and
    selector-registry membership. *)
Definition propose_optimistic
    (pid : U256.t) (proposer : Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply : U256.t)
    (throttleCharges : U256.t)
    (targets : list Address) (selectors : list Selector)
    (allow : list (Address * Selector))
    (now : U256.t)
    : Result.t Proposal.t :=
  if throttleCharges <? 1 then revert_throttle_exceeded
  else if Nat.eqb (length targets) 0 then revert_invalid_proposal
  else if negb (lengths_match targets selectors) then revert_invalid_proposal
  else if negb (all_calls_allowed allow targets selectors) then revert_invalid_call
  else
    (* CRIT-V / T1.4: store the un-snapped vetoThresholdD18 fraction.
       The contract writes [optimisticParams.vetoThreshold] into
       [optimisticProposalDetails[proposalId].vetoThreshold] at
       create time (ROG.sol:166) and re-reads it at every state()
       call (ROG.sol:241). Snapping into {tok} happens live in
       [observe], NOT here. *)
    Result.Success
      (fresh_optimistic pid proposer (now + vetoDelay) vetoPeriod
                        vetoThresholdD18 pastSupply).

Definition phase_eq (a b : Phase) : bool :=
  match a, b with
  | PhaseSubmitted, PhaseSubmitted => true
  | PhaseActive, PhaseActive => true
  | PhaseDefeated, PhaseDefeated => true
  | PhaseSucceeded, PhaseSucceeded => true
  | PhaseExecuted, PhaseExecuted => true
  | PhaseCanceled, PhaseCanceled => true
  | PhaseStdPending, PhaseStdPending => true
  | PhaseStdActive, PhaseStdActive => true
  | PhaseStdSucceeded, PhaseStdSucceeded => true
  | PhaseStdQueued, PhaseStdQueued => true
  | PhaseStdExecuted, PhaseStdExecuted => true
  | _, _ => false
  end.

(** [add_veto] — adds [delta] to the running tally. *)
Definition add_veto (p : Proposal.t) (delta : U256.t) : Proposal.t :=
  {|
    Proposal.pid               := p.(Proposal.pid);
    Proposal.proposer          := p.(Proposal.proposer);
    Proposal.voteStart         := p.(Proposal.voteStart);
    Proposal.voteDuration      := p.(Proposal.voteDuration);
    Proposal.vetoThresholdD18  := p.(Proposal.vetoThresholdD18);
    Proposal.againstVotes      := p.(Proposal.againstVotes) + delta;
    Proposal.phase             := p.(Proposal.phase);
    Proposal.isOptimistic      := p.(Proposal.isOptimistic);
    Proposal.parent            := p.(Proposal.parent);
    Proposal.pastSupply        := p.(Proposal.pastSupply);
  |}.

(** [transition_to_pessimistic] — spawns a fresh standard child
    carrying the same calls. The parent's
    [vetoThresholdD18] is written to [TRANSITIONED_VETO_THRESHOLD]
    (mirroring the contract at ProposalLib.sol:122) AND its phase is
    pinned to Defeated. Either change alone would suffice to keep
    [observe] returning Defeated; we apply both so the sim's stored
    representation mirrors the contract field-for-field, and so the
    sentinel-encoding lemmas in [Governor_no_de_escalation.v] hold
    against the existing [transition_to_pessimistic] entry point
    rather than a sister definition. The child is in
    PhaseStdPending. *)
Definition transition_to_pessimistic
    (parent : Proposal.t) (new_pid : U256.t)
    (votingDelay votingPeriod now : U256.t)
    : Result.t (Proposal.t * Proposal.t) :=
  match observe parent now with
  | PhaseDefeated =>
      let parent' :=
        {|
          Proposal.pid               := parent.(Proposal.pid);
          Proposal.proposer          := parent.(Proposal.proposer);
          Proposal.voteStart         := parent.(Proposal.voteStart);
          Proposal.voteDuration      := parent.(Proposal.voteDuration);
          Proposal.vetoThresholdD18  := TRANSITIONED_VETO_THRESHOLD;
          Proposal.againstVotes      := parent.(Proposal.againstVotes);
          Proposal.phase             := PhaseDefeated;
          Proposal.isOptimistic      := parent.(Proposal.isOptimistic);
          Proposal.parent            := parent.(Proposal.parent);
          Proposal.pastSupply        := parent.(Proposal.pastSupply);
        |}
      in
      let child := fresh_standard_child
                     parent.(Proposal.pid)
                     new_pid
                     parent.(Proposal.proposer)
                     (now + votingDelay)
                     votingPeriod in
      Result.Success (parent', child)
  | _ => revert_wrong_phase
  end.

(** Reach PhaseStdSucceeded — modeled as a phase write after a
    successful confirmation vote (post-deadline, !defeated, quorum
    met). The actual vote-tally semantics live inside the OZ Governor
    base; here we expose only the phase transition.

    Gating: stored phase must be PhaseStdActive (still in the voting
    window — the contract's _executeOperations would not be called
    yet) or PhaseStdPending (caller hasn't observed the snapshot
    flip), and the wall-clock must place the proposal past the
    deadline. We model this as the simpler observable: stored phase
    must be PhaseStdActive *and* [now >= voteStart + voteDuration]. *)
Definition mark_std_succeeded (p : Proposal.t) (now : U256.t)
    : Result.t Proposal.t :=
  if p.(Proposal.isOptimistic) then revert_wrong_phase
  else if negb (phase_eq p.(Proposal.phase) PhaseStdActive) then
    revert_wrong_phase
  else if now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration) then
    revert_wrong_phase
  else
    Result.Success
      {|
        Proposal.pid              := p.(Proposal.pid);
        Proposal.proposer         := p.(Proposal.proposer);
        Proposal.voteStart        := p.(Proposal.voteStart);
        Proposal.voteDuration     := p.(Proposal.voteDuration);
        Proposal.vetoThresholdD18 := p.(Proposal.vetoThresholdD18);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdSucceeded;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
        Proposal.pastSupply       := p.(Proposal.pastSupply);
      |}.

(** [queue_operations] — gates on (a) not-optimistic and (b)
    phase = PhaseStdSucceeded. Mirrors the
    OptimisticProposalCannotBeQueued revert at line 340. *)
Definition queue_operations (p : Proposal.t) : Result.t Proposal.t :=
  if p.(Proposal.isOptimistic) then revert_optimistic_no_queue
  else if phase_eq p.(Proposal.phase) PhaseStdSucceeded then
    Result.Success
      {|
        Proposal.pid              := p.(Proposal.pid);
        Proposal.proposer         := p.(Proposal.proposer);
        Proposal.voteStart        := p.(Proposal.voteStart);
        Proposal.voteDuration     := p.(Proposal.voteDuration);
        Proposal.vetoThresholdD18 := p.(Proposal.vetoThresholdD18);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdQueued;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
        Proposal.pastSupply       := p.(Proposal.pastSupply);
      |}
  else revert_wrong_phase.

(** [execute_standard] — requires PhaseStdQueued. *)
Definition execute_standard (p : Proposal.t) : Result.t Proposal.t :=
  if p.(Proposal.isOptimistic) then revert_wrong_phase
  else if phase_eq p.(Proposal.phase) PhaseStdQueued then
    Result.Success
      {|
        Proposal.pid              := p.(Proposal.pid);
        Proposal.proposer         := p.(Proposal.proposer);
        Proposal.voteStart        := p.(Proposal.voteStart);
        Proposal.voteDuration     := p.(Proposal.voteDuration);
        Proposal.vetoThresholdD18 := p.(Proposal.vetoThresholdD18);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdExecuted;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
        Proposal.pastSupply       := p.(Proposal.pastSupply);
      |}
  else revert_wrong_phase.

(** [execute_optimistic] — requires observe = PhaseSucceeded
    (post-deadline AND not defeated AND not canceled). The bypass-into-
    timelock side effect is not modeled; only the phase write. *)
Definition execute_optimistic (p : Proposal.t) (now : U256.t) : Result.t Proposal.t :=
  if negb p.(Proposal.isOptimistic) then revert_not_optimistic
  else
    match observe p now with
    | PhaseSucceeded =>
        Result.Success
          {|
            Proposal.pid              := p.(Proposal.pid);
            Proposal.proposer         := p.(Proposal.proposer);
            Proposal.voteStart        := p.(Proposal.voteStart);
            Proposal.voteDuration     := p.(Proposal.voteDuration);
            Proposal.vetoThresholdD18 := p.(Proposal.vetoThresholdD18);
            Proposal.againstVotes     := p.(Proposal.againstVotes);
            Proposal.phase            := PhaseExecuted;
            Proposal.isOptimistic     := p.(Proposal.isOptimistic);
            Proposal.parent           := p.(Proposal.parent);
            Proposal.pastSupply       := p.(Proposal.pastSupply);
          |}
    | _ => revert_wrong_phase
    end.

(** [cancel] — terminal-to-cancel transition. The contract permits
    cancellation from many phases (Pending, Active, etc.) modulo the
    _validateCancel rules; for the state machine we just block cancel
    from already-terminal Executed. *)
Definition cancel (p : Proposal.t) : Result.t Proposal.t :=
  match p.(Proposal.phase) with
  | PhaseExecuted    => revert_already_terminal
  | PhaseStdExecuted => revert_already_terminal
  | _ =>
      Result.Success
        {|
          Proposal.pid              := p.(Proposal.pid);
          Proposal.proposer         := p.(Proposal.proposer);
          Proposal.voteStart        := p.(Proposal.voteStart);
          Proposal.voteDuration     := p.(Proposal.voteDuration);
          Proposal.vetoThresholdD18 := p.(Proposal.vetoThresholdD18);
          Proposal.againstVotes     := p.(Proposal.againstVotes);
          Proposal.phase            := PhaseCanceled;
          Proposal.isOptimistic     := p.(Proposal.isOptimistic);
          Proposal.parent           := p.(Proposal.parent);
          Proposal.pastSupply       := p.(Proposal.pastSupply);
        |}
  end.

(** ===== Contract-faithful variants =====

    Adversarial review (G3, G4) found that the total [add_veto] and
    permissive [cancel] above accept inputs the contract refuses.
    Specifically:
      - Solidity [_castVote] is gated by [_validateStateBitmap(Active)]
        and [_countVote(Against only)] — votes only count on an
        Active proposal in the Against direction.
      - Solidity [_validateCancel] is gated by CANCELLER_ROLE OR
        (caller == proposer AND state-specific rule) — see
        ReserveOptimisticGovernor.sol:374-388.

    The two operations below add the missing preconditions. They are
    the contract-faithful entry points; the looser [add_veto] /
    [cancel] above remain for proofs that don't need the precondition
    (e.g. "after a successful add_veto, the state delta is X" — the
    proof's conclusion holds regardless of whether the precondition
    actually held at the call site).

    Audit notations should prefer the validated variants for any
    claim that asserts a state transition is REACHABLE on chain. *)

(** [add_veto_validated]: only mutates state if the proposal is
    Active. The Solidity [Active] state means [voteStart <= now <=
    voteStart + voteDuration] AND [phase == PhaseSubmitted] for
    optimistic OR [phase == PhaseStdActive] for standard. This
    simulation models phase only; the time check is the caller's
    responsibility via [now] passed in. *)
Definition add_veto_validated
    (p : Proposal.t) (now delta : U256.t) : Result.t Proposal.t :=
  (* Phase gate: only Active proposals accept votes. *)
  match p.(Proposal.phase) with
  | PhaseSubmitted
  | PhaseStdActive =>
      (* Time gate: now must be within the vote window. *)
      if (now <? p.(Proposal.voteStart)) then
        revert_inactive_phase
      else if (now >? p.(Proposal.voteStart) + p.(Proposal.voteDuration)) then
        revert_inactive_phase
      else
        Result.Success (add_veto p delta)
  | _ => revert_inactive_phase
  end.

(** [cancel_validated]: enforces the CANCELLER_ROLE OR proposer-with-
    state-specific-rule auth from [_validateCancel]. The simulation
    abstracts the role check via a [has_canceller_role] oracle bool
    and the proposer-equality check via [is_proposer] bool. *)
Definition cancel_validated
    (p : Proposal.t)
    (caller_has_canceller_role : bool)
    (caller_is_proposer : bool)
    : Result.t Proposal.t :=
  if caller_has_canceller_role then
    (* CANCELLER_ROLE can cancel anything that's not already terminal. *)
    cancel p
  else if negb caller_is_proposer then
    (* Neither admin nor proposer -> revert. *)
    revert_invalid_state
  else
    (* Proposer-cancel rule, per _validateCancel:
       - optimistic AND state != Defeated -> allow
       - !optimistic (standard) AND state == Pending -> allow
       The simulation maps state() roughly to phase; the contract's
       state() is computed from phase + time + supply + votes. We
       approximate with phase comparison.

       Note (Caveat-11, SV3): the optimistic branch allows the
       proposer to cancel a Succeeded proposal, which the
       attack-surface review flagged as a censorship vector. The
       behavior is here-as-on-chain; whether to tighten is a
       design call. See test/ProposerCancelSucceeded.t.sol. *)
    if p.(Proposal.isOptimistic) then
      (* state != Defeated -> phase != PhaseDefeated *)
      match p.(Proposal.phase) with
      | PhaseDefeated => revert_invalid_state
      | _ => cancel p
      end
    else
      (* Standard: only Pending allowed for proposer-cancel.
         PhaseStdPending is the standard-track Pending. *)
      match p.(Proposal.phase) with
      | PhaseStdPending => cancel p
      | _ => revert_invalid_state
      end.

(** ===== Throttle oracle =====

    The throttle interaction is modeled as the simplest possible
    surface: a counter that decrements per successful
    [propose_optimistic]. The detailed time-decay semantics live in
    [ProposerThrottle] and are out of scope here. *)
Definition consume_throttle_oracle (charges : U256.t) : Result.t U256.t :=
  if charges <? 1 then revert_throttle_exceeded
  else Result.Success (charges - 1).

(** ===== Validity ===== *)
Module Valid.
  Record proposal (p : Proposal.t) : Prop := {
    pid_u256          : U256.Valid.t p.(Proposal.pid);
    voteStart_u256    : U256.Valid.t p.(Proposal.voteStart);
    voteDuration_u256 : U256.Valid.t p.(Proposal.voteDuration);
    vtt_u256          : U256.Valid.t p.(Proposal.vetoThresholdD18);
    avotes_u256       : U256.Valid.t p.(Proposal.againstVotes);
    parent_u256       : U256.Valid.t p.(Proposal.parent);
    pastSupply_u256   : U256.Valid.t p.(Proposal.pastSupply);
  }.

  (** A "veto delta" coming in from an external caller is, on chain,
      a [uint256] — so it's non-negative and bounded. We surface
      the convention as a named predicate so downstream proofs can
      cite [Valid.delta d] rather than restating [0 <= d < 2^256]. *)
  Definition delta (d : U256.t) : Prop := U256.Valid.t d.
End Valid.

End Governor.
