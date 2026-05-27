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

(** ===== Proposal record =====

    The simulation tracks the minimal fields needed for the state
    machine: when voting opens, how long it lasts, the snapped
    threshold (in {tok}, i.e. already vetoThreshold*supply/1e18 with
    the Math.max(_, 1) snap applied), the running tally of veto
    votes, the current phase, and whether this is an optimistic or a
    standard proposal. [parent] is 0 for fresh proposals and equals
    the parent proposalId for confirmation children. *)
Module Proposal.
  Record t : Set := {
    pid               : U256.t;
    proposer          : Address;
    voteStart         : U256.t;   (** {seconds} *)
    voteDuration      : U256.t;   (** {seconds} *)
    vetoThresholdTok  : U256.t;   (** {tok}, post-Math.max snap *)
    againstVotes      : U256.t;   (** {tok} *)
    phase             : Phase;
    isOptimistic      : bool;
    parent            : U256.t;   (** 0 = no parent *)
  }.
End Proposal.

Definition fresh_optimistic
    (pid : U256.t) (proposer : Address)
    (voteStart voteDuration vetoThresholdTok : U256.t)
    : Proposal.t :=
  {|
    Proposal.pid               := pid;
    Proposal.proposer          := proposer;
    Proposal.voteStart         := voteStart;
    Proposal.voteDuration      := voteDuration;
    Proposal.vetoThresholdTok  := vetoThresholdTok;
    Proposal.againstVotes      := 0;
    Proposal.phase             := PhaseSubmitted;
    Proposal.isOptimistic      := true;
    Proposal.parent            := 0;
  |}.

Definition fresh_standard_child
    (parent_pid new_pid : U256.t) (proposer : Address)
    (voteStart voteDuration : U256.t)
    : Proposal.t :=
  {|
    Proposal.pid               := new_pid;
    Proposal.proposer          := proposer;
    Proposal.voteStart         := voteStart;
    Proposal.voteDuration      := voteDuration;
    Proposal.vetoThresholdTok  := 0;
    Proposal.againstVotes      := 0;
    Proposal.phase             := PhaseStdPending;
    Proposal.isOptimistic      := false;
    Proposal.parent            := parent_pid;
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

(** ===== Veto-threshold snap (Math.max(_, 1)) ===== *)
Definition vetoThresholdTokOf (vetoThresholdD18 pastSupply : U256.t) : U256.t :=
  let raw := (vetoThresholdD18 * pastSupply) / FIX_ONE in
  if raw <? 1 then 1 else raw.

(** ===== state() — observable proposal phase at [now] =====

    Mirrors ReserveOptimisticGovernor.state() for optimistic and
    standard tracks. The pre-deadline cases are derived from the
    stored fields; the post-deadline outcomes (executed, canceled,
    succeeded, queued, std_succeeded) are reflected by the [phase]
    field after they are written. *)
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
          (* Optimistic: veto-threshold check has precedence over
             deadline check. *)
          if p.(Proposal.againstVotes) >=? p.(Proposal.vetoThresholdTok)
          then PhaseDefeated
          else if now <? deadline then PhaseActive
          else PhaseSucceeded
        else
          if now <? deadline then PhaseStdActive
          else p.(Proposal.phase)  (* post-deadline outcome is stored *)
  end.

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
    let vtt := vetoThresholdTokOf vetoThresholdD18 pastSupply in
    Result.Success
      (fresh_optimistic pid proposer (now + vetoDelay) vetoPeriod vtt).

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
    Proposal.vetoThresholdTok  := p.(Proposal.vetoThresholdTok);
    Proposal.againstVotes      := p.(Proposal.againstVotes) + delta;
    Proposal.phase             := p.(Proposal.phase);
    Proposal.isOptimistic      := p.(Proposal.isOptimistic);
    Proposal.parent            := p.(Proposal.parent);
  |}.

(** [transition_to_pessimistic] — spawns a fresh standard child
    carrying the same calls. The parent's phase is marked Defeated
    (the contract sets vetoThreshold to UINT256_MAX which the state()
    view interprets as Defeated). The child is in PhaseStdPending. *)
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
          Proposal.vetoThresholdTok  := parent.(Proposal.vetoThresholdTok);
          Proposal.againstVotes      := parent.(Proposal.againstVotes);
          Proposal.phase             := PhaseDefeated;
          Proposal.isOptimistic      := parent.(Proposal.isOptimistic);
          Proposal.parent            := parent.(Proposal.parent);
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
        Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdSucceeded;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
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
        Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdQueued;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
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
        Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
        Proposal.againstVotes     := p.(Proposal.againstVotes);
        Proposal.phase            := PhaseStdExecuted;
        Proposal.isOptimistic     := p.(Proposal.isOptimistic);
        Proposal.parent           := p.(Proposal.parent);
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
            Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
            Proposal.againstVotes     := p.(Proposal.againstVotes);
            Proposal.phase            := PhaseExecuted;
            Proposal.isOptimistic     := p.(Proposal.isOptimistic);
            Proposal.parent           := p.(Proposal.parent);
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
          Proposal.vetoThresholdTok := p.(Proposal.vetoThresholdTok);
          Proposal.againstVotes     := p.(Proposal.againstVotes);
          Proposal.phase            := PhaseCanceled;
          Proposal.isOptimistic     := p.(Proposal.isOptimistic);
          Proposal.parent           := p.(Proposal.parent);
        |}
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
    vtt_u256          : U256.Valid.t p.(Proposal.vetoThresholdTok);
    avotes_u256       : U256.Valid.t p.(Proposal.againstVotes);
    parent_u256       : U256.Valid.t p.(Proposal.parent);
  }.
End Valid.

End Governor.
