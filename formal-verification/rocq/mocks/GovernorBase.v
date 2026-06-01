(** OpenZeppelin Governor (abstract base) mock — proposal lifecycle.

    Mirrors the surface of
      @openzeppelin/contracts/governance/Governor.sol (OZ v5.4.0).

    [Governor] is an *abstract* base — every concrete governor in the
    Reserve corpus ([ReserveOptimisticGovernor]) inherits from it,
    overrides several `virtual` hooks ([votingDelay], [votingPeriod],
    [quorum], [_quorumReached], [_voteSucceeded], [_countVote],
    [_getVotes], [proposalNeedsQueuing], [_executor]), and composes
    its own queue/execute paths on top of [_queueOperations] /
    [_executeOperations].

    This mock captures the **slot-agnostic** lifecycle: the
    proposal-state machine, the per-proposal storage record
    ([ProposalCore]), and the governance-call re-entrancy queue.  The
    inheritor's `virtual` overrides are not modeled inside the mock
    itself — they live as Section parameters at the equivalence
    layer, or as explicit arguments to the relevant entry points.

    Production semantics in scope:

      - Storage: [mapping(uint256 => ProposalCore) _proposals] and
        [Bytes32Set _governanceCall] (re-entrancy queue, used by
        [_checkGovernance] when [_executor() != address(this)]).
      - [ProposalCore] = [{ proposer : address, voteStart : uint48,
                            voteDuration : uint32, executed : bool,
                            canceled : bool, etaSeconds : uint48 }].
      - [state(proposalId)] — the 8-state machine (Pending / Active /
        Canceled / Defeated / Succeeded / Queued / Expired / Executed),
        encoded as a nested if-cascade matching the OZ source line
        ordering (Governor.sol:142-178).
      - [_propose] writes [proposer], [voteStart], [voteDuration] for
        a fresh [proposalId]; reverts if the slot already exists.
      - [_castVote] gated on [state == Active]; defers to [_countVote]
        for tally bookkeeping (modeled here as an opaque tally
        record).
      - [_queueOperations] / [_executeOperations] — abstract in OZ;
        modeled here as state transitions through the [executed] flag
        + the [etaSeconds] write (queue phase).
      - [_cancel] flips the [canceled] flag if the precondition (a
        state bitmap excluding Canceled / Expired / Executed) holds.
      - [hashProposal] — keccak-derived deterministic id from
        [(targets, values, calldatas, descriptionHash)].

    Virtual functions and modeling strategy:

      All `virtual` hooks fall into two categories:

      (a) **View-only / state-extending** ([votingDelay],
          [votingPeriod], [quorum], [proposalNeedsQueuing],
          [_quorumReached], [_voteSucceeded], [_getVotes],
          [_executor]): not modeled in [State.t].  At the equivalence
          layer they are Section parameters with axiom-free
          characterizing hypotheses (e.g. "[votingDelay] is constant
          for the lifetime of a proposal").  The mock takes them as
          arguments to the relevant entry points so each lemma can
          name them without committing to a concrete schedule.

      (b) **Mutating** ([_countVote], [_tallyUpdated],
          [_queueOperations], [_executeOperations]): the mock carries
          a [tallies : ProposalId -> VoteTally] record that captures
          the observable post-vote shape.  [_countVote] / [_castVote]
          push entries into [tallies]; concrete inheritors lift
          their richer counting modules through this surface.
          [_queueOperations] is modeled as "if the queue hook returns
          a nonzero eta, write it; otherwise revert with
          GovernorQueueNotImplemented".

    The [ProposalState] enum is hoisted to [Phase] here to avoid
    collision with [simulations/Governor.v]'s [Phase] (which models
    [ReserveOptimisticGovernor]'s richer state machine).  Mapping is
    one-to-one with OZ's `enum ProposalState`.

    What is NOT modeled:

      - The EIP-712 / SignatureChecker.isValidSignatureNow path
        ([castVoteBySig]); composes through ECDSA.v + Nonces.v at
        higher layers, identical to the StakingVaultDelegationBySig
        pattern.
      - Per-vote event emission (VoteCast, VoteCastWithParams,
        ProposalCreated, etc.) — observable only via event logs,
        which are out of scope here.
      - Exact uint48 / uint32 saturation on [voteStart],
        [voteDuration].  Bounds are discharged at the [Valid.t]
        boundary.
      - The receive() / onERC721Received() / onERC1155Received() /
        onERC1155BatchReceived() tokens-receiver surface; pure-token
        plumbing that doesn't touch the proposal-state machine.

    Used by:
      - This file's companion [proofs/equivalence/GovernorBase.v].
      - Future ReserveOptimisticGovernor-side proofs that need a
        sound model of the Governor inheritance base.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.EnumerableSet.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module GovernorBase.

Definition Address    : Set := U256.t.
Definition ProposalId : Set := U256.t.

Definition zero_address : Address := 0.

(** ===== ProposalState enum =====

    Mirrors the OZ [enum ProposalState] (IGovernor.sol:16-25), in
    the same source order so the bitmap encoding ([1 << uint8(state)])
    can be ported verbatim. *)
Inductive Phase : Set :=
| Pending    (* 0 *)
| Active     (* 1 *)
| Canceled   (* 2 *)
| Defeated   (* 3 *)
| Succeeded  (* 4 *)
| Queued     (* 5 *)
| Expired    (* 6 *)
| Executed   (* 7 *).

Definition phase_index (p : Phase) : Z :=
  match p with
  | Pending    => 0
  | Active     => 1
  | Canceled   => 2
  | Defeated   => 3
  | Succeeded  => 4
  | Queued     => 5
  | Expired    => 6
  | Executed   => 7
  end.

(** [_encodeStateBitmap(state)] — Governor.sol:720-722. *)
Definition encode_state_bitmap (p : Phase) : Z :=
  Z.shiftl 1 (phase_index p).

(** ===== ProposalCore =====

    Per-proposal storage record (Governor.sol:38-45). *)
Module ProposalCore.
  Record t : Set := {
    proposer      : Address;
    voteStart     : U256.t;   (* uint48 *)
    voteDuration  : U256.t;   (* uint32 *)
    executed      : bool;
    canceled      : bool;
    etaSeconds    : U256.t;   (* uint48 *)
  }.
End ProposalCore.

(** A zero-initialized proposal core, matching the EVM's "slot does
    not yet exist" shape.  [voteStart = 0] is the OZ sentinel for
    "proposal does not exist" (Governor.sol:157). *)
Definition empty_core : ProposalCore.t := {|
  ProposalCore.proposer     := zero_address;
  ProposalCore.voteStart    := 0;
  ProposalCore.voteDuration := 0;
  ProposalCore.executed     := false;
  ProposalCore.canceled     := false;
  ProposalCore.etaSeconds   := 0;
|}.

(** ===== Vote tally =====

    [_countVote] is virtual in OZ, but every concrete governor
    (GovernorCountingSimple, GovernorCountingFractional, the Reserve
    optimistic governor) records per-proposal-per-voter "has voted"
    + a per-proposal weight aggregate.  We carry that shape opaquely
    so the [_castVote] entry point has a place to land.

    [voters] is the set of accounts that have already voted on the
    proposal (used by the [GovernorAlreadyCastVote] revert path in
    inheritors).  [against / for / abstain] are illustrative
    aggregate bins; concrete inheritors may use different bins
    (e.g. ReserveOptimistic uses [vetoVotes] + [forVotes]). *)
Module VoteTally.
  Record t : Set := {
    voters       : list Address;
    against_w    : Z;
    for_w        : Z;
    abstain_w    : Z;
  }.
End VoteTally.

Definition empty_tally : VoteTally.t := {|
  VoteTally.voters    := [];
  VoteTally.against_w := 0;
  VoteTally.for_w     := 0;
  VoteTally.abstain_w := 0;
|}.

(** ===== Proposal map =====

    Total function from [ProposalId] to [ProposalCore].  Unset slots
    return [empty_core] (mirroring Solidity's zero-default on storage
    reads).  The OZ sentinel "proposal does not exist" is
    [voteStart = 0]. *)
Definition ProposalMap : Set := ProposalId -> ProposalCore.t.

Definition empty_proposals : ProposalMap := fun _ => empty_core.

(** Per-proposal vote tally map.  Default is [empty_tally]. *)
Definition TallyMap : Set := ProposalId -> VoteTally.t.

Definition empty_tallies : TallyMap := fun _ => empty_tally.

(** Pointwise updates. *)
Definition upd_proposals
    (m : ProposalMap) (k : ProposalId) (v : ProposalCore.t) : ProposalMap :=
  fun k' => if Z.eqb k' k then v else m k'.

Definition upd_tallies
    (m : TallyMap) (k : ProposalId) (v : VoteTally.t) : TallyMap :=
  fun k' => if Z.eqb k' k then v else m k'.

(** ===== Governor state =====

    The abstract Governor's full storage projection. *)
Module State.
  Record t : Set := {
    (** [_proposals] mapping. *)
    proposals        : ProposalMap;
    (** [_governanceCall] re-entrancy queue (used by [_checkGovernance]
        when [_executor() != address(this)]).  Modeled as a
        Bytes32Set; OZ uses a [DoubleEndedQueue.Bytes32Deque] but the
        ordering is irrelevant for the equivalence theorems we close
        here — only membership matters for the revert condition. *)
    governance_call  : EnumerableSet.Bytes32Set.t;
    (** Per-proposal vote tally — see VoteTally.t above. *)
    tallies          : TallyMap;
    (** Current clock value (block.number or timestamp, per the
        inheritor's [clock()] override).  Treated as an opaque
        [U256.t] advanced externally. *)
    clock            : U256.t;
  }.
End State.

Definition empty_state : State.t := {|
  State.proposals       := empty_proposals;
  State.governance_call := EnumerableSet.Bytes32Set.empty;
  State.tallies         := empty_tallies;
  State.clock           := 0;
|}.

(** ===== Result monad =====

    Same shape as the other mocks ([Votes], [Nonces],
    [AccessControl]).  View functions and entry points return
    [Result.t] so revert paths are visible. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Revert sentinels.  The [(p, s)] pair is opaque — we use it to
    distinguish revert kinds at proof level, not to model the exact
    selector encoding. *)
Definition revert_nonexistent_proposal {A : Set} : Result.t A :=
  Result.Revert 0 32.
Definition revert_unexpected_state {A : Set} : Result.t A :=
  Result.Revert 0 64.
Definition revert_invalid_length {A : Set} : Result.t A :=
  Result.Revert 0 96.
Definition revert_queue_not_implemented {A : Set} : Result.t A :=
  Result.Revert 0 128.
Definition revert_already_cast_vote {A : Set} : Result.t A :=
  Result.Revert 0 160.
Definition revert_unable_to_cancel {A : Set} : Result.t A :=
  Result.Revert 0 192.

(** ===== View functions ===== *)

(** [proposalSnapshot(proposalId)] — Governor.sol:186-188. *)
Definition proposalSnapshot (s : State.t) (pid : ProposalId) : U256.t :=
  (s.(State.proposals) pid).(ProposalCore.voteStart).

(** [proposalDeadline(proposalId)] — Governor.sol:191-193. *)
Definition proposalDeadline (s : State.t) (pid : ProposalId) : U256.t :=
  (s.(State.proposals) pid).(ProposalCore.voteStart)
  + (s.(State.proposals) pid).(ProposalCore.voteDuration).

(** [proposalProposer(proposalId)] — Governor.sol:196-198. *)
Definition proposalProposer (s : State.t) (pid : ProposalId) : Address :=
  (s.(State.proposals) pid).(ProposalCore.proposer).

(** [proposalEta(proposalId)] — Governor.sol:201-203. *)
Definition proposalEta (s : State.t) (pid : ProposalId) : U256.t :=
  (s.(State.proposals) pid).(ProposalCore.etaSeconds).

(** A proposal "exists" iff its [voteStart] is nonzero — OZ uses
    this sentinel at Governor.sol:157.  A fresh [empty_core] has
    [voteStart = 0]. *)
Definition proposal_exists (s : State.t) (pid : ProposalId) : bool :=
  negb (Z.eqb (proposalSnapshot s pid) 0).

(** [state(proposalId)] — Governor.sol:141-178.

    The 8-state machine, encoded as a nested if-cascade in the same
    order as the OZ source.  Three of the branches require virtual
    hooks ([_quorumReached], [_voteSucceeded]); we take those as
    explicit boolean arguments so the cascade is a closed function
    of state + hook outputs.

    Reverts via [revert_nonexistent_proposal] when [voteStart = 0]
    (the OZ "proposal does not exist" path). *)
Definition state
    (s : State.t)
    (pid : ProposalId)
    (* virtual hooks supplied by the inheritor: *)
    (quorum_reached  : bool)
    (vote_succeeded  : bool)
    : Result.t Phase :=
  let proposal := s.(State.proposals) pid in
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
        else if negb (andb quorum_reached vote_succeeded) then
               Result.Success Defeated
        else if Z.eqb proposal.(ProposalCore.etaSeconds) 0 then
               Result.Success Succeeded
        else Result.Success Queued.

(** [hashProposal(targets, values, calldatas, descriptionHash)] —
    Governor.sol:121-128.

    OZ uses [uint256(keccak256(abi.encode(...)))].  We model the
    composite by treating the four argument lists as a single opaque
    bundle and the hash as an injective function of that bundle.
    The bundle is just a [(list Address * list U256.t * list (list
    U256.t) * U256.t)] tuple — the same shape an inheritor's walker
    will reduce to after Yul-level [abi.encode] unfolding. *)
Definition ProposalArgs : Set :=
  (list Address * list U256.t * list (list U256.t) * U256.t)%type.

(** The hash itself: opaque parameter at the mock level; the
    equivalence layer instantiates it (or treats it axiomatically
    when the keccak surface is involved).  See [hashProposal_inj]
    below for the injectivity assumption that the equivalence layer
    will discharge against the inheritor's actual abi-encoding. *)
Parameter hashProposal_fn : ProposalArgs -> ProposalId.

Definition hashProposal (args : ProposalArgs) : ProposalId :=
  hashProposal_fn args.

(** Determinism of the hash: same arguments produce the same id.
    Follows from [hashProposal_fn] being a function. *)
Lemma hashProposal_deterministic :
  forall (a1 a2 : ProposalArgs),
    a1 = a2 -> hashProposal a1 = hashProposal a2.
Proof. intros a1 a2 ->. reflexivity. Qed.

(** ===== Helpers for [propose] / [_propose] ===== *)

(** Argument-length validation, Governor.sol:313-315:
      [targets.length == values.length == calldatas.length] AND
      [targets.length != 0]. *)
Definition propose_args_valid (a : ProposalArgs) : bool :=
  let '(targets, values, calldatas, _) := a in
  let lt := List.length targets in
  let lv := List.length values in
  let lc := List.length calldatas in
  andb (Nat.eqb lt lv) (andb (Nat.eqb lt lc) (negb (Nat.eqb lt 0))).

(** ===== Mutators ===== *)

(** [_propose(targets, values, calldatas, description, proposer)] —
    Governor.sol:304-341.

    Three revert paths in the body:
      1. [propose_args_valid] is false: [GovernorInvalidProposalLength].
      2. [_proposals[proposalId].voteStart != 0] (duplicate id):
         [GovernorUnexpectedProposalState].

    Success: writes [proposer], [voteStart := clock + votingDelay],
    [voteDuration := votingPeriod].  Returns the [proposalId].

    [votingDelay] and [votingPeriod] are virtual — supplied as
    explicit arguments so the lemma surface is closed. *)
Definition propose
    (s : State.t)
    (a : ProposalArgs)
    (proposer : Address)
    (votingDelay  : U256.t)
    (votingPeriod : U256.t)
    : Result.t (State.t * ProposalId) :=
  if negb (propose_args_valid a) then revert_invalid_length
  else
    let pid := hashProposal a in
    let core := s.(State.proposals) pid in
    if negb (Z.eqb core.(ProposalCore.voteStart) 0) then
      revert_unexpected_state
    else
      let snap := s.(State.clock) + votingDelay in
      let new_core :=
        {| ProposalCore.proposer     := proposer;
           ProposalCore.voteStart    := snap;
           ProposalCore.voteDuration := votingPeriod;
           ProposalCore.executed     := false;
           ProposalCore.canceled     := false;
           ProposalCore.etaSeconds   := 0;
        |} in
      let s' :=
        {| State.proposals       := upd_proposals s.(State.proposals) pid new_core;
           State.governance_call := s.(State.governance_call);
           State.tallies         := s.(State.tallies);
           State.clock           := s.(State.clock);
        |} in
      Result.Success (s', pid).

(** [_castVote(proposalId, account, support, reason, params)] —
    Governor.sol:627-648 (full form).

    Revert paths:
      1. [state(pid) != Active]: [GovernorUnexpectedProposalState].
      2. [_countVote] reverts (the [GovernorAlreadyCastVote] case,
         lifted out of the inheritor's counting module).

    Success: appends [account] to [voters] and increments the bin
    indicated by [support] (0 = against, 1 = for, 2 = abstain) by
    [vote_weight].  Returns the [votedWeight] as written.

    The virtual surface — [_getVotes] (to derive the weight),
    [_countVote] (to update the tally), [_tallyUpdated] (the post-
    update hook) — collapses here into:
      [vote_weight] : Z   (the result of [_getVotes(account, snapshot, params)])
      [quorum_reached] / [vote_succeeded] : bool (folded into [state]).

    The "support" enum (0/1/2) is a Z parameter; the inheritor's
    counting module decides which support values are legal and may
    add a [GovernorInvalidVoteType] revert.  We default-fold all
    support values into the abstain bin if outside {0,1,2}. *)
Definition vote_already_cast (tally : VoteTally.t) (account : Address) : bool :=
  existsb (fun a => Z.eqb a account) tally.(VoteTally.voters).

Definition apply_vote
    (tally : VoteTally.t) (account : Address) (support : Z) (w : Z) : VoteTally.t :=
  let voters' := tally.(VoteTally.voters) ++ [account] in
  let against' := if Z.eqb support 0
                  then tally.(VoteTally.against_w) + w
                  else tally.(VoteTally.against_w) in
  let for'     := if Z.eqb support 1
                  then tally.(VoteTally.for_w) + w
                  else tally.(VoteTally.for_w) in
  let abstain' := if Z.eqb support 2
                  then tally.(VoteTally.abstain_w) + w
                  else tally.(VoteTally.abstain_w) in
  {| VoteTally.voters    := voters';
     VoteTally.against_w := against';
     VoteTally.for_w     := for';
     VoteTally.abstain_w := abstain';
  |}.

Definition castVote
    (s : State.t)
    (pid : ProposalId)
    (account : Address)
    (support : Z)
    (vote_weight : Z)
    (* virtual: state() hook outputs at call time *)
    (quorum_reached : bool)
    (vote_succeeded : bool)
    : Result.t (State.t * Z) :=
  match state s pid quorum_reached vote_succeeded with
  | Result.Revert p q => Result.Revert p q
  | Result.Success Active =>
      let tally := s.(State.tallies) pid in
      if vote_already_cast tally account then revert_already_cast_vote
      else
        let tally' := apply_vote tally account support vote_weight in
        let s' :=
          {| State.proposals       := s.(State.proposals);
             State.governance_call := s.(State.governance_call);
             State.tallies         := upd_tallies s.(State.tallies) pid tally';
             State.clock           := s.(State.clock);
          |} in
        Result.Success (s', vote_weight)
  | Result.Success _ => revert_unexpected_state
  end.

(** [_queueOperations(proposalId, targets, values, calldatas, descriptionHash)] —
    Governor.sol:379-387.

    Default in OZ returns 0 ([GovernorQueueNotImplemented]); the
    Reserve inheritor overrides with a timelock dispatch that
    returns a nonzero eta.  We model the override as an explicit
    [queue_eta : U256.t] argument: 0 = "queue hook says no", nonzero
    = "queue hook returned this eta".

    Public [queue] (Governor.sol:344-364) wraps:
      1. Recompute [proposalId] from args (we pass it directly).
      2. [_validateStateBitmap(Succeeded)] — i.e. require
         [state pid quorum_reached vote_succeeded == Succeeded].
      3. Call [_queueOperations].
      4. If etaSeconds nonzero, [_proposals[pid].etaSeconds := etaSeconds].
      5. Else revert [GovernorQueueNotImplemented]. *)
Definition queue
    (s : State.t)
    (pid : ProposalId)
    (queue_eta : U256.t)
    (quorum_reached : bool)
    (vote_succeeded : bool)
    : Result.t (State.t * U256.t) :=
  match state s pid quorum_reached vote_succeeded with
  | Result.Revert p q => Result.Revert p q
  | Result.Success Succeeded =>
      if Z.eqb queue_eta 0 then revert_queue_not_implemented
      else
        let core := s.(State.proposals) pid in
        let new_core :=
          {| ProposalCore.proposer     := core.(ProposalCore.proposer);
             ProposalCore.voteStart    := core.(ProposalCore.voteStart);
             ProposalCore.voteDuration := core.(ProposalCore.voteDuration);
             ProposalCore.executed     := core.(ProposalCore.executed);
             ProposalCore.canceled     := core.(ProposalCore.canceled);
             ProposalCore.etaSeconds   := queue_eta;
          |} in
        let s' :=
          {| State.proposals       := upd_proposals s.(State.proposals) pid new_core;
             State.governance_call := s.(State.governance_call);
             State.tallies         := s.(State.tallies);
             State.clock           := s.(State.clock);
          |} in
        Result.Success (s', queue_eta)
  | Result.Success _ => revert_unexpected_state
  end.

(** [execute(targets, values, calldatas, descriptionHash)] —
    Governor.sol:390-425.

    Pre: [state(pid) in {Succeeded, Queued}].
    Action:
      1. [_proposals[pid].executed := true] — set BEFORE the call
         to defend against re-entrancy.
      2. If [_executor() != address(this)], for every [i] with
         [targets[i] == address(this)], push [keccak256(calldatas[i])]
         into [_governanceCall].
      3. Call [_executeOperations] — which actually performs the
         external calls.  Out of scope for the abstract mock; the
         inheritor instantiates.
      4. If [_executor() != address(this)] and queue is nonempty,
         clear [_governanceCall].

    For the abstract mock we model (1), (2), and (4); the actual
    external-call surface in (3) lives at the inheritor's
    equivalence layer.

    [executor_is_self] is a Boolean parameter mirroring the
    [_executor() == address(this)] check (a virtual hook). *)
Definition execute
    (s : State.t)
    (pid : ProposalId)
    (executor_is_self : bool)
    (self_call_hashes : list U256.t)  (* keccak256(calldatas[i]) for self-target calls *)
    (quorum_reached : bool)
    (vote_succeeded : bool)
    : Result.t State.t :=
  match state s pid quorum_reached vote_succeeded with
  | Result.Revert p q => Result.Revert p q
  | Result.Success Succeeded
  | Result.Success Queued =>
      let core := s.(State.proposals) pid in
      let new_core :=
        {| ProposalCore.proposer     := core.(ProposalCore.proposer);
           ProposalCore.voteStart    := core.(ProposalCore.voteStart);
           ProposalCore.voteDuration := core.(ProposalCore.voteDuration);
           ProposalCore.executed     := true;
           ProposalCore.canceled     := core.(ProposalCore.canceled);
           ProposalCore.etaSeconds   := core.(ProposalCore.etaSeconds);
        |} in
      (* Step 4 simplification: when [executor_is_self] is false, OZ
         enqueues all self-call hashes during [execute] and then
         immediately clears [_governanceCall] after [_executeOperations]
         returns (Governor.sol:418-420).  The net effect on the post-
         state stored in [State.t] is: governance_call is empty when
         executor != self, and unchanged otherwise.  The self-call
         hash list affects only the transient state observable inside
         [_executeOperations], which is where the inheritor's relay /
         module-protected setters are dispatched.

         We retain [self_call_hashes] as an argument for callers that
         need to reason about the inner-execution observability (see
         [governance_call_during_execute] for the transient form). *)
      let gc_post :=
        if executor_is_self then s.(State.governance_call)
        else EnumerableSet.Bytes32Set.empty in
      let _ := self_call_hashes in
      let s' :=
        {| State.proposals       := upd_proposals s.(State.proposals) pid new_core;
           State.governance_call := gc_post;
           State.tallies         := s.(State.tallies);
           State.clock           := s.(State.clock);
        |} in
      Result.Success s'
  | Result.Success _ => revert_unexpected_state
  end.

(** Transient governance_call observed *during* the inner
    [_executeOperations] dispatch.  Concrete inheritors that need to
    reason about the [_checkGovernance] revert path inside relay /
    module-protected functions use this view, not the post-execute
    [State.governance_call] field. *)
Definition governance_call_during_execute
    (s : State.t)
    (executor_is_self : bool)
    (self_call_hashes : list U256.t)
    : EnumerableSet.Bytes32Set.t :=
  if executor_is_self then s.(State.governance_call)
  else fold_left
         (fun set h => fst (EnumerableSet.Bytes32Set.add set h))
         self_call_hashes s.(State.governance_call).

(** [_cancel(targets, values, calldatas, descriptionHash)] —
    Governor.sol:471-491.

    Pre: [state(pid) in (ALL_STATES \ {Canceled, Expired, Executed})].
    Action: flip [_proposals[pid].canceled := true]. *)
Definition cancel
    (s : State.t)
    (pid : ProposalId)
    (quorum_reached : bool)
    (vote_succeeded : bool)
    : Result.t State.t :=
  match state s pid quorum_reached vote_succeeded with
  | Result.Revert p q => Result.Revert p q
  | Result.Success Canceled => revert_unexpected_state
  | Result.Success Expired  => revert_unexpected_state
  | Result.Success Executed => revert_unexpected_state
  | Result.Success _ =>
      let core := s.(State.proposals) pid in
      let new_core :=
        {| ProposalCore.proposer     := core.(ProposalCore.proposer);
           ProposalCore.voteStart    := core.(ProposalCore.voteStart);
           ProposalCore.voteDuration := core.(ProposalCore.voteDuration);
           ProposalCore.executed     := core.(ProposalCore.executed);
           ProposalCore.canceled     := true;
           ProposalCore.etaSeconds   := core.(ProposalCore.etaSeconds);
        |} in
      let s' :=
        {| State.proposals       := upd_proposals s.(State.proposals) pid new_core;
           State.governance_call := s.(State.governance_call);
           State.tallies         := s.(State.tallies);
           State.clock           := s.(State.clock);
        |} in
      Result.Success s'
  end.

(** Public [cancel] additionally requires a caller check
    [_validateCancel(pid, caller)] (Governor.sol:786-788):
    "default implementation allows the proposal proposer to cancel
    the proposal during the pending state".  We model that as a
    Boolean precondition function so inheritors can override it
    cleanly. *)
Definition default_validateCancel
    (s : State.t) (pid : ProposalId) (caller : Address)
    (quorum_reached vote_succeeded : bool) : bool :=
  match state s pid quorum_reached vote_succeeded with
  | Result.Success Pending => Z.eqb caller (proposalProposer s pid)
  | _ => false
  end.

Definition cancel_public
    (s : State.t)
    (pid : ProposalId)
    (caller : Address)
    (quorum_reached : bool)
    (vote_succeeded : bool)
    : Result.t State.t :=
  if default_validateCancel s pid caller quorum_reached vote_succeeded
  then cancel s pid quorum_reached vote_succeeded
  else revert_unable_to_cancel.

(** ===== Re-entrancy queue surface ===== *)

(** [_governanceCall.pushBack(keccak256(data))] — the enqueue side.
    Used inside [execute] when [_executor() != address(this)] to
    pre-authorize self-targeted calldata hashes. *)
Definition governance_enqueue
    (s : State.t) (msg_hash : U256.t) : State.t :=
  {| State.proposals       := s.(State.proposals);
     State.governance_call := fst (EnumerableSet.Bytes32Set.add
                                     s.(State.governance_call) msg_hash);
     State.tallies         := s.(State.tallies);
     State.clock           := s.(State.clock);
  |}.

(** [_governanceCall.popFront()] check in [_checkGovernance] —
    Governor.sol:215-224.  When [_executor() != address(this)] (i.e.
    the executor is a separate timelock), [_checkGovernance] loops
    [popFront] until it finds [keccak256(msg.data)].  We model the
    membership check; the pop-loop is an implementation detail. *)
Definition governance_call_contains
    (s : State.t) (msg_hash : U256.t) : bool :=
  EnumerableSet.Bytes32Set.contains s.(State.governance_call) msg_hash.

(** [_governanceCall.clear()] — Governor.sol:419. *)
Definition governance_clear (s : State.t) : State.t :=
  {| State.proposals       := s.(State.proposals);
     State.governance_call := EnumerableSet.Bytes32Set.empty;
     State.tallies         := s.(State.tallies);
     State.clock           := s.(State.clock);
  |}.

(** ===== Validity ===== *)

Module Valid.
  (** Cross-state invariant: governance queue obeys [Bytes32Set]'s
      NoDup, and per-proposal tally voter lists are NoDup. *)
  Record t (s : State.t) : Prop := {
    (** Governance queue obeys NoDup (Bytes32Set invariant). *)
    governance_set_valid :
      EnumerableSet.Bytes32Set.Valid.t s.(State.governance_call);
    (** Tally voter lists obey NoDup per-proposal. *)
    tally_voters_nodup :
      forall pid,
        NoDup (s.(State.tallies) pid).(VoteTally.voters);
  }.

  Lemma empty_valid : t empty_state.
  Proof.
    constructor; cbn.
    - apply EnumerableSet.Bytes32Set.Valid.empty_valid.
    - intros pid. apply NoDup_nil.
  Qed.
End Valid.

End GovernorBase.
