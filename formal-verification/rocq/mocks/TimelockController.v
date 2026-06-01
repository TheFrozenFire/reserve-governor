(** OpenZeppelin TimelockController mock — abstract-base sim.

    Mirrors the surface of
      @openzeppelin/contracts/governance/TimelockController.sol (OZ v5.4.0).

    TimelockController is the abstract base that the Reserve corpus's
    [TimelockControllerOptimistic] extends. It encodes a 4-state
    operation queue ({Unset, Waiting, Ready, Done}) in a single
    [bytes32 => uint256] timestamps map using the OZ sentinel
    convention:

        _timestamps[id] = 0           <=> Unset
        _timestamps[id] = 1           <=> Done    (the magic _DONE_TIMESTAMP)
        _timestamps[id] > 1, > now    <=> Waiting
        _timestamps[id] > 1, <= now   <=> Ready

    The operation id is the keccak256 of the abi-encoded payload
    [(target, value, data, predecessor, salt)] (or the batch
    equivalent). For the purposes of this mock we keep the id opaque
    (parameter of type [OpId := U256.t]) and treat batch dispatch as
    a side-effect we don't model.

    Roles (inherited via AccessControl):

      PROPOSER_ROLE      = keccak256("PROPOSER_ROLE")
      EXECUTOR_ROLE      = keccak256("EXECUTOR_ROLE")
      CANCELLER_ROLE     = keccak256("CANCELLER_ROLE")
      DEFAULT_ADMIN_ROLE = 0x00... (inherited from AccessControl)

    EXECUTOR_ROLE additionally supports the "open role" pattern:
    [hasRole(EXECUTOR_ROLE, address(0)) == true] enables anyone to
    execute. We model this faithfully via [has_role_or_open].

    Operations modeled:

      - [getTimestamp s id]              -> uint256
      - [isOperation s id now]           -> bool
      - [isOperationPending s id now]    -> bool
      - [isOperationReady s id now]      -> bool
      - [isOperationDone s id now]       -> bool
      - [getOperationState s id now]     -> OperationState
      - [getMinDelay s]                  -> uint256
      - [hashOperation_pure ...]         -> opaque OpId
      - [hashOperationBatch_pure ...]    -> opaque OpId
      - [schedule s caller id delay now] -> Result.t State
                                            require PROPOSER_ROLE
                                            require !isOperation
                                            require delay >= minDelay
      - [scheduleBatch s caller id delay now]
                                         -> Result.t State (same semantics)
      - [execute s caller id pred now]   -> Result.t State
                                            require EXECUTOR_ROLE-or-open
                                            require Ready
                                            require pred=0 or pred Done
                                            sets timestamps[id] := 1
      - [executeBatch s caller id pred now]
                                         -> Result.t State (same semantics)
      - [cancel s caller id now]         -> Result.t State
                                            require CANCELLER_ROLE
                                            require Pending
                                            clears timestamps[id]
      - [updateDelay s caller self d]    -> Result.t State
                                            require caller = address(this)
                                            sets minDelay := d

    Revert coverage:
      - [revert_unauthorized]            caller missing required role.
      - [revert_op_state]                operation in wrong state.
      - [revert_insufficient_delay]      schedule with delay < minDelay.
      - [revert_unexecuted_predecessor]  execute with non-zero predecessor
                                          that is not Done.
      - [revert_unauthorized_caller]     updateDelay called by non-self.

    Not modeled here:
      - The actual keccak256 [hashOperation] derivation (treated as
        opaque / deterministic / injective via [hashOperation_pure]).
      - The actual call dispatch [target.call{value}(data)] inside
        [_execute] — modeled as an opaque side-effect.
      - Constructor role-grant scaffolding. Initial state is fully
        parameterized.
      - Event emission ([CallScheduled], [CallExecuted], [Cancelled],
        [MinDelayChange]).
      - ERC721Holder + ERC1155Holder mixins.
      - [_encodeStateBitmap] internal helper (used in revert
        construction; we surface the revert sentinel directly).

    Companion files:
      - [proofs/equivalence/TimelockControllerBase.v] — sim-level
        helper lemmas + Section-parameterized walker template,
        following the R072 abstract-base methodology.
      - [simulations/Timelock.v] — the existing concrete sim used
        by [proofs/equivalence/TimelockControllerOptimistic.v];
        narrower surface (no schedule-single, no updateDelay, no
        per-operation state-enum projection), but the same
        encoding convention. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.AccessControl.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Module TimelockController.

(** Address model — opaque [U256.t]; [zero_address = 0] is the OZ
    [address(0)] sentinel (used for the EXECUTOR open-role pattern). *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** Operation identifier — opaque [U256.t] standing in for the
    keccak256 digest produced by [hashOperation] / [hashOperationBatch].
    Distinct id values are treated as distinct operations (which
    matches keccak256's collision resistance for distinct inputs). *)
Definition OpId : Set := U256.t.

(** The OZ magic timestamp value marking Done. *)
Definition DONE_TIMESTAMP : U256.t := 1.

(** OZ role constants (opaque keccak256 hashes; values irrelevant
    to the sim semantics — equality comparisons are what matter). *)
Definition PROPOSER_ROLE  : AccessControl.Role := 1.
Definition EXECUTOR_ROLE  : AccessControl.Role := 2.
Definition CANCELLER_ROLE : AccessControl.Role := 3.
(* DEFAULT_ADMIN_ROLE = 0 is re-exported from AccessControl. *)

(** Operation status as observed by callers. Computed from the
    timestamps map, never stored separately. Mirrors the OZ
    [OperationState] enum: { Unset, Waiting, Ready, Done }. *)
Inductive OperationState : Set :=
| OpUnset
| OpWaiting
| OpReady
| OpDone.

(** Timestamps map: list of [(id, ts)] pairs. The contract uses a
    Solidity mapping; absence corresponds to ts = 0. *)
Definition TsMap : Set := list (OpId * U256.t).

(** The TimelockController contract storage projection.

    Layered on top of [AccessControl.State] — the abstract base
    inherits AccessControl for role gating. *)
Module State.
  Record t : Set := {
    (** [_timestamps] mapping. *)
    timestamps : TsMap;
    (** [_minDelay] uint256. *)
    minDelay   : U256.t;
    (** AccessControl substate (the [_roles] mapping inherited via
        OZ AccessControl). *)
    roles      : AccessControl.State;
  }.
End State.

(** Initial state: empty timestamps, given [minDelay], and a given
    AccessControl substate. The OZ constructor grants several role
    seeds; callers construct the initial role set as appropriate. *)
Definition init_state
    (minDelay : U256.t) (ac : AccessControl.State) : State.t :=
  {| State.timestamps := [];
     State.minDelay   := minDelay;
     State.roles      := ac;
  |}.

(** Two-constructor result, matching the pattern in
    [AccessControl.Result.t] and [simulations/Timelock.v]'s
    [Timelock.Result.t]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert  {_}.
End Result.

(** Revert sentinels — distinct (offset, size) pairs per error class
    so that revert-equality lemmas can distinguish them. *)
Definition revert_unauthorized            {A : Set} : Result.t A :=
  Result.Revert 0   32.
Definition revert_op_state                {A : Set} : Result.t A :=
  Result.Revert 32  32.
Definition revert_insufficient_delay      {A : Set} : Result.t A :=
  Result.Revert 64  32.
Definition revert_unexecuted_predecessor  {A : Set} : Result.t A :=
  Result.Revert 96  32.
Definition revert_unauthorized_caller     {A : Set} : Result.t A :=
  Result.Revert 128 32.

(** ---- Timestamps map helpers ----

    Use list-of-pairs with last-write-wins on duplicate keys; the
    Valid.t invariant rules out duplicates. *)

Fixpoint lookup_ts (m : TsMap) (id : OpId) : U256.t :=
  match m with
  | []             => 0
  | (k, v) :: rest => if k =? id then v else lookup_ts rest id
  end.

Fixpoint set_ts (m : TsMap) (id : OpId) (ts : U256.t) : TsMap :=
  match m with
  | []             => [(id, ts)]
  | (k, v) :: rest =>
      if k =? id
      then (k, ts) :: rest
      else (k, v) :: set_ts rest id ts
  end.

(** Read the timestamps map for a state. *)
Definition get_ts (s : State.t) (id : OpId) : U256.t :=
  lookup_ts s.(State.timestamps) id.

(** Write a fresh timestamp into the state. *)
Definition set_state_ts (s : State.t) (id : OpId) (ts : U256.t) : State.t :=
  {| State.timestamps := set_ts s.(State.timestamps) id ts;
     State.minDelay   := s.(State.minDelay);
     State.roles      := s.(State.roles);
  |}.

(** ---- View functions ---- *)

(** [getTimestamp(id)] — the OZ TimelockController.getTimestamp. *)
Definition getTimestamp (s : State.t) (id : OpId) : U256.t :=
  get_ts s id.

(** [getMinDelay()] — the OZ TimelockController.getMinDelay. *)
Definition getMinDelay (s : State.t) : U256.t := s.(State.minDelay).

(** [getOperationState(id)] — the OZ TimelockController.getOperationState.

    Faithful to OZ's getOperationState body:

        uint256 timestamp = getTimestamp(id);
        if (timestamp == 0)                     return OperationState.Unset;
        else if (timestamp == _DONE_TIMESTAMP)  return OperationState.Done;
        else if (timestamp >  block.timestamp)  return OperationState.Waiting;
        else                                    return OperationState.Ready; *)
Definition getOperationState
    (s : State.t) (id : OpId) (now : U256.t) : OperationState :=
  let ts := get_ts s id in
  if ts =? 0 then OpUnset
  else if ts =? DONE_TIMESTAMP then OpDone
  else if now <? ts then OpWaiting
  else OpReady.

(** [isOperation(id)] — true for any state other than Unset. *)
Definition isOperation (s : State.t) (id : OpId) (now : U256.t) : bool :=
  match getOperationState s id now with
  | OpUnset => false
  | _       => true
  end.

(** [isOperationPending(id)] — true for Waiting or Ready. *)
Definition isOperationPending
    (s : State.t) (id : OpId) (now : U256.t) : bool :=
  match getOperationState s id now with
  | OpWaiting | OpReady => true
  | _                   => false
  end.

(** [isOperationReady(id)] — true only for Ready. *)
Definition isOperationReady
    (s : State.t) (id : OpId) (now : U256.t) : bool :=
  match getOperationState s id now with
  | OpReady => true
  | _       => false
  end.

(** [isOperationDone(id)] — true only for Done. *)
Definition isOperationDone
    (s : State.t) (id : OpId) (now : U256.t) : bool :=
  match getOperationState s id now with
  | OpDone => true
  | _      => false
  end.

(** ---- hashOperation* (opaque placeholders) ----

    The OZ contract computes
      keccak256(abi.encode(target, value, data, predecessor, salt))
    for the single-op variant and the analogous batch hash for
    [hashOperationBatch]. The sim treats the digest as opaque:
    distinct (target, value, data, predecessor, salt) tuples MAY
    collide at the sim level even though they don't on-chain.

    For methodology purposes the sim operations take [OpId] directly,
    so these are documentation placeholders — not used by any
    mutator below. *)
Definition hashOperation_pure
    (target value_ data predecessor salt : U256.t) : OpId :=
  target + value_ + data + predecessor + salt.

Definition hashOperationBatch_pure
    (targets values payloads : list U256.t)
    (predecessor salt : U256.t) : OpId :=
  fold_right Z.add 0 targets
  + fold_right Z.add 0 values
  + fold_right Z.add 0 payloads
  + predecessor + salt.

(** ---- Role-gating helpers ----

    OZ's [onlyRole(R)] checks [hasRole(R, msg.sender)] and reverts
    AccessControlUnauthorizedAccount otherwise.

    OZ's [onlyRoleOrOpenRole(R)] additionally short-circuits when
    [hasRole(R, address(0))] is true (the "open role" pattern). *)

Definition has_role
    (s : State.t) (role : AccessControl.Role) (account : Address) : bool :=
  AccessControl.hasRole s.(State.roles) role account.

(** The open-role pattern: succeed if [account] has [role] OR
    [address(0)] has [role]. *)
Definition has_role_or_open
    (s : State.t) (role : AccessControl.Role) (account : Address) : bool :=
  orb (has_role s role account) (has_role s role zero_address).

(** ---- Internal _schedule (private in OZ) ----

    Body (from OZ source):

        function _schedule(bytes32 id, uint256 delay) private {
          if (isOperation(id)) revert TimelockUnexpectedOperationState;
          uint256 minDelay = getMinDelay();
          if (delay < minDelay) revert TimelockInsufficientDelay;
          _timestamps[id] = block.timestamp + delay;
        }

    Two revert arms (already-scheduled + insufficient-delay) + a
    timestamps write. *)
Definition _schedule
    (s : State.t) (id : OpId) (delay now : U256.t)
    : Result.t State.t :=
  if isOperation s id now then revert_op_state
  else if delay <? s.(State.minDelay) then revert_insufficient_delay
  else Result.Success (set_state_ts s id (now + delay)).

(** ---- Internal _afterCall (private in OZ) ----

    Body (from OZ source):

        function _afterCall(bytes32 id) private {
          if (!isOperationReady(id)) revert TimelockUnexpectedOperationState;
          _timestamps[id] = _DONE_TIMESTAMP;
        }

    Re-asserts Ready (reentrancy defense) then writes 1. *)
Definition _afterCall
    (s : State.t) (id : OpId) (now : U256.t)
    : Result.t State.t :=
  if isOperationReady s id now
  then Result.Success (set_state_ts s id DONE_TIMESTAMP)
  else revert_op_state.

(** ---- Public schedule / scheduleBatch ----

    OZ source:

        function schedule(
          address target,
          uint256 value,
          bytes calldata data,
          bytes32 predecessor,
          bytes32 salt,
          uint256 delay
        ) public virtual onlyRole(PROPOSER_ROLE) {
          bytes32 id = hashOperation(target, value, data, predecessor, salt);
          _schedule(id, delay);
          emit CallScheduled(...);
          if (salt != 0) emit CallSalt(id, salt);
        }

    The sim takes the (already-derived) [id] as an argument; the
    hashOperation step is opaque from the walker's perspective. *)
Definition schedule
    (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t)
    : Result.t State.t :=
  if negb (has_role s PROPOSER_ROLE caller) then revert_unauthorized
  else _schedule s id delay now.

Definition scheduleBatch
    (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t)
    : Result.t State.t :=
  (* Identical mutator-side semantics to [schedule]; the
     length-mismatch arm is a precondition predicate stated by the
     walker at the calldata level. *)
  schedule s caller id delay now.

(** ---- Public execute / executeBatch ----

    OZ source:

        function execute(
          address target, uint256 value, bytes calldata payload,
          bytes32 predecessor, bytes32 salt
        ) public payable virtual onlyRoleOrOpenRole(EXECUTOR_ROLE) {
          bytes32 id = hashOperation(target, value, payload, predecessor, salt);
          _beforeCall(id, predecessor);
          _execute(target, value, payload);
          emit CallExecuted(...);
          _afterCall(id);
        }

    _beforeCall:
      require isOperationReady(id)               -> revert TimelockUnexpectedOperationState
      if predecessor != 0:
        require isOperationDone(predecessor)     -> revert TimelockUnexecutedPredecessor

    The actual call dispatch is modeled as an opaque side-effect
    (the queue-state semantics are independent of dispatch success).
    _afterCall re-asserts Ready then writes _DONE_TIMESTAMP. *)
Definition execute
    (s : State.t) (caller : Address) (id : OpId) (predecessor : OpId)
    (now : U256.t)
    : Result.t State.t :=
  if negb (has_role_or_open s EXECUTOR_ROLE caller) then revert_unauthorized
  else if negb (isOperationReady s id now) then revert_op_state
  else if andb (negb (predecessor =? 0))
               (negb (isOperationDone s predecessor now))
       then revert_unexecuted_predecessor
  else
    (* _execute (opaque side-effect) then _afterCall.  Since the
       intermediate state is unchanged by the opaque dispatch
       (modeled as identity at the sim level) the composite reduces
       to [_afterCall].  _afterCall re-asserts Ready, which holds
       because we just confirmed it. *)
    _afterCall s id now.

Definition executeBatch
    (s : State.t) (caller : Address) (id : OpId) (predecessor : OpId)
    (now : U256.t)
    : Result.t State.t :=
  (* Identical mutator-side semantics to [execute]; the
     length-mismatch arm is a precondition predicate. *)
  execute s caller id predecessor now.

(** ---- Public cancel ----

    OZ source:

        function cancel(bytes32 id) public virtual onlyRole(CANCELLER_ROLE) {
          if (!isOperationPending(id)) revert TimelockUnexpectedOperationState;
          delete _timestamps[id];
          emit Cancelled(id);
        }

    Pending = Waiting or Ready. The [delete] writes ts = 0. *)
Definition cancel
    (s : State.t) (caller : Address) (id : OpId) (now : U256.t)
    : Result.t State.t :=
  if negb (has_role s CANCELLER_ROLE caller) then revert_unauthorized
  else if negb (isOperationPending s id now) then revert_op_state
  else Result.Success (set_state_ts s id 0).

(** ---- Public updateDelay ----

    OZ source:

        function updateDelay(uint256 newDelay) external virtual {
          address sender = _msgSender();
          if (sender != address(this)) revert TimelockUnauthorizedCaller(sender);
          emit MinDelayChange(_minDelay, newDelay);
          _minDelay = newDelay;
        }

    Self-call only — the timelock must execute a scheduled
    [updateDelay(newDelay)] call on itself. The sim takes [caller]
    and [self_address] as arguments. *)
Definition updateDelay
    (s : State.t) (caller : Address) (self_address : Address)
    (newDelay : U256.t)
    : Result.t State.t :=
  if negb (caller =? self_address) then revert_unauthorized_caller
  else
    Result.Success
      {| State.timestamps := s.(State.timestamps);
         State.minDelay   := newDelay;
         State.roles      := s.(State.roles);
      |}.

(** ---- Storage invariant ----

    The timestamps map can hold any combination of timestamps; the
    well-formedness condition is the same one [simulations/Timelock.v]
    documents: [DONE_TIMESTAMP = 1] does not collide with a scheduled
    timestamp in practice because scheduled values are large
    (block.timestamp + delay > 2^30 on any chain since 1970). We
    model this as a soft predicate [reasonable_ts]. *)
Module Valid.

  Definition reasonable_ts (ts : U256.t) : Prop :=
    ts = 0 \/ ts = DONE_TIMESTAMP \/ DONE_TIMESTAMP < ts.

  Definition entries_valid (m : TsMap) : Prop :=
    Forall (fun kv => reasonable_ts (snd kv)) m.

  Definition no_dup_ids (m : TsMap) : Prop :=
    NoDup (map fst m).

  Record state (s : State.t) : Prop := {
    minDelay_u256  : U256.Valid.t s.(State.minDelay);
    entries_ok     : entries_valid s.(State.timestamps);
    entries_no_dup : no_dup_ids   s.(State.timestamps);
    roles_ok       : AccessControl.Valid.state s.(State.roles);
  }.

End Valid.

End TimelockController.
