(** Timelock simulation.

    Mirrors contracts/governance/TimelockControllerOptimistic.sol — an
    OZ-derived timelock with two execution paths:

      1. Standard schedule / execute (inherited from
         TimelockControllerUpgradeable): the proposer calls
         [scheduleBatch] which records [now + delay] as the operation's
         [executableAt]; once the chain time reaches that, an executor
         can call [executeBatch] to dispatch the calls and mark the
         operation Done.

      2. Optimistic bypass: [executeBatchBypass] short-circuits the
         delay for an Unset operation, requiring PROPOSER_ROLE and
         EXECUTOR_ROLE. It writes [executableAt = now] then immediately
         dispatches, transitioning Unset -> Done in one transaction.

    The OZ contract encodes the four-state OperationState enum
    {Unset, Waiting, Ready, Done} in a single mapping
    [timestamps : id -> uint256] with the convention:

        timestamps[id] = 0      <=> Unset
        timestamps[id] = 1      <=> Done    (the magic _DONE_TIMESTAMP)
        timestamps[id] > 1, > now      <=> Waiting
        timestamps[id] > 1, <= now     <=> Ready

    Here we expose the [OpStatus] view as a derived function from the
    timestamps map, faithfully reproducing the OZ encoding.

    The operation id is the [hashOperationBatch] digest of (targets,
    values, payloads, predecessor, salt) — a keccak256 over abi.encode.
    For the purposes of this simulation we keep the id opaque
    (parameter of type [OpId := U256.t]) and treat batch dispatch as a
    side-effect we don't model. The on-chain semantics that matter for
    the queue ordering and bypass-vs-slow-path properties are entirely
    captured by the operation-status state machine.

    Operation set (with caller-side role gating modeled as booleans):

      [scheduleBatch s id delay now hasProposer]
                                  — only PROPOSER_ROLE; requires Unset;
                                    requires delay >= minDelay; writes
                                    timestamps[id] = now + delay.
      [executeBatch s id now hasExecutor]
                                  — only EXECUTOR_ROLE; requires Ready;
                                    writes timestamps[id] = 1.
      [cancel s id now hasCanceller]
                                  — only CANCELLER_ROLE; requires
                                    Pending (Waiting or Ready); clears
                                    timestamps[id] = 0.
      [executeBatchBypass s id now hasProposer hasExecutor]
                                  — only PROPOSER_ROLE; requires Unset
                                    (OperationConflict otherwise);
                                    sets timestamps[id] = now then
                                    immediately runs executeBatch which
                                    marks it Done. Inner exec needs
                                    EXECUTOR_ROLE.

    Revert coverage:
      - [revert_unauthorized]      caller missing the required role.
      - [revert_op_conflict]       scheduleBatch / bypass on an op
                                   already in the map.
      - [revert_insufficient_delay] scheduleBatch with delay below
                                   minDelay.
      - [revert_not_ready]         executeBatch on a non-Ready op.
      - [revert_not_pending]       cancel on an Unset or Done op.

    Not modeled here:
      - The keccak256 op-id derivation (treated as opaque /
        deterministic / injective).
      - The actual call dispatch (target.call{value}(data)) — modeled
        as an opaque side-effect, independent of the queue state.
      - The optional predecessor chaining (the contract requires the
        predecessor to be Done before _beforeCall succeeds). We model
        a single op in isolation; multi-op predecessor relations are
        out of scope for the headline bypass / queue-ordering
        properties.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module Timelock.

(** Address model — opaque U256.t. *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** Operation identifier — opaque U256.t standing in for the
    keccak256 digest. The simulation treats distinct id values as
    distinct operations (which matches keccak256's collision
    resistance for distinct inputs). *)
Definition OpId : Set := U256.t.

(** The OZ magic timestamp value marking Done. *)
Definition DONE_TIMESTAMP : U256.t := 1.

(** Operation status as observed by callers. Computed from the
    timestamps map, never stored separately. *)
Inductive OpStatus : Set :=
| OpUnset
| OpWaiting
| OpReady
| OpDone.

(** Timestamps map: list of [(id, ts)] pairs. The contract uses a
    Solidity mapping; absence corresponds to ts = 0. *)
Definition TsMap : Set := list (OpId * U256.t).

Module State.
  Record t : Set := {
    timestamps : TsMap;
    minDelay   : U256.t;
  }.
End State.

Definition empty_state (minDelay : U256.t) : State.t := {|
  State.timestamps := [];
  State.minDelay   := minDelay;
|}.

(** Two-constructor result, matching the pattern in
    [UnstakingManager.Result.t]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_unauthorized        {A : Set} : Result.t A := Result.Revert 0 32.
Definition revert_op_conflict         {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_insufficient_delay  {A : Set} : Result.t A := Result.Revert 64 32.
Definition revert_not_ready           {A : Set} : Result.t A := Result.Revert 96 32.
Definition revert_not_pending         {A : Set} : Result.t A := Result.Revert 128 32.

(** ---- map helpers ---- *)

Fixpoint lookup_ts (m : TsMap) (id : OpId) : U256.t :=
  match m with
  | [] => 0
  | (k, v) :: rest => if k =? id then v else lookup_ts rest id
  end.

Fixpoint set_ts (m : TsMap) (id : OpId) (ts : U256.t) : TsMap :=
  match m with
  | [] => [(id, ts)]
  | (k, v) :: rest =>
      if k =? id
      then (k, ts) :: rest
      else (k, v) :: set_ts rest id ts
  end.

(** Read the timestamps map for a state. *)
Definition get_ts (s : State.t) (id : OpId) : U256.t :=
  lookup_ts s.(State.timestamps) id.

(** Compute the OpStatus from a stored timestamp at chain time [now].

    Faithful to the OZ enum encoding:
      ts = 0  -> Unset
      ts = 1  -> Done
      ts > 1, > now -> Waiting
      ts > 1, <= now -> Ready

    Because [DONE_TIMESTAMP = 1] is below any plausible
    [block.timestamp + delay], this is unambiguous in real flows. *)
Definition op_status (s : State.t) (id : OpId) (now : U256.t) : OpStatus :=
  let ts := get_ts s id in
  if ts =? 0 then OpUnset
  else if ts =? DONE_TIMESTAMP then OpDone
  else if ts <=? now then OpReady
  else OpWaiting.

(** Write a fresh timestamp into the state. *)
Definition set_state_ts (s : State.t) (id : OpId) (ts : U256.t) : State.t :=
  {| State.timestamps := set_ts s.(State.timestamps) id ts;
     State.minDelay   := s.(State.minDelay) |}.

(** ---- operations ---- *)

(** [scheduleBatch] — only PROPOSER_ROLE. Schedules the operation
    with executableAt = now + delay; rejects if already scheduled
    (OperationConflict) or if delay < minDelay. *)
Definition scheduleBatch
    (s : State.t) (id : OpId) (delay now : U256.t) (hasProposer : bool)
    : Result.t State.t :=
  if negb hasProposer then revert_unauthorized
  else if negb (get_ts s id =? 0) then revert_op_conflict
  else if delay <? s.(State.minDelay) then revert_insufficient_delay
  else Result.Success (set_state_ts s id (now + delay)).

(** [executeBatch] — only EXECUTOR_ROLE. Requires the operation to
    be Ready (matured but not yet Done). Marks it Done by writing
    [DONE_TIMESTAMP = 1]. *)
Definition executeBatch
    (s : State.t) (id : OpId) (now : U256.t) (hasExecutor : bool)
    : Result.t State.t :=
  if negb hasExecutor then revert_unauthorized
  else match op_status s id now with
       | OpReady => Result.Success (set_state_ts s id DONE_TIMESTAMP)
       | _ => revert_not_ready
       end.

(** [cancel] — only CANCELLER_ROLE. Requires the operation to be
    pending (Waiting or Ready). Clears the timestamp, returning the
    op to Unset. *)
Definition cancel
    (s : State.t) (id : OpId) (now : U256.t) (hasCanceller : bool)
    : Result.t State.t :=
  if negb hasCanceller then revert_unauthorized
  else match op_status s id now with
       | OpWaiting | OpReady => Result.Success (set_state_ts s id 0)
       | _ => revert_not_pending
       end.

(** [executeBatchBypass] — only PROPOSER_ROLE (and the inner
    [executeBatch] needs EXECUTOR_ROLE). Requires the op to be Unset
    (OperationConflict otherwise). Writes timestamps[id] = now, then
    immediately invokes [executeBatch]. Net effect: Unset -> Done. *)
Definition executeBatchBypass
    (s : State.t) (id : OpId) (now : U256.t)
    (hasProposer hasExecutor : bool) : Result.t State.t :=
  if negb hasProposer then revert_unauthorized
  else if negb (get_ts s id =? 0) then revert_op_conflict
  else
    let s' := set_state_ts s id now in
    executeBatch s' id now hasExecutor.

(** Storage invariants. The timestamps map can hold any combination
    of timestamps; the well-formedness condition is just that
    [DONE_TIMESTAMP = 1] does not collide with a scheduled timestamp
    in practice (i.e. scheduled values are large because they include
    block.timestamp + delay, and block.timestamp >> 1 on every real
    chain since 1970).

    We model this as a soft predicate [reasonable_ts]: every
    non-zero, non-Done timestamp must exceed [DONE_TIMESTAMP]. This
    matches the OZ contract's safety reasoning: the magic value 1
    cannot be produced by [now + delay] for any plausible chain
    time. *)
Module Valid.

  Definition reasonable_ts (ts : U256.t) : Prop :=
    ts = 0 \/ ts = DONE_TIMESTAMP \/ DONE_TIMESTAMP < ts.

  Definition entries_valid (m : TsMap) : Prop :=
    Forall (fun kv => reasonable_ts (snd kv)) m.

  Record state (s : State.t) : Prop := {
    minDelay_u256 : U256.Valid.t s.(State.minDelay);
    entries_ok    : entries_valid s.(State.timestamps);
  }.

End Valid.

End Timelock.
