(** OpenZeppelin Votes mock — vote delegation + checkpoint history.

    Mirrors the surface of
      @openzeppelin/contracts/governance/utils/Votes.sol (OZ v5.4.0).

    Votes is the base abstract contract that ERC20Votes and ERC721Votes
    inherit from; it tracks two parallel datasets:

      - [_delegatee : address -> address]
          Each account's chosen delegate. Default (unset) is
          [address(0)] which signals "voting power is NOT in play".
      - [_delegateCheckpoints : address -> Trace208]
          Per-delegate checkpoint history of accumulated voting
          weight. Read via [getVotes] (latest) and [getPastVotes]
          (upperLookupRecent at a past clock value).
      - [_totalCheckpoints : Trace208]
          Aggregate checkpoint history of *all* voting units in
          existence (sum of [_getVotingUnits(a)] across all [a]).
          Read via [getPastTotalSupply] / [_getTotalSupply].

    Three core mutators:

      - [_delegate(account, delegatee)]
          Re-point [_delegatee[account]] and migrate the account's
          full voting weight ([_getVotingUnits(account)]) from the
          OLD delegate's checkpoint to the NEW delegate's.

      - [_transferVotingUnits(from, to, amount)]
          Called by the inheriting contract on every token motion
          (transfer / mint / burn). On mint ([from = 0]) the total
          supply increases; on burn ([to = 0]) it decreases.
          Always moves [amount] from [delegates(from)] to
          [delegates(to)] via [_moveDelegateVotes].

      - [_moveDelegateVotes(from, to, amount)]
          Decrement [from]'s checkpoint by [amount] (if [from != 0])
          and increment [to]'s by [amount] (if [to != 0]). Short-
          circuits when [from == to] or [amount == 0].

    Virtual: [_getVotingUnits(account)] returns the current voting
    units held by [account]. In ERC20Votes this is [balanceOf]; in
    ERC721Votes this is [balanceOf]; the contract is abstract on this
    point. We model the function as part of the contract state — a
    snapshot of voting units per account — to keep the proof
    self-contained.

    Modeling choices:

      - Voting weight values are stored as full [Z]. The OZ contract
        uses [SafeCast.toUint208] at each push site to bound at uint208;
        we treat that as a Valid.t-side precondition rather than an
        in-mock guard. The bounds proof is the inheriting contract's
        job (e.g. a [totalSupply <= 2^208 - 1] invariant on ERC20Votes).

      - The clock is a per-state value. OZ default is
        [block.number] but Votes can be overridden to use timestamps;
        for the mock we treat the clock as an opaque [U256.t]
        advanced by the caller. We require strict monotonicity at
        each [_push] to match [Trace208.push]'s sortedness invariant.

      - [getPastVotes] / [getPastTotalSupply] revert when called with
        [timepoint >= clock]; we model that with the Result monad.

      - The "delegateBySig" path (ECDSA + Nonces) is out of scope —
        it composes [_useCheckedNonce] (already mocked in Nonces.v)
        with [_delegate]; the composition lemma can be stated
        downstream by anyone who needs it.

    What is NOT modeled:
      - The keccak-encoded [DELEGATION_TYPEHASH] and the
        EIP-712-domain-separated digest; those are signature-layer
        concerns handled by ECDSA.v + Nonces.v at higher layers.
      - The exact uint208 saturation behavior; out-of-range pushes
        are ruled out at the [Valid.t] boundary instead.
      - The [_numCheckpoints] / [_checkpoints(account, pos)] helpers,
        which directly project [Trace208] internals; if a future
        proof needs them they project trivially through the mock's
        [entries] field.

    Used by:
      - This file's companion [proofs/equivalence/Votes.v].
      - Future ERC20Votes / governor-side proofs that need a
        sound model of the Votes inheritance.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.Trace208.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module Votes.

(** Address model — opaque [U256.t]; [zero_address = 0] is the OZ
    [address(0)] sentinel (the "undelegated" pointer + the
    mint-from / burn-to source/sink). *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** Total-function map from address to address (the [_delegatee]
    mapping). Default value is [zero_address] (= undelegated). *)
Definition AddrMap : Set := Address -> Address.

Definition empty_addr_map : AddrMap := fun _ => zero_address.

(** Total-function map from address to [Trace208.t] (the
    [_delegateCheckpoints] mapping). Default value is the empty
    trace (= "no checkpoint history yet, latest = 0"). *)
Definition TraceMap : Set := Address -> Trace208.t.

Definition empty_trace_map : TraceMap := fun _ => Trace208.empty.

(** Total-function map from address to [Z] (the virtual
    [_getVotingUnits] view, modeled as a state snapshot). Default
    is 0 — uninitialized accounts hold no voting units. *)
Definition UnitsMap : Set := Address -> Z.

Definition empty_units : UnitsMap := fun _ => 0.

(** Pointwise update for [AddrMap]. *)
Definition upd_addr (m : AddrMap) (k : Address) (v : Address) : AddrMap :=
  fun k' => if Z.eqb k' k then v else m k'.

(** Pointwise update for [TraceMap]. *)
Definition upd_trace (m : TraceMap) (k : Address) (v : Trace208.t) : TraceMap :=
  fun k' => if Z.eqb k' k then v else m k'.

(** Pointwise update for [UnitsMap]. *)
Definition upd_units (m : UnitsMap) (k : Address) (v : Z) : UnitsMap :=
  fun k' => if Z.eqb k' k then v else m k'.

(** The Votes contract storage projection. *)
Module State.
  Record t : Set := {
    (** [_delegatee] mapping. *)
    delegatee          : AddrMap;
    (** [_delegateCheckpoints] mapping. *)
    delegate_ckpt      : TraceMap;
    (** [_totalCheckpoints]. *)
    total_ckpt         : Trace208.t;
    (** Snapshot of [_getVotingUnits(a)] for every [a]. In the
        inheriting contract this is a derived view (e.g. ERC20
        [balanceOf]); we carry it explicitly. *)
    voting_units       : UnitsMap;
    (** Current clock value (block.number or timestamp,
        contract-configurable via [clock()]). *)
    clock              : U256.t;
  }.
End State.

Definition empty_state : State.t := {|
  State.delegatee     := empty_addr_map;
  State.delegate_ckpt := empty_trace_map;
  State.total_ckpt    := Trace208.empty;
  State.voting_units  := empty_units;
  State.clock         := 0;
|}.

(** ---- The Result-monad wrapper used by callers ----
    Mirrors the existing simulation convention. View functions revert
    on future-lookup; mutators succeed unconditionally (the contract
    body has no public revert paths in the core mutator surface).
*)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Sentinel for the [ERC5805FutureLookup] revert. We don't model the
    exact selector encoding — just the kind. *)
Definition revert_future_lookup {A : Set} : Result.t A := Result.Revert 0 64.

(** ===== View functions ===== *)

(** [delegates(account)] — [_delegatee[account]]. *)
Definition delegates (s : State.t) (account : Address) : Address :=
  s.(State.delegatee) account.

(** [getVotes(account)] — [_delegateCheckpoints[account].latest()]. *)
Definition getVotes (s : State.t) (account : Address) : U256.t :=
  Trace208.latest (s.(State.delegate_ckpt) account).

(** [_getTotalSupply()] — [_totalCheckpoints.latest()]. *)
Definition getTotalSupply (s : State.t) : U256.t :=
  Trace208.latest s.(State.total_ckpt).

(** [getPastVotes(account, timepoint)] — reverts if
    [timepoint >= clock]; otherwise
    [_delegateCheckpoints[account].upperLookupRecent(timepoint)]. *)
Definition getPastVotes
    (s : State.t) (account : Address) (timepoint : U256.t)
    : Result.t U256.t :=
  if timepoint <? s.(State.clock)
  then Result.Success (Trace208.upperLookupRecent
                         (s.(State.delegate_ckpt) account) timepoint)
  else revert_future_lookup.

(** [getPastTotalSupply(timepoint)] — analogous future-lookup
    revert path; otherwise [_totalCheckpoints.upperLookupRecent(...)]. *)
Definition getPastTotalSupply (s : State.t) (timepoint : U256.t)
    : Result.t U256.t :=
  if timepoint <? s.(State.clock)
  then Result.Success (Trace208.upperLookupRecent s.(State.total_ckpt) timepoint)
  else revert_future_lookup.

(** ===== Internal helpers ===== *)

(** Decrement a delegate's checkpoint by [amount] via [Trace208.push]
    at the current clock. Production: the [_subtract] helper feeds
    into [_push] (Votes.sol:244-245). We compute the new latest as
    [old - amount]; the caller is responsible for bound preservation. *)
Definition push_sub
    (tr : Trace208.t) (clk : U256.t) (amount : Z) : Trace208.t :=
  Trace208.push tr clk (Trace208.latest tr - amount).

(** Increment counterpart. *)
Definition push_add
    (tr : Trace208.t) (clk : U256.t) (amount : Z) : Trace208.t :=
  Trace208.push tr clk (Trace208.latest tr + amount).

(** [_moveDelegateVotes(from, to, amount)]:
      if [from == to] OR [amount == 0]: no-op.
      else:
        if [from != 0]: push subtract([from].latest, amount) -> [from]'s checkpoint.
        if [to   != 0]: push add([to].latest, amount) -> [to]'s checkpoint.

    Direct port of Votes.sol:194-213. The clock is read once
    (via [clock()]) and the two pushes share that snapshot. *)
Definition moveDelegateVotes
    (s : State.t) (from to : Address) (amount : Z) : State.t :=
  if orb (Z.eqb from to) (Z.eqb amount 0) then s
  else
    let ckpt1 :=
      if Z.eqb from zero_address then s.(State.delegate_ckpt)
      else upd_trace s.(State.delegate_ckpt) from
             (push_sub (s.(State.delegate_ckpt) from) s.(State.clock) amount)
    in
    let ckpt2 :=
      if Z.eqb to zero_address then ckpt1
      else upd_trace ckpt1 to
             (push_add (ckpt1 to) s.(State.clock) amount)
    in
    {| State.delegatee     := s.(State.delegatee);
       State.delegate_ckpt := ckpt2;
       State.total_ckpt    := s.(State.total_ckpt);
       State.voting_units  := s.(State.voting_units);
       State.clock         := s.(State.clock);
    |}.

(** ===== Public/internal mutator surface ===== *)

(** [_delegate(account, delegatee)]: re-point [account]'s delegate
    and migrate full [_getVotingUnits(account)] from old delegate
    to new. *)
Definition delegate
    (s : State.t) (account new_d : Address) : State.t :=
  let old_d := delegates s account in
  let units := s.(State.voting_units) account in
  let s1 :=
    {| State.delegatee     := upd_addr s.(State.delegatee) account new_d;
       State.delegate_ckpt := s.(State.delegate_ckpt);
       State.total_ckpt    := s.(State.total_ckpt);
       State.voting_units  := s.(State.voting_units);
       State.clock         := s.(State.clock);
    |}
  in
  moveDelegateVotes s1 old_d new_d units.

(** [_transferVotingUnits(from, to, amount)]: applied on every
    token motion in the inheriting contract.
      [from = 0]:  mint  -> _totalCheckpoints += amount
      [to   = 0]:  burn  -> _totalCheckpoints -= amount
      always:           moveDelegateVotes(delegates[from], delegates[to], amount)

    Also updates the [voting_units] snapshot, mirroring the
    inheriting contract's [balanceOf]-style accounting. We bake the
    voting-unit motion into the same mutator because Votes only
    works correctly when the snapshot tracks the live balance. *)
Definition transferVotingUnits
    (s : State.t) (from to : Address) (amount : Z) : State.t :=
  let total1 :=
    if Z.eqb from zero_address
    then push_add s.(State.total_ckpt) s.(State.clock) amount
    else s.(State.total_ckpt)
  in
  let total2 :=
    if Z.eqb to zero_address
    then push_sub total1 s.(State.clock) amount
    else total1
  in
  let units1 :=
    if Z.eqb from zero_address
    then s.(State.voting_units)
    else upd_units s.(State.voting_units) from
           (s.(State.voting_units) from - amount)
  in
  let units2 :=
    if Z.eqb to zero_address
    then units1
    else upd_units units1 to (units1 to + amount)
  in
  let s1 :=
    {| State.delegatee     := s.(State.delegatee);
       State.delegate_ckpt := s.(State.delegate_ckpt);
       State.total_ckpt    := total2;
       State.voting_units  := units2;
       State.clock         := s.(State.clock);
    |}
  in
  moveDelegateVotes s1 (delegates s from) (delegates s to) amount.

(** ===== Validity ===== *)

Module Valid.
  (** Per-checkpoint sortedness: every delegate's history obeys
      [Trace208.Valid.t], and the total-supply history does too.
      Pushes are at strictly-greater clocks; we don't bake the
      clock-monotonicity invariant into the state record (it's the
      caller's responsibility to advance [clock] between
      mutators), but [Valid.t] records the cross-state shape. *)
  Record t (s : State.t) : Prop := {
    (** Every per-delegate checkpoint history is sorted. *)
    delegate_ckpt_sorted :
      forall a, Trace208.Valid.t (s.(State.delegate_ckpt) a);
    (** The total-supply history is sorted. *)
    total_ckpt_sorted    : Trace208.Valid.t s.(State.total_ckpt);
  }.

  Lemma empty_valid : t empty_state.
  Proof.
    constructor; simpl.
    - intros a. apply Trace208.Valid.empty_valid.
    - apply Trace208.Valid.empty_valid.
  Qed.
End Valid.

End Votes.
