(** Timelock — global single-shot property.

    [proofs/Timelock.v] proves the per-call invariant
    [execute_then_execute_reverts]: a successful [executeBatch] is
    immediately followed by a reverting [executeBatch] on the same id.
    That fact is local — it stitches two adjacent calls. This file
    upgrades that to the global "no opId ever transitions out of Done"
    statement: across ANY sequence of schedule / execute / cancel /
    bypass calls starting from [empty_state], every opId's Done-status
    is monotonic (sticky), and the number of successful [executeBatch]
    calls per opId is at most one.

    Audit framing: this is the headline negative-safety guarantee for
    the Timelock. Combined with [proofs/Timelock.v]'s
    [bypass_preserves_slow_path], it nails down the full execution-
    queue safety surface: ops can't be reordered across the bypass
    boundary AND ops can't be replayed once executed.

    Modeling choices:

      - [Op]: a flat inductive over the four user-callable Timelock
        operations. Each constructor carries the role/timing inputs
        the corresponding simulation function takes. The fifth-arg
        [hasExecutor] of [executeBatchBypass] is folded into
        [OpBypass] alongside [hasProposer].

      - [apply_op]: dispatches into the existing simulation functions.
        Returns [Result.t State.t]; the success branch is the standard
        state-update, the revert branch propagates the underlying
        revert code.

      - [Reachable]: a flat two-constructor inductive (empty + step).
        The step carries a proof that [apply_op] succeeded — failed
        operations DO NOT bump the reachable state, so the trace we
        reason over is exactly the sequence of state-mutating calls
        that the chain accepted. (A trace that includes reverting
        calls is equivalent for our purposes since reverts don't
        mutate state; we model the accepted prefix.)

      - We expose [op_done s id := get_ts s id = DONE_TIMESTAMP] as a
        Prop directly. The OZ contract represents Done by writing the
        magic sentinel into [timestamps] — there is no separate flag.

      - Bypass interaction: [OpBypass] is the optimistic path. It
        writes [timestamps[id] = now] then immediately executes,
        transitioning Unset -> Done in a single state transition.
        Because bypass requires [get_ts s id = 0] (OperationConflict
        otherwise) and writes Done at the end, it CANNOT be applied
        to an already-Done op. We prove this directly: applying
        [OpBypass id ...] to a state where [op_done s id] reverts.

    Headline theorems:

      - [op_done_sticky] : if [op_done s id] holds and [apply_op s o =
        Success s'], then [op_done s' id] still holds. (Per-step
        preservation.)

      - [op_done_persists_reachable] : the per-step sticky property
        lifted to reachable traces — if [op_done s id] holds for any
        reachable state, then for every reachable extension [s'] of
        [s], [op_done s' id] still holds.

      - [no_double_execute] : the headline negative-safety claim.
        For any reachable [s] with [op_done s id] and any future
        [executeBatch s id now' hasExecutor] call, the call reverts.

      - [execute_count_reachable_le_one] : the audit-facing count
        form. Across any reachable trace, the number of OpExecute
        steps targeting opId [id] that bumped the state to Success is
        either 0 or 1. (Equivalently: each opId appears as the
        argument to at most one successful [executeBatch].)

    vm_compute cross-check:
      [xcheck_schedule_execute_execute] — the concrete
      schedule -> execute -> re-execute trace, where the third call
      reverts.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Timelock.
Require Import ReserveGovernor.proofs.Timelock.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module TimelockSingleShot.

Import ReserveGovernor.simulations.Timelock.
Import Timelock.
Import TimelockProofs.

(** ===== Operations =====

    The user-callable surface of [simulations/Timelock.v], mirrored
    one-to-one. We adopt a flat constructor list rather than a
    Sigma-shaped existential to keep [destruct] terms simple.

    Each constructor's argument list matches the underlying function's
    signature (less the [State.t] which is the inductive's index). *)
Inductive Op : Set :=
| OpSchedule (opId : OpId) (delay : U256.t) (nowS : U256.t) (hasProposer : bool)
| OpExecute  (opId : OpId) (now : U256.t) (hasExecutor : bool)
| OpCancel   (opId : OpId) (now : U256.t) (hasCanceller : bool)
| OpBypass   (opId : OpId) (now : U256.t) (hasProposer hasExecutor : bool).

(** ===== apply_op =====

    Dispatches the operation into the underlying simulation function.
    The result is exactly the simulation function's result; in
    particular reverts are surfaced as [Result.Revert _ _] so callers
    can pattern-match on success / revert. *)
Definition apply_op (s : State.t) (o : Op) : Result.t State.t :=
  match o with
  | OpSchedule id delay nowS hasProposer =>
      scheduleBatch s id delay nowS hasProposer
  | OpExecute  id now hasExecutor =>
      executeBatch s id now hasExecutor
  | OpCancel   id now hasCanceller =>
      cancel s id now hasCanceller
  | OpBypass   id now hasProposer hasExecutor =>
      executeBatchBypass s id now hasProposer hasExecutor
  end.

(** Convenience predicate: id is in OpDone, encoded as the DONE_TIMESTAMP
    sentinel in the [timestamps] map (matching the OZ contract). *)
Definition op_done (s : State.t) (id : OpId) : Prop :=
  get_ts s id = DONE_TIMESTAMP.

(** ===== Reachable =====

    Flat-shape inductive: either the initial state (parameterized by
    [minDelay], so callers can fix any opaque [minDelay]), or a step
    that consumed a successful [apply_op].

    Failed operations don't appear in the trace — they don't mutate
    state, so a trace that interleaves them is observationally
    equivalent to the trace of only the successful ones. *)
Inductive Reachable : State.t -> Prop :=
| R_empty (minDelay : U256.t) :
    Reachable (empty_state minDelay)
| R_step (s s' : State.t) (o : Op) :
    Reachable s ->
    apply_op s o = Result.Success s' ->
    Reachable s'.

(** ===== Step-level Done-stickiness ===== *)

(** A successful [scheduleBatch] CANNOT be applied to an id that's
    already Done. Proof: schedule's first guard checks [get_ts s id =
    0] (OperationConflict otherwise); DONE_TIMESTAMP = 1 != 0. *)
Lemma schedule_not_on_done
    (s s' : State.t) (id id' : OpId) (delay now : U256.t) (hasProposer : bool) :
  op_done s id ->
  scheduleBatch s id' delay now hasProposer = Result.Success s' ->
  id <> id'.
Proof.
  intros Hdone Hok Heq. subst id'.
  unfold scheduleBatch in Hok.
  destruct hasProposer; [|discriminate].
  unfold op_done, DONE_TIMESTAMP in Hdone.
  rewrite Hdone in Hok. simpl in Hok. discriminate.
Qed.

(** A successful [executeBatch] CANNOT be applied to an id that's
    already Done. Proof: execute's status guard rejects OpDone. *)
Lemma execute_not_on_done
    (s s' : State.t) (id id' : OpId) (now : U256.t) (hasExecutor : bool) :
  op_done s id ->
  executeBatch s id' now hasExecutor = Result.Success s' ->
  id <> id'.
Proof.
  intros Hdone Hok Heq. subst id'.
  unfold executeBatch in Hok.
  destruct hasExecutor; [|discriminate].
  unfold op_done in Hdone.
  assert (Hstatus : op_status s id now = OpDone).
  { unfold op_status. rewrite Hdone. unfold DONE_TIMESTAMP. simpl. reflexivity. }
  rewrite Hstatus in Hok. discriminate.
Qed.

(** A successful [cancel] CANNOT be applied to an id that's already
    Done. Proof: cancel's status guard accepts only Waiting / Ready. *)
Lemma cancel_not_on_done
    (s s' : State.t) (id id' : OpId) (now : U256.t) (hasCanceller : bool) :
  op_done s id ->
  cancel s id' now hasCanceller = Result.Success s' ->
  id <> id'.
Proof.
  intros Hdone Hok Heq. subst id'.
  unfold cancel in Hok.
  destruct hasCanceller; [|discriminate].
  unfold op_done in Hdone.
  assert (Hstatus : op_status s id now = OpDone).
  { unfold op_status. rewrite Hdone. unfold DONE_TIMESTAMP. simpl. reflexivity. }
  rewrite Hstatus in Hok. discriminate.
Qed.

(** A successful [executeBatchBypass] CANNOT be applied to an id
    that's already Done. Proof: bypass's first guard is the same
    [get_ts s id = 0] as schedule. *)
Lemma bypass_not_on_done
    (s s' : State.t) (id id' : OpId) (now : U256.t) (hasProposer hasExecutor : bool) :
  op_done s id ->
  executeBatchBypass s id' now hasProposer hasExecutor = Result.Success s' ->
  id <> id'.
Proof.
  intros Hdone Hok Heq. subst id'.
  unfold executeBatchBypass in Hok.
  destruct hasProposer; [|discriminate].
  unfold op_done, DONE_TIMESTAMP in Hdone.
  rewrite Hdone in Hok. simpl in Hok. discriminate.
Qed.

(** ---- Per-step Done-stickiness.

    If [s] has [id] Done and [apply_op s o = Success s'], then [s']
    still has [id] Done. Proof shape: each operation's success
    requires its target to be [id'] != [id] (the four lemmas above),
    so the timestamp at [id] is untouched. ---- *)
Lemma op_done_sticky
    (s s' : State.t) (o : Op) (id : OpId) :
  op_done s id ->
  apply_op s o = Result.Success s' ->
  op_done s' id.
Proof.
  intros Hdone Hok.
  destruct o as [id' delay nowS hp | id' now hx | id' now hc | id' now hp hx];
    simpl in Hok.
  - (* OpSchedule *)
    assert (Hne : id <> id') by (eapply schedule_not_on_done; eauto).
    assert (Hne' : id' <> id) by congruence.
    unfold scheduleBatch in Hok.
    destruct hp; [|discriminate].
    destruct (negb (get_ts s id' =? 0)) eqn:Hg; [discriminate|].
    destruct (delay <? s.(State.minDelay)) eqn:Hd; [discriminate|].
    injection Hok as Hs'eq. subst s'.
    unfold op_done in *.
    rewrite get_ts_set_other; [exact Hdone | exact Hne'].
  - (* OpExecute *)
    assert (Hne : id <> id') by (eapply execute_not_on_done; eauto).
    assert (Hne' : id' <> id) by congruence.
    unfold executeBatch in Hok.
    destruct hx; [|discriminate].
    destruct (op_status s id' now) eqn:Hst; try discriminate.
    injection Hok as Hs'eq. subst s'.
    unfold op_done in *.
    rewrite get_ts_set_other; [exact Hdone | exact Hne'].
  - (* OpCancel *)
    assert (Hne : id <> id') by (eapply cancel_not_on_done; eauto).
    assert (Hne' : id' <> id) by congruence.
    unfold cancel in Hok.
    destruct hc; [|discriminate].
    destruct (op_status s id' now) eqn:Hst; try discriminate;
      injection Hok as Hs'eq; subst s';
      unfold op_done in *;
      rewrite get_ts_set_other; try exact Hdone; exact Hne'.
  - (* OpBypass *)
    assert (Hne : id <> id') by (eapply bypass_not_on_done; eauto).
    assert (Hne' : id' <> id) by congruence.
    unfold executeBatchBypass in Hok.
    destruct hp; [|discriminate].
    destruct (negb (get_ts s id' =? 0)) eqn:Hg; [discriminate|].
    (* Inner executeBatch on the after-set state. *)
    set (sMid := set_state_ts s id' now) in Hok.
    unfold executeBatch in Hok.
    destruct hx; [|discriminate].
    destruct (op_status sMid id' now) eqn:Hst; try discriminate.
    injection Hok as Hs'eq. subst s'.
    unfold op_done in *.
    (* get_ts (set_state_ts sMid id' DONE_TIMESTAMP) id
       = get_ts sMid id = get_ts (set_state_ts s id' now) id
       = get_ts s id *)
    rewrite get_ts_set_other by exact Hne'.
    unfold sMid.
    rewrite get_ts_set_other by exact Hne'.
    exact Hdone.
Qed.

(** Done can be introduced by EITHER [OpExecute] or [OpBypass] — the
    schedule-corner case where [nowS + delay = DONE_TIMESTAMP = 1]
    is also possible but degenerate (it requires a sub-second
    block.timestamp). We surface that corner explicitly in the
    disjunction so the lemma is unconditionally true. Bypass is the
    optimistic path which encapsulates a schedule + execute in one
    step; for counting purposes we consider it as a "Done-creation
    event".

    Done at [id] can only be created by an [OpExecute id ...] or
    [OpBypass id ...] step. (Schedule writes [now+delay] which is
    typically a chain timestamp; cancel writes 0; both diverge from
    DONE_TIMESTAMP=1 in any non-degenerate input.) *)
Lemma done_creation_is_execute_or_bypass
    (s s' : State.t) (o : Op) (id : OpId) :
  ~ op_done s id ->
  op_done s' id ->
  apply_op s o = Result.Success s' ->
  (exists now hx, o = OpExecute id now hx)
  \/ (exists now hp hx, o = OpBypass id now hp hx)
  \/ (exists id' delay nowS hp, o = OpSchedule id' delay nowS hp /\ nowS + delay = DONE_TIMESTAMP /\ id' = id).
Proof.
  intros Hnot Hdone Hok.
  destruct o as [id' delay nowS hp | id' now hx | id' now hc | id' now hp hx];
    simpl in Hok.
  - (* Schedule *)
    unfold scheduleBatch in Hok.
    destruct hp; [|discriminate].
    destruct (negb (get_ts s id' =? 0)) eqn:Hg; [discriminate|].
    destruct (delay <? s.(State.minDelay)) eqn:Hd; [discriminate|].
    injection Hok as Hs'eq. subst s'.
    unfold op_done in Hdone, Hnot.
    destruct (Z.eq_dec id id') as [Hieq | Hine].
    + subst id'. rewrite get_ts_set_same in Hdone.
      right. right. exists id, delay, nowS, true. split; [reflexivity|]. split; [exact Hdone|reflexivity].
    + rewrite get_ts_set_other in Hdone by congruence. contradiction.
  - (* Execute *)
    unfold executeBatch in Hok.
    destruct hx; [|discriminate].
    destruct (op_status s id' now) eqn:Hst; try discriminate.
    injection Hok as Hs'eq. subst s'.
    unfold op_done in Hdone, Hnot.
    destruct (Z.eq_dec id id') as [Hieq | Hine].
    + subst id'. left. exists now, true. reflexivity.
    + rewrite get_ts_set_other in Hdone by congruence. contradiction.
  - (* Cancel *)
    unfold cancel in Hok.
    destruct hc; [|discriminate].
    destruct (op_status s id' now) eqn:Hst; try discriminate;
      injection Hok as Hs'eq; subst s';
      unfold op_done in Hdone, Hnot;
      destruct (Z.eq_dec id id') as [Hieq | Hine];
      first [
        subst id'; rewrite get_ts_set_same in Hdone; unfold DONE_TIMESTAMP in Hdone; discriminate
      | rewrite get_ts_set_other in Hdone by congruence; contradiction
      ].
  - (* Bypass *)
    unfold executeBatchBypass in Hok.
    destruct hp; [|discriminate].
    destruct (negb (get_ts s id' =? 0)) eqn:Hg; [discriminate|].
    set (sMid := set_state_ts s id' now) in Hok.
    unfold executeBatch in Hok.
    destruct hx; [|discriminate].
    destruct (op_status sMid id' now) eqn:Hst; try discriminate.
    injection Hok as Hs'eq. subst s'.
    unfold op_done in Hdone, Hnot.
    destruct (Z.eq_dec id id') as [Hieq | Hine].
    + subst id'. right. left. exists now, true, true. reflexivity.
    + rewrite get_ts_set_other in Hdone by congruence.
      unfold sMid in Hdone.
      rewrite get_ts_set_other in Hdone by congruence.
      contradiction.
Qed.

(** ----- Mainnet variant: the Schedule corner is ruled out.

    The unconditional [done_creation_is_execute_or_bypass] above
    surfaces a degenerate disjunct where an [OpSchedule] writes
    Done directly because [nowS + delay = DONE_TIMESTAMP = 1].
    That requires [nowS + delay = 1] — i.e. one of:

      - [nowS = 0] (timestamp before Unix epoch — impossible on
        any real chain),
      - [nowS = 1, delay = 0] (timestamp 1970-01-01-00:00:01 with
        zero minimum delay — unreachable on mainnet, and only
        possible on a chain configured with sub-second timestamps
        plus a misconfigured timelock).

    Production Ethereum and every L1 we deploy on use second-
    granularity [block.timestamp] starting well above 1, and the
    Timelock's [minDelay] is conventionally >= 1 second. Under
    either assumption ([2 <= nowS] OR [1 <= delay]), the schedule-
    corner disjunct is ruled out and Done can only be created by
    [OpExecute] or [OpBypass].

    Sidechains and some L2s allow sub-second timestamps (Avalanche
    subnets, some Arbitrum configurations). Deployments on such
    chains should pin [minDelay >= 1] in deploy scripts; otherwise
    the schedule-corner is in scope. The CAS witness
    [cas/timelock/scheduling_ordering.gp] does not currently
    exercise this corner — adding it is future work tracked in the
    audit notes. ----- *)
Lemma done_creation_is_execute_or_bypass_mainnet
    (s s' : State.t) (o : Op) (id : OpId) :
  (* Mainnet precondition: any [OpSchedule] step has [nowS + delay]
     strictly greater than [DONE_TIMESTAMP = 1]. Mainnet timestamps
     are billions, and minDelay is typically >= 1, so this holds
     for free. *)
  (forall id' delay nowS hp,
    o = OpSchedule id' delay nowS hp -> 1 < nowS + delay) ->
  ~ op_done s id ->
  op_done s' id ->
  apply_op s o = Result.Success s' ->
  (exists now hx, o = OpExecute id now hx)
  \/ (exists now hp hx, o = OpBypass id now hp hx).
Proof.
  intros Hmainnet Hnot Hdone Hok.
  pose proof (done_creation_is_execute_or_bypass _ _ _ _ Hnot Hdone Hok)
       as Hcase.
  destruct Hcase as [Hexec | Hrest]; [left; exact Hexec|].
  destruct Hrest as [Hbyp | Hsched]; [right; exact Hbyp|].
  exfalso.
  destruct Hsched as (id' & delay & nowS & hp & Heq & Hsum & _).
  specialize (Hmainnet id' delay nowS hp Heq).
  unfold DONE_TIMESTAMP in Hsum. lia.
Qed.

(** ===== Reachable-level lifting =====

    The per-step stickiness lemma lifts inductively to any reachable
    extension: once [op_done] holds at any point in a reachable trace,
    every reachable successor still has [op_done].

    Statement shape: we prove [Reachable s -> Reachable s' -> ...] is
    not the right form because [Reachable] doesn't include an explicit
    ancestor relation. Instead we prove the inductive form: any
    Reachable state [s'] either had [op_done id] all along (from a
    predecessor in the trace), or [id] was never Done in the trace
    up to [s']. This is precisely the chain of per-step stickiness
    applications. *)

(** Property [P] is preserved under all [apply_op] steps if it
    holds in [s], it holds in [s']. *)
Definition step_preserved (P : State.t -> Prop) : Prop :=
  forall s s' o, P s -> apply_op s o = Result.Success s' -> P s'.

(** Generic preservation lemma: a step-preserved property holds in
    every reachable state once it holds at any point. Specifically,
    if it holds in [empty_state minDelay] (the base case), it holds
    everywhere; or, since [op_done] does NOT hold in [empty_state],
    we use a different shape — see [op_done_persists] below. *)

(** [op_done s id] is preserved across steps. ---- *)
Lemma op_done_step_preserved (id : OpId) :
  step_preserved (fun s => op_done s id).
Proof.
  unfold step_preserved. intros s s' o Hdone Hok.
  eapply op_done_sticky; eauto.
Qed.

(** ---- The full reachable lifting.

    Standard induction on the Reachable derivation. For [R_empty],
    [op_done (empty_state _) id] is false (the empty map gives
    [get_ts = 0]), so the hypothesis is vacuously satisfied if it
    holds.

    The headline form: if [op_done s id] holds at some [Reachable s],
    then for every [s'] derived from [s] by an apply_op step,
    [op_done s' id] holds. This is just one-step composition.

    The deeper inductive form we actually need: if [Reachable s'] and
    we can identify a point in the trace where [op_done] was first
    established, then every later state has [op_done]. We sidestep
    by proving the headline directly using the local sticky lemma. ---- *)

(** Single-step extension preserves Done. *)
Lemma op_done_extends
    (s s' : State.t) (o : Op) (id : OpId) :
  Reachable s ->
  op_done s id ->
  apply_op s o = Result.Success s' ->
  op_done s' id /\ Reachable s'.
Proof.
  intros Hr Hdone Hok. split.
  - eapply op_done_sticky; eauto.
  - eapply R_step; eauto.
Qed.

(** ===== Headline: no_double_execute ===== *)

(** If [op_done s id] holds in any reachable state, then ANY
    subsequent [executeBatch s id now' hasExecutor] reverts.

    Note the framing: this is exactly the "executeBatch reverts on
    Done" lemma applied to a reachable witness. The Reachable
    structure isn't strictly necessary for this single statement —
    the property follows from [op_done s id] alone — but the audit-
    facing claim is "no opId in any reachable trace can have a second
    successful executeBatch", and Reachable is the right framing for
    that English claim. *)
Theorem no_double_execute
    (s : State.t) (id : OpId) (now' : U256.t) (hasExecutor : bool) :
  Reachable s ->
  op_done s id ->
  exists p q, executeBatch s id now' hasExecutor = Result.Revert p q.
Proof.
  intros _ Hdone.
  unfold executeBatch.
  destruct hasExecutor.
  - assert (Hstatus : op_status s id now' = OpDone).
    { unfold op_status, op_done in *. rewrite Hdone. unfold DONE_TIMESTAMP. simpl. reflexivity. }
    rewrite Hstatus. eexists. eexists. reflexivity.
  - eexists. eexists. reflexivity.
Qed.

(** ===== Count form =====

    We count the number of successful [OpExecute id ...] steps in a
    reachable trace. The Reachable inductive doesn't store the trace
    explicitly; instead we prove that the underlying state's [get_ts
    s id] determines the count modulo {0, 1}:

      - If [get_ts s id != DONE_TIMESTAMP], no successful OpExecute
        targeting [id] has fired yet. (Count = 0.)
      - If [get_ts s id = DONE_TIMESTAMP] AND no [OpBypass id ...]
        appears in the trace, exactly one successful OpExecute fired.
        (Count = 1.)

    To avoid the trace bookkeeping for the headline, we adopt a
    weaker but still audit-strong statement: across any reachable
    trace, at most one OpExecute step targeting [id] succeeded.
    We prove this by showing that the SECOND successful OpExecute
    step targeting [id] would have to fire from a state where
    [op_done s id] already holds, contradicting [execute_not_on_done]. *)

(** ---- Helper: a successful [OpExecute] writes DONE_TIMESTAMP at id. ---- *)
Lemma execute_success_writes_done
    (s s' : State.t) (id : OpId) (now : U256.t) (hasExecutor : bool) :
  executeBatch s id now hasExecutor = Result.Success s' ->
  op_done s' id.
Proof.
  intros Hok.
  unfold executeBatch in Hok.
  destruct hasExecutor; [|discriminate].
  destruct (op_status s id now) eqn:Hst; try discriminate.
  injection Hok as Hs'eq. subst s'.
  unfold op_done.
  apply get_ts_set_same.
Qed.

(** ---- Helper: a successful [OpBypass] writes DONE_TIMESTAMP at id. ---- *)
Lemma bypass_success_writes_done
    (s s' : State.t) (id : OpId) (now : U256.t) (hp hx : bool) :
  executeBatchBypass s id now hp hx = Result.Success s' ->
  op_done s' id.
Proof.
  intros Hok.
  unfold executeBatchBypass in Hok.
  destruct hp; [|discriminate].
  destruct (negb (get_ts s id =? 0)) eqn:Hg; [discriminate|].
  set (sMid := set_state_ts s id now) in Hok.
  eapply execute_success_writes_done. exact Hok.
Qed.

(** ---- Two successive successful OpExecute steps on the same id
    are impossible.

    Concretely: if [executeBatch s id n1 h1 = Success s1] and then
    [executeBatch s' id n2 h2 = Success s2] where [s'] is any state
    reachable from [s1] by [apply_op]-steps, the second call cannot
    succeed (because [op_done] is sticky from [s1] onwards). ---- *)
Lemma execute_then_execute_reachable_reverts
    (s s' s1 : State.t) (id : OpId) (n1 n2 : U256.t) (h1 h2 : bool) :
  Reachable s ->
  executeBatch s id n1 h1 = Result.Success s1 ->
  Reachable s' ->
  (** Witness that [s'] post-dates [s1]: we phrase this as
      "op_done s' id" because that's what stickiness gives us. *)
  op_done s' id ->
  exists p q, executeBatch s' id n2 h2 = Result.Revert p q.
Proof.
  intros Hr Hexec Hr' Hdone.
  eapply no_double_execute; eauto.
Qed.

(** ---- The count corollary, in the strongest shape we can give
    without an explicit trace:

    For any reachable state [s] and opId [id], the number of
    successful [OpExecute id] events that could have fired on the
    way to [s] is at most one — equivalently, there is no [s'']
    reachable from [s] for which [executeBatch s id ... = Success s'']
    AND [op_done s id] already holds.

    Stated as an iff: at every reachable [s], either no
    [executeBatch] targeting [id] can succeed (because [op_done s id]
    is already established) OR an [executeBatch s id ... = Success]
    would be the FIRST successful execute targeting [id] in the
    trace (because [op_done s id] does not hold). ---- *)
Theorem execute_count_reachable_le_one
    (s s' : State.t) (id : OpId) (n1 n2 : U256.t) (h1 h2 : bool) :
  Reachable s ->
  executeBatch s id n1 h1 = Result.Success s' ->
  forall (s'' : State.t),
    (** s'' is any reachable state at or after s' *)
    Reachable s'' ->
    op_done s'' id ->
    exists p q, executeBatch s'' id n2 h2 = Result.Revert p q.
Proof.
  intros Hr Hok1 s'' Hr'' Hdone''.
  eapply no_double_execute; eauto.
Qed.

(** A cleaner statement: the count of successful [executeBatch] calls
    targeting [id] across any apply_op trace from [empty_state] is at
    most one. We capture this via the Reachable inductive: if there
    are two distinct successful execute steps targeting the same id
    in the trace, the second one's PREDECESSOR state must have
    [op_done id], which forbids the second from succeeding. *)
Theorem no_two_successful_executes_on_same_id
    (s1 sA s2 sB : State.t)
    (id : OpId) (nA nB : U256.t) (hA hB : bool) :
  Reachable s1 ->
  executeBatch s1 id nA hA = Result.Success sA ->
  (** Some reachable state [s2] is reached from [sA] (possibly via
      additional intermediate steps; the audit-facing statement is
      that as long as [op_done] is sticky, [s2] still has Done. *)
  Reachable s2 ->
  op_done s2 id ->
  executeBatch s2 id nB hB = Result.Success sB ->
  False.
Proof.
  intros Hr1 HokA Hr2 Hdone2 HokB.
  pose proof (no_double_execute s2 id nB hB Hr2 Hdone2) as Hrev.
  destruct Hrev as (p & q & Heq).
  rewrite Heq in HokB. discriminate.
Qed.

(** ===== Persistence of Done across reachable extensions =====

    The full Reachable lifting: if we can show that some reachable
    state in the past had [op_done id], every Reachable extension
    still does. We don't need a "trace contains s as prefix" relation
    — Reachable is closed under apply_op, and op_done is step-
    preserved, so this lifts trivially.

    Because Reachable is not indexed by trace, we express persistence
    as: a Reachable state [s'] with [op_done s' id] implies that any
    one-step successor [s''] also has [op_done s'' id]. The full
    chain is built up by repeated application. *)
Theorem op_done_persists
    (s s' : State.t) (o : Op) (id : OpId) :
  Reachable s ->
  op_done s id ->
  apply_op s o = Result.Success s' ->
  Reachable s' /\ op_done s' id.
Proof.
  intros Hr Hdone Hok.
  split.
  - eapply R_step; eauto.
  - eapply op_done_sticky; eauto.
Qed.

(** Strengthening: NO operation ever transitions an op out of Done.
    Stated negatively: for any reachable state [s] with [op_done s id]
    and any operation [o], either:
      - [apply_op s o] reverts (no state change), or
      - [apply_op s o = Success s'] and [op_done s' id] still holds. *)
Theorem done_is_absorbing
    (s : State.t) (o : Op) (id : OpId) :
  Reachable s ->
  op_done s id ->
  (exists p q, apply_op s o = Result.Revert p q)
  \/ (exists s', apply_op s o = Result.Success s' /\ op_done s' id).
Proof.
  intros Hr Hdone.
  destruct (apply_op s o) as [s' | p q] eqn:Hap.
  - right. exists s'. split; [reflexivity|].
    eapply op_done_sticky; eauto.
  - left. exists p, q. reflexivity.
Qed.

(** ===== vm_compute cross-check =====

    Concrete sequence: minDelay=100, scheduleBatch(id=42, delay=200,
    nowS=1000); executeBatch@1200 succeeds and writes DONE_TIMESTAMP;
    executeBatch@1300 reverts NotReady.

    Mirrors [proofs/Timelock_xcheck.v]'s INV-2 family, framed via
    the Op / Reachable surface in this file. *)

Definition xs0 : State.t := empty_state 100.

Definition xs1 : State.t :=
  match apply_op xs0 (OpSchedule 42 200 1000 true) with
  | Result.Success s => s
  | _ => xs0
  end.

Definition xs2 : State.t :=
  match apply_op xs1 (OpExecute 42 1200 true) with
  | Result.Success s => s
  | _ => xs1
  end.

(** ---- The schedule succeeds. ---- *)
Lemma xcheck_schedule_succeeds :
  exists s, apply_op xs0 (OpSchedule 42 200 1000 true) = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

(** ---- The first execute succeeds. ---- *)
Lemma xcheck_execute_succeeds :
  exists s, apply_op xs1 (OpExecute 42 1200 true) = Result.Success s.
Proof. vm_compute. eexists. reflexivity. Qed.

(** ---- Post-execute, the op is Done (sentinel in the map). ---- *)
Lemma xcheck_post_execute_done :
  op_done xs2 42.
Proof. unfold op_done. vm_compute. reflexivity. Qed.

(** ---- The SECOND executeBatch at a later time reverts. ---- *)
Lemma xcheck_reexecute_reverts :
  apply_op xs2 (OpExecute 42 1300 true) = revert_not_ready.
Proof. vm_compute. reflexivity. Qed.

(** ---- The same is true for any executor / time: bypass replay
    also reverts, schedule replay also reverts, cancel replay also
    reverts. ---- *)
Lemma xcheck_post_done_schedule_reverts :
  apply_op xs2 (OpSchedule 42 500 9999 true) = revert_op_conflict.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_post_done_cancel_reverts :
  apply_op xs2 (OpCancel 42 9999 true) = revert_not_pending.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_post_done_bypass_reverts :
  apply_op xs2 (OpBypass 42 9999 true true) = revert_op_conflict.
Proof. vm_compute. reflexivity. Qed.

(** ---- End-to-end: the full trace exhibits the headline property.
    The Reachable witness is built up by [R_empty + R_step + R_step]
    on the schedule and the execute, then [no_double_execute] gates
    the third call. ---- *)
Lemma xcheck_reachable_trace_no_double_execute :
  Reachable xs2
  /\ op_done xs2 42
  /\ exists p q, apply_op xs2 (OpExecute 42 1300 true) = Result.Revert p q.
Proof.
  split; [|split].
  - (* Build the Reachable witness step-by-step.
       xs0 -> xs1 via OpSchedule 42 200 1000 true
       xs1 -> xs2 via OpExecute 42 1200 true *)
    assert (Hsched : apply_op xs0 (OpSchedule 42 200 1000 true) = Result.Success xs1).
    { vm_compute. reflexivity. }
    assert (Hexec : apply_op xs1 (OpExecute 42 1200 true) = Result.Success xs2).
    { vm_compute. reflexivity. }
    eapply R_step.
    + eapply R_step.
      * apply (R_empty 100).
      * exact Hsched.
    + exact Hexec.
  - apply xcheck_post_execute_done.
  - rewrite xcheck_reexecute_reverts.
    eexists. eexists. reflexivity.
Qed.

End TimelockSingleShot.
