(** Task #243 — OpenZeppelin TimelockController equivalence methodology stub.

    [TimelockController] (OZ v5.4.0, governance/TimelockController.sol)
    is an *abstract*-style base: although it can be deployed standalone,
    in the Reserve corpus it is consumed via inheritance by
    [TimelockControllerOptimistic] (upgradeable variant), which fixes
    the storage layout via the EIP-7201 namespaced anchor for
    [TimelockControllerStorage] (the [$._timestamps] / [$._minDelay]
    pair). The shallow-form Yul translation of each public method
    lands inside the inheritor's shallow form, with the timestamps map
    keyed at [keccak256(<id>, slot_timestamps)] and the minDelay at
    [slot_minDelay].

    There is therefore no standalone [TimelockController_shallow.v]
    from solc; the established methodology for abstract bases (R072)
    applies. This file delivers:

      1. A set of sim-level helper lemmas about [mocks/TimelockController.v]
         — the pure-Coq facts every inheritor's walker proof will
         reuse ([Qed], no axioms beyond what the mock already imports).

      2. A documented walker-template surface — for each public
         TimelockController operation, what the Yul body's walker arms
         look like, parameterized over slot indices and a projection
         lens.

      3. A skeletal [Section TimelockControllerBaseEquivalenceTemplate]
         showing how downstream inheritors instantiate the methodology
         when the corresponding shallow form lands.

    Methodology decision (Option 2 per R072):
    -----------------------------------------
    Slot-agnostic helpers parameterized over slot indices, mirroring
    the abstract-base pattern in [proofs/equivalence/Votes.v],
    [proofs/equivalence/Nonces.v], [proofs/equivalence/EnumerableSet.v],
    and [proofs/equivalence/Checkpoints.v]. Inheritors instantiate by
    supplying their own [proj_sim] and slot indices; the sim-level
    helper lemmas below close once and are reused.

    What this file does NOT do:
    ---------------------------
    - It does not bind any Yul function to the sim.  No
      [TimelockController_shallow.v] from solc exists to bind against.
    - It does not duplicate the existing
      [proofs/equivalence/TimelockControllerOptimistic.v] proofs:
      those are concrete-inheritor walker theorems against the
      narrower [simulations/Timelock.v] sim. They remain valid; this
      file gives them (and any future inheritor) a reusable sim-level
      layer to lift onto.
    - It does not add new framework axioms.  Every closed lemma is
      [Qed] against [mocks/TimelockController.v] and the foundation
      tier.

    Cross-references:
    -----------------
    - [mocks/TimelockController.v] for the sim model.
    - [mocks/AccessControl.v] for the role-gating substrate the
      mock layers on top of.
    - [simulations/Timelock.v] for the narrower concrete sim used by
      [proofs/equivalence/TimelockControllerOptimistic.v].
    - WISDOM.md R072 (abstract-base methodology) and R073
      (this file's specific timestamp-sentinel-encoding decisions). *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.mocks.AccessControl.
Require Import ReserveGovernor.mocks.TimelockController.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module TimelockControllerBaseEquivalence.

  Import TimelockController.

  (** ============================================================
      Section 1 — Sim-level helper lemmas (Qed)

      These are pure-Coq properties of [TimelockController.schedule] /
      [execute] / [cancel] / [updateDelay] / [getOperationState] / the
      isOperation* family.  Every concrete inheritor walker proof will
      reuse them as post-state predicates; closing them here means the
      inheritor instantiation does not have to re-derive sim-side facts.

      Convention: each lemma states an *invariant* of the mutator —
      what stays the same across the operation, or how the observable
      view-function output transforms.  Walker proofs combine these
      with the inheritor's projection lens to assemble the milestone
      Hoare triple.
      ============================================================ *)

  (** ---- 1.1  [get_ts] / [set_state_ts] basic algebra ----

      [set_ts] inserts or overwrites the entry for [id]; subsequent
      [lookup_ts] returns the freshly-written value.  Independent of
      duplicates the mock's Valid.t will rule out. *)
  Lemma lookup_set_ts_same :
    forall (m : TsMap) (id : OpId) (ts : U256.t),
      lookup_ts (set_ts m id ts) id = ts.
  Proof.
    intros m id ts.
    induction m as [|[k v] rest IH]; simpl.
    - rewrite Z.eqb_refl. reflexivity.
    - destruct (k =? id) eqn:Hk; simpl.
      + rewrite Hk. reflexivity.
      + rewrite Hk. exact IH.
  Qed.

  Lemma lookup_set_ts_other :
    forall (m : TsMap) (id id' : OpId) (ts : U256.t),
      id <> id' ->
      lookup_ts (set_ts m id ts) id' = lookup_ts m id'.
  Proof.
    intros m id id' ts Hne.
    induction m as [|[k v] rest IH]; simpl.
    - assert (Hid : (id =? id') = false)
        by (apply Z.eqb_neq; exact Hne).
      rewrite Hid. reflexivity.
    - destruct (k =? id) eqn:Hkid; simpl.
      + apply Z.eqb_eq in Hkid. subst k.
        destruct (id =? id') eqn:Hid; simpl.
        * apply Z.eqb_eq in Hid. contradiction.
        * reflexivity.
      + destruct (k =? id') eqn:Hkid'; simpl.
        * reflexivity.
        * exact IH.
  Qed.

  Lemma get_set_state_ts_same :
    forall (s : State.t) (id : OpId) (ts : U256.t),
      get_ts (set_state_ts s id ts) id = ts.
  Proof.
    intros s id ts. unfold get_ts, set_state_ts. simpl.
    apply lookup_set_ts_same.
  Qed.

  Lemma get_set_state_ts_other :
    forall (s : State.t) (id id' : OpId) (ts : U256.t),
      id <> id' ->
      get_ts (set_state_ts s id ts) id' = get_ts s id'.
  Proof.
    intros s id id' ts Hne. unfold get_ts, set_state_ts. simpl.
    apply lookup_set_ts_other. exact Hne.
  Qed.

  (** ---- 1.2  [set_state_ts] preserves unrelated fields ----

      The timestamps write only touches [State.timestamps].  The
      [minDelay] and [roles] substates are preserved. *)
  Lemma set_state_ts_preserves_minDelay :
    forall (s : State.t) (id : OpId) (ts : U256.t),
      (set_state_ts s id ts).(State.minDelay) = s.(State.minDelay).
  Proof. intros. reflexivity. Qed.

  Lemma set_state_ts_preserves_roles :
    forall (s : State.t) (id : OpId) (ts : U256.t),
      (set_state_ts s id ts).(State.roles) = s.(State.roles).
  Proof. intros. reflexivity. Qed.

  (** ---- 1.3  [getOperationState] case-split unfold ----

      The 4-state enum projection from a single uint256 is the
      cornerstone of the OZ encoding.  This lemma is the definitional
      unfolding, lifted to a Qed so walker proofs can cite it without
      re-unfolding the local boolean cascade.

      Cases follow the OZ source order: Unset / Done / Waiting / Ready. *)
  Lemma getOperationState_unfold :
    forall (s : State.t) (id : OpId) (now : U256.t),
      getOperationState s id now
      = (let ts := get_ts s id in
         if ts =? 0 then OpUnset
         else if ts =? DONE_TIMESTAMP then OpDone
         else if now <? ts then OpWaiting
         else OpReady).
  Proof. intros. reflexivity. Qed.

  (** ---- 1.4  [getOperationState] from raw timestamp ----

      The state is fully determined by the [get_ts] result and [now];
      lifted as a Qed to factor out the common case-split walker
      proofs will perform. *)
  Lemma getOperationState_zero :
    forall (s : State.t) (id : OpId) (now : U256.t),
      get_ts s id = 0 ->
      getOperationState s id now = OpUnset.
  Proof.
    intros s id now Hzero. unfold getOperationState. rewrite Hzero.
    cbn. reflexivity.
  Qed.

  Lemma getOperationState_done :
    forall (s : State.t) (id : OpId) (now : U256.t),
      get_ts s id = DONE_TIMESTAMP ->
      getOperationState s id now = OpDone.
  Proof.
    intros s id now Hdone. unfold getOperationState. rewrite Hdone.
    cbn. reflexivity.
  Qed.

  Lemma getOperationState_waiting :
    forall (s : State.t) (id : OpId) (now : U256.t),
      get_ts s id <> 0 ->
      get_ts s id <> DONE_TIMESTAMP ->
      now < get_ts s id ->
      getOperationState s id now = OpWaiting.
  Proof.
    intros s id now Hne0 HneD Hlt. unfold getOperationState.
    destruct (get_ts s id =? 0) eqn:H0.
    - apply Z.eqb_eq in H0. contradiction.
    - destruct (get_ts s id =? DONE_TIMESTAMP) eqn:HD.
      + apply Z.eqb_eq in HD. contradiction.
      + assert (Hlt' : (now <? get_ts s id) = true)
          by (apply Z.ltb_lt; exact Hlt).
        rewrite Hlt'. reflexivity.
  Qed.

  Lemma getOperationState_ready :
    forall (s : State.t) (id : OpId) (now : U256.t),
      get_ts s id <> 0 ->
      get_ts s id <> DONE_TIMESTAMP ->
      get_ts s id <= now ->
      getOperationState s id now = OpReady.
  Proof.
    intros s id now Hne0 HneD Hle. unfold getOperationState.
    destruct (get_ts s id =? 0) eqn:H0.
    - apply Z.eqb_eq in H0. contradiction.
    - destruct (get_ts s id =? DONE_TIMESTAMP) eqn:HD.
      + apply Z.eqb_eq in HD. contradiction.
      + assert (Hge : (now <? get_ts s id) = false)
          by (apply Z.ltb_ge; lia).
        rewrite Hge. reflexivity.
  Qed.

  (** ---- 1.5  isOperation* correctness lemmas ----

      Each predicate is a thin projection on [getOperationState].
      Stated as iff lemmas so walker proofs can rewrite in both
      directions. *)
  Lemma isOperation_iff_not_unset :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperation s id now = true
      <-> getOperationState s id now <> OpUnset.
  Proof.
    intros s id now. unfold isOperation.
    destruct (getOperationState s id now); split; intro H;
      try discriminate; try reflexivity; congruence.
  Qed.

  Lemma isOperationPending_iff_waiting_or_ready :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperationPending s id now = true
      <-> (getOperationState s id now = OpWaiting \/
           getOperationState s id now = OpReady).
  Proof.
    intros s id now. unfold isOperationPending.
    destruct (getOperationState s id now); split; intro H;
      try discriminate; try reflexivity;
      try (destruct H as [H|H]; discriminate);
      auto.
  Qed.

  Lemma isOperationReady_iff_ready :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperationReady s id now = true
      <-> getOperationState s id now = OpReady.
  Proof.
    intros s id now. unfold isOperationReady.
    destruct (getOperationState s id now); split; intro H;
      try discriminate; try reflexivity.
  Qed.

  Lemma isOperationDone_iff_done :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperationDone s id now = true
      <-> getOperationState s id now = OpDone.
  Proof.
    intros s id now. unfold isOperationDone.
    destruct (getOperationState s id now); split; intro H;
      try discriminate; try reflexivity.
  Qed.

  (** ---- 1.6  isOperation false iff Unset ----

      The complementary direction: when [isOperation] is false, the
      stored timestamp is zero (i.e. Unset).  Useful for the
      already-scheduled check inside [_schedule]. *)
  Lemma isOperation_false_iff_zero :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperation s id now = false
      <-> get_ts s id = 0.
  Proof.
    intros s id now. unfold isOperation, getOperationState.
    destruct (get_ts s id =? 0) eqn:H0.
    - apply Z.eqb_eq in H0. split; auto.
    - apply Z.eqb_neq in H0.
      destruct (get_ts s id =? DONE_TIMESTAMP); cbn.
      + split; intro H; [discriminate | contradiction].
      + destruct (now <? get_ts s id); cbn;
          split; intro H; try discriminate; contradiction.
  Qed.

  (** ---- 1.7  [schedule] revert-and-success arms ----

      [schedule] reverts in three cases (unauthorized / op-state /
      insufficient-delay) and succeeds with a timestamps[id] := now +
      delay write.  Each arm is exposed as a separate Qed so walker
      proofs can dispatch on the discriminating boolean. *)
  Lemma schedule_revert_no_proposer :
    forall (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      has_role s PROPOSER_ROLE caller = false ->
      schedule s caller id delay now = revert_unauthorized.
  Proof.
    intros s caller id delay now H.
    unfold schedule. rewrite H. cbn. reflexivity.
  Qed.

  Lemma schedule_revert_already_scheduled :
    forall (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      has_role s PROPOSER_ROLE caller = true ->
      isOperation s id now = true ->
      schedule s caller id delay now = revert_op_state.
  Proof.
    intros s caller id delay now Hrole Hop.
    unfold schedule. rewrite Hrole. cbn.
    unfold _schedule. rewrite Hop. reflexivity.
  Qed.

  Lemma schedule_revert_insufficient_delay :
    forall (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      has_role s PROPOSER_ROLE caller = true ->
      isOperation s id now = false ->
      delay < s.(State.minDelay) ->
      schedule s caller id delay now = revert_insufficient_delay.
  Proof.
    intros s caller id delay now Hrole Hop Hdelay.
    unfold schedule. rewrite Hrole. cbn.
    unfold _schedule. rewrite Hop.
    assert (Hltb : (delay <? s.(State.minDelay)) = true)
      by (apply Z.ltb_lt; exact Hdelay).
    rewrite Hltb. reflexivity.
  Qed.

  Lemma schedule_success :
    forall (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      has_role s PROPOSER_ROLE caller = true ->
      isOperation s id now = false ->
      s.(State.minDelay) <= delay ->
      schedule s caller id delay now
      = Result.Success (set_state_ts s id (now + delay)).
  Proof.
    intros s caller id delay now Hrole Hop Hdelay.
    unfold schedule. rewrite Hrole. cbn.
    unfold _schedule. rewrite Hop.
    assert (Hgeb : (delay <? s.(State.minDelay)) = false)
      by (apply Z.ltb_ge; exact Hdelay).
    rewrite Hgeb. reflexivity.
  Qed.

  (** ---- 1.8  [schedule] preserves minDelay and roles ----

      The schedule operation writes only the timestamps map; on the
      success path, [minDelay] and [roles] are preserved.  The
      revert path doesn't update state at all. *)
  Lemma schedule_preserves_minDelay :
    forall (s s' : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      schedule s caller id delay now = Result.Success s' ->
      s'.(State.minDelay) = s.(State.minDelay).
  Proof.
    intros s s' caller id delay now Hsucc.
    unfold schedule in Hsucc.
    destruct (has_role s PROPOSER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    unfold _schedule in Hsucc.
    destruct (isOperation s id now); [discriminate|].
    destruct (delay <? s.(State.minDelay)); [discriminate|].
    injection Hsucc as Hs. rewrite <- Hs. reflexivity.
  Qed.

  Lemma schedule_preserves_roles :
    forall (s s' : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      schedule s caller id delay now = Result.Success s' ->
      s'.(State.roles) = s.(State.roles).
  Proof.
    intros s s' caller id delay now Hsucc.
    unfold schedule in Hsucc.
    destruct (has_role s PROPOSER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    unfold _schedule in Hsucc.
    destruct (isOperation s id now); [discriminate|].
    destruct (delay <? s.(State.minDelay)); [discriminate|].
    injection Hsucc as Hs. rewrite <- Hs. reflexivity.
  Qed.

  (** ---- 1.9  [schedule] sets timestamp to now+delay ----

      On the success path, the freshly-scheduled operation reads back
      [get_ts] = now + delay.  Walker arms cite this to discharge the
      "after schedule, op is Waiting" post-condition. *)
  Lemma schedule_sets_timestamp :
    forall (s s' : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      schedule s caller id delay now = Result.Success s' ->
      get_ts s' id = now + delay.
  Proof.
    intros s s' caller id delay now Hsucc.
    unfold schedule in Hsucc.
    destruct (has_role s PROPOSER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    unfold _schedule in Hsucc.
    destruct (isOperation s id now); [discriminate|].
    destruct (delay <? s.(State.minDelay)); [discriminate|].
    injection Hsucc as <-. apply get_set_state_ts_same.
  Qed.

  (** ---- 1.10  [scheduleBatch] is exactly [schedule] ----

      Mutator-side, [scheduleBatch] reuses [schedule] verbatim (the
      length-mismatch arm is a precondition predicate the walker
      discharges separately).  This Qed is the cosmetic re-expression. *)
  Lemma scheduleBatch_unfold :
    forall (s : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      scheduleBatch s caller id delay now = schedule s caller id delay now.
  Proof. intros. reflexivity. Qed.

  (** ---- 1.11  [execute] revert-and-success arms ---- *)
  Lemma execute_revert_no_executor :
    forall (s : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      has_role_or_open s EXECUTOR_ROLE caller = false ->
      execute s caller id pred now = revert_unauthorized.
  Proof.
    intros s caller id pred now H.
    unfold execute. rewrite H. cbn. reflexivity.
  Qed.

  Lemma execute_revert_not_ready :
    forall (s : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      has_role_or_open s EXECUTOR_ROLE caller = true ->
      isOperationReady s id now = false ->
      execute s caller id pred now = revert_op_state.
  Proof.
    intros s caller id pred now Hrole Hready.
    unfold execute. rewrite Hrole. cbn. rewrite Hready. reflexivity.
  Qed.

  Lemma execute_revert_unexecuted_predecessor :
    forall (s : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      has_role_or_open s EXECUTOR_ROLE caller = true ->
      isOperationReady s id now = true ->
      pred <> 0 ->
      isOperationDone s pred now = false ->
      execute s caller id pred now = revert_unexecuted_predecessor.
  Proof.
    intros s caller id pred now Hrole Hready Hpred Hdone.
    unfold execute. rewrite Hrole. cbn. rewrite Hready. cbn.
    assert (Hp : (pred =? 0) = false) by (apply Z.eqb_neq; exact Hpred).
    rewrite Hp. cbn. rewrite Hdone. cbn. reflexivity.
  Qed.

  Lemma execute_success_no_predecessor :
    forall (s : State.t) (caller : Address) (id : OpId) (now : U256.t),
      has_role_or_open s EXECUTOR_ROLE caller = true ->
      isOperationReady s id now = true ->
      execute s caller id 0 now
      = Result.Success (set_state_ts s id DONE_TIMESTAMP).
  Proof.
    intros s caller id now Hrole Hready.
    unfold execute. rewrite Hrole. cbn. rewrite Hready. cbn.
    (* pred = 0 so (0 =? 0) reduces to true; negb true = false; the
       and reduces to false; the outer if takes the else branch. *)
    unfold _afterCall. rewrite Hready. reflexivity.
  Qed.

  Lemma execute_success_with_done_predecessor :
    forall (s : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      has_role_or_open s EXECUTOR_ROLE caller = true ->
      isOperationReady s id now = true ->
      pred <> 0 ->
      isOperationDone s pred now = true ->
      execute s caller id pred now
      = Result.Success (set_state_ts s id DONE_TIMESTAMP).
  Proof.
    intros s caller id pred now Hrole Hready Hpred Hdone.
    unfold execute. rewrite Hrole. cbn. rewrite Hready. cbn.
    assert (Hp : (pred =? 0) = false) by (apply Z.eqb_neq; exact Hpred).
    rewrite Hp. cbn. rewrite Hdone. cbn.
    unfold _afterCall. rewrite Hready. reflexivity.
  Qed.

  (** ---- 1.12  [execute] sets DONE sentinel ---- *)
  Lemma execute_sets_done_sentinel :
    forall (s s' : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      execute s caller id pred now = Result.Success s' ->
      get_ts s' id = DONE_TIMESTAMP.
  Proof.
    intros s s' caller id pred now Hsucc.
    unfold execute in Hsucc.
    destruct (has_role_or_open s EXECUTOR_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationReady s id now) eqn:Hready; cbn in Hsucc;
      [|discriminate].
    destruct (andb (negb (pred =? 0))
                   (negb (isOperationDone s pred now))) eqn:Hpred;
      cbn in Hsucc; [discriminate|].
    unfold _afterCall in Hsucc. rewrite Hready in Hsucc.
    injection Hsucc as <-. apply get_set_state_ts_same.
  Qed.

  (** ---- 1.13  [execute] preserves minDelay and roles ---- *)
  Lemma execute_preserves_minDelay :
    forall (s s' : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      execute s caller id pred now = Result.Success s' ->
      s'.(State.minDelay) = s.(State.minDelay).
  Proof.
    intros s s' caller id pred now Hsucc.
    unfold execute in Hsucc.
    destruct (has_role_or_open s EXECUTOR_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationReady s id now) eqn:Hready; cbn in Hsucc;
      [|discriminate].
    destruct (andb (negb (pred =? 0))
                   (negb (isOperationDone s pred now))) eqn:Hpred;
      cbn in Hsucc; [discriminate|].
    unfold _afterCall in Hsucc. rewrite Hready in Hsucc.
    injection Hsucc as <-. reflexivity.
  Qed.

  Lemma execute_preserves_roles :
    forall (s s' : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      execute s caller id pred now = Result.Success s' ->
      s'.(State.roles) = s.(State.roles).
  Proof.
    intros s s' caller id pred now Hsucc.
    unfold execute in Hsucc.
    destruct (has_role_or_open s EXECUTOR_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationReady s id now) eqn:Hready; cbn in Hsucc;
      [|discriminate].
    destruct (andb (negb (pred =? 0))
                   (negb (isOperationDone s pred now))) eqn:Hpred;
      cbn in Hsucc; [discriminate|].
    unfold _afterCall in Hsucc. rewrite Hready in Hsucc.
    injection Hsucc as <-. reflexivity.
  Qed.

  (** ---- 1.14  [executeBatch] is exactly [execute] ---- *)
  Lemma executeBatch_unfold :
    forall (s : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      executeBatch s caller id pred now = execute s caller id pred now.
  Proof. intros. reflexivity. Qed.

  (** ---- 1.15  [_afterCall] characterizations ----

      _afterCall returns success iff the op is Ready at the moment
      of call.  The result writes the DONE sentinel. *)
  Lemma afterCall_revert_not_ready :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperationReady s id now = false ->
      _afterCall s id now = revert_op_state.
  Proof.
    intros s id now H. unfold _afterCall. rewrite H. reflexivity.
  Qed.

  Lemma afterCall_success :
    forall (s : State.t) (id : OpId) (now : U256.t),
      isOperationReady s id now = true ->
      _afterCall s id now = Result.Success (set_state_ts s id DONE_TIMESTAMP).
  Proof.
    intros s id now H. unfold _afterCall. rewrite H. reflexivity.
  Qed.

  (** ---- 1.16  [cancel] revert-and-success arms ---- *)
  Lemma cancel_revert_no_canceller :
    forall (s : State.t) (caller : Address) (id : OpId) (now : U256.t),
      has_role s CANCELLER_ROLE caller = false ->
      cancel s caller id now = revert_unauthorized.
  Proof.
    intros s caller id now H.
    unfold cancel. rewrite H. cbn. reflexivity.
  Qed.

  Lemma cancel_revert_not_pending :
    forall (s : State.t) (caller : Address) (id : OpId) (now : U256.t),
      has_role s CANCELLER_ROLE caller = true ->
      isOperationPending s id now = false ->
      cancel s caller id now = revert_op_state.
  Proof.
    intros s caller id now Hrole Hpend.
    unfold cancel. rewrite Hrole. cbn. rewrite Hpend. reflexivity.
  Qed.

  Lemma cancel_success :
    forall (s : State.t) (caller : Address) (id : OpId) (now : U256.t),
      has_role s CANCELLER_ROLE caller = true ->
      isOperationPending s id now = true ->
      cancel s caller id now = Result.Success (set_state_ts s id 0).
  Proof.
    intros s caller id now Hrole Hpend.
    unfold cancel. rewrite Hrole. cbn. rewrite Hpend. reflexivity.
  Qed.

  (** ---- 1.17  [cancel] clears timestamp ---- *)
  Lemma cancel_clears_timestamp :
    forall (s s' : State.t) (caller : Address) (id : OpId) (now : U256.t),
      cancel s caller id now = Result.Success s' ->
      get_ts s' id = 0.
  Proof.
    intros s s' caller id now Hsucc.
    unfold cancel in Hsucc.
    destruct (has_role s CANCELLER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationPending s id now); cbn in Hsucc;
      [|discriminate].
    injection Hsucc as <-. apply get_set_state_ts_same.
  Qed.

  (** ---- 1.18  [cancel] preserves minDelay and roles ---- *)
  Lemma cancel_preserves_minDelay :
    forall (s s' : State.t) (caller : Address) (id : OpId) (now : U256.t),
      cancel s caller id now = Result.Success s' ->
      s'.(State.minDelay) = s.(State.minDelay).
  Proof.
    intros s s' caller id now Hsucc.
    unfold cancel in Hsucc.
    destruct (has_role s CANCELLER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationPending s id now); cbn in Hsucc;
      [|discriminate].
    injection Hsucc as <-. reflexivity.
  Qed.

  Lemma cancel_preserves_roles :
    forall (s s' : State.t) (caller : Address) (id : OpId) (now : U256.t),
      cancel s caller id now = Result.Success s' ->
      s'.(State.roles) = s.(State.roles).
  Proof.
    intros s s' caller id now Hsucc.
    unfold cancel in Hsucc.
    destruct (has_role s CANCELLER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationPending s id now); cbn in Hsucc;
      [|discriminate].
    injection Hsucc as <-. reflexivity.
  Qed.

  (** ---- 1.19  [updateDelay] arms ---- *)
  Lemma updateDelay_revert_non_self :
    forall (s : State.t) (caller self : Address) (newDelay : U256.t),
      caller <> self ->
      updateDelay s caller self newDelay = revert_unauthorized_caller.
  Proof.
    intros s caller self newDelay Hne.
    unfold updateDelay.
    assert (H : (caller =? self) = false) by (apply Z.eqb_neq; exact Hne).
    rewrite H. cbn. reflexivity.
  Qed.

  Lemma updateDelay_success :
    forall (s : State.t) (caller self : Address) (newDelay : U256.t),
      caller = self ->
      updateDelay s caller self newDelay
      = Result.Success {| State.timestamps := s.(State.timestamps);
                          State.minDelay   := newDelay;
                          State.roles      := s.(State.roles); |}.
  Proof.
    intros s caller self newDelay Heq.
    unfold updateDelay. rewrite Heq, Z.eqb_refl. cbn. reflexivity.
  Qed.

  (** ---- 1.20  [updateDelay] preserves timestamps and roles ---- *)
  Lemma updateDelay_preserves_timestamps :
    forall (s s' : State.t) (caller self : Address) (newDelay : U256.t),
      updateDelay s caller self newDelay = Result.Success s' ->
      s'.(State.timestamps) = s.(State.timestamps).
  Proof.
    intros s s' caller self newDelay Hsucc.
    unfold updateDelay in Hsucc.
    destruct (caller =? self); cbn in Hsucc; [|discriminate].
    injection Hsucc as <-. reflexivity.
  Qed.

  Lemma updateDelay_preserves_roles :
    forall (s s' : State.t) (caller self : Address) (newDelay : U256.t),
      updateDelay s caller self newDelay = Result.Success s' ->
      s'.(State.roles) = s.(State.roles).
  Proof.
    intros s s' caller self newDelay Hsucc.
    unfold updateDelay in Hsucc.
    destruct (caller =? self); cbn in Hsucc; [|discriminate].
    injection Hsucc as <-. reflexivity.
  Qed.

  Lemma updateDelay_sets_minDelay :
    forall (s s' : State.t) (caller self : Address) (newDelay : U256.t),
      updateDelay s caller self newDelay = Result.Success s' ->
      s'.(State.minDelay) = newDelay.
  Proof.
    intros s s' caller self newDelay Hsucc.
    unfold updateDelay in Hsucc.
    destruct (caller =? self); cbn in Hsucc; [|discriminate].
    injection Hsucc as <-. reflexivity.
  Qed.

  (** ---- 1.21  Post-schedule observation: op is Waiting if delay > 0 ----

      Walker arms targeting [schedule] can dispatch to this lemma to
      conclude that after a successful schedule with positive delay,
      the op is Waiting (until [now] advances past [now + delay]). *)
  (** Post-schedule observation: with a strictly positive delay and a
      now > 0 (so the resulting timestamp differs from [DONE_TIMESTAMP =
      1]), the op transitions to Waiting.  The [0 < delay] hypothesis
      is the OZ "minDelay > 0" assumption; the [0 < now] hypothesis
      rules out the degenerate "block.timestamp = 0" pre-launch case. *)
  Lemma schedule_post_state_waiting :
    forall (s s' : State.t) (caller : Address) (id : OpId) (delay now : U256.t),
      schedule s caller id delay now = Result.Success s' ->
      0 < delay ->
      0 < now ->
      getOperationState s' id now = OpWaiting.
  Proof.
    intros s s' caller id delay now Hsucc Hdelay Hnow.
    pose proof (schedule_sets_timestamp s s' caller id delay now Hsucc)
      as Hts.
    apply getOperationState_waiting.
    - rewrite Hts. lia.
    - rewrite Hts. unfold DONE_TIMESTAMP. lia.
    - rewrite Hts. lia.
  Qed.

  (** ---- 1.22  Post-execute observation: op is Done ----

      After a successful [execute], the op is Done.  This is the
      key invariant any later cancel/re-schedule walker proof leans
      on (re-scheduling a Done op is blocked by [_schedule]'s
      [isOperation] check, which Done satisfies). *)
  Lemma execute_post_state_done :
    forall (s s' : State.t) (caller : Address) (id pred : OpId) (now : U256.t),
      execute s caller id pred now = Result.Success s' ->
      getOperationState s' id now = OpDone.
  Proof.
    intros s s' caller id pred now Hsucc.
    pose proof (execute_sets_done_sentinel s s' caller id pred now Hsucc)
      as Hts.
    apply getOperationState_done. exact Hts.
  Qed.

  (** ---- 1.23  Post-cancel observation: op is Unset ----

      After a successful [cancel], the op is back to Unset.  This is
      what enables re-scheduling the same id after cancellation. *)
  Lemma cancel_post_state_unset :
    forall (s s' : State.t) (caller : Address) (id : OpId) (now : U256.t),
      cancel s caller id now = Result.Success s' ->
      getOperationState s' id now = OpUnset.
  Proof.
    intros s s' caller id now Hsucc.
    pose proof (cancel_clears_timestamp s s' caller id now Hsucc) as Hts.
    apply getOperationState_zero. exact Hts.
  Qed.

  (** ---- 1.24  Other operations are unaffected by single-op mutations ----

      The state-transition isolation property: a schedule / execute /
      cancel on id [k] leaves the state of any [k' <> k] unchanged at
      [get_ts] level.  Walker proofs cite this to discharge
      unrelated-id observers. *)
  Lemma schedule_isolates_other_ids :
    forall (s s' : State.t) (caller : Address)
           (id id' : OpId) (delay now : U256.t),
      schedule s caller id delay now = Result.Success s' ->
      id <> id' ->
      get_ts s' id' = get_ts s id'.
  Proof.
    intros s s' caller id id' delay now Hsucc Hne.
    unfold schedule in Hsucc.
    destruct (has_role s PROPOSER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    unfold _schedule in Hsucc.
    destruct (isOperation s id now); [discriminate|].
    destruct (delay <? s.(State.minDelay)); [discriminate|].
    injection Hsucc as <-.
    apply get_set_state_ts_other. exact Hne.
  Qed.

  Lemma execute_isolates_other_ids :
    forall (s s' : State.t) (caller : Address)
           (id id' pred : OpId) (now : U256.t),
      execute s caller id pred now = Result.Success s' ->
      id <> id' ->
      get_ts s' id' = get_ts s id'.
  Proof.
    intros s s' caller id id' pred now Hsucc Hne.
    unfold execute in Hsucc.
    destruct (has_role_or_open s EXECUTOR_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationReady s id now) eqn:Hready; cbn in Hsucc;
      [|discriminate].
    destruct (andb (negb (pred =? 0))
                   (negb (isOperationDone s pred now)));
      cbn in Hsucc; [discriminate|].
    unfold _afterCall in Hsucc. rewrite Hready in Hsucc.
    injection Hsucc as <-.
    apply get_set_state_ts_other. exact Hne.
  Qed.

  Lemma cancel_isolates_other_ids :
    forall (s s' : State.t) (caller : Address)
           (id id' : OpId) (now : U256.t),
      cancel s caller id now = Result.Success s' ->
      id <> id' ->
      get_ts s' id' = get_ts s id'.
  Proof.
    intros s s' caller id id' now Hsucc Hne.
    unfold cancel in Hsucc.
    destruct (has_role s CANCELLER_ROLE caller); cbn in Hsucc;
      [|discriminate].
    destruct (isOperationPending s id now); cbn in Hsucc;
      [|discriminate].
    injection Hsucc as <-.
    apply get_set_state_ts_other. exact Hne.
  Qed.

  (** ============================================================
      Section 2 — Slot-agnostic walker-template scaffolding

      Each inheriting contract will open this Section with concrete
      slot indices and a projection lens; the section parameters
      below document the abstract API.

      Note: we declare the section but do NOT instantiate concrete
      walker lemmas inside it — the walker arms require a shallow
      form to point at, which does not exist for the abstract
      TimelockController base.  Inheritors (e.g.
      [TimelockControllerOptimistic]) re-open the section in their
      own equivalence file and supply the shallow-form bindings.

      The Section here exists primarily as documentation — the names
      and types of the parameters are the API surface a
      [TimelockControllerOptimisticEquivalence] file fills in.
      ============================================================ *)

  Section TimelockControllerBaseEquivalenceTemplate.

    (** Slot indices on the inheriting contract's [SimulatedStorage.t].
        For example, in OZ's TimelockControllerStorage the
        [$._timestamps] is at the EIP-7201 namespace anchor (a single
        keccak256-derived slot) and the [$._minDelay] is at the next
        offset. *)
    Variable slot_timestamps : nat.
    Variable slot_minDelay   : nat.

    (** AccessControl substate slot indices (mirroring Guardian's
        Section parameterization in [proofs/equivalence/Guardian.v]).
        The [_roles] mapping is layered behind a single namespace
        anchor; we expose it as one slot index here and let the
        inheritor refine if necessary. *)
    Variable slot_roles : nat.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the TimelockController substate.
        The inheritor supplies this from its own [proj_sim] structure. *)
    Variable project_tlc : SimulatedStorage.t -> State.t.

    (** Lens-correctness hypotheses — discharged by [reflexivity] (or
        a small [cbn]/[unfold] chain) at the instantiation site.
        Each says: the projected TimelockController substate's
        [State.<field>] equals the inheritor's storage at the right
        slot. *)

    Hypothesis lens_timestamps_correct :
      forall (storage : SimulatedStorage.t) (id : OpId),
        getTimestamp (project_tlc storage) id
        = lookup_ts (project_tlc storage).(State.timestamps) id.

    Hypothesis lens_minDelay_correct :
      forall (storage : SimulatedStorage.t),
        getMinDelay (project_tlc storage)
        = (project_tlc storage).(State.minDelay).

    Hypothesis lens_roles_correct :
      forall (storage : SimulatedStorage.t)
             (role : AccessControl.Role) (account : Address),
        has_role (project_tlc storage) role account
        = AccessControl.hasRole (project_tlc storage).(State.roles)
            role account.

    (** Walker-template documentation lives in the section as proven
        observations about the lens — these are tautological under
        the hypotheses above and serve to fix the names downstream
        walker proofs will cite. *)

    Lemma walker_obs_getTimestamp :
      forall (storage : SimulatedStorage.t) (id : OpId),
        getTimestamp (project_tlc storage) id
        = lookup_ts (project_tlc storage).(State.timestamps) id.
    Proof. intros. apply lens_timestamps_correct. Qed.

    Lemma walker_obs_getMinDelay :
      forall (storage : SimulatedStorage.t),
        getMinDelay (project_tlc storage)
        = (project_tlc storage).(State.minDelay).
    Proof. intros. apply lens_minDelay_correct. Qed.

    Lemma walker_obs_hasRole :
      forall (storage : SimulatedStorage.t)
             (role : AccessControl.Role) (account : Address),
        has_role (project_tlc storage) role account
        = AccessControl.hasRole (project_tlc storage).(State.roles)
            role account.
    Proof. intros. apply lens_roles_correct. Qed.

    (** Composite observation: the [isOperation*] family projects
        through the lens correctness hypotheses to definitional
        unfoldings on the projected state. *)
    Lemma walker_obs_isOperation :
      forall (storage : SimulatedStorage.t) (id : OpId) (now : U256.t),
        isOperation (project_tlc storage) id now
        = match getOperationState (project_tlc storage) id now with
          | OpUnset => false
          | _       => true
          end.
    Proof. intros. reflexivity. Qed.

  End TimelockControllerBaseEquivalenceTemplate.

  (** ============================================================
      Section 3 — Walker-template documentation (commentary only)

      For each public TimelockController operation, the comment block
      below describes what the Yul body's walker arms look like.  The
      walker proofs themselves cannot be written until a concrete
      shallow form (from an inheriting contract) is available.

      Cross-reference: [proofs/equivalence/TimelockControllerOptimistic.v]
      Section 3 walks through the same shapes against the existing
      [TimelockControllerOptimistic] shallow form.
      ============================================================ *)

  (** ---- getTimestamp(id) ----

        Yul body shape (inlined into inheritor):
          slot    := slot_timestamps
          ptr     := mapping_index_access_<bytes32>_<uint256>(slot, id)
          ts      := sload(ptr)

        Walker arms:
          - sload at <keccak(id, slot_timestamps)>
              ↓ via the existing mapping_index_access leaf
            (project_tlc storage).timestamps lookup at [id]
          - matches: [getTimestamp (project_tlc storage) id]
            via [lens_timestamps_correct]. *)

  (** ---- getMinDelay() ----

        Yul body shape:
          slot    := slot_minDelay
          d       := sload(slot)

        Walker arms:
          - direct sload at slot_minDelay (no mapping_index_access).
          - matches: [getMinDelay (project_tlc storage)] via
            [lens_minDelay_correct]. *)

  (** ---- getOperationState(id) ----

        Yul body shape (inlined as a 4-way branch):
          let ts := <getTimestamp(id)>
          if iszero(ts):       leave with 0   // Unset
          else if eq(ts, 1):   leave with 3   // Done
          else if gt(ts, ts0): leave with 1   // Waiting (where ts0 = block.timestamp)
          else:                leave with 2   // Ready

        Walker arms (R047 case-split on the disjoint branches):
          - Unset arm: composes through [getOperationState_zero].
          - Done arm:  composes through [getOperationState_done].
          - Waiting arm: composes through [getOperationState_waiting]
            with H_ts_lt_now.
          - Ready arm:  composes through [getOperationState_ready]
            with H_ts_le_now.

        Note: the OZ source uses [timestamp > block.timestamp] for
        the Waiting branch, which in Coq's order is [now < ts].  The
        mock and the lemmas above use that orientation consistently. *)

  (** ---- isOperation(id) / isOperationPending / isOperationReady / isOperationDone ----

        Yul body shape: each computes [getOperationState(id)] then
        matches against the relevant enum slot(s).

        Walker arms: thin wrappers — each lemma in 1.5 above gives
        the correctness statement (iff getOperationState = ...).  The
        walker collapses the if-cascade into a single boolean value
        equal to the lemma's RHS. *)

  (** ---- schedule(target, value, data, predecessor, salt, delay) ----

      Phase 1 — role gate (modifier_onlyRole):
        sload(<role_PROPOSER_ROLE[caller]>) via the AccessControl
        substate; revert with [AccessControlUnauthorizedAccount] if
        false.

      Phase 2 — id derivation:
        id := keccak256(abi.encode(target, value, data, predecessor, salt))
        (an opaque digest; the walker treats the keccak as a
        deterministic transducer on the abi-encoded preimage).

      Phase 3 — _schedule body:
        - if isOperation(id): revert TimelockUnexpectedOperationState
        - read minDelay; if delay < minDelay: revert TimelockInsufficientDelay
        - sstore(<timestamps[id]>, now + delay)

      Phase 4 — event emission (CallScheduled + optional CallSalt):
        not modeled at the equivalence level (no sim-side state
        depends on event emission).

      Composite post-state matches:
        - On role-revert:        [schedule_revert_no_proposer].
        - On already-scheduled:  [schedule_revert_already_scheduled].
        - On delay-too-short:    [schedule_revert_insufficient_delay].
        - On success:            [schedule_success] +
                                 [schedule_sets_timestamp] (for the
                                 post-state observation). *)

  (** ---- scheduleBatch(targets, values, payloads, predecessor, salt, delay) ----

      Yul body shape: like [schedule] but with a length-check guard
      on the three arrays:

        if (targets.length != values.length || targets.length != payloads.length):
          revert TimelockInvalidOperationLength;

      then proceeds as [schedule] with the batch hash.

      Walker arms:
        - Length-check arm: a calldata-level [eq]/[and] composition.
          The walker discharges it as a precondition predicate; the
          mutator-level mock collapses [scheduleBatch] to [schedule]
          (see [scheduleBatch_unfold]).
        - Hash and _schedule arms: same as [schedule] (Phase 2-3
          above), targeting the batch hash. *)

  (** ---- execute(target, value, payload, predecessor, salt) ----

      Phase 1 — open-role gate (modifier_onlyRoleOrOpenRole):
        sload(<role_EXECUTOR_ROLE[address(0)]>) — short-circuit to
        success if true (the open-role pattern); else
        sload(<role_EXECUTOR_ROLE[caller]>) and revert if false.

      Phase 2 — id derivation:
        id := keccak256(abi.encode(target, value, payload, predecessor, salt))

      Phase 3 — _beforeCall(id, predecessor):
        - if !isOperationReady(id):
            revert TimelockUnexpectedOperationState
        - if predecessor != 0 && !isOperationDone(predecessor):
            revert TimelockUnexecutedPredecessor

      Phase 4 — _execute(target, value, payload):
        target.call{value}(payload).  Modeled as an opaque side-effect
        — the queue-state semantics are independent of dispatch
        success.  Audit-time check at the inheritor walker: the call
        either succeeds (continuation) or bubbles via
        Address.verifyCallResult.

      Phase 5 — _afterCall(id):
        - re-assert isOperationReady(id) (defensive against
          reentrancy that might have changed the op state)
        - sstore(<timestamps[id]>, _DONE_TIMESTAMP)

      Composite post-state matches:
        - On role-revert:        [execute_revert_no_executor].
        - On not-ready:          [execute_revert_not_ready].
        - On bad-predecessor:    [execute_revert_unexecuted_predecessor].
        - On success:            [execute_success_no_predecessor] or
                                 [execute_success_with_done_predecessor]
                                 + [execute_sets_done_sentinel] +
                                 [execute_post_state_done]. *)

  (** ---- executeBatch(targets, values, payloads, predecessor, salt) ----

      Yul body shape: like [execute] but with a length-check guard
      analogous to [scheduleBatch], a loop over [_execute] calls per
      target.  Walker arms: the length check is a precondition
      predicate; the mutator collapses to [execute] (see
      [executeBatch_unfold]). *)

  (** ---- cancel(id) ----

      Phase 1 — role gate (modifier_onlyRole):
        sload(<role_CANCELLER_ROLE[caller]>); revert if false.

      Phase 2 — pending check:
        if !isOperationPending(id):
          revert TimelockUnexpectedOperationState

      Phase 3 — delete _timestamps[id]:
        sstore(<timestamps[id]>, 0)

      Phase 4 — event emission (Cancelled).

      Composite post-state matches:
        - On role-revert:  [cancel_revert_no_canceller].
        - On not-pending:  [cancel_revert_not_pending].
        - On success:      [cancel_success] +
                           [cancel_clears_timestamp] +
                           [cancel_post_state_unset]. *)

  (** ---- updateDelay(newDelay) ----

      Phase 1 — self-call gate:
        sender := caller
        if sender != address(this):
          revert TimelockUnauthorizedCaller(sender)

      Phase 2 — write:
        sstore(<minDelay>, newDelay)

      Phase 3 — event emission (MinDelayChange).

      Note: this function does NOT use a role modifier.  The self-call
      check enforces that updates flow through the normal
      schedule/execute pipeline (i.e. the timelock executes its own
      [updateDelay] call after the delay window expires).

      Composite post-state matches:
        - On non-self call: [updateDelay_revert_non_self].
        - On success:       [updateDelay_success] +
                            [updateDelay_sets_minDelay] +
                            [updateDelay_preserves_timestamps]. *)

  (** ---- hashOperation / hashOperationBatch ----

      Pure-function shape (view functions, no state read):
        let ptr := allocate_unbounded()
        let tail := abi_encode_tuple_<types>(ptr, ...args)
        result := keccak256(ptr, sub(tail, ptr))

      Walker arms:
        - Reuses R064's [AbiEncoding.v] leaves for the
          abi-encode-tuple step.
        - keccak256 is treated as an opaque deterministic transducer
          at the equivalence layer; the audit-time witness is that
          the abi-encoded preimage is byte-identical to OZ's
          abi.encode output.

      No sim-side state transition — these are pure functions. *)

  (** ============================================================
      Section 4 — Sanity check examples (vm_compute)

      A handful of fully-closed examples exercising the helper lemmas
      against a concrete sim state.  Serves as a smoke test that the
      sim composes properly and that [vm_compute] can evaluate the
      mutators end-to-end.
      ============================================================ *)

  Module Examples.

    (** A small state: minDelay = 100, three operations a/b/c with
        distinct id values.  Roles seeded so that [caller_p] has
        PROPOSER and CANCELLER, [caller_e] has EXECUTOR. *)
    Definition caller_p : Address := 10.
    Definition caller_e : Address := 20.
    Definition self_addr : Address := 30.

    Definition op_a : OpId := 100.
    Definition op_b : OpId := 200.

    Definition ac0 : AccessControl.State :=
      {| AccessControl.roles :=
           [ (PROPOSER_ROLE,
              {| AccessControl.members := [caller_p];
                 AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
           ; (EXECUTOR_ROLE,
              {| AccessControl.members := [caller_e];
                 AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
           ; (CANCELLER_ROLE,
              {| AccessControl.members := [caller_p];
                 AccessControl.admin   := AccessControl.DEFAULT_ADMIN_ROLE |})
           ] |}.

    Definition s0 : State.t := init_state 100 ac0.

    (** After [schedule] of op_a with delay 100 at now=5, the op is
        Waiting (since 5 + 100 = 105 > 5). *)
    Example ex_schedule_to_waiting :
      forall s',
        schedule s0 caller_p op_a 100 5 = Result.Success s' ->
        getOperationState s' op_a 5 = OpWaiting.
    Proof.
      intros s' Hsucc.
      eapply schedule_post_state_waiting; [exact Hsucc| |]; lia.
    Qed.

    Example ex_schedule_runs :
      schedule s0 caller_p op_a 100 5
      = Result.Success (set_state_ts s0 op_a 105).
    Proof.
      apply schedule_success.
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
      - cbv [s0 init_state State.minDelay]. lia.
    Qed.

    (** A non-proposer can't schedule. *)
    Example ex_schedule_unauth :
      schedule s0 caller_e op_a 100 5 = revert_unauthorized.
    Proof. apply schedule_revert_no_proposer. vm_compute. reflexivity. Qed.

    (** Insufficient delay reverts. *)
    Example ex_schedule_short_delay :
      schedule s0 caller_p op_a 50 5 = revert_insufficient_delay.
    Proof.
      apply schedule_revert_insufficient_delay.
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
      - cbv [s0 init_state State.minDelay]. lia.
    Qed.

    (** Cancel on Unset reverts (not pending). *)
    Example ex_cancel_unset_reverts :
      cancel s0 caller_p op_a 5 = revert_op_state.
    Proof.
      apply cancel_revert_not_pending.
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
    Qed.

    (** updateDelay must be self-called. *)
    Example ex_updateDelay_non_self :
      updateDelay s0 caller_p self_addr 200 = revert_unauthorized_caller.
    Proof. apply updateDelay_revert_non_self. discriminate. Qed.

    Example ex_updateDelay_self :
      updateDelay s0 self_addr self_addr 200
      = Result.Success
          {| State.timestamps := s0.(State.timestamps);
             State.minDelay   := 200;
             State.roles      := s0.(State.roles); |}.
    Proof. apply updateDelay_success. reflexivity. Qed.

  End Examples.

End TimelockControllerBaseEquivalence.
