(** Timelock headline lemmas.

    Proves the load-bearing safety invariants for the [Timelock]
    simulation defined in [ReserveGovernor.simulations.Timelock]:

      INV-1   [executeBatch] before maturity reverts NotReady.
              An op in [OpWaiting] (executableAt > now) cannot be
              executed.

      INV-2   No double execute. After a successful [executeBatch]
              the op is Done; a second [executeBatch] sees Done and
              reverts NotReady.

      INV-3   After [cancel], the op is Unset; subsequent
              [executeBatch] reverts NotReady.

      INV-4   [executeBatchBypass] requires the caller to have
              PROPOSER_ROLE (hasProposer = true). Without the role it
              reverts Unauthorized — independent of state.

      INV-5   Bypass preserves slow-path queue ordering. Concretely:
              [scheduleBatch s idA delay nowS = Success sA] followed
              by [executeBatchBypass sA idB nowB ... = Success sB]
              with [idA != idB] leaves A's executableAt unchanged
              and A still Waiting at [nowB] when [nowB < nowS + delay].

      INV-6   Bypass on an already-scheduled op reverts
              OperationConflict.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Timelock.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module TimelockProofs.

Import ReserveGovernor.simulations.Timelock.
Import Timelock.

(** ---- map helpers ---- *)

(** [lookup_ts] after [set_ts] at the same key returns the new value. *)
Lemma lookup_set_same (m : TsMap) (id : OpId) (ts : U256.t) :
  lookup_ts (set_ts m id ts) id = ts.
Proof.
  induction m as [|[k v] rest IH]; simpl.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (k =? id) eqn:Hk; simpl.
    + rewrite Hk. reflexivity.
    + rewrite Hk. apply IH.
Qed.

(** [lookup_ts] after [set_ts] at a different key is unchanged.
    Uses the contrapositive of [k =? id'] when [id != id']. *)
Lemma lookup_set_other (m : TsMap) (id id' : OpId) (ts : U256.t) :
  id <> id' ->
  lookup_ts (set_ts m id ts) id' = lookup_ts m id'.
Proof.
  intros Hne.
  induction m as [|[k v] rest IH]; simpl.
  - assert (Hid : (id =? id') = false) by (apply Z.eqb_neq; congruence).
    rewrite Hid. reflexivity.
  - destruct (k =? id) eqn:Hk; simpl.
    + apply Z.eqb_eq in Hk. subst k.
      assert (Hid : (id =? id') = false) by (apply Z.eqb_neq; congruence).
      rewrite Hid. reflexivity.
    + destruct (k =? id') eqn:Hk'; auto.
Qed.

(** Convenience: [get_ts] after writing the same id. *)
Lemma get_ts_set_same (s : State.t) (id : OpId) (ts : U256.t) :
  get_ts (set_state_ts s id ts) id = ts.
Proof.
  unfold get_ts, set_state_ts. simpl.
  apply lookup_set_same.
Qed.

Lemma get_ts_set_other (s : State.t) (id id' : OpId) (ts : U256.t) :
  id <> id' ->
  get_ts (set_state_ts s id ts) id' = get_ts s id'.
Proof.
  intros Hne. unfold get_ts, set_state_ts. simpl.
  apply lookup_set_other. exact Hne.
Qed.

(** ---- INV-1: execute before maturity reverts. ---- *)

Lemma execute_before_maturity_reverts
    (s : State.t) (id : OpId) (now : U256.t) (hasExecutor : bool) :
  op_status s id now = OpWaiting ->
  exists p q, executeBatch s id now hasExecutor = Result.Revert p q.
Proof.
  intros Hst.
  unfold executeBatch.
  destruct hasExecutor; simpl.
  - rewrite Hst. eexists. eexists. reflexivity.
  - eexists. eexists. reflexivity.
Qed.

(** ---- INV-2: re-execute after Done reverts. ----

    Strategy: a successful [executeBatch] writes [DONE_TIMESTAMP = 1]
    at id. The next [op_status] reads ts = 1, which the second branch
    of [op_status] maps to OpDone. Then [executeBatch] sees OpDone
    (not OpReady) and reverts NotReady. *)
Lemma execute_then_execute_reverts
    (s s' : State.t) (id : OpId) (now1 now2 : U256.t)
    (hasExecutor : bool) :
  executeBatch s id now1 hasExecutor = Result.Success s' ->
  exists p q, executeBatch s' id now2 hasExecutor = Result.Revert p q.
Proof.
  intros Hok.
  unfold executeBatch in Hok.
  destruct hasExecutor; [|discriminate].
  destruct (op_status s id now1) eqn:Hst1; try discriminate.
  injection Hok as Hs'.
  (* Now s' is the state with timestamps[id] = DONE_TIMESTAMP. *)
  assert (Hread : get_ts s' id = DONE_TIMESTAMP).
  { rewrite <- Hs'. apply get_ts_set_same. }
  unfold executeBatch.
  assert (Hstdone : op_status s' id now2 = OpDone).
  { unfold op_status. rewrite Hread.
    unfold DONE_TIMESTAMP. simpl. reflexivity. }
  rewrite Hstdone.
  eexists. eexists. reflexivity.
Qed.

(** ---- INV-3: execute after cancel reverts. ----

    Strategy: a successful [cancel] writes 0 at id. Next [op_status]
    is OpUnset; [executeBatch] reverts. *)
Lemma cancel_then_execute_reverts
    (s s' : State.t) (id : OpId) (now1 now2 : U256.t)
    (hasCanceller hasExecutor : bool) :
  cancel s id now1 hasCanceller = Result.Success s' ->
  exists p q, executeBatch s' id now2 hasExecutor = Result.Revert p q.
Proof.
  intros Hok.
  unfold cancel in Hok.
  destruct hasCanceller; [|discriminate].
  destruct (op_status s id now1) eqn:Hst1; try discriminate;
    injection Hok as Hs'.
  - (* OpWaiting -> Success setting ts := 0 *)
    unfold executeBatch.
    destruct hasExecutor; [|eexists; eexists; reflexivity].
    assert (Hread : get_ts s' id = 0)
      by (rewrite <- Hs'; apply get_ts_set_same).
    unfold op_status. rewrite Hread. simpl.
    eexists. eexists. reflexivity.
  - (* OpReady -> Success setting ts := 0 *)
    unfold executeBatch.
    destruct hasExecutor; [|eexists; eexists; reflexivity].
    assert (Hread : get_ts s' id = 0)
      by (rewrite <- Hs'; apply get_ts_set_same).
    unfold op_status. rewrite Hread. simpl.
    eexists. eexists. reflexivity.
Qed.

(** ---- INV-4: bypass requires PROPOSER_ROLE. ---- *)
Lemma bypass_without_proposer_reverts
    (s : State.t) (id : OpId) (now : U256.t) (hasExecutor : bool) :
  executeBatchBypass s id now false hasExecutor = revert_unauthorized.
Proof.
  unfold executeBatchBypass. simpl. reflexivity.
Qed.

(** ---- INV-5: bypass preserves slow-path queue ordering. ----

    The key safety property. After scheduling op A and then executing
    a bypass op B (with B != A), A's executableAt timestamp is
    unchanged, and A's status at [nowB] is still Waiting whenever
    [nowB < executableAt(A)].

    This is the formal statement of "the bypass path doesn't reorder
    or skip the queued operations on the standard path".

    Note on the positivity hypothesis [DONE_TIMESTAMP < nowS + delay]:
    the OZ contract reserves timestamp 1 to mean Done. Any sane
    schedule has [now + delay >> 1] (chain time is in seconds since
    1970), and this hypothesis rules out the degenerate corner case
    where the scheduled ts collides with the Done sentinel. *)
Lemma bypass_preserves_slow_path
    (s s1 s2 : State.t) (idA idB : OpId)
    (delay nowS nowB : U256.t)
    (hasProposer hasExecutor : bool) :
  idA <> idB ->
  DONE_TIMESTAMP < nowS + delay ->
  scheduleBatch s idA delay nowS hasProposer = Result.Success s1 ->
  executeBatchBypass s1 idB nowB hasProposer hasExecutor = Result.Success s2 ->
  get_ts s2 idA = nowS + delay
  /\ (nowB < nowS + delay -> op_status s2 idA nowB = OpWaiting)
  /\ op_status s2 idA (nowS + delay) = OpReady.
Proof.
  intros Hne Hpos HokA HokB.
  unfold scheduleBatch in HokA.
  destruct hasProposer; [|discriminate].
  destruct (negb (get_ts s idA =? 0)) eqn:Hcheck1; [discriminate|].
  destruct (delay <? s.(State.minDelay)) eqn:Hdelay; [discriminate|].
  injection HokA as Hs1.
  unfold executeBatchBypass in HokB.
  destruct (negb (get_ts s1 idB =? 0)) eqn:HcheckB; [discriminate|].
  unfold executeBatch in HokB.
  destruct hasExecutor; [|discriminate].
  destruct (op_status (set_state_ts s1 idB nowB) idB nowB) eqn:HstB;
    try discriminate.
  injection HokB as Hs2.
  assert (HtsA : get_ts s2 idA = nowS + delay).
  { rewrite <- Hs2.
    rewrite (get_ts_set_other _ idB idA DONE_TIMESTAMP); [|congruence].
    rewrite (get_ts_set_other _ idB idA nowB); [|congruence].
    rewrite <- Hs1. apply get_ts_set_same. }
  split; [exact HtsA|].
  unfold DONE_TIMESTAMP in Hpos.
  assert (Hnz : (nowS + delay =? 0) = false)
    by (apply Z.eqb_neq; lia).
  assert (Hnd : (nowS + delay =? 1) = false)
    by (apply Z.eqb_neq; lia).
  split.
  - intros HltNowB.
    unfold op_status. rewrite HtsA.
    rewrite Hnz. unfold DONE_TIMESTAMP. rewrite Hnd.
    assert (HleF : (nowS + delay <=? nowB) = false)
      by (apply Z.leb_gt; lia).
    rewrite HleF. reflexivity.
  - unfold op_status. rewrite HtsA.
    rewrite Hnz. unfold DONE_TIMESTAMP. rewrite Hnd.
    assert (HleT : (nowS + delay <=? nowS + delay) = true)
      by (apply Z.leb_le; lia).
    rewrite HleT. reflexivity.
Qed.

(** ---- INV-6: bypass on an already-scheduled op reverts.

    Same positivity caveat as INV-5: if [nowS + delay = 0] the
    stored timestamp equals the Unset sentinel and the OperationConflict
    guard wouldn't trigger. A non-degenerate schedule satisfies
    [0 < nowS + delay] trivially. ---- *)
Lemma bypass_after_schedule_conflicts
    (s s1 : State.t) (id : OpId) (delay nowS nowB : U256.t)
    (hasProposer hasExecutor : bool) :
  0 < nowS + delay ->
  scheduleBatch s id delay nowS hasProposer = Result.Success s1 ->
  executeBatchBypass s1 id nowB hasProposer hasExecutor = revert_op_conflict.
Proof.
  intros Hpos HokA.
  unfold scheduleBatch in HokA.
  destruct hasProposer; [|discriminate].
  destruct (negb (get_ts s id =? 0)) eqn:Hcheck1; [discriminate|].
  destruct (delay <? s.(State.minDelay)) eqn:Hdelay; [discriminate|].
  injection HokA as Hs1.
  unfold executeBatchBypass. simpl.
  assert (HtsId : get_ts s1 id = nowS + delay)
    by (rewrite <- Hs1; apply get_ts_set_same).
  rewrite HtsId.
  assert (Hnz : (nowS + delay =? 0) = false)
    by (apply Z.eqb_neq; lia).
  rewrite Hnz. simpl.
  reflexivity.
Qed.

End TimelockProofs.
