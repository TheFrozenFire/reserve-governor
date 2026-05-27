(** Timelock validity preservation.

    Each of [scheduleBatch], [executeBatch], [cancel],
    [executeBatchBypass] preserves the structural invariants on the
    state, formalized as [Timelock.Valid.state]:

      - [minDelay] is bounded by U256
      - every stored timestamp [ts] is either 0, [DONE_TIMESTAMP], or
        strictly greater than [DONE_TIMESTAMP] (no scheduled value
        sits exactly at the magic Done sentinel).

    The four operations write:
      - [scheduleBatch]      writes [now + delay] (assumed > 1 for
                             non-degenerate inputs)
      - [executeBatch]       writes [DONE_TIMESTAMP] (always valid)
      - [cancel]             writes 0 (always valid)
      - [executeBatchBypass] writes [now] then [DONE_TIMESTAMP]
                             (the intermediate [now] must be > 1)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Timelock.
Require Import ReserveGovernor.proofs.Timelock.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module TimelockValidity.

Import ReserveGovernor.simulations.Timelock.
Import Timelock.
Import Timelock.Valid.
Import TimelockProofs.

(** ---- Helper: setting a reasonable ts preserves entries_valid. ---- *)
Lemma set_ts_entries_valid (m : TsMap) (id : OpId) (ts : U256.t) :
  entries_valid m ->
  reasonable_ts ts ->
  entries_valid (set_ts m id ts).
Proof.
  intros HF Hts.
  unfold entries_valid in *.
  induction m as [|[k v] rest IH]; simpl in *.
  - constructor; simpl; [exact Hts | constructor].
  - inversion HF as [|? ? Hhd Htl]; subst.
    destruct (k =? id) eqn:Hk; simpl.
    + constructor; simpl; [exact Hts | exact Htl].
    + constructor; simpl; [exact Hhd | apply IH; exact Htl].
Qed.

(** ---- scheduleBatch preserves validity, given a non-degenerate ts.

    The non-degeneracy condition: [DONE_TIMESTAMP < now + delay]. In
    practice [now] is [block.timestamp] which is comfortably above 1
    since 1970. ---- *)
Lemma scheduleBatch_preserves_validity
    (s s' : State.t) (id : OpId) (delay now : U256.t) (hasProposer : bool) :
  Valid.state s ->
  DONE_TIMESTAMP < now + delay ->
  scheduleBatch s id delay now hasProposer = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hpos Hok.
  destruct Hv as [Hmin Hentries].
  unfold scheduleBatch in Hok.
  destruct hasProposer; [|discriminate].
  destruct (negb (get_ts s id =? 0)) eqn:Hcheck; [discriminate|].
  destruct (delay <? s.(State.minDelay)) eqn:Hdelay; [discriminate|].
  injection Hok as Hs'. rewrite <- Hs'.
  constructor; simpl.
  - exact Hmin.
  - apply set_ts_entries_valid; [exact Hentries|].
    right. right. exact Hpos.
Qed.

(** ---- executeBatch preserves validity (writes [DONE_TIMESTAMP]). ---- *)
Lemma executeBatch_preserves_validity
    (s s' : State.t) (id : OpId) (now : U256.t) (hasExecutor : bool) :
  Valid.state s ->
  executeBatch s id now hasExecutor = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hmin Hentries].
  unfold executeBatch in Hok.
  destruct hasExecutor; [|discriminate].
  destruct (op_status s id now) eqn:Hst; try discriminate.
  injection Hok as Hs'. rewrite <- Hs'.
  constructor; simpl.
  - exact Hmin.
  - apply set_ts_entries_valid; [exact Hentries|].
    right. left. reflexivity.
Qed.

(** ---- cancel preserves validity (writes 0). ---- *)
Lemma cancel_preserves_validity
    (s s' : State.t) (id : OpId) (now : U256.t) (hasCanceller : bool) :
  Valid.state s ->
  cancel s id now hasCanceller = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hmin Hentries].
  unfold cancel in Hok.
  destruct hasCanceller; [|discriminate].
  destruct (op_status s id now) eqn:Hst; try discriminate;
    injection Hok as Hs'; rewrite <- Hs'; constructor; simpl;
    try exact Hmin;
    apply set_ts_entries_valid; try exact Hentries; left; reflexivity.
Qed.

(** ---- executeBatchBypass preserves validity, given a non-degenerate
    [now] (DONE_TIMESTAMP < now). The bypass writes [now] first, then
    [DONE_TIMESTAMP]; both writes must respect [reasonable_ts]. ---- *)
Lemma executeBatchBypass_preserves_validity
    (s s' : State.t) (id : OpId) (now : U256.t)
    (hasProposer hasExecutor : bool) :
  Valid.state s ->
  DONE_TIMESTAMP < now ->
  executeBatchBypass s id now hasProposer hasExecutor = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hpos Hok.
  unfold executeBatchBypass in Hok.
  destruct hasProposer; [|discriminate].
  destruct (negb (get_ts s id =? 0)) eqn:Hcheck; [discriminate|].
  set (s1 := set_state_ts s id now) in Hok.
  assert (Hv1 : Valid.state s1).
  { destruct Hv as [Hmin Hentries].
    unfold s1. constructor; simpl.
    - exact Hmin.
    - apply set_ts_entries_valid; [exact Hentries|].
      right. right. exact Hpos. }
  exact (executeBatch_preserves_validity s1 s' id now hasExecutor Hv1 Hok).
Qed.

End TimelockValidity.
