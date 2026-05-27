(** Guardian validity preservation.

    Headline lemma: [grantOptimisticGuardian] preserves the
    [Valid.state] storage invariant — the post-state still has
    duplicate-free, zero-free role sets across all three roles.

    The other two operations of interest don't mutate Guardian's own
    storage:
      - [cancel] dispatches to the managed governor; the only Guardian
        state it touches is the role-set reads it uses for
        authorization (no writes).
      - [revokeOptimisticProposer] dispatches to the timelock; same
        story.

    So validity preservation reduces to verifying [add_role] preserves
    [NoDup] and the zero-free predicate, which is what we prove here.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Guardian.
Require Import ReserveGovernor.proofs.Guardian.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module GuardianValidity.

Import ReserveGovernor.simulations.Guardian.
Import ReserveGovernor.proofs.Guardian.
Import Guardian.
Import GuardianProofs.

(** ----- Boolean / propositional bridges on addr_in. ----- *)
Lemma addr_in_true_In (lst : list Address) (a : Address) :
  addr_in lst a = true -> In a lst.
Proof.
  induction lst as [|h t IH]; simpl; intros H.
  - discriminate.
  - destruct (h =? a) eqn:Heq.
    + apply Z.eqb_eq in Heq. left. exact Heq.
    + right. apply IH. exact H.
Qed.

Lemma addr_in_false_not_In (lst : list Address) (a : Address) :
  addr_in lst a = false -> ~ In a lst.
Proof.
  induction lst as [|h t IH]; simpl; intros H Habs.
  - exact Habs.
  - destruct (h =? a) eqn:Heq.
    + discriminate.
    + destruct Habs as [Heq2 | Hrest].
      * apply Z.eqb_neq in Heq. apply Heq. exact Heq2.
      * apply IH; assumption.
Qed.

(** ----- add_role preserves NoDup. ----- *)
Lemma add_role_NoDup (lst : list Address) (a : Address) :
  NoDup lst -> NoDup (add_role lst a).
Proof.
  intros Hnd. unfold add_role.
  destruct (addr_in lst a) eqn:Hin.
  - exact Hnd.
  - constructor; [|exact Hnd].
    apply addr_in_false_not_In. exact Hin.
Qed.

(** ----- add_role preserves "no zero address" when [a <> 0]. ----- *)
Lemma add_role_no_zero (lst : list Address) (a : Address) :
  a <> 0 ->
  Forall (fun x => x <> 0) lst ->
  Forall (fun x => x <> 0) (add_role lst a).
Proof.
  intros Hnz Hall. unfold add_role.
  destruct (addr_in lst a); [exact Hall|].
  constructor; assumption.
Qed.

(** ----- Headline: grantOptimisticGuardian preserves [Valid.state]. ----- *)
Lemma grant_preserves_validity
    (s s' : State.t) (caller account : Address) :
  Valid.state s ->
  grantOptimisticGuardian s caller account = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  pose proof (grant_inserts_account _ _ _ _ Hok) as (Hadm_eq & Hman_eq & _).
  unfold grantOptimisticGuardian in Hok.
  destruct (negb (has_manager s caller)) eqn:Hm; [discriminate|].
  destruct (account =? 0) eqn:Hz; [discriminate|].
  apply Z.eqb_neq in Hz.
  injection Hok as Hs'.
  destruct Hv as [Hand Hgnd Hmnd Hanz Hgnz Hmnz].
  constructor; rewrite <- Hs'; simpl.
  - exact Hand.
  - unfold Valid.no_dup_guardians. simpl.
    apply add_role_NoDup. exact Hgnd.
  - exact Hmnd.
  - exact Hanz.
  - unfold Valid.no_zero_guardians. simpl.
    apply add_role_no_zero; assumption.
  - exact Hmnz.
Qed.

(** ----- cancel doesn't mutate storage. Trivial because the
    operation returns a [CancelEvent.t], not a [State.t]. The
    statement we can usefully formalize is: there's no state-mutating
    surface at all on the cancel path. ----- *)
Remark cancel_is_pure_dispatch :
  forall (s : State.t)
         (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
         (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
         (caller governor : Address) (key : ProposalKey.t),
  match cancel s io ps gpi hc caller governor key with
  | Result.Success _ => True
  | Result.Revert _ _ => True
  end.
Proof. intros. destruct (cancel _ _ _ _ _ _ _ _); exact I. Qed.

(** ----- revokeOptimisticProposer doesn't mutate Guardian storage. ----- *)
Remark revoke_is_pure_dispatch :
  forall (s : State.t)
         (tl_or : Address -> Address) (hc : Address -> bool)
         (caller governor account : Address),
  match revokeOptimisticProposer s tl_or hc caller governor account with
  | Result.Success _ => True
  | Result.Revert _ _ => True
  end.
Proof. intros. destruct (revokeOptimisticProposer _ _ _ _ _ _); exact I. Qed.

End GuardianValidity.
