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

(** ----- remove_role preserves NoDup. ----- *)
Lemma remove_role_NoDup (lst : list Address) (a : Address) :
  NoDup lst -> NoDup (remove_role lst a).
Proof.
  induction lst as [|h t IH]; simpl; intros Hnd.
  - constructor.
  - inversion Hnd as [|x xs Hnx Hndt]; subst.
    destruct (h =? a) eqn:Heq.
    + apply IH; exact Hndt.
    + constructor; [|apply IH; exact Hndt].
      intro Hin_rt.
      apply Hnx.
      (* Show: In h (remove_role t a) -> In h t. *)
      clear -Hin_rt.
      induction t as [|x xs IHt]; simpl in *; [exact Hin_rt|].
      destruct (x =? a) eqn:Hxa.
      * right. apply IHt. exact Hin_rt.
      * destruct Hin_rt as [Hl | Hr].
        -- left. exact Hl.
        -- right. apply IHt. exact Hr.
Qed.

(** ----- remove_role preserves "no zero address". ----- *)
Lemma remove_role_no_zero (lst : list Address) (a : Address) :
  Forall (fun x => x <> 0) lst ->
  Forall (fun x => x <> 0) (remove_role lst a).
Proof.
  induction lst as [|h t IH]; simpl; intros Hall.
  - constructor.
  - inversion Hall as [|x xs Hnz Hrest]; subst.
    destruct (h =? a).
    + apply IH; exact Hrest.
    + constructor; [exact Hnz | apply IH; exact Hrest].
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

(** ----- Headline: revokeRole preserves [Valid.state] for every role kind.

    Both gates that matter are encoded in the operation:
      * caller must hold the admin role (revert otherwise — no state
        change to break the invariant)
      * removing an absent or zero account is a no-op on the
        affected role set, so [Forall (<> 0)] survives even when
        someone calls revokeRole with account = 0. ----- *)
Lemma revoke_preserves_validity
    (s s' : State.t) (role : RoleKind) (caller account : Address) :
  Valid.state s ->
  revokeRole s role caller account = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  unfold revokeRole in Hok.
  destruct (negb (has_admin s caller)); [discriminate|].
  destruct Hv as [Hand Hgnd Hmnd Hanz Hgnz Hmnz].
  destruct role; injection Hok as Hs'; constructor; rewrite <- Hs'; simpl.
  - unfold Valid.no_dup_admins; simpl; apply remove_role_NoDup; exact Hand.
  - exact Hgnd.
  - exact Hmnd.
  - unfold Valid.no_zero_admins; simpl; apply remove_role_no_zero; exact Hanz.
  - exact Hgnz.
  - exact Hmnz.
  - exact Hand.
  - exact Hgnd.
  - unfold Valid.no_dup_managers; simpl; apply remove_role_NoDup; exact Hmnd.
  - exact Hanz.
  - exact Hgnz.
  - unfold Valid.no_zero_managers; simpl; apply remove_role_no_zero; exact Hmnz.
  - exact Hand.
  - unfold Valid.no_dup_guardians; simpl; apply remove_role_NoDup; exact Hgnd.
  - exact Hmnd.
  - exact Hanz.
  - unfold Valid.no_zero_guardians; simpl; apply remove_role_no_zero; exact Hgnz.
  - exact Hmnz.
Qed.

(** ----- renounceRole preserves [Valid.state] for every role kind.
    Same structure as [revoke_preserves_validity] but with the caller
    in the account slot and no admin gate (the OZ contract allows
    self-renounce regardless of role membership of the caller). ----- *)
Lemma renounce_preserves_validity
    (s s' : State.t) (role : RoleKind) (caller : Address) :
  Valid.state s ->
  renounceRole s role caller = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  unfold renounceRole in Hok.
  destruct Hv as [Hand Hgnd Hmnd Hanz Hgnz Hmnz].
  destruct role; injection Hok as Hs'; constructor; rewrite <- Hs'; simpl.
  - unfold Valid.no_dup_admins; simpl; apply remove_role_NoDup; exact Hand.
  - exact Hgnd.
  - exact Hmnd.
  - unfold Valid.no_zero_admins; simpl; apply remove_role_no_zero; exact Hanz.
  - exact Hgnz.
  - exact Hmnz.
  - exact Hand.
  - exact Hgnd.
  - unfold Valid.no_dup_managers; simpl; apply remove_role_NoDup; exact Hmnd.
  - exact Hanz.
  - exact Hgnz.
  - unfold Valid.no_zero_managers; simpl; apply remove_role_no_zero; exact Hmnz.
  - exact Hand.
  - unfold Valid.no_dup_guardians; simpl; apply remove_role_NoDup; exact Hgnd.
  - exact Hmnd.
  - exact Hanz.
  - unfold Valid.no_zero_guardians; simpl; apply remove_role_no_zero; exact Hgnz.
  - exact Hmnz.
Qed.

(** ----- cancel doesn't mutate Guardian storage at all.

    Unlike grant / revoke / renounce, [cancel] returns a [CancelEvent.t]
    rather than a [State.t] — the simulation tracks the dispatched call
    without modeling the downstream governor's mutation. Validity
    preservation is therefore trivial: there is no post-state distinct
    from the pre-state. The statement below makes that explicit so the
    audit can reference it. ----- *)
Lemma cancel_preserves_validity
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller governor : Address) (key : ProposalKey.t) (ev : CancelEvent.t) :
  Valid.state s ->
  cancel s io ps gpi hc caller governor key = Result.Success ev ->
  Valid.state s.
Proof. intros Hv _. exact Hv. Qed.

(** ----- revokeOptimisticProposer doesn't mutate Guardian storage either.

    The operation dispatches to the timelock; Guardian's own role
    sets are untouched. Same shape as [cancel_preserves_validity]. ----- *)
Lemma revoke_optimistic_proposer_preserves_validity
    (s : State.t)
    (tl_or : Address -> Address) (hc : Address -> bool)
    (caller governor account : Address) (ev : RevokeEvent.t) :
  Valid.state s ->
  revokeOptimisticProposer s tl_or hc caller governor account = Result.Success ev ->
  Valid.state s.
Proof. intros Hv _. exact Hv. Qed.

End GuardianValidity.
