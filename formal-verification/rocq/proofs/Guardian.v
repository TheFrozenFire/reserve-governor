(** Guardian simulation invariant proofs.

    Headline lemmas (mirroring CAS INV-1..INV-6):

      INV-1   cancel_requires_authorization : [cancel] succeeds only
              when the caller holds admin or guardian role.

      INV-1b  cancel_admin_unrestricted : an admin caller bypasses the
              optimistic / defeated checks — every governor input that
              has code lets the admin reach the inner cancel.

      INV-1c  cancel_guardian_requires_optimistic_and_not_defeated :
              a non-admin guardian caller can only reach the inner
              cancel when [is_optimistic_oracle pid = true] AND
              [proposal_state_oracle pid <> PSDefeated].

      INV-2   grant_requires_manager : [grantOptimisticGuardian]
              succeeds only when the caller holds
              OPTIMISTIC_GUARDIAN_MANAGER_ROLE.

      INV-2b  grant_inserts_account : a successful grant places
              [account] into the guardian set and does not touch the
              admin / manager sets.

      INV-3   revoke_proposer_requires_admin : [revokeOptimisticProposer]
              succeeds only when the caller holds DEFAULT_ADMIN_ROLE.

      INV-3b  revoke_proposer_validates_governor_and_timelock :
              [revokeOptimisticProposer] reverts when the governor or
              its timelock has no code.

      INV-4   add_role_monotone : [add_role] never removes any
              existing member.

      INV-4b  add_role_idempotent : [add_role lst a = add_role
              (add_role lst a) a].

      INV-5   grant_rejects_zero : grant with account = 0 reverts.

      INV-6   admin_cancel_succeeds_on_defeated_pessimistic : the
              two-tier behaviour exhibited by the CAS INV-6 probe.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Guardian.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module GuardianProofs.

Import Guardian.

(** ----- INV-1: cancel requires admin OR guardian. ----- *)
Lemma cancel_requires_authorization
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller : Address) (governor : Address) (key : ProposalKey.t)
    (ev : CancelEvent.t) :
  cancel s io ps gpi hc caller governor key = Result.Success ev ->
  has_admin s caller = true \/ has_guardian s caller = true.
Proof.
  intros Hok. unfold cancel in Hok.
  destruct (negb (has_admin s caller || has_guardian s caller)) eqn:Hauth;
    [discriminate|].
  apply negb_false_iff in Hauth.
  apply orb_true_iff in Hauth. exact Hauth.
Qed.

(** ----- INV-1b: admin path bypasses optimistic / defeated checks. -----

    For an admin caller, the only obstacles are the governor's
    code-validity gates; the inner cancel proceeds regardless of the
    proposal's state or optimistic-ness. *)
Lemma cancel_admin_unrestricted
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller : Address) (governor : Address) (key : ProposalKey.t) :
  has_admin s caller = true ->
  governor <> 0 ->
  hc governor = true ->
  cancel s io ps gpi hc caller governor key
    = Result.Success {|
        CancelEvent.governor   := governor;
        CancelEvent.proposalId := gpi key;
      |}.
Proof.
  intros Hadm Hg Hhc.
  unfold cancel.
  rewrite Hadm. simpl.
  assert (Hgb : (governor =? 0) = false).
  { apply Z.eqb_neq. exact Hg. }
  rewrite Hgb.
  rewrite Hhc. simpl.
  reflexivity.
Qed.

(** ----- INV-1c: guardian-only caller needs optimistic AND not defeated. -----

    Phrased as a "success decomposition": every successful guardian
    (non-admin) cancel pins down the oracle outcomes that had to hold. *)
Lemma cancel_guardian_path
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller : Address) (governor : Address) (key : ProposalKey.t)
    (ev : CancelEvent.t) :
  has_admin s caller = false ->
  cancel s io ps gpi hc caller governor key = Result.Success ev ->
  has_guardian s caller = true /\
  io (gpi key) = true /\
  ps (gpi key) <> PSDefeated /\
  governor <> 0 /\
  hc governor = true /\
  ev = {|
    CancelEvent.governor   := governor;
    CancelEvent.proposalId := gpi key;
  |}.
Proof.
  intros Hadm Hok. unfold cancel in Hok.
  rewrite Hadm in Hok. simpl in Hok.
  destruct (has_guardian s caller) eqn:Hguard; [|discriminate].
  destruct (governor =? 0) eqn:Hg0; [discriminate|].
  apply Z.eqb_neq in Hg0.
  destruct (hc governor) eqn:Hhc; [|discriminate].
  destruct (io (gpi key)) eqn:Hopt; [|discriminate].
  destruct (ps (gpi key)) eqn:Hps; try discriminate;
    injection Hok as Hev;
    repeat split; try assumption; try discriminate;
    rewrite <- Hev; reflexivity.
Qed.

(** ----- INV-2: grant requires manager role. ----- *)
Lemma grant_requires_manager
    (s s' : State.t) (caller account : Address) :
  grantOptimisticGuardian s caller account = Result.Success s' ->
  has_manager s caller = true.
Proof.
  intros Hok. unfold grantOptimisticGuardian in Hok.
  destruct (has_manager s caller) eqn:Hm; [reflexivity|].
  simpl in Hok. discriminate.
Qed.

(** ----- INV-2b: grant inserts the account into the guardian set; ---
    admin and manager sets stay untouched. ----- *)
Lemma grant_inserts_account
    (s s' : State.t) (caller account : Address) :
  grantOptimisticGuardian s caller account = Result.Success s' ->
  s'.(State.admins)                     = s.(State.admins) /\
  s'.(State.optimisticGuardianManagers) = s.(State.optimisticGuardianManagers) /\
  addr_in s'.(State.optimisticGuardians) account = true.
Proof.
  intros Hok. unfold grantOptimisticGuardian in Hok.
  destruct (negb (has_manager s caller)) eqn:Hm; [discriminate|].
  destruct (account =? 0) eqn:Hz; [discriminate|].
  injection Hok as Hs'. rewrite <- Hs'. simpl.
  repeat split.
  (* Show account is in [add_role lst account]. *)
  unfold add_role.
  destruct (addr_in s.(State.optimisticGuardians) account) eqn:Hin.
  - exact Hin.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** ----- INV-3: revokeOptimisticProposer requires admin. ----- *)
Lemma revoke_proposer_requires_admin
    (s : State.t)
    (tl_or : Address -> Address) (hc : Address -> bool)
    (caller governor account : Address) (ev : RevokeEvent.t) :
  revokeOptimisticProposer s tl_or hc caller governor account = Result.Success ev ->
  has_admin s caller = true.
Proof.
  intros Hok. unfold revokeOptimisticProposer in Hok.
  destruct (has_admin s caller) eqn:Hadm; [reflexivity|].
  simpl in Hok. discriminate.
Qed.

(** ----- INV-3b: revokeOptimisticProposer validates governor & timelock. ----- *)
Lemma revoke_proposer_validates_addresses
    (s : State.t)
    (tl_or : Address -> Address) (hc : Address -> bool)
    (caller governor account : Address) (ev : RevokeEvent.t) :
  revokeOptimisticProposer s tl_or hc caller governor account = Result.Success ev ->
  governor <> 0 /\
  hc governor = true /\
  tl_or governor <> 0 /\
  hc (tl_or governor) = true /\
  ev = {|
    RevokeEvent.timelock := tl_or governor;
    RevokeEvent.account  := account;
  |}.
Proof.
  intros Hok. unfold revokeOptimisticProposer in Hok.
  destruct (negb (has_admin s caller)) eqn:Hadm; [discriminate|].
  destruct (governor =? 0) eqn:Hg0; [discriminate|].
  apply Z.eqb_neq in Hg0.
  destruct (negb (hc governor)) eqn:Hhcg; [discriminate|].
  apply negb_false_iff in Hhcg.
  destruct (tl_or governor =? 0) eqn:Htl0; [discriminate|].
  apply Z.eqb_neq in Htl0.
  destruct (negb (hc (tl_or governor))) eqn:Hhct; [discriminate|].
  apply negb_false_iff in Hhct.
  injection Hok as Hev. rewrite <- Hev.
  repeat split; assumption.
Qed.

(** ----- INV-4: add_role is monotone — every prior member persists. ----- *)
Lemma add_role_preserves_membership
    (lst : list Address) (a x : Address) :
  addr_in lst x = true ->
  addr_in (add_role lst a) x = true.
Proof.
  intros Hin. unfold add_role.
  destruct (addr_in lst a); [exact Hin|].
  simpl.
  destruct (a =? x); [reflexivity|exact Hin].
Qed.

(** ----- INV-4b: add_role is idempotent. ----- *)
Lemma add_role_idempotent (lst : list Address) (a : Address) :
  add_role (add_role lst a) a = add_role lst a.
Proof.
  unfold add_role.
  destruct (addr_in lst a) eqn:Hin.
  - rewrite Hin. reflexivity.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** add_role inserts: account is in the post-state regardless of
    initial membership. *)
Lemma add_role_inserts (lst : list Address) (a : Address) :
  addr_in (add_role lst a) a = true.
Proof.
  unfold add_role.
  destruct (addr_in lst a) eqn:Hin.
  - exact Hin.
  - simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(** ----- INV-5: grant rejects zero address. ----- *)
Lemma grant_rejects_zero (s : State.t) (caller : Address) :
  has_manager s caller = true ->
  grantOptimisticGuardian s caller 0 = revert_zero_address.
Proof.
  intros Hm. unfold grantOptimisticGuardian.
  rewrite Hm. simpl. reflexivity.
Qed.

(** ----- INV-6: admin can cancel a Defeated proposal (where a
    guardian-only caller cannot). This is the headline two-tier
    behaviour that motivates the role split. ----- *)
Lemma admin_cancel_succeeds_on_defeated
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller governor : Address) (key : ProposalKey.t) :
  has_admin s caller = true ->
  governor <> 0 ->
  hc governor = true ->
  ps (gpi key) = PSDefeated ->
  cancel s io ps gpi hc caller governor key
    = Result.Success {|
        CancelEvent.governor   := governor;
        CancelEvent.proposalId := gpi key;
      |}.
Proof.
  intros Hadm Hg Hhc _.
  apply cancel_admin_unrestricted; assumption.
Qed.

Lemma guardian_only_cancel_reverts_on_defeated
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller governor : Address) (key : ProposalKey.t) :
  has_admin s caller = false ->
  has_guardian s caller = true ->
  governor <> 0 ->
  hc governor = true ->
  io (gpi key) = true ->
  ps (gpi key) = PSDefeated ->
  cancel s io ps gpi hc caller governor key = revert_defeated.
Proof.
  intros Hadm Hguard Hg Hhc Hopt Hdef.
  unfold cancel.
  rewrite Hadm, Hguard. simpl.
  assert (Hgb : (governor =? 0) = false) by (apply Z.eqb_neq; exact Hg).
  rewrite Hgb.
  rewrite Hhc. simpl.
  rewrite Hopt. simpl.
  rewrite Hdef. reflexivity.
Qed.

(** Bonus: an unauthorized caller (neither admin nor guardian) is
    refused — even before the governor-validity gates fire. *)
Lemma cancel_unauthorized
    (s : State.t)
    (io : ProposalId -> bool) (ps : ProposalId -> ProposalState)
    (gpi : ProposalKey.t -> ProposalId) (hc : Address -> bool)
    (caller governor : Address) (key : ProposalKey.t) :
  has_admin s caller = false ->
  has_guardian s caller = false ->
  cancel s io ps gpi hc caller governor key = revert_unauthorized.
Proof.
  intros Hadm Hg. unfold cancel.
  rewrite Hadm, Hg. simpl. reflexivity.
Qed.

(** A non-manager grant call always reverts. *)
Lemma grant_non_manager_reverts
    (s : State.t) (caller account : Address) :
  has_manager s caller = false ->
  grantOptimisticGuardian s caller account = revert_missing_manager.
Proof.
  intros Hm. unfold grantOptimisticGuardian.
  rewrite Hm. simpl. reflexivity.
Qed.

(** A non-admin revoke call always reverts. *)
Lemma revoke_non_admin_reverts
    (s : State.t) (tl_or : Address -> Address) (hc : Address -> bool)
    (caller governor account : Address) :
  has_admin s caller = false ->
  revokeOptimisticProposer s tl_or hc caller governor account
    = revert_missing_admin.
Proof.
  intros Hadm. unfold revokeOptimisticProposer.
  rewrite Hadm. simpl. reflexivity.
Qed.

End GuardianProofs.
