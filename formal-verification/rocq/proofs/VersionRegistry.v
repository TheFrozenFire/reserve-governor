(** VersionRegistry simulation invariant proofs.

    Headline safety lemmas for the [VersionRegistry] simulation:

      INV-1   Append-only history. A successful [registerVersion]
              extends the history by exactly one element. Re-registration
              of the same version reverts.

      INV-2   Latest is monotone. After [registerVersion(s, ..., v)],
              [getLatestVersion] returns the entry just registered.

      INV-3   Deprecation is sticky. Re-deprecation of an already-
              deprecated version reverts AlreadyDeprecated.

      INV-4   Implementation triple integrity. After
              [registerVersion(_, _, v, _, svi, gi, ti)], the call
              [getImplementationsForVersion(version_hash v)] returns
              exactly [(svi, gi, ti)].

      INV-5   Role-gated mutations. [registerVersion] requires
              [is_owner caller]; [deprecateVersion] requires
              [is_owner_or_emergency caller].

    The validity-preservation lemmas live in
    [VersionRegistry_validity.v]; the vm_compute cross-check witnesses
    live in [VersionRegistry_xcheck.v].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.VersionRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Module VersionRegistryProofs.

Import VersionRegistry.

(** ============================================================
    Section: low-level helpers on find_entry / set_nth.
    ============================================================ *)

Lemma set_nth_length {A : Type} (n : nat) (xs : list A) (a : A) :
  length (set_nth n a xs) = length xs.
Proof.
  revert xs. induction n; intros xs; destruct xs; simpl; auto.
Qed.

(** nth_error of (xs ++ [e]) at index (length xs) is Some e. *)
Lemma nth_error_app_last {A : Type} (xs : list A) (e : A) :
  nth_error (xs ++ [e]) (length xs) = Some e.
Proof.
  induction xs as [|x rest IH]; simpl; auto.
Qed.

(** find_entry on [hist ++ [e]] preserves any pre-existing hit. *)
Lemma find_entry_idx_app_some_left :
  forall hist e h i j e',
    find_entry_idx hist h i = Some (j, e') ->
    find_entry_idx (hist ++ [e]) h i = Some (j, e').
Proof.
  induction hist as [|x rest IH]; intros e h i j e' Hf; simpl in *.
  - discriminate.
  - destruct (x.(VersionEntry.versionHash) =? h) eqn:Hx.
    + exact Hf.
    + apply IH. exact Hf.
Qed.

Lemma find_entry_idx_app_none :
  forall hist e h i,
    find_entry_idx hist h i = None ->
    e.(VersionEntry.versionHash) = h ->
    find_entry_idx (hist ++ [e]) h i = Some ((i + length hist)%nat, e).
Proof.
  induction hist as [|x rest IH]; intros e h i Hf Hh; simpl in *.
  - rewrite Hh. rewrite Z.eqb_refl. f_equal. f_equal. lia.
  - destruct (x.(VersionEntry.versionHash) =? h) eqn:Hx; [discriminate|].
    rewrite (IH e h (S i) Hf Hh).
    f_equal. f_equal. lia.
Qed.

(** A find_entry_idx hit gives nth_error agreement at its index. *)
Lemma find_entry_idx_nth :
  forall hist h start i e,
    find_entry_idx hist h start = Some (i, e) ->
    (i >= start)%nat /\
    nth_error hist (i - start) = Some e /\
    e.(VersionEntry.versionHash) = h.
Proof.
  induction hist as [|x rest IH]; intros h start i e Hf; simpl in *.
  - discriminate.
  - destruct (x.(VersionEntry.versionHash) =? h) eqn:Hx.
    + apply Z.eqb_eq in Hx. injection Hf as Hi Hxe. subst i e.
      replace (start - start)%nat with 0%nat by lia.
      simpl. repeat split; auto; lia.
    + apply IH in Hf as (Hge & Hnth & Hh).
      split; [lia | split].
      * replace (i - start)%nat with (S (i - S start)) by lia.
        simpl. exact Hnth.
      * exact Hh.
Qed.

Lemma find_entry_nth :
  forall s h i e,
    find_entry s h = Some (i, e) ->
    nth_error s.(State.history) i = Some e /\
    e.(VersionEntry.versionHash) = h.
Proof.
  intros s h i e Hf. unfold find_entry in Hf.
  apply find_entry_idx_nth in Hf as (_ & Hnth & Hh).
  replace (i - 0)%nat with i in Hnth by lia.
  auto.
Qed.

(** find_entry_idx is the first-hit walker: every prior position has
    a non-matching hash. *)
Lemma find_entry_idx_first_hit :
  forall hist h start i e,
    find_entry_idx hist h start = Some (i, e) ->
    forall j x,
      (start <= j < i)%nat ->
      nth_error hist (j - start) = Some x ->
      x.(VersionEntry.versionHash) <> h.
Proof.
  induction hist as [|y rest IH]; intros h start i e Hf j x Hrange Hnth;
    simpl in *.
  - destruct (j - start)%nat; simpl in Hnth; discriminate.
  - destruct (y.(VersionEntry.versionHash) =? h) eqn:Hy.
    + injection Hf as -> ->. lia.
    + apply Z.eqb_neq in Hy.
      destruct (Nat.eq_dec j start) as [-> | Hjs].
      * replace (start - start)%nat with 0%nat in Hnth by lia.
        simpl in Hnth. injection Hnth as ->. exact Hy.
      * assert (Hsub : (j - start = S (j - S start))%nat) by lia.
        rewrite Hsub in Hnth. simpl in Hnth.
        eapply IH; [exact Hf | | exact Hnth]. lia.
Qed.

(** ============================================================
    Section: INV-5 — role-gated mutations.
    ============================================================ *)

Lemma registerVersion_requires_owner :
  forall s caller v deployer svi gi ti,
    is_owner caller = false ->
    registerVersion s caller v deployer svi gi ti = revert_invalid_caller.
Proof.
  intros s caller v deployer svi gi ti Hno.
  unfold registerVersion. rewrite Hno. simpl. reflexivity.
Qed.

Lemma deprecateVersion_requires_role :
  forall s caller h,
    is_owner_or_emergency caller = false ->
    deprecateVersion s caller h = revert_invalid_caller.
Proof.
  intros s caller h Hno.
  unfold deprecateVersion. rewrite Hno. simpl. reflexivity.
Qed.

Lemma registerVersion_success_caller_owner :
  forall s caller v deployer svi gi ti s',
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    is_owner caller = true.
Proof.
  intros s caller v deployer svi gi ti s' Hok.
  unfold registerVersion in Hok.
  destruct (is_owner caller) eqn:Hown; [reflexivity|].
  simpl in Hok. discriminate.
Qed.

Lemma deprecateVersion_success_caller_role :
  forall s caller h s',
    deprecateVersion s caller h = Result.Success s' ->
    is_owner_or_emergency caller = true.
Proof.
  intros s caller h s' Hok.
  unfold deprecateVersion in Hok.
  destruct (is_owner_or_emergency caller) eqn:Hrole; [reflexivity|].
  simpl in Hok. discriminate.
Qed.

(** ============================================================
    Section: INV-1 — append-only history.
    ============================================================ *)

Lemma registerVersion_extends_history :
  forall s caller v deployer svi gi ti s',
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    exists e,
      s'.(State.history) = s.(State.history) ++ [e] /\
      e.(VersionEntry.versionHash)      = version_hash v /\
      e.(VersionEntry.version)          = v /\
      e.(VersionEntry.deployer)         = deployer /\
      e.(VersionEntry.stakingVaultImpl) = svi /\
      e.(VersionEntry.governorImpl)     = gi /\
      e.(VersionEntry.timelockImpl)     = ti /\
      e.(VersionEntry.deprecated)       = false.
Proof.
  intros s caller v deployer svi gi ti s' Hok.
  unfold registerVersion in Hok.
  destruct (is_owner caller) eqn:Hown; [|simpl in Hok; discriminate].
  destruct (deployer =? zero_address) eqn:Hdep; [discriminate|].
  destruct (find_entry s (version_hash v)) eqn:Hpre; [discriminate|].
  injection Hok as <-.
  simpl. eexists. repeat split; reflexivity.
Qed.

Lemma registerVersion_reregister_reverts :
  forall s caller1 caller2 v deployer1 deployer2 svi1 gi1 ti1 svi2 gi2 ti2 s',
    registerVersion s caller1 v deployer1 svi1 gi1 ti1 = Result.Success s' ->
    deployer2 <> zero_address ->
    is_owner caller2 = true ->
    registerVersion s' caller2 v deployer2 svi2 gi2 ti2 = revert_invalid_registration.
Proof.
  intros s c1 c2 v d1 d2 svi1 gi1 ti1 svi2 gi2 ti2 s' Hok Hd2 Hown2.
  unfold registerVersion at 1.
  rewrite Hown2. simpl.
  assert (Hd2b : (d2 =? zero_address) = false).
  { unfold zero_address. apply Z.eqb_neq. exact Hd2. }
  rewrite Hd2b. simpl.
  pose proof (registerVersion_extends_history _ _ _ _ _ _ _ _ Hok) as
       (e & Hhist & Hh & _ & _ & _ & _ & _ & _).
  unfold find_entry. rewrite Hhist.
  unfold registerVersion in Hok.
  destruct (is_owner c1) eqn:Hc1; [|simpl in Hok; discriminate].
  destruct (d1 =? zero_address) eqn:Hd1; [discriminate|].
  destruct (find_entry s (version_hash v)) eqn:Hpre; [discriminate|].
  unfold find_entry in Hpre.
  rewrite (find_entry_idx_app_none _ _ _ _ Hpre Hh).
  reflexivity.
Qed.

(** ============================================================
    Section: INV-2 — getLatestVersion returns the latest entry.
    ============================================================ *)

Lemma registerVersion_getLatestVersion :
  forall s caller v deployer svi gi ti s',
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    exists lv,
      getLatestVersion s' = Result.Success lv /\
      lv.(LatestView.versionHash) = version_hash v /\
      lv.(LatestView.version)     = v /\
      lv.(LatestView.deployer)    = deployer /\
      lv.(LatestView.deprecated)  = false.
Proof.
  intros s caller v deployer svi gi ti s' Hok.
  unfold registerVersion in Hok.
  destruct (is_owner caller) eqn:Hown; [|simpl in Hok; discriminate].
  destruct (deployer =? zero_address) eqn:Hdep; [discriminate|].
  destruct (find_entry s (version_hash v)) eqn:Hpre; [discriminate|].
  injection Hok as <-.
  unfold getLatestVersion. simpl.
  rewrite nth_error_app_last.
  eexists. repeat split; reflexivity.
Qed.

(** Empty state: getLatestVersion reverts NotConfigured. *)
Lemma getLatestVersion_empty_reverts :
  getLatestVersion empty_state = revert_not_configured.
Proof. reflexivity. Qed.

(** ============================================================
    Section: INV-4 — implementation triple at register.
    ============================================================ *)

Lemma registerVersion_impl_triple :
  forall s caller v deployer svi gi ti s',
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    getImplementationsForVersion s' (version_hash v) =
      Some {| ImplTriple.stakingVaultImpl := svi;
              ImplTriple.governorImpl     := gi;
              ImplTriple.timelockImpl     := ti; |}.
Proof.
  intros s caller v deployer svi gi ti s' Hok.
  unfold registerVersion in Hok.
  destruct (is_owner caller) eqn:Hown; [|simpl in Hok; discriminate].
  destruct (deployer =? zero_address) eqn:Hdep; [discriminate|].
  destruct (find_entry s (version_hash v)) eqn:Hpre; [discriminate|].
  injection Hok as <-.
  unfold getImplementationsForVersion, entry_for_hash, find_entry.
  simpl.
  unfold find_entry in Hpre.
  set (e := {|
    VersionEntry.versionHash      := version_hash v;
    VersionEntry.version          := v;
    VersionEntry.deployer         := deployer;
    VersionEntry.stakingVaultImpl := svi;
    VersionEntry.governorImpl     := gi;
    VersionEntry.timelockImpl     := ti;
    VersionEntry.deprecated       := false;
  |}).
  assert (He_hash : e.(VersionEntry.versionHash) = version_hash v) by reflexivity.
  rewrite (find_entry_idx_app_none _ e _ _ Hpre He_hash).
  reflexivity.
Qed.

(** ============================================================
    Section: INV-3 — deprecation is sticky.
    ============================================================ *)

(** find_entry on the deprecate_at state returns the in-place-updated
    entry at the same index. *)
Lemma find_entry_after_deprecate :
  forall s h i e,
    find_entry s h = Some (i, e) ->
    exists e',
      find_entry (deprecate_at s i) h = Some (i, e') /\
      e'.(VersionEntry.versionHash) = h /\
      e'.(VersionEntry.deprecated)  = true.
Proof.
  intros s h i e Hfind.
  pose proof (find_entry_nth _ _ _ _ Hfind) as (Hnth_e & Hh).
  unfold deprecate_at. rewrite Hnth_e. simpl.
  set (e' := {|
    VersionEntry.versionHash      := e.(VersionEntry.versionHash);
    VersionEntry.version          := e.(VersionEntry.version);
    VersionEntry.deployer         := e.(VersionEntry.deployer);
    VersionEntry.stakingVaultImpl := e.(VersionEntry.stakingVaultImpl);
    VersionEntry.governorImpl     := e.(VersionEntry.governorImpl);
    VersionEntry.timelockImpl     := e.(VersionEntry.timelockImpl);
    VersionEntry.deprecated       := true;
  |}).
  unfold find_entry.
  assert (Hwalk :
    forall hist start j,
      (j < length hist)%nat ->
      nth_error hist j = Some e ->
      (forall k x, (k < j)%nat -> nth_error hist k = Some x ->
                    x.(VersionEntry.versionHash) <> h) ->
      find_entry_idx (set_nth j e' hist) h start = Some ((start + j)%nat, e')).
  { clear Hnth_e Hfind.
    induction hist as [|y rest IHh]; intros start j Hlen Hnth Hpref; simpl in *.
    - lia.
    - destruct j as [|j'].
      + cbn. rewrite Hh. rewrite Z.eqb_refl. f_equal. f_equal. lia.
      + cbn.
        assert (Hy_ne : y.(VersionEntry.versionHash) <> h).
        { apply (Hpref 0%nat y); [lia | reflexivity]. }
        assert (Hy_b : (y.(VersionEntry.versionHash) =? h) = false).
        { apply Z.eqb_neq. exact Hy_ne. }
        rewrite Hy_b.
        replace (start + S j')%nat with (S start + j')%nat by lia.
        apply IHh.
        * simpl in Hlen. lia.
        * simpl in Hnth. exact Hnth.
        * intros k x Hk Hnk.
          apply (Hpref (S k) x); [lia | exact Hnk]. }
  exists e'. split; [|split].
  - replace i with (0 + i)%nat at 2 by lia.
    apply Hwalk.
    + apply nth_error_Some. rewrite Hnth_e. discriminate.
    + exact Hnth_e.
    + intros k x Hk Hnk.
      pose proof (find_entry_idx_first_hit _ _ _ _ _ Hfind k x) as Hne.
      apply Hne; [lia|].
      replace (k - 0)%nat with k by lia. exact Hnk.
  - unfold e'. simpl. exact Hh.
  - unfold e'. simpl. reflexivity.
Qed.

(** ----- INV-3 headline: deprecation is sticky. ----- *)
Theorem deprecateVersion_sticky :
  forall s caller1 caller2 h s',
    is_owner_or_emergency caller1 = true ->
    is_owner_or_emergency caller2 = true ->
    (exists i e, find_entry s h = Some (i, e)) ->
    deprecateVersion s caller1 h = Result.Success s' ->
    deprecateVersion s' caller2 h = revert_already_deprecated.
Proof.
  intros s c1 c2 h s' Hr1 Hr2 (i & e & Hfind) Hok.
  unfold deprecateVersion in Hok.
  rewrite Hr1 in Hok. simpl in Hok.
  rewrite Hfind in Hok.
  destruct (e.(VersionEntry.deprecated)) eqn:Hdep; [discriminate|].
  injection Hok as <-.
  pose proof (find_entry_after_deprecate _ _ _ _ Hfind)
       as (e' & Hf' & _ & Hdep_true).
  unfold deprecateVersion. rewrite Hr2. simpl.
  rewrite Hf'. rewrite Hdep_true. reflexivity.
Qed.

End VersionRegistryProofs.
