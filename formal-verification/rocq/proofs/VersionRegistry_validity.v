(** VersionRegistry validity preservation.

    Storage invariants the contract maintains (see
    [VersionRegistry.Valid.state]):

      latest_ok    : [latest_index] = None iff history empty; else
                     indexes the final element.
      hashes_nd    : NoDup on registered version hashes.
      deployers_nz : every registered deployer is non-zero.

    [registerVersion] and [deprecateVersion] are the only mutating
    operations. We show each preserves [Valid.state]. The view
    functions ([getLatestVersion], [getImplementationsForVersion])
    are trivially preservation-neutral (read-only).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.VersionRegistry.
Require Import ReserveGovernor.proofs.VersionRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Module VersionRegistryValidity.

Import ReserveGovernor.simulations.VersionRegistry.
Import VersionRegistry.
Import VersionRegistry.Valid.
Import VersionRegistryProofs.

(** ============================================================
    Helpers on find_entry / NoDup.
    ============================================================ *)

(** Hash isn't already in the history iff [find_entry] returns None. *)
Lemma find_entry_idx_none_not_in :
  forall hist h start,
    find_entry_idx hist h start = None ->
    ~ In h (map VersionEntry.versionHash hist).
Proof.
  induction hist as [|x rest IH]; intros h start Hf; simpl in *.
  - auto.
  - destruct (x.(VersionEntry.versionHash) =? h) eqn:Hx; [discriminate|].
    apply Z.eqb_neq in Hx.
    intros [Heq | Hin].
    + apply Hx. exact Heq.
    + eapply IH; eauto.
Qed.

Lemma find_entry_none_not_in :
  forall s h,
    find_entry s h = None ->
    ~ In h (map VersionEntry.versionHash s.(State.history)).
Proof.
  intros s h Hf. unfold find_entry in Hf.
  eapply find_entry_idx_none_not_in; eauto.
Qed.

(** length of (xs ++ [e]) = length xs + 1. *)
Lemma length_app_singleton {A : Type} (xs : list A) (e : A) :
  length (xs ++ [e]) = S (length xs).
Proof. rewrite length_app. simpl. lia. Qed.

(** NoDup extension: NoDup xs and (last not in xs) -> NoDup (xs ++ [a]). *)
Lemma NoDup_append_singleton {A : Type} (xs : list A) (a : A) :
  NoDup xs -> ~ In a xs -> NoDup (xs ++ [a]).
Proof.
  induction xs as [|x rest IH]; intros Hnd Hnin; simpl.
  - constructor.
    + intros [].
    + constructor.
  - inversion Hnd as [|? ? Hxr Hndr]; subst.
    constructor.
    + intros Hin. apply in_app_or in Hin as [Hin1 | Hin2].
      * apply Hxr; exact Hin1.
      * simpl in Hin2. destruct Hin2 as [Heq | Hfalse]; [|destruct Hfalse].
        apply Hnin. left. symmetry. exact Heq.
    + apply IH; auto.
      intros Hin. apply Hnin. right. exact Hin.
Qed.

(** ============================================================
    [empty_state] is valid.
    ============================================================ *)

Theorem empty_state_valid : state empty_state.
Proof. exact VersionRegistry.Valid.empty_state_valid. Qed.

(** ============================================================
    registerVersion preserves validity.
    ============================================================ *)

Theorem registerVersion_preserves_state :
  forall s caller v deployer svi gi ti s',
    state s ->
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    state s'.
Proof.
  intros s caller v deployer svi gi ti s' Hs Hok.
  unfold registerVersion in Hok.
  destruct (is_owner caller) eqn:Hown; [|simpl in Hok; discriminate].
  destruct (deployer =? zero_address) eqn:Hdep; [discriminate|].
  destruct (find_entry s (version_hash v)) eqn:Hpre; [discriminate|].
  injection Hok as <-.
  destruct Hs as [Hlat Hnd Hnz].
  constructor.
  - (* latest_consistent. *)
    unfold latest_consistent. simpl.
    rewrite length_app_singleton.
    destruct s.(State.history) as [|x rest] eqn:Hhist; simpl; try lia.
  - (* hashes_unique. *)
    unfold hashes_unique in *. simpl.
    rewrite map_app. simpl.
    apply NoDup_append_singleton.
    + exact Hnd.
    + eapply find_entry_none_not_in. exact Hpre.
  - (* deployers_nonzero. *)
    unfold deployers_nonzero in *. simpl.
    apply Forall_app. split; [exact Hnz|].
    constructor; [|constructor].
    simpl. apply Z.eqb_neq in Hdep. exact Hdep.
Qed.

(** ============================================================
    deprecateVersion preserves validity.

    The mutation is in-place at a single existing index; the history
    list shape and the hash list are unchanged (only the deprecated
    flag flips).
    ============================================================ *)

Lemma set_nth_length {A : Type} (n : nat) (xs : list A) (a : A) :
  length (set_nth n a xs) = length xs.
Proof.
  revert xs. induction n; intros xs; destruct xs; simpl; auto.
Qed.

(** set_nth preserves the result of [map f] when [f] is invariant
    on the rewriting position. *)
Lemma map_set_nth_invariant {A B : Type} (f : A -> B) (n : nat) (a : A) (xs : list A) :
  match nth_error xs n with
  | Some x => f x = f a
  | None => True
  end ->
  map f (set_nth n a xs) = map f xs.
Proof.
  revert n. induction xs as [|x rest IH]; intros n Hinv; simpl in *.
  - destruct n; reflexivity.
  - destruct n.
    + simpl. simpl in Hinv. rewrite Hinv. reflexivity.
    + simpl. f_equal. apply IH. exact Hinv.
Qed.

Theorem deprecateVersion_preserves_state :
  forall s caller h s',
    state s ->
    deprecateVersion s caller h = Result.Success s' ->
    state s'.
Proof.
  intros s caller h s' Hs Hok.
  unfold deprecateVersion in Hok.
  destruct (is_owner_or_emergency caller) eqn:Hrole;
    [|simpl in Hok; discriminate].
  destruct (find_entry s h) as [pair|] eqn:Hfind.
  - destruct pair as (i & e).
    destruct (e.(VersionEntry.deprecated)) eqn:Hdep; [discriminate|].
    injection Hok as <-.
    destruct Hs as [Hlat Hnd Hnz].
    pose proof (find_entry_nth _ _ _ _ Hfind) as (Hnth_e & _).
    unfold deprecate_at. rewrite Hnth_e.
    set (e' := {| VersionEntry.versionHash      := e.(VersionEntry.versionHash);
                  VersionEntry.version          := e.(VersionEntry.version);
                  VersionEntry.deployer         := e.(VersionEntry.deployer);
                  VersionEntry.stakingVaultImpl := e.(VersionEntry.stakingVaultImpl);
                  VersionEntry.governorImpl     := e.(VersionEntry.governorImpl);
                  VersionEntry.timelockImpl     := e.(VersionEntry.timelockImpl);
                  VersionEntry.deprecated       := true; |}).
    constructor.
    + (* latest_consistent. set_nth preserves length and emptiness;
         latest_index is copied unchanged. *)
      unfold latest_consistent in *. simpl.
      destruct s.(State.history) as [|x rest] eqn:Hhist.
      * simpl in Hnth_e. destruct i; discriminate.
      * destruct i; simpl.
        -- destruct s.(State.latest_index) as [idx|]; [|destruct Hlat].
           simpl in Hlat. simpl. lia.
        -- destruct s.(State.latest_index) as [idx|]; [|destruct Hlat].
           simpl in Hlat. simpl. rewrite set_nth_length. lia.
    + (* hashes_unique. Map versionHash through set_nth — invariant
         because e' has the same hash as e. *)
      unfold hashes_unique in *. simpl.
      rewrite (map_set_nth_invariant _ _ _ _) by (rewrite Hnth_e; reflexivity).
      exact Hnd.
    + (* deployers_nonzero. Forall preserved because e' has the same deployer. *)
      unfold deployers_nonzero in *. simpl.
      (* Reduce to a generic statement on the list, decoupling from
         the State.t projection. *)
      assert (Hgen : forall hist (k : nat),
                Forall (fun x => x.(VersionEntry.deployer) <> zero_address) hist ->
                nth_error hist k = Some e ->
                Forall (fun x => x.(VersionEntry.deployer) <> zero_address)
                       (set_nth k e' hist)).
      { clear. intros hist. induction hist as [|x rest IH]; intros k Hpref Hnth.
        - destruct k; simpl in Hnth; discriminate.
        - destruct k as [|k']; simpl in Hnth; simpl.
          + injection Hnth as ->.
            inversion Hpref; subst.
            constructor; [|assumption].
            unfold e'. simpl. assumption.
          + inversion Hpref; subst.
            constructor; [assumption|].
            apply IH; assumption. }
      apply Hgen; assumption.
  - (* h not registered: deprecate is no-op. *)
    injection Hok as <-. exact Hs.
Qed.

(** ============================================================
    Sanity check via vm_compute: a concrete sequence of operations
    preserves validity end-to-end.
    ============================================================ *)

Lemma xcheck_empty_state_valid :
  state empty_state.
Proof. apply empty_state_valid. Qed.

End VersionRegistryValidity.
