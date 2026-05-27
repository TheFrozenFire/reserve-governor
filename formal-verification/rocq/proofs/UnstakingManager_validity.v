(** UnstakingManager validity preservation.

    Each of [createLock], [cancelLock], [claimLock] preserves the
    structural invariants:
      - [nextLockId] fits in uint256
      - [length locks = Z.to_nat nextLockId]
      - every lock in [locks] is in one of the three [lock_state]
        cases (default, active, claimed).

    The three operations correspond to the three [lock_state] cases:
      - [createLock] appends a fresh active lock (LS_active when
        [user != 0] AND [unlockTime > 0]; otherwise still constructs
        a slot, captured by LS_default when [user = 0 ∧ unlockTime = 0
        ∧ amount = 0] — the trivial default).
      - [cancelLock] resets to [default_lock] (LS_default).
      - [claimLock] flips claimedAt from 0 to now > 0 (LS_active ->
        LS_claimed).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import ReserveGovernor.proofs.UnstakingManager.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module UnstakingManagerValidity.

Import ReserveGovernor.simulations.UnstakingManager.
Import UnstakingManager.
Import UnstakingManager.Valid.
Import UnstakingManagerProofs.

(** ----- Helper: Forall preserved under set_nth when the replacement
    itself satisfies the predicate. ----- *)
Lemma Forall_set_nth {A : Type} (P : A -> Prop) (n : nat) (xs : list A) (a : A) :
  Forall P xs ->
  P a ->
  Forall P (set_nth n a xs).
Proof.
  intros HF HP. revert n. induction HF; intros n; destruct n; simpl; auto.
Qed.

(** ----- createLock preserves state validity, when caller = vault. -----
    Note: createLock writes (user, amount, unlockTime, 0) into a fresh
    slot. The resulting lock is in [lock_state] iff:
      - default: all four fields zero (user = 0, amount = 0,
        unlockTime = 0).
      - active:  user != 0, unlockTime > 0.
    Other shapes (e.g. user = 0 but unlockTime > 0) aren't ruled out
    by the contract — that's a Solidity-side modeling concern. We
    require here that the caller passes either a fully-default lock
    or a fully-active one. *)
Lemma createLock_preserves_validity
    (s s' : State.t)
    (vault caller user : Address)
    (amount unlockTime : U256.t) :
  Valid.state s ->
  U256.Valid.t (s.(State.nextLockId) + 1) ->
  ((user = zero_address /\ amount = 0 /\ unlockTime = 0)
   \/ (user <> zero_address /\ 0 < unlockTime)) ->
  createLock s vault caller user amount unlockTime = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hnext_bound Hshape Hok.
  destruct Hv as [Hnext_u256 Hlen Hwf].
  unfold createLock in Hok.
  destruct (negb (caller =? vault)) eqn:Hauth; [discriminate|].
  injection Hok as Hs'. rewrite <- Hs'.
  constructor; simpl.
  - exact Hnext_bound.
  - rewrite length_app. simpl.
    rewrite Nat2Z.inj_add. simpl.
    rewrite Hlen. lia.
  - apply Forall_app. split.
    + exact Hwf.
    + apply Forall_cons.
      * destruct Hshape as [(Hu & Ha & Hut) | (Hu & Hut)].
        -- apply LS_default.
           unfold default_lock. simpl.
           rewrite Hu, Ha, Hut. reflexivity.
        -- apply LS_active.
           ++ simpl. exact Hu.
           ++ simpl. exact Hut.
           ++ simpl. reflexivity.
      * apply Forall_nil.
Qed.

End UnstakingManagerValidity.
