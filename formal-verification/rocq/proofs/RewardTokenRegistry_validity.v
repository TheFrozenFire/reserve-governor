(** RewardTokenRegistry validity preservation.

    Storage-level invariant the contract maintains (see
    [RewardTokenRegistry.Valid.state]):

      tokens_nd : NoDup on the registered-tokens list.

    [registerRewardToken] and [unregisterRewardToken] are the only
    state-mutating operations. We show each preserves [Valid.state]:

      registerRewardToken_preserves_validity
      unregisterRewardToken_preserves_validity

    Plus:
      empty_state_valid — initial state vacuously satisfies NoDup.

    This file is structurally simpler than the analogous
    [SelectorRegistry_validity] because RewardTokenRegistry has a single
    set with no cross-invariant: there's no per-target map to keep in
    sync, no pruning discipline, just NoDup on one list. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.RewardTokenRegistry.
Require Import ReserveGovernor.proofs.RewardTokenRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module RewardTokenRegistryValidity.

Import ReserveGovernor.simulations.RewardTokenRegistry.
Import RewardTokenRegistry.
Import RewardTokenRegistry.Valid.
Import RewardTokenRegistryProofs.

(** ============================================================
    Section: list_remove preserves NoDup.
    ============================================================ *)

Lemma list_remove_subset (xs : list U256.t) (x y : U256.t) :
  In y (list_remove xs x) -> In y xs.
Proof.
  induction xs as [|z rest IH]; simpl.
  - intros [].
  - destruct (z =? x) eqn:Hzx.
    + intros Hin. right. apply IH. exact Hin.
    + intros [Heq | Hin]; [left; exact Heq | right; apply IH; exact Hin].
Qed.

Lemma NoDup_list_remove (xs : list U256.t) (x : U256.t) :
  NoDup xs -> NoDup (list_remove xs x).
Proof.
  induction 1 as [|y rest Hni Hnd IH]; simpl.
  - constructor.
  - destruct (y =? x) eqn:Hyx.
    + exact IH.
    + constructor; [|exact IH].
      intros Hin. apply Hni. apply list_remove_subset in Hin. exact Hin.
Qed.

(** ============================================================
    Section: empty_state validity.
    ============================================================ *)

Lemma empty_state_valid : Valid.state empty_state.
Proof.
  constructor.
  unfold no_dup_tokens. simpl. apply NoDup_nil.
Qed.

(** ============================================================
    Section: validity preservation for registerRewardToken.
    ============================================================ *)

Lemma registerRewardToken_preserves_validity
    (s s' : State.t) (token : Address) (is_owner : bool) :
  Valid.state s ->
  registerRewardToken s token is_owner = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hnd].
  unfold no_dup_tokens in Hnd.
  unfold registerRewardToken in Hok.
  destruct is_owner; simpl in Hok; [|discriminate].
  destruct (token =? zero_address) eqn:Hz; [discriminate|].
  destruct (list_contains s.(State.rewardTokens) token) eqn:Hin; [discriminate|].
  injection Hok as Hs'. rewrite <- Hs'.
  constructor. unfold no_dup_tokens. simpl.
  apply NoDup_cons; [|exact Hnd].
  apply list_contains_false_iff. exact Hin.
Qed.

(** ============================================================
    Section: validity preservation for unregisterRewardToken.
    ============================================================ *)

Lemma unregisterRewardToken_preserves_validity
    (s s' : State.t) (token : Address) (is_owner_or_council : bool) :
  Valid.state s ->
  unregisterRewardToken s token is_owner_or_council = Result.Success s' ->
  Valid.state s'.
Proof.
  intros Hv Hok.
  destruct Hv as [Hnd].
  unfold no_dup_tokens in Hnd.
  unfold unregisterRewardToken in Hok.
  destruct is_owner_or_council; simpl in Hok; [|discriminate].
  destruct (list_contains s.(State.rewardTokens) token) eqn:Hin; [|discriminate].
  injection Hok as Hs'. rewrite <- Hs'.
  constructor. unfold no_dup_tokens. simpl.
  apply NoDup_list_remove. exact Hnd.
Qed.

End RewardTokenRegistryValidity.
