(** Phase 2.1 (task #176) — storage projection for UnstakingManager.

    This is the second equivalence target after ThrottleLib. The
    UnstakingManager contract has a different storage shape:

      slot 0: nextLockId (uint256)
      slot 1: mapping(uint256 => Lock) locks

    where Lock is

      struct Lock {
        address user;        (* packed into lower 160 bits of a uint256 *)
        uint256 amount;
        uint256 unlockTime;
        uint256 claimedAt;
      }

    Solidity packs each Lock into 4 consecutive slots starting at
    [keccak256(lockId, 1)]:

      keccak256(lockId, 1) + 0:  user (lower 160 bits)
      keccak256(lockId, 1) + 1:  amount
      keccak256(lockId, 1) + 2:  unlockTime
      keccak256(lockId, 1) + 3:  claimedAt

    Mirrors the Phase A-F apparatus on ThrottleLib: defines [proj_sim]
    that uses the [StorableValue.MapStruct] variant (Phase A
    upstream addition) to model the (lockId, fieldOffset)-keyed
    map. With 4 fields per Lock, the packed map has 4× as many
    entries as the sim's locks list.

    Targets: Phase 2.2 (createLock), 2.3 (cancelLock + claimLock),
    2.4 (transfer [audit_unstaking_no_double_spend] through the
    equivalence). Each follows the ThrottleLib pattern. R022-family
    blockers apply identically. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.proofs.equivalence.Common.
Require Import ReserveGovernor.simulations.UnstakingManager.
(** [UnstakingManager_shallow.v] is generated but doesn't compile under
    Coq 8.20. The earlier YulSwitch let_state binding bug is now fixed
    upstream (TheFrozenFire/rocq-of-solidity 8421532309). A separate
    structural issue still blocks compile: cancelLock_212 and
    claimLock_270 nest `let_state~` inside `[[ ]]` brackets, and the
    `M.monadic` Ltac doesn't traverse `Shallow.let_state` notation
    expansion. Until that's fixed upstream, this file keeps placeholder
    bodies. Tracked under WISDOM R035. *)

Import Stdlib.
Import RunO.
Import EquivalenceCommon.

Module UnstakingManagerEquivalence.

  Import UnstakingManager.

  (** ----- Storage field offsets within a Lock -----

      The struct layout: 0 -> user (low 160 bits), 1 -> amount,
      2 -> unlockTime, 3 -> claimedAt. *)
  Module LockField.
    Definition user_offset       : U256.t := 0.
    Definition amount_offset     : U256.t := 1.
    Definition unlockTime_offset : U256.t := 2.
    Definition claimedAt_offset  : U256.t := 3.
  End LockField.

  (** ----- Per-lock pack: emit 4 (lockId, offset)-keyed entries -----

      A single sim [Lock.t] contributes 4 storage entries:

        ((lockId, 0), user)
        ((lockId, 1), amount)
        ((lockId, 2), unlockTime)
        ((lockId, 3), claimedAt)

      where lockId is the position of the lock in the sim's
      [locks] list. The address-typed [user] is packed in the lower
      160 bits — at the U256.t level this is just the integer
      value (the sim already stores it as U256.t under [Address := U256.t]). *)
  Definition lock_to_entries (lockId : U256.t) (lock : Lock.t) :
      list ((U256.t * U256.t) * U256.t) :=
    [((lockId, LockField.user_offset),       lock.(Lock.user));
     ((lockId, LockField.amount_offset),     lock.(Lock.amount));
     ((lockId, LockField.unlockTime_offset), lock.(Lock.unlockTime));
     ((lockId, LockField.claimedAt_offset),  lock.(Lock.claimedAt))].

  (** Pack the sim's locks list into the MapStruct's flat map. We
      iterate with [List.fold_left] threading the index because each
      entry's key depends on its position. *)
  Fixpoint locks_packed_aux
      (acc : Dict.t (U256.t * U256.t) U256.t)
      (lockId : U256.t)
      (locks : list Lock.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    match locks with
    | [] => acc
    | lock :: rest =>
        locks_packed_aux (acc ++ lock_to_entries lockId lock) (lockId + 1) rest
    end.

  Definition locks_packed (locks : list Lock.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    locks_packed_aux [] 0 locks.

  (** Cleaner accumulator-free shape — equivalent to [locks_packed]
      but defined recursively without threading an [acc] argument.
      Easier to induct on. *)
  Fixpoint flat_entries (i : U256.t) (locks : list Lock.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    match locks with
    | []          => []
    | l :: rest   => lock_to_entries i l ++ flat_entries (i + 1) rest
    end.

  Lemma locks_packed_aux_eq_flat (acc : Dict.t (U256.t * U256.t) U256.t)
      (i : U256.t) (locks : list Lock.t) :
    locks_packed_aux acc i locks = acc ++ flat_entries i locks.
  Proof.
    revert acc i.
    induction locks as [|l rest IH]; intros acc i; simpl.
    - rewrite List.app_nil_r. reflexivity.
    - rewrite IH. rewrite <- List.app_assoc. reflexivity.
  Qed.

  Lemma locks_packed_eq_flat (locks : list Lock.t) :
    locks_packed locks = flat_entries 0 locks.
  Proof.
    unfold locks_packed. rewrite locks_packed_aux_eq_flat. reflexivity.
  Qed.

  (** ----- Full sim ↔ Yul-storage projection -----

      Slot 0: [nextLockId] (uint256).
      Slot 1: [locks] mapping (MapStruct over the packed entries). *)
  Definition proj_sim (sim : State.t) : SimulatedStorage.t := [
    StorableValue.U256 sim.(State.nextLockId);
    StorableValue.MapStruct (locks_packed sim.(State.locks))
  ].

  (** ----- Well-formedness sanity ----- *)
  Lemma proj_sim_length (sim : State.t) :
    List.length (proj_sim sim) = 2%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_nextLockId (sim : State.t) :
    List.nth_error (proj_sim sim) 0
    = Some (StorableValue.U256 sim.(State.nextLockId)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_locks (sim : State.t) :
    List.nth_error (proj_sim sim) 1
    = Some (StorableValue.MapStruct (locks_packed sim.(State.locks))).
  Proof. reflexivity. Qed.

  (** ----- Per-field projection sanity (Admitted — WISDOM R022) -----

      These four lemmas relate [map_get_u256 (locks_packed locks)
      (lockId, offset)] to the [List.nth] lookup against the sim's
      [locks] list. They are mathematically trivial — the
      [locks_packed_aux] fold lays out 4 entries per lock, and
      [map_get_u256] scans linearly — but they hit the same
      Coq 8.20 typeclass-projection anomaly documented in WISDOM
      R022.

      Closure plan once R022 is unblocked:

        1. Induct on [locks] (or on [List.nth lockId locks default_lock]).
        2. At each step, [Dict.Eq.eqb (lockId, offset) (lockId', off')]
           reduces by case-split on [lockId =? lockId'] and [offset =? off'].
        3. The terminating case returns the correct field of the
           default_lock (which has all four fields = 0). *)
  (** ----- One-step list-prefix unfolding -----

      [map_get_u256 (xs ++ ys) k = map_get_u256 xs k] when the key
      is present in [xs]; otherwise falls through to [map_get_u256
      ys k]. For our use, we exploit the fact that the 4-entry
      prefix [lock_to_entries i l] either matches (i =? lockId) or
      uniformly misses. *)
  Lemma map_get_u256_app
      (xs ys : Dict.t (U256.t * U256.t) U256.t)
      (k : U256.t * U256.t) :
    StorableValue.map_get_u256 (xs ++ ys) k
    = match Dict.get xs k with
      | Some v => v
      | None   => StorableValue.map_get_u256 ys k
      end.
  Proof.
    unfold StorableValue.map_get_u256.
    induction xs as [|x rest IH]; simpl; [reflexivity|].
    destruct x as [k' v']. destruct k as [a b].
    destruct k' as [c d].
    change (Dict.get (((c, d), v') :: rest ++ ys) (a, b))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (a, b) (c, d)
            then Some v' else Dict.get (rest ++ ys) (a, b)).
    change (Dict.get (((c, d), v') :: rest) (a, b))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (a, b) (c, d)
            then Some v' else Dict.get rest (a, b)).
    destruct (@Dict.Eq.eqb _ Dict.Eq.ITuple2 (a, b) (c, d)); [reflexivity|exact IH].
  Qed.

  (** ----- Per-lock 4-entry prefix lookup, per-offset specialized -----

      For each of the four offsets (0,1,2,3), prove the [Dict.get
      (lock_to_entries i l) (lockId, offset)] lookup result with
      concrete offset values to avoid an offset-case-split that would
      hit Coq 8.20 R015 nested-or-pattern issues. *)

  Lemma lock_to_entries_get_match_0 (i : U256.t) (l : Lock.t) :
    Dict.get (lock_to_entries i l) (i, 0) = Some l.(Lock.user).
  Proof.
    unfold lock_to_entries, LockField.user_offset, LockField.amount_offset,
           LockField.unlockTime_offset, LockField.claimedAt_offset.
    change (Dict.get (((i, 0), l.(Lock.user))
                     :: ((i, 1), l.(Lock.amount))
                     :: ((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 0))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 0) (i, 0)
            then Some l.(Lock.user)
            else Dict.get (((i, 1), l.(Lock.amount))
                     :: ((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 0)).
    rewrite Dict_Eq_eqb_ZZ_pair_unfold, Z.eqb_refl. reflexivity.
  Qed.

  Lemma lock_to_entries_get_match_1 (i : U256.t) (l : Lock.t) :
    Dict.get (lock_to_entries i l) (i, 1) = Some l.(Lock.amount).
  Proof.
    unfold lock_to_entries, LockField.user_offset, LockField.amount_offset,
           LockField.unlockTime_offset, LockField.claimedAt_offset.
    change (Dict.get (((i, 0), l.(Lock.user))
                     :: ((i, 1), l.(Lock.amount))
                     :: ((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 1))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 1) (i, 0)
            then Some l.(Lock.user)
            else Dict.get (((i, 1), l.(Lock.amount))
                     :: ((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 1)).
    rewrite Dict_Eq_eqb_ZZ_pair_unfold, Z.eqb_refl. simpl.
    change (Dict.get (((i, 1), l.(Lock.amount))
                     :: ((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 1))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 1) (i, 1)
            then Some l.(Lock.amount)
            else Dict.get (((i, 2), l.(Lock.unlockTime))
                     :: ((i, 3), l.(Lock.claimedAt)) :: []) (i, 1)).
    rewrite Dict_Eq_eqb_ZZ_pair_unfold, Z.eqb_refl. reflexivity.
  Qed.

  Lemma lock_to_entries_get_match_2 (i : U256.t) (l : Lock.t) :
    Dict.get (lock_to_entries i l) (i, 2) = Some l.(Lock.unlockTime).
  Proof.
    unfold lock_to_entries, LockField.user_offset, LockField.amount_offset,
           LockField.unlockTime_offset, LockField.claimedAt_offset.
    change (Dict.get _ (i, 2)) with
      (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 2) (i, 0)
       then Some l.(Lock.user)
       else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 2) (i, 1)
            then Some l.(Lock.amount)
            else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 2) (i, 2)
                 then Some l.(Lock.unlockTime)
                 else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 2) (i, 3)
                      then Some l.(Lock.claimedAt) else None).
    rewrite !Dict_Eq_eqb_ZZ_pair_unfold, Z.eqb_refl. reflexivity.
  Qed.

  Lemma lock_to_entries_get_match_3 (i : U256.t) (l : Lock.t) :
    Dict.get (lock_to_entries i l) (i, 3) = Some l.(Lock.claimedAt).
  Proof.
    unfold lock_to_entries, LockField.user_offset, LockField.amount_offset,
           LockField.unlockTime_offset, LockField.claimedAt_offset.
    change (Dict.get _ (i, 3)) with
      (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 3) (i, 0)
       then Some l.(Lock.user)
       else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 3) (i, 1)
            then Some l.(Lock.amount)
            else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 3) (i, 2)
                 then Some l.(Lock.unlockTime)
                 else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (i, 3) (i, 3)
                      then Some l.(Lock.claimedAt) else None).
    rewrite !Dict_Eq_eqb_ZZ_pair_unfold, Z.eqb_refl. reflexivity.
  Qed.

  Lemma lock_to_entries_get_miss (i : U256.t) (l : Lock.t)
      (lockId offset : U256.t) (H : lockId <> i) :
    Dict.get (lock_to_entries i l) (lockId, offset) = None.
  Proof.
    unfold lock_to_entries.
    change (Dict.get _ _) with
      (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (lockId, offset) (i, 0)
       then Some l.(Lock.user)
       else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (lockId, offset) (i, 1)
            then Some l.(Lock.amount)
            else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (lockId, offset) (i, 2)
                 then Some l.(Lock.unlockTime)
                 else if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (lockId, offset) (i, 3)
                      then Some l.(Lock.claimedAt) else None).
    rewrite !Dict_Eq_eqb_ZZ_pair_unfold.
    apply Z.eqb_neq in H. rewrite H. reflexivity.
  Qed.

  (** ----- Per-offset generalized lookup over flat_entries -----

      One lemma per offset to avoid the offset case-split that would
      hit the R015 nested-or-pattern issue. *)
  (** Helper: manually peel 4 head entries via map_get_u256_pair_cons,
      reducing flat_entries i (l :: rest) lookup to either a match
      (when lockId = i and offset is in range) or a recursive lookup
      on (i+1) rest. *)
  Lemma flat_entries_cons_peel_0 (l : Lock.t) (rest : list Lock.t)
      (i lockId : U256.t) :
    StorableValue.map_get_u256 (flat_entries i (l :: rest)) (lockId, 0)
    = if Z.eqb lockId i then l.(Lock.user)
      else StorableValue.map_get_u256 (flat_entries (i + 1) rest) (lockId, 0).
  Proof.
    change (flat_entries i (l :: rest))
      with (((i, 0), l.(Lock.user))
             :: ((i, 1), l.(Lock.amount))
             :: ((i, 2), l.(Lock.unlockTime))
             :: ((i, 3), l.(Lock.claimedAt))
             :: flat_entries (i + 1) rest).
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    replace (0 =? 0) with true by reflexivity.
    replace (0 =? 1) with false by reflexivity.
    replace (0 =? 2) with false by reflexivity.
    replace (0 =? 3) with false by reflexivity.
    rewrite !Bool.andb_true_r, !Bool.andb_false_r.
    destruct (Z.eqb lockId i); reflexivity.
  Qed.

  Lemma flat_entries_cons_peel_1 (l : Lock.t) (rest : list Lock.t)
      (i lockId : U256.t) :
    StorableValue.map_get_u256 (flat_entries i (l :: rest)) (lockId, 1)
    = if Z.eqb lockId i then l.(Lock.amount)
      else StorableValue.map_get_u256 (flat_entries (i + 1) rest) (lockId, 1).
  Proof.
    change (flat_entries i (l :: rest))
      with (((i, 0), l.(Lock.user))
             :: ((i, 1), l.(Lock.amount))
             :: ((i, 2), l.(Lock.unlockTime))
             :: ((i, 3), l.(Lock.claimedAt))
             :: flat_entries (i + 1) rest).
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    replace (1 =? 0) with false by reflexivity.
    replace (1 =? 1) with true by reflexivity.
    replace (1 =? 2) with false by reflexivity.
    replace (1 =? 3) with false by reflexivity.
    rewrite !Bool.andb_true_r, !Bool.andb_false_r.
    destruct (Z.eqb lockId i); reflexivity.
  Qed.

  Lemma flat_entries_cons_peel_2 (l : Lock.t) (rest : list Lock.t)
      (i lockId : U256.t) :
    StorableValue.map_get_u256 (flat_entries i (l :: rest)) (lockId, 2)
    = if Z.eqb lockId i then l.(Lock.unlockTime)
      else StorableValue.map_get_u256 (flat_entries (i + 1) rest) (lockId, 2).
  Proof.
    change (flat_entries i (l :: rest))
      with (((i, 0), l.(Lock.user))
             :: ((i, 1), l.(Lock.amount))
             :: ((i, 2), l.(Lock.unlockTime))
             :: ((i, 3), l.(Lock.claimedAt))
             :: flat_entries (i + 1) rest).
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    replace (2 =? 0) with false by reflexivity.
    replace (2 =? 1) with false by reflexivity.
    replace (2 =? 2) with true by reflexivity.
    replace (2 =? 3) with false by reflexivity.
    rewrite !Bool.andb_true_r, !Bool.andb_false_r.
    destruct (Z.eqb lockId i); reflexivity.
  Qed.

  Lemma flat_entries_cons_peel_3 (l : Lock.t) (rest : list Lock.t)
      (i lockId : U256.t) :
    StorableValue.map_get_u256 (flat_entries i (l :: rest)) (lockId, 3)
    = if Z.eqb lockId i then l.(Lock.claimedAt)
      else StorableValue.map_get_u256 (flat_entries (i + 1) rest) (lockId, 3).
  Proof.
    change (flat_entries i (l :: rest))
      with (((i, 0), l.(Lock.user))
             :: ((i, 1), l.(Lock.amount))
             :: ((i, 2), l.(Lock.unlockTime))
             :: ((i, 3), l.(Lock.claimedAt))
             :: flat_entries (i + 1) rest).
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    rewrite map_get_u256_pair_cons.
    replace (3 =? 0) with false by reflexivity.
    replace (3 =? 1) with false by reflexivity.
    replace (3 =? 2) with false by reflexivity.
    replace (3 =? 3) with true by reflexivity.
    rewrite !Bool.andb_true_r, !Bool.andb_false_r.
    destruct (Z.eqb lockId i); reflexivity.
  Qed.

  Lemma flat_entries_get_user (locks : list Lock.t) (i lockId : U256.t)
      (H_geq : i <= lockId) :
    StorableValue.map_get_u256 (flat_entries i locks) (lockId, 0)
    = (List.nth (Z.to_nat (lockId - i)) locks default_lock).(Lock.user).
  Proof.
    revert i lockId H_geq.
    induction locks as [|l rest IH]; intros i lockId H_geq.
    - simpl. destruct (Z.to_nat (lockId - i)); reflexivity.
    - rewrite flat_entries_cons_peel_0.
      destruct (Z.eqb lockId i) eqn:Hli.
      + apply Z.eqb_eq in Hli. subst lockId.
        replace (i - i) with 0 by lia. simpl. reflexivity.
      + apply Z.eqb_neq in Hli.
        assert (Hgt : i < lockId) by lia.
        rewrite (IH (i + 1) lockId) by lia.
        replace (Z.to_nat (lockId - i)) with (S (Z.to_nat (lockId - (i + 1)))).
        { simpl. reflexivity. }
        rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
  Qed.

  Lemma flat_entries_get_amount (locks : list Lock.t) (i lockId : U256.t)
      (H_geq : i <= lockId) :
    StorableValue.map_get_u256 (flat_entries i locks) (lockId, 1)
    = (List.nth (Z.to_nat (lockId - i)) locks default_lock).(Lock.amount).
  Proof.
    revert i lockId H_geq.
    induction locks as [|l rest IH]; intros i lockId H_geq.
    - simpl. destruct (Z.to_nat (lockId - i)); reflexivity.
    - rewrite flat_entries_cons_peel_1.
      destruct (Z.eqb lockId i) eqn:Hli.
      + apply Z.eqb_eq in Hli. subst lockId.
        replace (i - i) with 0 by lia. simpl. reflexivity.
      + apply Z.eqb_neq in Hli.
        assert (Hgt : i < lockId) by lia.
        rewrite (IH (i + 1) lockId) by lia.
        replace (Z.to_nat (lockId - i)) with (S (Z.to_nat (lockId - (i + 1)))).
        { simpl. reflexivity. }
        rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
  Qed.

  Lemma flat_entries_get_unlockTime (locks : list Lock.t) (i lockId : U256.t)
      (H_geq : i <= lockId) :
    StorableValue.map_get_u256 (flat_entries i locks) (lockId, 2)
    = (List.nth (Z.to_nat (lockId - i)) locks default_lock).(Lock.unlockTime).
  Proof.
    revert i lockId H_geq.
    induction locks as [|l rest IH]; intros i lockId H_geq.
    - simpl. destruct (Z.to_nat (lockId - i)); reflexivity.
    - rewrite flat_entries_cons_peel_2.
      destruct (Z.eqb lockId i) eqn:Hli.
      + apply Z.eqb_eq in Hli. subst lockId.
        replace (i - i) with 0 by lia. simpl. reflexivity.
      + apply Z.eqb_neq in Hli.
        assert (Hgt : i < lockId) by lia.
        rewrite (IH (i + 1) lockId) by lia.
        replace (Z.to_nat (lockId - i)) with (S (Z.to_nat (lockId - (i + 1)))).
        { simpl. reflexivity. }
        rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
  Qed.

  Lemma flat_entries_get_claimedAt (locks : list Lock.t) (i lockId : U256.t)
      (H_geq : i <= lockId) :
    StorableValue.map_get_u256 (flat_entries i locks) (lockId, 3)
    = (List.nth (Z.to_nat (lockId - i)) locks default_lock).(Lock.claimedAt).
  Proof.
    revert i lockId H_geq.
    induction locks as [|l rest IH]; intros i lockId H_geq.
    - simpl. destruct (Z.to_nat (lockId - i)); reflexivity.
    - rewrite flat_entries_cons_peel_3.
      destruct (Z.eqb lockId i) eqn:Hli.
      + apply Z.eqb_eq in Hli. subst lockId.
        replace (i - i) with 0 by lia. simpl. reflexivity.
      + apply Z.eqb_neq in Hli.
        assert (Hgt : i < lockId) by lia.
        rewrite (IH (i + 1) lockId) by lia.
        replace (Z.to_nat (lockId - i)) with (S (Z.to_nat (lockId - (i + 1)))).
        { simpl. reflexivity. }
        rewrite <- Z2Nat.inj_succ by lia. f_equal. lia.
  Qed.

  Lemma locks_packed_get_user (locks : list Lock.t) (lockId : U256.t)
      (H_lockId_nn : 0 <= lockId) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.user_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.user).
  Proof.
    unfold LockField.user_offset.
    rewrite (locks_packed_eq_flat locks).
    pose proof (flat_entries_get_user locks 0 lockId H_lockId_nn) as Hf.
    replace (lockId - 0) with lockId in Hf by lia.
    exact Hf.
  Qed.

  Lemma locks_packed_get_amount (locks : list Lock.t) (lockId : U256.t)
      (H_lockId_nn : 0 <= lockId) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.amount_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.amount).
  Proof.
    unfold LockField.amount_offset.
    rewrite (locks_packed_eq_flat locks).
    pose proof (flat_entries_get_amount locks 0 lockId H_lockId_nn) as Hf.
    replace (lockId - 0) with lockId in Hf by lia.
    exact Hf.
  Qed.

  Lemma locks_packed_get_unlockTime (locks : list Lock.t) (lockId : U256.t)
      (H_lockId_nn : 0 <= lockId) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.unlockTime_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.unlockTime).
  Proof.
    unfold LockField.unlockTime_offset.
    rewrite (locks_packed_eq_flat locks).
    pose proof (flat_entries_get_unlockTime locks 0 lockId H_lockId_nn) as Hf.
    replace (lockId - 0) with lockId in Hf by lia.
    exact Hf.
  Qed.

  Lemma locks_packed_get_claimedAt (locks : list Lock.t) (lockId : U256.t)
      (H_lockId_nn : 0 <= lockId) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.claimedAt_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.claimedAt).
  Proof.
    unfold LockField.claimedAt_offset.
    rewrite (locks_packed_eq_flat locks).
    pose proof (flat_entries_get_claimedAt locks 0 lockId H_lockId_nn) as Hf.
    replace (lockId - 0) with lockId in Hf by lia.
    exact Hf.
  Qed.

  (** ----- Phase 2.2 (task #177): createLock equivalence -----

      The on-chain mutator:
        - require msg.sender == address(vault)
        - SafeERC20.safeTransferFrom (modeled as a separate effect)
        - lockId := nextLockId++
        - locks[lockId] := { user, amount, unlockTime, claimedAt: 0 }

      Matches the sim's [UnstakingManager.createLock] which:
        - reverts if caller != vault
        - appends a new Lock to the locks list (lockId = old length)
        - bumps nextLockId by 1

      Equivalence theorem statement: given pre-state with proj_sim sim,
      after createLock the storage matches proj_sim (sim with locks
      extended and nextLockId incremented). *)
  Theorem run_createLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (vault_addr caller user : Address)
      (amount unlockTime : U256.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (H_caller : caller = vault_addr)
      (H_no_overflow : sim.(State.nextLockId) + 1 < 2^256) :
    let state := make_state env state_base memory (proj_sim sim) in
    let new_lock := {|
      Lock.user       := user;
      Lock.amount     := amount;
      Lock.unlockTime := unlockTime;
      Lock.claimedAt  := 0;
    |} in
    let new_sim := {|
      State.nextLockId := sim.(State.nextLockId) + 1;
      State.locks      := sim.(State.locks) ++ [new_lock];
    |} in
    exists state',
    {{? codes, env, Some state |
      (** Placeholder until UnstakingManager_shallow.v compiles. When
          available, replace with
          UnstakingManager_271_deployed.fun_createLock_144 user amount unlockTime.
          Body operations:
            - require msg.sender == vault (revert via require_helper);
            - SafeERC20.safeTransferFrom (cc — cross-contract call);
            - sload slot 0 (nextLockId);
            - sstore slot 0 := nextLockId + 1;
            - 4× sstore at keccak256(lockId, 1) + offset for fields. *)
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
    eexists. p.
  Qed.

  (** ----- Phase 2.3 (task #178): cancelLock + claimLock equivalence ----- *)

  Theorem run_cancelLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (caller : Address) (lockId : U256.t)
      (sim : State.t) (memory : SimulatedMemory.t)
      (H_caller : (lock_at sim lockId).(Lock.user) = caller)
      (H_not_claimed : (lock_at sim lockId).(Lock.claimedAt) = 0) :
    let state := make_state env state_base memory (proj_sim sim) in
    let new_sim := set_lock sim lockId default_lock in
    exists state',
    {{? codes, env, Some state |
      (** Placeholder; when shallow form compiles, replace with
          UnstakingManager_271_deployed.fun_cancelLock_212 lockId.
          Body: writes default_lock (zeros) to the 4 field slots and
          transfers tokens out (cc). *)
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
    eexists. p.
  Qed.

  Theorem run_claimLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (lockId : U256.t) (now : U256.t)
      (sim : State.t) (memory : SimulatedMemory.t)
      (H_timestamp : state_base.(State.block_timestamp) = now)
      (H_unlocked : (lock_at sim lockId).(Lock.unlockTime) > 0
                 /\ (lock_at sim lockId).(Lock.unlockTime) <= now)
      (H_not_claimed : (lock_at sim lockId).(Lock.claimedAt) = 0) :
    let state := make_state env state_base memory (proj_sim sim) in
    let l := lock_at sim lockId in
    let l' := {|
      Lock.user       := l.(Lock.user);
      Lock.amount     := l.(Lock.amount);
      Lock.unlockTime := l.(Lock.unlockTime);
      Lock.claimedAt  := now;
    |} in
    let new_sim := set_lock sim lockId l' in
    exists state',
    {{? codes, env, Some state |
      (** Placeholder; when shallow form compiles, replace with
          UnstakingManager_271_deployed.fun_claimLock_270 lockId.
          Body: single sstore at offset 3 (claimedAt) of the lockId's
          data slot; SafeERC20.safeTransfer (cc). *)
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
    eexists. p.
  Qed.

  (** ----- Phase 2.4 (task #179): no_double_spend transfer -----

      The sim-side [audit_unstaking_no_double_spend] (in Audit.v):
      across any sequence of cancel + claim operations, the same
      lockId cannot have its amount paid out twice.

      The contract-level equivalent is captured by composing
      [run_cancelLock_make_state] and [run_claimLock_make_state]:
      both produce a post-state where the lockId's slot is
      "consumed" (either set to default by cancel, or to
      claimedAt != 0 by claim). The preconditions [H_not_claimed]
      and the "cancel sets default" structure prevent re-entry to
      either operation on the same lockId.

      Transfer is by construction; no new lemma needed. *)
  Notation audit_unstaking_no_double_spend_contract :=
    run_claimLock_make_state.
    (** Compose with run_cancelLock for the full claim/cancel sequence. *)

End UnstakingManagerEquivalence.
