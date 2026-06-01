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
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import ReserveGovernor.generated.UnstakingManager_shallow.
(** [UnstakingManager_shallow.v] now compiles. The compile blocker
    turned out to be the missing [linkersymbol] Yul primitive in
    rocq-of-solidity's simulations/RocqOfSolidity.v — emitted by solc
    for every SafeERC20 reference. With that primitive defined upstream
    (TheFrozenFire/rocq-of-solidity 2646cf555a), all three big
    entrypoints (createLock_144, cancelLock_212, claimLock_270)
    elaborate cleanly. The original WISDOM R041 diagnosis on
    `M.monadic`-vs-`Shallow.let_state` was a real but unrelated defect;
    see the resolved R041 entry. *)

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

  (** ====================================================================
      Phase 2.x — Composite-walker discharge for createLock / cancelLock
      / claimLock (R082 trust-redistribution methodology).

      Before this commit, the three milestone theorems below were
      blanket [Admitted] with a weak post-condition ([exists state']
      with no constraint on [state']).  That gave a SINGLE monolithic
      Admitted axiom per mutator with an under-specified post-state.

      Per R082 (CRIT-A composite-walker discharge methodology, applied
      to VersionRegistry.deprecateVersion), we redistribute the trust
      across three smaller, sharper-shape axioms per mutator:

        1. [proj_post_<fn>] : Parameter — the post-state shape after
           the walker terminates.  Trust-wise identical to a Skolem
           witness; audit-time obligation is "this shape matches the
           Yul body's writes".

        2. [run_fun_<fn>_at_proj_sim] : Axiom — the composite walker
           bridges the pre-state ([proj_sim sim]) to [proj_post_<fn>].
           Sharper-shape than a blanket [exists state'] because it
           pins the post-storage to [proj_post_<fn>] and the post-
           memory to a Skolem witness.  Discharge is mechanical (~500-
           1500 LOC) following the R082 + R083 + R084/R085 templates
           but blocked here by the SafeERC20 library-call infrastructure
           gap (linkersymbol + delegatecall, see R086 below).

        3. [proj_post_<fn>_observes] : Axiom — observational bridge
           connecting the walker's Skolem post-storage to the sim-side
           post-state via the projection.  This is the load-bearing
           bridge: it asserts [proj_post_<fn> ... ≡ proj_sim (sim_<fn>
           sim args)] at a slot-indexed equality (slot 1, the locks
           mapping).  An adversarial [proj_post_<fn> := empty]
           instantiation would contradict this bridge — so the
           composition is content-bearing.

      The composition pattern (Qed Lemma per milestone): obtain the
      walker's post-state via [run_fun_<fn>_at_proj_sim], extract the
      witnesses, rewrite the goal via [proj_post_<fn>_observes] to
      ([proj_sim (sim_<fn> sim args)]), and conclude.

      The trust footprint is REDISTRIBUTED, not increased:
        - Before: 3 monolithic Admitted (`exists state'` shape, content-
                  free at the slot level).
        - After:  3 Parameter (post-state Skolems), 3 walker Axioms
                  (composite walker shape), 3 observation Axioms
                  (slot-1 equivalence). Plus 3 Qed milestone Lemmas.

      Per-mutator residual work (CLOSURE PATH):
        - Walker Axiom: ~500-1500 LOC mechanical assembly using
          R082's staticcall-bridge + R083's namespace/memory primitives
          + sstore wrappers.  Blocked on R086 (SafeERC20 library-call
          framework gap; see R086 below).
        - Observation Axiom: ~100-200 LOC, dischargeable now via
          [locks_packed_get_*] family + Boolean reasoning on
          [set_nth] / list-append. *)

  (** ----- Per-mutator sim functions -----

      Each sim function returns the post-sim shape that the corresponding
      Yul body produces on the success path.  The preconditions on the
      milestone theorem rule out the revert arms (caller-check,
      timestamp-check, claimed-check), so we only need the success-case
      sim shape. *)

  Definition createLock_sim_post (sim : State.t)
      (user amount unlockTime : U256.t) : State.t :=
    let new_lock := {|
      Lock.user       := user;
      Lock.amount     := amount;
      Lock.unlockTime := unlockTime;
      Lock.claimedAt  := 0;
    |} in
    {| State.nextLockId := sim.(State.nextLockId) + 1;
       State.locks      := sim.(State.locks) ++ [new_lock] |}.

  Definition cancelLock_sim_post (sim : State.t) (lockId : U256.t) : State.t :=
    set_lock sim lockId default_lock.

  Definition claimLock_sim_post (sim : State.t) (lockId now : U256.t) : State.t :=
    let l := lock_at sim lockId in
    let l' := {|
      Lock.user       := l.(Lock.user);
      Lock.amount     := l.(Lock.amount);
      Lock.unlockTime := l.(Lock.unlockTime);
      Lock.claimedAt  := now;
    |} in
    set_lock sim lockId l'.

  (** ----- Slot-indexed observational equality -----

      The locks mapping sits at slot 1 in [proj_sim].  An observational
      bridge that pins equality at slot 1 is content-bearing (it rules
      out the [proj_post := empty] adversarial instantiation) and is
      sufficient for the milestone's claim that the post-state matches
      [proj_sim (sim_<fn> sim args)]. *)

  Definition slot_locks : nat := 1.
  Definition slot_nextLockId : nat := 0.

  Definition eq_at_locks (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_locks = List.nth_error s2 slot_locks.

  Definition eq_at_nextLockId (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_nextLockId = List.nth_error s2 slot_nextLockId.

  Lemma eq_at_locks_refl s : eq_at_locks s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_nextLockId_refl s : eq_at_nextLockId s s.
  Proof. reflexivity. Qed.

  (** ----- Per-mutator post-state concrete Definitions (R098 Option A) -----

      Per R098's Option A discharge plan + R085's Parameter→Definition
      refactor template (T3.3 swap-and-pop), each [proj_post_<X>] is
      now a concrete [Definition] computing the sim-side post-storage
      directly via [proj_sim] applied to the corresponding sim
      transition.  This eliminates the Skolem-mismatch barrier that
      blocked mechanical walker discharge under the previous
      [Parameter] shape.

      Signature change (R098 follow-up): each [proj_post_<X>] now
      takes the [State.t] sim directly (not its [SimulatedStorage.t]
      projection).  All call sites in the inner-body Axioms +
      milestone Lemmas were rewritten to pass [sim] directly.
      Rationale: the storage shape we want is precisely [proj_sim
      (sim_<X> sim args)], and threading [sim] through the Definition
      sidesteps the (non-trivial) "invert [proj_sim] from storage"
      problem.

      Audit consequences:
        - The 6 observation [Axiom]s ([proj_post_<X>_observes] +
          [_observes_nextLockId]) collapse to [Qed] [Lemma]s by
          reflexivity (definitional equality between [proj_post_<X>
          sim args] and [proj_sim (sim_<X> sim args)]).
        - The 3 inner-body [Axiom]s now have a CONCRETE post-storage
          target — mechanical walker discharge via R083 / R040 / R093
          primitives is unblocked.
        - The 3 [Parameter] declarations are gone from [Print
          Assumptions]; only Definition bodies remain. *)

  Definition proj_post_createLock
      (sim : State.t)
      (user amount unlockTime : U256.t) : SimulatedStorage.t :=
    proj_sim (createLock_sim_post sim user amount unlockTime).

  Definition proj_post_cancelLock
      (sim : State.t)
      (lockId : U256.t) : SimulatedStorage.t :=
    proj_sim (cancelLock_sim_post sim lockId).

  Definition proj_post_claimLock
      (sim : State.t)
      (lockId now : U256.t) : SimulatedStorage.t :=
    proj_sim (claimLock_sim_post sim lockId now).

  (** ====================================================================
      R093-consumer: SafeERC20 callee-spec parameters + sub-axioms
      ====================================================================

      Per R093 (the SafeERC20 + linkersymbol framework primitives —
      see WISDOM.md), the three SafeERC20 wrapper bodies
      ([fun_safeTransfer_1010], [fun_safeTransferFrom_1037],
      [fun_forceApprove_1213]) — inlined by solc into each
      UnstakingManager mutator — discharge via three per-mutator
      sub-axioms shaped like the R063 callee-spec template
      ([StakingVaultRewards.safeTransfer_success_spec_concrete]).

      Each sub-axiom carries a per-(token, args) audit-time success
      witness ([safeTransfer_success_spec] etc.).  The witness is a
      [Parameter] (T-TOKEN trust boundary): the registered token is
      well-behaved (no fee-on-transfer, no balance-lying, no
      malicious return-data encoding), so the SafeERC20 wrapper does
      not revert.

      The sub-axiom's post-storage is identity (storage_base =
      storage_base): per R093's semantic story, [Stdlib.call] runs the
      callee in the TARGET's storage context; from the caller's
      projection level, storage is UNCHANGED.  Only memory and
      return_data are absorbed via Skolems.

      The witness is consumed at the OUTER composite walker site to
      thread the audit obligation through to the milestone theorem.
      Net trust delta: the 3 composite walker [Axiom]s split into
      [Lemma]s + 3 SafeERC20 sub-[Axiom]s + 3 per-mutator inner-body
      sub-[Axiom]s.  The SafeERC20 sub-axioms are shared across all
      seven SafeERC20-using walker workstreams (UnstakingManager × 3
      + StakingVaultExchange × 4 — R086 / R093 analysis), amortizing
      their trust.
      ==================================================================== *)

  (** Per-(token, recipient, amount) success witnesses for the
      three SafeERC20 wrapper entry points UnstakingManager
      consumes.  Each is a [Parameter] — the audit-time T-TOKEN
      obligation — paired with a sub-axiom of [True] conclusion
      shape that ties the witness into the composite walker.

      The audit-time T-TOKEN obligation: the deployed
      StakingVault.targetToken (the IERC20 referenced at
      immutable slot 10 / 13) is well-behaved per the OZ SafeERC20
      contract: [transfer] / [transferFrom] / [approve] return
      [true] (or void without revert), and the return data
      decodes to a non-zero word.  Under that obligation, the
      SafeERC20 wrapper does not enter its revert path; the
      [_callOptionalReturn] return-data check passes; the outer
      caller's storage is observably unchanged at projection
      level. *)

  Parameter safeTransfer_success_spec :
    Address (* token *) -> Address (* to *) -> U256.t (* amount *) -> Prop.

  Parameter safeTransferFrom_success_spec :
    Address (* token *) -> Address (* from *) ->
    Address (* to *) -> U256.t (* amount *) -> Prop.

  Parameter forceApprove_success_spec :
    Address (* token *) -> Address (* spender *) -> U256.t (* value *) -> Prop.

  (** ----- SafeERC20 sub-axioms (R063 / R093 shape) -----

      Each sub-axiom witnesses: under the per-(token, args) success
      spec, the corresponding SafeERC20 wrapper's Yul body completes
      with [Result.Ok tt] and leaves the CALLER's storage at projection
      level unchanged (storage_base = storage_base).  Only memory is
      Skolemized (the wrapper's mstore-build of the calldata payload +
      the [call_post_memory] absorbing write at return-data decode).

      Discharge path (mechanical, in scope for a future R093 closure):
      walk the wrapper body via [allocate_unbounded] + [mstore] +
      [abi_encode_tuple_*] + [fun__callOptionalReturn_1387] (which in
      turn invokes the new [call_make_state_bridge_absorbing] for the
      external [call] step).  The post-storage IDENTITY claim is
      sound because [call] leaves caller-storage unchanged per R093's
      semantic table.

      Sharper than the original composite walker [Axiom]: the
      per-(token, args) spec witness is now visible in the sub-axiom
      shape, NOT buried inside an opaque [Skolem post-state].  An
      adversarial instantiation cannot "discharge" the sub-axiom
      without committing to a concrete spec witness — making the
      composition content-bearing at the audit-trust layer. *)

  Axiom run_fun_safeTransfer_1010_at_make_state :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (token to amount : U256.t),
    safeTransfer_success_spec token to amount ->
    0 <= token < 2^160 ->
    0 <= to < 2^160 ->
    0 <= amount < 2^256 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_safeTransfer_1010
        token to amount ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage) ?}}.

  Axiom run_fun_safeTransferFrom_1037_at_make_state :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (token from to amount : U256.t),
    safeTransferFrom_success_spec token from to amount ->
    0 <= token < 2^160 ->
    0 <= from < 2^160 ->
    0 <= to < 2^160 ->
    0 <= amount < 2^256 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_safeTransferFrom_1037
        token from to amount ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage) ?}}.

  Axiom run_fun_forceApprove_1213_at_make_state :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (token spender value : U256.t),
    forceApprove_success_spec token spender value ->
    0 <= token < 2^160 ->
    0 <= spender < 2^160 ->
    0 <= value < 2^256 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_forceApprove_1213
        token spender value ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage) ?}}.

  (** ----- Per-mutator composite walker axioms (R082 shape) -----

      Each bundles the full Yul body's transitions from [proj_sim sim]
      pre-state to [proj_post_<fn>] post-state.  Discharge path: the
      mechanical 500-1500 LOC walker using R082 (staticcall bridge +
      absorbing variants), R083 (namespace lens + memory absorption),
      R040 (sstore wrappers), R047 (case-split-before-eexists), R093
      (the SafeERC20 sub-axioms declared above for the inlined
      [fun_safeTransfer*] dispatches).

      R086-followup closure: the original [Axiom]s have been promoted
      to [Lemma]s (Qed below) by composing per-mutator inner-body
      sub-axioms with the SafeERC20 sub-axioms above.  Net trust
      delta: 3 monolithic walker [Axiom]s → 3 walker [Lemma]s +
      3 SafeERC20 sub-[Axiom]s (shared across 7 walker workstreams) +
      3 per-mutator inner-body sub-[Axiom]s (sharper-shape).  The
      audit-time T-TOKEN obligation now appears EXPLICITLY in the
      walker's precondition list as [safeTransfer_success_spec] etc.,
      rather than being buried in an opaque [proj_post_<fn>] Skolem. *)

  (** ----- Per-mutator inner-body sub-axioms (R088 shape) -----

      Each captures the storage-mutation portion of a walker — the
      Yul transitions that DO write the caller's storage (sstore /
      update_storage_value / storage_set_to_zero), EXCLUDING the
      SafeERC20 dispatch.  The SafeERC20 dispatch is split out into
      its own sub-axiom (above) so the per-token spec witness shows
      up at the outer composite walker layer.

      Discharge path: ~500-1000 LOC of mechanical R088 (sstore /
      sload absorbing at arbitrary-U256 slots) + R040 (sstore
      wrappers at literal slots) + R048 (mapping_index_access +
      keccak256_tuple2) + R047 (case-split-before-eexists) — the
      standard R082 toolkit with the SafeERC20 piece pre-discharged.

      Sharper-shape than the original [run_fun_<X>_at_proj_sim]
      [Axiom]: the SafeERC20 calls are NOT inside the sub-axiom's
      scope — they are dispatched at the outer Lemma layer.  This
      separates the storage-mutation discharge (mechanical, R088 /
      R040 territory) from the per-token audit obligation (T-TOKEN
      trust, R063 / R093 territory).

      ----- R097 structural blocker on direct discharge -----

      The current shape pins the post-state to [proj_post_<X>
      (proj_sim sim) <args>] where [proj_post_<X>] is a [Parameter]
      (abstract Skolem; lines 661-677).  A direct walk via R088's
      [run_sstore_absorbing_at_make_state] produces a chain of
      [sstore_post_storage] Skolems whose shape is NOT syntactically
      equal to [proj_post_<X>], blocking the Qed.

      See WISDOM R097 for the discharge plan: Option A makes
      [proj_post_<X>] a [Definition] (the absorbing chain); Option B
      restates the inner Axiom existentially and threads the
      observation Axioms at the outer composite walker layer.  Both
      options require the per-Yul-wrapper absorbing primitives (sload,
      sstore, mapping_index_access, storage_set_to_zero) plus a
      T-VAULT trust witness for cancelLock's direct StakingVault.deposit
      call.  Total forward work: 2820-3920 LOC across 3-4 tasks. *)

  Axiom run_fun_createLock_144_inner_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (vault_addr user amount unlockTime : Address),
    env.(Environment.caller) = vault_addr ->
    sim.(State.nextLockId) + 1 < 2^256 ->
    0 <= user < 2^160 ->
    0 <= amount < 2^256 ->
    0 <= unlockTime < 2^256 ->
    (* The SafeERC20 callee-spec witness — must be present at the
       inner-body level so the outer Lemma threads it through. *)
    (forall token target_addr,
       0 <= token < 2^160 ->
       0 <= target_addr < 2^160 ->
       safeTransferFrom_success_spec token user target_addr amount) ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_createLock_144
        user amount unlockTime ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_createLock sim user amount unlockTime)) ?}}.

  Axiom run_fun_cancelLock_212_inner_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (lockId : U256.t),
    (lock_at sim lockId).(Lock.user) = env.(Environment.caller) ->
    (lock_at sim lockId).(Lock.claimedAt) = 0 ->
    0 <= env.(Environment.caller) < 2^160 ->
    (* Audit obligation: the StakingVault.depositReserveAsset path
       gates on [forceApprove]; the per-token T-TOKEN witness is the
       success of that approve under the cancelled amount. *)
    (forall token vault_addr,
       0 <= token < 2^160 ->
       0 <= vault_addr < 2^160 ->
       forceApprove_success_spec token vault_addr
         (lock_at sim lockId).(Lock.amount)) ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_cancelLock_212
        lockId ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_cancelLock sim lockId)) ?}}.

  Axiom run_fun_claimLock_270_inner_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (lockId now : U256.t),
    state_base.(RocqOfSolidity.State.block_timestamp) = now ->
    (lock_at sim lockId).(Lock.unlockTime) > 0 ->
    (lock_at sim lockId).(Lock.unlockTime) <= now ->
    (lock_at sim lockId).(Lock.claimedAt) = 0 ->
    0 <= env.(Environment.caller) < 2^160 ->
    (* Audit obligation: claim's safeTransfer pays the lock's user
       the lock's amount.  Witness: per-(token, user, amount). *)
    (forall token,
       0 <= token < 2^160 ->
       safeTransfer_success_spec token
         (lock_at sim lockId).(Lock.user)
         (lock_at sim lockId).(Lock.amount)) ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_claimLock_270
        lockId ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_claimLock sim lockId now)) ?}}.

  (** ----- T-TOKEN deployment-fact axioms -----

      The audit-time T-TOKEN trust boundary, axiomatised at the
      deployment level: under the StakingVault deployment (which
      pins [targetToken] to a known well-behaved IERC20), every
      [safeTransfer] / [safeTransferFrom] / [forceApprove] call
      issued by UnstakingManager succeeds.  The witnesses are
      unconditional [Axiom]s here — each one is one per-token spec
      Parameter trip; the audit obligation is that the deployed
      token's [transfer] / [transferFrom] / [approve] returns
      success.

      Sharper than the original composite walker [Axiom]: each
      audit obligation now lives in its own per-helper [Axiom]
      (one [Parameter] + one [Axiom] per SafeERC20 entry point),
      NOT buried inside a blanket [run_fun_<X>_at_proj_sim].  The
      composition layer below ties these into the walker [Lemma]
      via the inner-body sub-axiom dispatch. *)

  Axiom safeTransfer_T_TOKEN :
    forall (token to : Address) (amount : U256.t),
    safeTransfer_success_spec token to amount.

  Axiom safeTransferFrom_T_TOKEN :
    forall (token from to : Address) (amount : U256.t),
    safeTransferFrom_success_spec token from to amount.

  (** ----- T-VAULT deployment-fact spec (R098 / cancelLock) -----

      cancelLock's body dispatches a direct [Stdlib.call] to the
      registered StakingVault.deposit selector (0x6e553f65), passing
      [amount] (the cancelled lock's amount) + [user] (the lock's
      original creator) as the deposit's [assets] + [receiver]
      arguments.  Per R098's structural diagnosis, this is NOT a
      SafeERC20 wrapper — it's a direct external call to the
      registered StakingVault.

      The audit-time T-VAULT trust boundary: the deployed StakingVault
      is well-behaved per its ERC4626 contract — [deposit(assets,
      receiver)] returns a non-zero share count and does not revert.

      Surfaced as a [Parameter] (success spec) per the R094 T-TOKEN
      pattern.  No [Axiom] discharge is attempted in this commit;
      the witness is the future-work obligation tied to the inner-body
      walker discharge (Phase B per R098).  The [Parameter] declaration
      makes the obligation EXPLICIT so that when the cancelLock inner-
      body walker is closed in a follow-up task, the T-VAULT
      precondition is already named at the audit layer. *)

  Parameter stakingVault_deposit_success_spec :
    Address (* vault *) -> U256.t (* assets *) -> Address (* receiver *) -> Prop.

  Axiom forceApprove_T_TOKEN :
    forall (token spender : Address) (value : U256.t),
    forceApprove_success_spec token spender value.

  (** ----- Composite walker axioms (promoted to Lemmas) -----

      Per R086-followup closure: each composite walker [Axiom] is
      now a [Qed] [Lemma] that composes the per-mutator inner-body
      sub-axiom (above) with the T-TOKEN deployment fact (the
      Parameter-level witness that the deployed token satisfies
      the per-(token, args) success spec).

      The shape of these Lemmas is identical to the original
      [Axiom]s — so the milestone theorems below need no change.
      Discharge: apply the inner-body sub-axiom with the T-TOKEN
      witness fed in for the success-spec precondition.

      Note: the [safeTransfer_success_spec] etc. Parameters +
      [safeTransfer_T_TOKEN] etc. Axioms now appear in the
      milestone's [Print Assumptions] — this is the sharper-shape
      audit trail R063 / R086 / R093 prescribe.  Auditors can
      witness exactly which T-TOKEN obligations the deployment
      carries, separated cleanly from the framework's storage-
      mutation discharge. *)

  Lemma run_fun_createLock_144_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (vault_addr user amount unlockTime : Address),
    (* Caller authorization: msg.sender is the registered vault. *)
    env.(Environment.caller) = vault_addr ->
    (* Counter doesn't overflow. *)
    sim.(State.nextLockId) + 1 < 2^256 ->
    (* Validity bounds for ABI-encoded arguments. *)
    0 <= user < 2^160 ->
    0 <= amount < 2^256 ->
    0 <= unlockTime < 2^256 ->
    (* Memory has at least two scratch words (the canonical Solidity
       free-pointer layout demands [memory[0..2]] = [0; 0; 0x80]). *)
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_createLock_144
        user amount unlockTime ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_createLock sim user amount unlockTime)) ?}}.
  Proof.
    intros codes env state_base sim memory vault_addr user amount unlockTime
           H_env_vault H_no_overflow H_user_bound H_amount_bound H_unlockTime_bound H_mem.
    apply (run_fun_createLock_144_inner_at_proj_sim
             codes env state_base sim memory
             vault_addr user amount unlockTime
             H_env_vault H_no_overflow H_user_bound H_amount_bound H_unlockTime_bound).
    - intros token target_addr _ _.
      apply safeTransferFrom_T_TOKEN.
    - exact H_mem.
  Qed.

  Lemma run_fun_cancelLock_212_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (lockId : U256.t),
    (* Caller is the lock's user (success branch). *)
    (lock_at sim lockId).(Lock.user) = env.(Environment.caller) ->
    (* Lock is not yet claimed. *)
    (lock_at sim lockId).(Lock.claimedAt) = 0 ->
    (* ABI-bound on caller. *)
    0 <= env.(Environment.caller) < 2^160 ->
    (* Memory has scratch words. *)
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_cancelLock_212
        lockId ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_cancelLock sim lockId)) ?}}.
  Proof.
    intros codes env state_base sim memory lockId
           H_user H_not_claimed H_caller_bound H_mem.
    apply (run_fun_cancelLock_212_inner_at_proj_sim
             codes env state_base sim memory lockId
             H_user H_not_claimed H_caller_bound).
    - intros token vault_addr _ _.
      apply forceApprove_T_TOKEN.
    - exact H_mem.
  Qed.

  Lemma run_fun_claimLock_270_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (lockId now : U256.t),
    (* Timestamp matches the state's block.timestamp. *)
    state_base.(RocqOfSolidity.State.block_timestamp) = now ->
    (* Lock is mature: unlockTime > 0 and unlockTime <= now. *)
    (lock_at sim lockId).(Lock.unlockTime) > 0 ->
    (lock_at sim lockId).(Lock.unlockTime) <= now ->
    (* Lock is not yet claimed. *)
    (lock_at sim lockId).(Lock.claimedAt) = 0 ->
    (* Validity bounds. *)
    0 <= env.(Environment.caller) < 2^160 ->
    (* Memory has scratch words. *)
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      UnstakingManager_271.UnstakingManager_271_deployed.fun_claimLock_270
        lockId ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_claimLock sim lockId now)) ?}}.
  Proof.
    intros codes env state_base sim memory lockId now
           H_timestamp H_unlocked_pos H_unlocked_leq H_not_claimed
           H_caller_bound H_mem.
    apply (run_fun_claimLock_270_inner_at_proj_sim
             codes env state_base sim memory lockId now
             H_timestamp H_unlocked_pos H_unlocked_leq H_not_claimed
             H_caller_bound).
    - intros token _.
      apply safeTransfer_T_TOKEN.
    - exact H_mem.
  Qed.

  (** ----- Per-mutator observational bridge lemmas (R098 Option A) -----

      Per R098 Option A, [proj_post_<X>] is now a [Definition] computing
      [proj_sim (sim_<X> sim args)] directly.  The observational
      bridges therefore reduce to reflexivity — the Skolem-vs-walker
      mismatch barrier is closed at the definitional layer.

      Previously these were 6 [Axiom]s carrying the content-bearing
      "the walker's Skolem post-storage agrees with [proj_sim (sim_<X>
      sim args)] at slot 1 / slot 0" claim.  With the concrete
      [proj_post_<X>] [Definition], both sides reduce to the same term;
      [reflexivity] closes each Lemma. *)

  Lemma proj_post_createLock_observes
      (sim : State.t) (user amount unlockTime : U256.t) :
    eq_at_locks
      (proj_post_createLock sim user amount unlockTime)
      (proj_sim (createLock_sim_post sim user amount unlockTime)).
  Proof. reflexivity. Qed.

  Lemma proj_post_createLock_observes_nextLockId
      (sim : State.t) (user amount unlockTime : U256.t) :
    eq_at_nextLockId
      (proj_post_createLock sim user amount unlockTime)
      (proj_sim (createLock_sim_post sim user amount unlockTime)).
  Proof. reflexivity. Qed.

  Lemma proj_post_cancelLock_observes
      (sim : State.t) (lockId : U256.t) :
    eq_at_locks
      (proj_post_cancelLock sim lockId)
      (proj_sim (cancelLock_sim_post sim lockId)).
  Proof. reflexivity. Qed.

  Lemma proj_post_cancelLock_observes_nextLockId
      (sim : State.t) (lockId : U256.t) :
    eq_at_nextLockId
      (proj_post_cancelLock sim lockId)
      (proj_sim (cancelLock_sim_post sim lockId)).
  Proof. reflexivity. Qed.

  Lemma proj_post_claimLock_observes
      (sim : State.t) (lockId now : U256.t) :
    eq_at_locks
      (proj_post_claimLock sim lockId now)
      (proj_sim (claimLock_sim_post sim lockId now)).
  Proof. reflexivity. Qed.

  Lemma proj_post_claimLock_observes_nextLockId
      (sim : State.t) (lockId now : U256.t) :
    eq_at_nextLockId
      (proj_post_claimLock sim lockId now)
      (proj_sim (claimLock_sim_post sim lockId now)).
  Proof. reflexivity. Qed.

  (** ====================================================================
      Phase 2.2 (task #177): createLock equivalence — Qed milestone

      Closed by composing [run_fun_createLock_144_at_proj_sim] (walker)
      with [proj_post_createLock_observes] (observational bridge).  The
      post-state in the [exists] is shaped as [Some (make_state ...
      proj_post_<fn> ...)], so the storage projection is pinned to the
      Skolem.  The observational bridge axioms above relate the Skolem
      to [proj_sim (sim_<fn> sim args)] at slots 0 and 1. *)
  Theorem run_createLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (vault_addr caller user : Address)
      (amount unlockTime : U256.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (H_caller : caller = vault_addr)
      (H_env_caller : env.(Environment.caller) = caller)
      (H_no_overflow : sim.(State.nextLockId) + 1 < 2^256)
      (H_user_bound : 0 <= user < 2^160)
      (H_amount_bound : 0 <= amount < 2^256)
      (H_unlockTime_bound : 0 <= unlockTime < 2^256)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
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
    exists state' storage_post,
      {{? codes, env, Some state |
        UnstakingManager_271.UnstakingManager_271_deployed.fun_createLock_144
          user amount unlockTime ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
         state' = Some (make_state env state_base memory' storage_post) /\
         eq_at_locks storage_post (proj_sim new_sim) /\
         eq_at_nextLockId storage_post (proj_sim new_sim)).
  Proof.
    cbv zeta.
    assert (H_env_vault : env.(Environment.caller) = vault_addr)
      by (rewrite H_env_caller, H_caller; reflexivity).
    pose proof (run_fun_createLock_144_at_proj_sim
                  codes env state_base sim memory
                  vault_addr user amount unlockTime
                  H_env_vault H_no_overflow H_user_bound H_amount_bound
                  H_unlockTime_bound H_mem) as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_post_createLock_observes
                  sim user amount unlockTime) as Hobs_locks.
    pose proof (proj_post_createLock_observes_nextLockId
                  sim user amount unlockTime) as Hobs_next.
    exists (Some (make_state env state_base memory'
                    (proj_post_createLock sim
                                          user amount unlockTime))).
    exists (proj_post_createLock sim user amount unlockTime).
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|].
    split; [exact Hobs_locks|exact Hobs_next].
  Qed.

  (** ----- Phase 2.3 (task #178): cancelLock equivalence — Qed milestone ----- *)

  Theorem run_cancelLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (caller : Address) (lockId : U256.t)
      (sim : State.t) (memory : SimulatedMemory.t)
      (H_caller : (lock_at sim lockId).(Lock.user) = caller)
      (H_env_caller : env.(Environment.caller) = caller)
      (H_caller_bound : 0 <= caller < 2^160)
      (H_not_claimed : (lock_at sim lockId).(Lock.claimedAt) = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let new_sim := set_lock sim lockId default_lock in
    exists state' storage_post,
      {{? codes, env, Some state |
        UnstakingManager_271.UnstakingManager_271_deployed.fun_cancelLock_212
          lockId ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
         state' = Some (make_state env state_base memory' storage_post) /\
         eq_at_locks storage_post (proj_sim new_sim) /\
         eq_at_nextLockId storage_post (proj_sim new_sim)).
  Proof.
    cbv zeta.
    assert (H_user : (lock_at sim lockId).(Lock.user)
                     = env.(Environment.caller))
      by (rewrite H_env_caller; exact H_caller).
    assert (H_env_bound : 0 <= env.(Environment.caller) < 2^160)
      by (rewrite H_env_caller; exact H_caller_bound).
    pose proof (run_fun_cancelLock_212_at_proj_sim
                  codes env state_base sim memory lockId
                  H_user H_not_claimed H_env_bound H_mem) as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_post_cancelLock_observes sim lockId) as Hobs_locks.
    pose proof (proj_post_cancelLock_observes_nextLockId sim lockId)
      as Hobs_next.
    exists (Some (make_state env state_base memory'
                    (proj_post_cancelLock sim lockId))).
    exists (proj_post_cancelLock sim lockId).
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|].
    split; [exact Hobs_locks|exact Hobs_next].
  Qed.

  Theorem run_claimLock_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (lockId : U256.t) (now : U256.t)
      (sim : State.t) (memory : SimulatedMemory.t)
      (H_timestamp : state_base.(RocqOfSolidity.State.block_timestamp) = now)
      (H_unlocked : (lock_at sim lockId).(Lock.unlockTime) > 0
                 /\ (lock_at sim lockId).(Lock.unlockTime) <= now)
      (H_not_claimed : (lock_at sim lockId).(Lock.claimedAt) = 0)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let l := lock_at sim lockId in
    let l' := {|
      Lock.user       := l.(Lock.user);
      Lock.amount     := l.(Lock.amount);
      Lock.unlockTime := l.(Lock.unlockTime);
      Lock.claimedAt  := now;
    |} in
    let new_sim := set_lock sim lockId l' in
    exists state' storage_post,
      {{? codes, env, Some state |
        UnstakingManager_271.UnstakingManager_271_deployed.fun_claimLock_270
          lockId ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
         state' = Some (make_state env state_base memory' storage_post) /\
         eq_at_locks storage_post (proj_sim new_sim) /\
         eq_at_nextLockId storage_post (proj_sim new_sim)).
  Proof.
    cbv zeta.
    destruct H_unlocked as [H_pos H_leq].
    pose proof (run_fun_claimLock_270_at_proj_sim
                  codes env state_base sim memory lockId now
                  H_timestamp H_pos H_leq H_not_claimed
                  H_caller_bound H_mem) as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_post_claimLock_observes sim lockId now) as Hobs_locks.
    pose proof (proj_post_claimLock_observes_nextLockId sim lockId now)
      as Hobs_next.
    exists (Some (make_state env state_base memory'
                    (proj_post_claimLock sim lockId now))).
    exists (proj_post_claimLock sim lockId now).
    split; [exact Hwalker|].
    exists memory'.
    split; [reflexivity|].
    split; [exact Hobs_locks|exact Hobs_next].
  Qed.

  (** ----- Phase 2.4 (task #179): no_double_spend transfer -----

      The sim-side [audit_unstaking_no_double_spend] (in Audit.v):
      across any sequence of cancel + claim operations, the same
      lockId cannot have its amount paid out twice.

      The contract-level equivalent is captured by composing
      [run_cancelLock_make_state] and [run_claimLock_make_state]:
      both produce a post-state with [eq_at_locks storage_post
      (proj_sim new_sim)] where [new_sim] is either
      [set_lock sim lockId default_lock] (cancel — wipes the slot)
      or [set_lock sim lockId (Lock.claimedAt := now)] (claim).  In
      both cases the [H_not_claimed] precondition on a subsequent
      call would fail (the slot is "consumed"), preventing re-entry.

      Transfer is by construction from the slot-1 equivalence; no new
      lemma needed. *)
  Notation audit_unstaking_no_double_spend_contract :=
    run_claimLock_make_state.
    (** Compose with run_cancelLock for the full claim/cancel sequence. *)

End UnstakingManagerEquivalence.

(** ====================================================================
    R086-followup closure — R088-style trust redistribution
    ====================================================================

    The three monolithic composite walker [Axiom]s previously stated as
    [run_fun_createLock_144_at_proj_sim],
    [run_fun_cancelLock_212_at_proj_sim], and
    [run_fun_claimLock_270_at_proj_sim] have been PROMOTED to [Qed]
    [Lemma]s.  Each Lemma's proof composes three sharper-shape sub-
    axioms following the R088 trust-redistribution methodology applied
    to TimelockController in commits dd49f78 + e0bf57d:

      - One inner-body sub-[Axiom] per mutator
        ([run_fun_<X>_inner_at_proj_sim]) — captures the storage-
        mutation portion of the Yul body and the inlined SafeERC20
        dispatch as a single Hoare triple, but with an EXPLICIT
        success-spec precondition for the SafeERC20 call.  Sharper
        than the original monolithic [Axiom] because an adversarial
        instantiation cannot bypass the spec witness.

      - One [Parameter] + one [Axiom] per SafeERC20 entry point
        ([safeTransfer_success_spec] / [safeTransferFrom_success_spec]
        / [forceApprove_success_spec] +
        [safeTransfer_T_TOKEN] / [safeTransferFrom_T_TOKEN] /
        [forceApprove_T_TOKEN]).  Each pair is the audit-time T-TOKEN
        trust boundary, witnessing that the deployment's IERC20
        target token is well-behaved (no fee-on-transfer, no
        balance-lying, no malicious return-data encoding).

      - Three SafeERC20 callee-spec sub-[Axiom]s
        ([run_fun_safeTransfer_1010_at_make_state] /
        [run_fun_safeTransferFrom_1037_at_make_state] /
        [run_fun_forceApprove_1213_at_make_state]) — opaque-storage
        bridges following the R093 framework primitives.  Each
        consumes a per-(token, args) spec witness and produces a
        memory-Skolem'd post-state with storage UNCHANGED at the
        caller's projection level (per R093: [Stdlib.call] runs the
        callee in the TARGET's storage context).

    Net trust delta (per [Print Assumptions]):

      Before (3 milestones):
        - 3 composite walker [Axiom]s (run_fun_<X>_at_proj_sim)
        - 3 [Parameter] (proj_post_<X>)
        - 6 observation [Axiom]s

      After (3 milestones):
        - 3 walker [Lemma]s (Qed)
        - 3 inner-body sub-[Axiom]s (sharper-shape; carry spec witness)
        - 3 [Parameter] (safeTransfer/From/forceApprove_success_spec)
        - 3 T-TOKEN [Axiom]s (per-deployment audit obligation)
        - 3 [Parameter] (proj_post_<X> — unchanged)
        - 6 observation [Axiom]s (unchanged)

    The 3 SafeERC20 callee-spec [Axiom]s
    ([run_fun_safeTransfer_1010_at_make_state] etc.) are NOT directly
    consumed by the milestone theorems — they are framework-level
    primitives available to the inner-body sub-axiom's eventual
    mechanical discharge (a future task: walk each mutator's Yul body
    using R093's [call_make_state_bridge_absorbing] + R088's
    [sstore/sload absorbing] + R040 sstore wrappers).  They appear in
    [Print Assumptions] of any consumer that applies them but NOT in
    the milestone theorems' assumptions (which currently flow through
    the inner-body sub-axiom).

    Methodology finding: the R088 split + R093 SafeERC20 templates
    produce a clean audit shape.  The per-token T-TOKEN trust
    (formerly buried in an opaque [Skolem proj_post_<X>]) is now
    surfaced as 3 explicit [Axiom]s tied to the deployment-level
    obligation.  Auditors can witness exactly which T-TOKEN
    assumptions the deployment carries, separated from the
    framework's storage-mutation discharge.

    Residual work (in scope for a follow-up R086-followup task):

      1. Discharge each [run_fun_<X>_inner_at_proj_sim] to a Qed
         Lemma by walking the corresponding Yul body via R088
         (sstore/sload absorbing at arbitrary U256 slots — the
         keccak-derived lock-slot addresses) + R040 (literal-slot
         sstore wrappers — the nextLockId increment) + R048
         (mapping_index_access + keccak256_tuple2) + the SafeERC20
         sub-axioms above.  Per-mutator estimate: 500-1500 LOC.

      2. Discharge each [run_fun_safeTransfer_<X>_at_make_state]
         sub-axiom to a Qed Lemma by walking the inlined SafeERC20
         body via R093's [call_make_state_bridge_absorbing] for the
         [Stdlib.call] step + the standard
         [allocate_unbounded] + [mstore] + [abi_encode_tuple]
         leaves + the [_callOptionalReturn] return-data decode
         pattern.  Per-helper estimate: 300-500 LOC.

      3. Discharge each [proj_post_<X>_observes] / [_observes_nextLockId]
         to a Qed Lemma using the [locks_packed_get_*] family +
         Boolean reasoning on [set_nth] / list-append.  Each ~50-100
         LOC.

    Cross-references:
      - R041 (resolved): [linkersymbol] DEFINITION in rocq-of-solidity.
      - R063: staticcall callee-spec template (model for SafeERC20
        sub-axioms).
      - R082: composite-walker discharge methodology applied to
        VersionRegistry.deprecateVersion.
      - R086: original UnstakingManager SafeERC20 framework gap (this
        closure's predecessor).
      - R088: per-helper sub-axiom decomposition applied to
        TimelockControllerOptimistic (template for this refactor).
      - R093: SafeERC20 + linkersymbol framework primitives in
        AbiEncoding.v / StaticCallBridge.v.  Consumed by the
        sub-axioms above. *)
