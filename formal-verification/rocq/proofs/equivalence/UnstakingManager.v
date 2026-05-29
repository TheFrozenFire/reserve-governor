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
Require Import ReserveGovernor.simulations.UnstakingManager.

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
  Lemma locks_packed_get_user (locks : list Lock.t) (lockId : U256.t) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.user_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.user).
  Proof.
  Admitted.

  Lemma locks_packed_get_amount (locks : list Lock.t) (lockId : U256.t) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.amount_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.amount).
  Proof.
  Admitted.

  Lemma locks_packed_get_unlockTime (locks : list Lock.t) (lockId : U256.t) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.unlockTime_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.unlockTime).
  Proof.
  Admitted.

  Lemma locks_packed_get_claimedAt (locks : list Lock.t) (lockId : U256.t) :
    StorableValue.map_get_u256 (locks_packed locks) (lockId, LockField.claimedAt_offset)
    = (List.nth (Z.to_nat lockId) locks default_lock).(Lock.claimedAt).
  Proof.
  Admitted.

End UnstakingManagerEquivalence.
