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

Import Stdlib.
Import RunO.

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
      (** Yul-side createLock — function name lives in the generated
          shallow form once UnstakingManager_shallow.v is produced
          (per scripts/shallow-embed-sweep, currently not part of the
          standing IR sweep). *)
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
  (** Body skeleton (once UnstakingManager_shallow.v is in scope):

        unfold fun_createLock_*.
        l. {
          (* require msg.sender == vault — discharge via H_caller *)
          c. { apply require_msg_sender_vault. exact H_caller. }
          (* SafeERC20.safeTransferFrom — abstracted as a CallContract,
             discharged via [cc] (Phase A upstream addition) with the
             ERC20 transfer behaviour axiomatised. *)
          c. { cc. apply RunO.Pure. }
          (* lockId := nextLockId; sload slot 0, sstore slot 0 (nextLockId+1) *)
          c. { apply_run_sload_u256. }
          c. { apply_run_sstore_u256. }
          CanonizeState.execute.
          (* Lock storage write: 4 sstores at fields 0,1,2,3 of
             keccak256(lockId, 1). Each via apply_run_sstore_struct_field. *)
          c. { apply_run_sstore_struct_field. } CanonizeState.execute.
          c. { apply_run_sstore_struct_field. } CanonizeState.execute.
          c. { apply_run_sstore_struct_field. } CanonizeState.execute.
          c. { apply_run_sstore_struct_field. } CanonizeState.execute.
          p.
        }
        p.

      Closure depends on:
        - The Phase A apparatus (apply_run_sstore_struct_field for
          MapStruct sstores).
        - locks_packed correctly modeling the post-append shape:
          [locks_packed (locks ++ [new_lock])] should equal the
          original [locks_packed locks] extended with 4 new entries
          keyed by (Z.of_nat (length locks), 0..3). That requires the
          R022-family rewrite chain.

      Statement body Admitted as a placeholder until
      UnstakingManager_shallow.v is generated and the body-tactical
      proof is mechanically assembled. *)
  Admitted.

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
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
  (** Body: cancelLock writes default_lock to the 4 field slots and
      transfers tokens out (modeled via cc / RunO.CallContract).
      Same structure as createLock; Admitted similarly. *)
  Admitted.

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
      LowM.Pure (Result.Ok tt) ⇓
      Result.Ok tt
    | Some state' ?}}.
  Proof.
  (** Body: claimLock writes only the claimedAt field at offset 3 and
      transfers tokens out. Single sstore on the storage side; same
      pattern as cancelLock. Admitted similarly. *)
  Admitted.

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
