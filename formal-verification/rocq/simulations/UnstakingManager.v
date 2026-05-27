(** UnstakingManager simulation.

    Mirrors contracts/staking/UnstakingManager.sol — a time-locked
    withdrawal queue. Each [Lock] is a 4-tuple

      { user : address;
        amount : U256.t;       (** {targetToken} *)
        unlockTime : U256.t;   (** {seconds} *)
        claimedAt  : U256.t;   (** {seconds}, 0 = unclaimed *)
      }

    indexed by a monotonically-increasing [lockId]. The contract
    exposes three external operations:

      createLock(user, amount, unlockTime)  — only vault may call;
                                              auto-assigns the next id.
      cancelLock(lockId)                    — only the lock's user;
                                              wipes storage and deposits
                                              [amount] back into the vault.
      claimLock(lockId)                     — anyone, once
                                              [unlockTime <= now] and the
                                              lock isn't already claimed.

    [block.timestamp] is read on-chain; here it is passed explicitly
    as [now : U256.t] so the simulation is pure.

    The simulation models the locks-store and the next-id counter; the
    actual ERC20 transfers and the vault.deposit call are modeled as
    abstract balance deltas (out of scope for this file — see the
    integration proof for the conservation theorem coupling
    UnstakingManager with StakingVault).

    Revert coverage:
      - [revert_unauthorized]   when caller != expected (vault on
                                create; lock.user on cancel).
      - [revert_not_unlocked]   when claimLock sees an immature or
                                default-zero slot.
      - [revert_already_claimed] when claim or cancel sees a slot
                                whose claimedAt is non-zero.

    Not modeled here:
      - SafeERC20 transfer reverts (token-side issue, not lock state).
      - Reentrancy through vault.deposit during cancel (defer to the
        StakingVault integration proof; this file pins the lock
        accounting independently).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module UnstakingManager.

(** Address model — opaque U256.t, with a distinguished [zero_address]
    representing both [address(0)] and the default-state user field
    of an uninitialized lock slot. *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

Module Lock.
  Record t : Set := {
    user       : Address;
    amount     : U256.t;
    unlockTime : U256.t;
    claimedAt  : U256.t;
  }.
End Lock.

(** The default Solidity-storage state for an unset Lock: all four
    fields are zero. The contract reads from this whenever a [lockId]
    is queried before [createLock] was called for it. *)
Definition default_lock : Lock.t := {|
  Lock.user := zero_address;
  Lock.amount := 0;
  Lock.unlockTime := 0;
  Lock.claimedAt := 0;
|}.

(** Manager state: [nextLockId] counter and the locks-store. We model
    the store as a list, where [List.nth lockId locks default_lock]
    matches [locks[lockId]] in Solidity (uninitialized slot returns
    default). *)
Module State.
  Record t : Set := {
    nextLockId : U256.t;
    locks      : list Lock.t;   (** indexed by lockId, [0, nextLockId) *)
  }.
End State.

Definition empty_state : State.t := {|
  State.nextLockId := 0;
  State.locks      := [];
|}.

(** Two-constructor result mirroring [ProposerThrottle.Result.t]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_unauthorized    {A : Set} : Result.t A := Result.Revert 0 32.
Definition revert_not_unlocked    {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_already_claimed {A : Set} : Result.t A := Result.Revert 64 32.

(** Helper: read lock at [lockId], returning [default_lock] if OOB.
    Mirrors Solidity's mapping default behaviour. *)
Definition lock_at (s : State.t) (lockId : U256.t) : Lock.t :=
  nth (Z.to_nat lockId) s.(State.locks) default_lock.

(** Helper: replace the lock at index [lockId] in the list. If OOB
    (which shouldn't happen for [lockId < nextLockId] in real flows),
    the list is returned unchanged. *)
Fixpoint set_nth {A : Type} (n : nat) (a : A) (xs : list A) : list A :=
  match xs, n with
  | [], _ => []
  | _ :: rest, O => a :: rest
  | x :: rest, S k => x :: set_nth k a rest
  end.

Definition set_lock (s : State.t) (lockId : U256.t) (l : Lock.t) : State.t :=
  {| State.nextLockId := s.(State.nextLockId);
     State.locks := set_nth (Z.to_nat lockId) l s.(State.locks) |}.

(** [createLock] — invoked by the vault. Adds a fresh lock at
    index [nextLockId], bumps the counter. *)
Definition createLock
    (s : State.t) (vault_addr caller user : Address)
    (amount unlockTime : U256.t)
    : Result.t State.t :=
  if negb (caller =? vault_addr) then
    revert_unauthorized
  else
    let new_lock := {|
      Lock.user       := user;
      Lock.amount     := amount;
      Lock.unlockTime := unlockTime;
      Lock.claimedAt  := 0;
    |} in
    Result.Success {|
      State.nextLockId := s.(State.nextLockId) + 1;
      State.locks      := s.(State.locks) ++ [new_lock];
    |}.

(** [cancelLock] — only callable by the lock's user, on an
    unclaimed lock. Wipes the slot to default. The vault deposit is
    not modeled here (a balance side-effect, not a store mutation). *)
Definition cancelLock
    (s : State.t) (lockId : U256.t) (caller : Address)
    : Result.t State.t :=
  let l := lock_at s lockId in
  if negb (l.(Lock.user) =? caller) then
    revert_unauthorized
  else if negb (l.(Lock.claimedAt) =? 0) then
    revert_already_claimed
  else
    Result.Success (set_lock s lockId default_lock).

(** [claimLock] — permissionless once [unlockTime <= now] and
    [unlockTime != 0] (the latter guards default-zero slots).
    Marks the slot claimed and transfers tokens to lock.user (modeled
    as a balance side-effect, not encoded here). *)
Definition claimLock
    (s : State.t) (lockId : U256.t) (now : U256.t)
    : Result.t State.t :=
  let l := lock_at s lockId in
  if negb (andb (negb (l.(Lock.unlockTime) =? 0))
                (l.(Lock.unlockTime) <=? now)) then
    revert_not_unlocked
  else if negb (l.(Lock.claimedAt) =? 0) then
    revert_already_claimed
  else
    let l' := {|
      Lock.user       := l.(Lock.user);
      Lock.amount     := l.(Lock.amount);
      Lock.unlockTime := l.(Lock.unlockTime);
      Lock.claimedAt  := now;
    |} in
    Result.Success (set_lock s lockId l').

(** Storage invariants. Each lock either:
    - is the default-zero slot (never created, or just cancelled), OR
    - is "active": user != 0, unlockTime > 0, claimedAt = 0, OR
    - is "claimed": user != 0, unlockTime > 0, claimedAt > 0.

    Plus structural invariants: [length locks = Z.to_nat nextLockId]. *)
Module Valid.

  Inductive lock_state (l : Lock.t) : Prop :=
  | LS_default : l = default_lock -> lock_state l
  | LS_active :
      l.(Lock.user) <> zero_address ->
      0 < l.(Lock.unlockTime) ->
      l.(Lock.claimedAt) = 0 ->
      lock_state l
  | LS_claimed :
      l.(Lock.user) <> zero_address ->
      0 < l.(Lock.unlockTime) ->
      0 < l.(Lock.claimedAt) ->
      lock_state l.

  Record state (s : State.t) : Prop := {
    next_u256       : U256.Valid.t s.(State.nextLockId);
    locks_len       : Z.of_nat (length s.(State.locks)) = s.(State.nextLockId);
    locks_well_formed :
      Forall lock_state s.(State.locks);
  }.

End Valid.

(** The headline conservation predicate: sum of [amount] over locks
    that are not (yet) claimed and not in default-zero. This is what
    must equal the contract's targetToken balance — the integration
    bound proved against the StakingVault side. *)
Definition active_amount (l : Lock.t) : U256.t :=
  if andb (l.(Lock.claimedAt) =? 0)
          (negb (l.(Lock.unlockTime) =? 0))
  then l.(Lock.amount) else 0.

Fixpoint total_active (locks : list Lock.t) : U256.t :=
  match locks with
  | [] => 0
  | l :: rest => active_amount l + total_active rest
  end.

End UnstakingManager.
