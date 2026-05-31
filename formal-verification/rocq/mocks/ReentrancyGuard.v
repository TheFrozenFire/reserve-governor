(** OpenZeppelin ReentrancyGuard mock — single-slot reentrancy lock.

    Captures the surface of
      @openzeppelin/contracts-upgradeable/utils/ReentrancyGuardUpgradeable.sol
    that [StakingVault.claimRewards] depends on via the [nonReentrant]
    modifier (the only governor-contract use site per the catalogue).

    OZ semantics (v5.x — ERC-7201 namespaced storage):

      uint256 private constant NOT_ENTERED = 1;
      uint256 private constant ENTERED     = 2;

      struct ReentrancyGuardStorage { uint256 _status; }
      // Stored at keccak("openzeppelin.storage.ReentrancyGuard")-derived slot

      modifier nonReentrant() {
        _nonReentrantBefore();
        _;                        // <user body>
        _nonReentrantAfter();
      }

      function _nonReentrantBefore() private {
        if ($._status == ENTERED) {
          revert ReentrancyGuardReentrantCall();
        }
        $._status = ENTERED;
      }

      function _nonReentrantAfter() private {
        $._status = NOT_ENTERED;
      }

    So the [_status] slot transitions: NOT_ENTERED (1) -> ENTERED (2) ->
    NOT_ENTERED (1) across a successful nonReentrant call. A second
    nonReentrant call entered while the first is in-flight reverts.

    Why mock rather than abstract: reentrancy protection is the property
    we want to verify, so the slot-transition semantics must be visible
    in the simulation. A bare axiom (e.g. "claimRewards cannot be
    re-entered") wouldn't let us bind the property to the [_status]
    storage that actual call sites read and write.

    Used by (planned):
      - [proofs/equivalence/StakingVault.v] (claimRewards nonReentrant
        modifier equivalence — bound to a yet-to-be-generated shallow
        form). No live consumer yet; this mock bedrock-tests the
        abstract semantics.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module ReentrancyGuard.

(** ---- Status constants matching OZ's storage encoding ----

    OZ stores the status as a uint256 with two reserved values. We
    model the abstract enum and a [to_u256] projection so callers can
    bridge to the on-chain encoding. *)
Definition NOT_ENTERED : U256.t := 1.
Definition ENTERED     : U256.t := 2.

Inductive Status : Set :=
| StatusNotEntered
| StatusEntered.

Definition to_u256 (s : Status) : U256.t :=
  match s with
  | StatusNotEntered => NOT_ENTERED
  | StatusEntered    => ENTERED
  end.

(** ---- State ----

    The single-field state corresponds to the ERC-7201 [_status] slot.
    Modelling it as the [Status] enum (rather than the raw U256) makes
    the transitions structural and prevents proofs from accidentally
    setting [_status] to a non-canonical value. The U256 projection is
    available via [to_u256] for sims that bind to actual storage. *)
Module State.
  Record t : Set := {
    status : Status;
  }.

  Definition initial : t := {| status := StatusNotEntered |}.
End State.

(** ---- The Result-monad wrapper used by callers ----
    Mirrors [mocks/Nonces.v]'s [Result.t]. A [nonReentrant_enter] call
    either succeeds (yielding the updated state) or reverts with the
    OZ selector for [ReentrancyGuardReentrantCall()]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Sentinel for ReentrancyGuardReentrantCall — we don't model the
    exact 4-byte selector, just the kind. Two arbitrary U256 values
    suffice to distinguish reverts at proof level. *)
Definition revert_reentrant_call {A : Set} : Result.t A := Result.Revert 0 32.

(** ---- Operations ----

    [nonReentrant_enter] is [_nonReentrantBefore]: revert if the lock
    is already taken, else flip to ENTERED.

    [nonReentrant_exit] is [_nonReentrantAfter]: unconditionally
    restore to NOT_ENTERED (no failure mode — OZ trusts the modifier's
    matched pair). *)
Definition nonReentrant_enter (s : State.t) : Result.t State.t :=
  match s.(State.status) with
  | StatusEntered    => revert_reentrant_call
  | StatusNotEntered => Result.Success {| State.status := StatusEntered |}
  end.

Definition nonReentrant_exit (s : State.t) : State.t :=
  {| State.status := StatusNotEntered |}.

(** ---- Validity ----

    The model is structurally bound to {NotEntered, Entered} by [Status]
    being a two-constructor inductive — there's no "invalid state" to
    reject at the [Valid.t] level. We keep the [Valid.t] definition for
    parity with other mocks ([Nonces.Valid], [Trace208.Valid]) and to
    allow downstream proofs to thread a predicate even if currently
    trivial.

    A stronger model would carry [U256.Valid.t (to_u256 ...)] but the
    [to_u256] image is {1, 2}, both in-range, so the property is vacuous
    by structure. *)
Module Valid.
  Definition state (s : State.t) : Prop := True.

  Lemma initial_valid : state State.initial.
  Proof. exact I. Qed.
End Valid.

(** ---- Headline lemmas ---- *)

(** [nonReentrant_enter] reverts exactly when the lock is already
    taken. The "iff" characterizes the OZ check at modifier entry. *)
Lemma nonReentrant_enter_revert_iff_entered :
  forall (s : State.t),
    nonReentrant_enter s = @revert_reentrant_call _ <->
    s.(State.status) = StatusEntered.
Proof.
  intros s.
  unfold nonReentrant_enter.
  destruct s.(State.status); split; intro H.
  - (* NotEntered, Success = Revert: impossible *)
    discriminate.
  - discriminate.
  - reflexivity.
  - reflexivity.
Qed.

(** Idempotent rejection: once entered, a fresh [nonReentrant_enter]
    call on the same state reverts. This is the structural form of
    "you cannot enter twice without exiting in between". *)
Lemma nonReentrant_enter_idempotent_revert :
  forall (s s' : State.t),
    nonReentrant_enter s = Result.Success s' ->
    nonReentrant_enter s' = @revert_reentrant_call _.
Proof.
  intros s s' H.
  unfold nonReentrant_enter in *.
  destruct s.(State.status); [|discriminate].
  injection H as <-.
  simpl.
  reflexivity.
Qed.

(** Successful enter flips status from NotEntered to Entered. The
    "post-condition" form of the lock transition. *)
Lemma nonReentrant_enter_flips_to_entered :
  forall (s s' : State.t),
    nonReentrant_enter s = Result.Success s' ->
    s.(State.status) = StatusNotEntered /\ s'.(State.status) = StatusEntered.
Proof.
  intros s s' H.
  unfold nonReentrant_enter in H.
  destruct s.(State.status); [|discriminate].
  injection H as <-.
  split; reflexivity.
Qed.

(** [nonReentrant_exit] unconditionally returns NotEntered status.
    The modifier-end half of the protocol. *)
Lemma exit_resets_to_not_entered :
  forall (s : State.t),
    (nonReentrant_exit s).(State.status) = StatusNotEntered.
Proof.
  intros s. reflexivity.
Qed.

(** Full round-trip: enter then exit returns the lock to NotEntered.
    Structural correctness of the modifier's enter/exit pairing — the
    observable [_status] slot is unchanged across a successful call. *)
Lemma round_trip_returns_to_not_entered :
  forall (s s' : State.t),
    s.(State.status) = StatusNotEntered ->
    nonReentrant_enter s = Result.Success s' ->
    (nonReentrant_exit s').(State.status) = StatusNotEntered.
Proof.
  intros s s' _ _.
  apply exit_resets_to_not_entered.
Qed.

(** ---- U256 projection lemmas ----

    Bridge the abstract Status to the on-chain encoding. Used by the
    equivalence layer when projecting [State.status] into the storage
    slot [_status] at the ERC-7201 namespaced location. *)
Lemma to_u256_NOT_ENTERED : to_u256 StatusNotEntered = NOT_ENTERED.
Proof. reflexivity. Qed.

Lemma to_u256_ENTERED : to_u256 StatusEntered = ENTERED.
Proof. reflexivity. Qed.

(** Both encoded values are U256-valid. The shape that downstream
    storage-projection lemmas will need when discharging
    [U256.Valid.t (to_u256 s.(State.status))]. *)
Lemma to_u256_valid : forall (st : Status), U256.Valid.t (to_u256 st).
Proof.
  intros st.
  unfold U256.Valid.t.
  destruct st; simpl; unfold NOT_ENTERED, ENTERED; lia.
Qed.

(** The constants are distinct in their U256 encoding — entered and
    not-entered are never confused. *)
Lemma NOT_ENTERED_neq_ENTERED : NOT_ENTERED <> ENTERED.
Proof. unfold NOT_ENTERED, ENTERED. discriminate. Qed.

End ReentrancyGuard.
