(** Task #238 — OpenZeppelin ReentrancyGuard equivalence (foundation tier).

    Standalone sanity-check proof against the mock at
    [mocks/ReentrancyGuard.v]. The natural target — binding the
    [nonReentrant] modifier expansion to a shallow form of
    [StakingVault.claimRewards] — is blocked because no shallow form
    has been generated for StakingVault. (The deep IR at
    [generated/StakingVault.v] expands its modifier as a
    [modifier_*_910]-style helper rather than inlining the
    [_nonReentrantBefore] / [_nonReentrantAfter] check chain visibly.)

    What this file delivers, in lieu of a real shallow-form binding:

      1. A symbolic model of the [nonReentrant body] expansion: enter
         the lock, run the body, exit the lock, returning the body's
         result on success and propagating reverts otherwise.
      2. Proofs of the headline properties the equivalence layer will
         eventually need on a per-call-site basis:
           - successful body call leaves the lock in NotEntered post-call,
           - a nested call within the body reverts,
           - the reverts pass through the modifier's pre-check.

    When a shallow form for StakingVault becomes available, this file
    upgrades to bind the `_nonReentrantBefore` / `_nonReentrantAfter`
    Yul functions to [ReentrancyGuard.nonReentrant_enter] /
    [ReentrancyGuard.nonReentrant_exit] using the storage projection
    pattern from Guardian.v (R040 wrapper-shape for sstore, R033
    PureEq for if-then-else branches, R036 upfront-pose for evar
    scope).

    Until then: the lemmas below are sanity-check theorems over the
    abstract semantics, and there are no Admitted goals. *)

Require Import ReserveGovernor.mocks.ReentrancyGuard.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module ReentrancyGuardEquivalence.

  Import ReentrancyGuard.

  (** ---- Abstract model of `f() nonReentrant { body }` ----

      The modifier expansion is:

        nonReentrant_enter;     // revert if already entered
        result := body;         // user code
        nonReentrant_exit;      // restore NotEntered
        return result;          // on success

      Modelled in the Result monad: any revert in either the enter
      check or the body propagates. The exit is unconditional in the
      success path. *)
  Definition with_nonReentrant {A : Set}
      (s : State.t) (body : State.t -> Result.t (State.t * A)) :
      Result.t (State.t * A) :=
    match nonReentrant_enter s with
    | Result.Revert p q => Result.Revert p q
    | Result.Success s_entered =>
        match body s_entered with
        | Result.Revert p q => Result.Revert p q
        | Result.Success (s_after_body, a) =>
            Result.Success (nonReentrant_exit s_after_body, a)
        end
    end.

  (** ---- Lock invariant across a successful nonReentrant call ----

      The status observed AFTER a successful with_nonReentrant call is
      always NotEntered — regardless of what the body did to the
      State.status (the exit unconditionally resets it). This is the
      "storage trace is unchanged across the modifier boundary"
      property that the equivalence layer will eventually need to
      thread through every caller. *)
  Lemma with_nonReentrant_post_status_not_entered
      {A : Set} (s : State.t)
      (body : State.t -> Result.t (State.t * A))
      (s' : State.t) (a : A) :
    with_nonReentrant s body = Result.Success (s', a) ->
    s'.(State.status) = StatusNotEntered.
  Proof.
    unfold with_nonReentrant.
    destruct (nonReentrant_enter s) eqn:Henter; [|discriminate].
    destruct (body value) as [[s_body a_body]|p q] eqn:Hbody; [|discriminate].
    intro Heq.
    injection Heq as <- <-.
    apply exit_resets_to_not_entered.
  Qed.

  (** ---- Re-entry from a nested call always reverts ----

      If the body attempts to enter again — modelled here as a direct
      `nonReentrant_enter` on the body's input state — that nested
      enter reverts. This is the structural form of OWASP SC01's
      "external call cannot re-enter a nonReentrant function". *)
  Lemma with_nonReentrant_nested_enter_reverts
      (s : State.t) :
    s.(State.status) = StatusNotEntered ->
    with_nonReentrant s
      (fun s_entered =>
        match nonReentrant_enter s_entered with
        | Result.Revert p q => Result.Revert p q
        | Result.Success _  => Result.Success (s_entered, tt)
        end)
    = Result.Revert 0 32.
  Proof.
    intro Hne.
    unfold with_nonReentrant, nonReentrant_enter.
    rewrite Hne.
    simpl.
    reflexivity.
  Qed.

  (** ---- Pre-check pass-through: if the lock is already taken, the
      enter check reverts and the body never runs ----

      The body argument never gets evaluated because the enter check
      reverts first. This is the modifier's "fail fast" property — the
      body cannot observe the pre-entered state. *)
  Lemma with_nonReentrant_already_entered_short_circuits
      {A : Set} (s : State.t)
      (body : State.t -> Result.t (State.t * A)) :
    s.(State.status) = StatusEntered ->
    with_nonReentrant s body = Result.Revert 0 32.
  Proof.
    intro He.
    unfold with_nonReentrant, nonReentrant_enter.
    rewrite He.
    reflexivity.
  Qed.

  (** ---- Successful pass-through preserves the body's output ----

      When the body succeeds (returning some [a]), with_nonReentrant
      returns the same [a]. The output side of "the modifier is
      transparent on success", as opposed to the storage-trace side
      proved above. *)
  Lemma with_nonReentrant_passthrough_output
      {A : Set} (s s_body : State.t) (a : A)
      (body : State.t -> Result.t (State.t * A)) :
    s.(State.status) = StatusNotEntered ->
    body {| State.status := StatusEntered |} = Result.Success (s_body, a) ->
    with_nonReentrant s body
    = Result.Success (nonReentrant_exit s_body, a).
  Proof.
    intros Hne Hbody.
    unfold with_nonReentrant, nonReentrant_enter.
    rewrite Hne.
    simpl.
    rewrite Hbody.
    reflexivity.
  Qed.

  (** ---- Body sees Entered status when invoked ----

      The body receives a state with [status = StatusEntered]. This is
      what a nested [nonReentrant_enter] check inside the body uses to
      reject re-entrance. *)
  Lemma with_nonReentrant_body_sees_entered
      {A : Set} (s s' : State.t) (a : A)
      (body : State.t -> Result.t (State.t * A)) :
    s.(State.status) = StatusNotEntered ->
    with_nonReentrant s body = Result.Success (s', a) ->
    exists s_body,
      body {| State.status := StatusEntered |} = Result.Success (s_body, a)
      /\ s' = nonReentrant_exit s_body.
  Proof.
    intros Hne H.
    unfold with_nonReentrant, nonReentrant_enter in H.
    rewrite Hne in H.
    simpl in H.
    destruct (body {| State.status := StatusEntered |})
      as [[s_body a']|p q] eqn:Hbody; [|discriminate].
    injection H as <- <-.
    exists s_body. split; reflexivity.
  Qed.

End ReentrancyGuardEquivalence.
