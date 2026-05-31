(** Task #236 — OpenZeppelin Nonces equivalence (foundation tier).

    Standalone sanity-check proof against the mock at
    [mocks/Nonces.v]. The natural target — binding the
    [_useCheckedNonce] internal helper to a shallow form of
    [ReserveOptimisticGovernor] (which inherits the OZ Governor's
    [castVoteBySig] / [castVoteWithReasonAndParamsBySig] paths, plus
    StakingVault.[delegateOptimisticBySig]) — is blocked because:

      - [ReserveOptimisticGovernor]'s shallow form is blocked by R035
        (switch-binding bug), so no equivalence-tier substrate exists
        for the Governor inheritance chain;
      - [Nonces] standalone emits only a deploy scaffold per
        [notes/shallow_embed_oz_gaps.md] — there is no Yul-body to
        bind for the [_useCheckedNonce] internal function.

    What this file delivers, in lieu of a real shallow-form binding:

      1. A symbolic model of the [_useCheckedNonce(owner, nonce); body]
         Yul shape: run the nonce check, then run the body against the
         post-check map. Reverts in either propagate.
      2. Proofs of the headline properties the equivalence layer will
         eventually need on a per-call-site basis (replay protection,
         body sees incremented map, monotonicity across calls, etc.).

    Adaptation from the R045 pattern (established by
    [proofs/equivalence/ReentrancyGuard.v]): [_useCheckedNonce] is not
    a wrapping modifier (no pre/post pair like
    [_nonReentrantBefore]/[_nonReentrantAfter]); it is a precondition
    check that mutates per-account state in the success path. The
    [with_useCheckedNonce] wrapper therefore models a sequenced check
    -> body shape, threading the post-check map into the body. The
    five sanity-check lemmas below mirror the mock's five headline
    lemmas, lifted onto the [with_useCheckedNonce] form so the same
    equivalence-side bridge can be reused when the shallow form lands.

    When a shallow form for ReserveOptimisticGovernor (or a direct
    [Nonces] body emission) becomes available, this file upgrades to
    bind the Yul [_useCheckedNonce] call sequence to
    [Nonces.useCheckedNonce] using the storage projection pattern from
    Guardian.v (R040 wrapper-shape for sstore, R033 PureEq for
    if-then-else branches, R036 upfront-pose for evar scope).

    Until then: the lemmas below are sanity-check theorems over the
    abstract semantics, and there are no Admitted goals. *)

Require Import ReserveGovernor.mocks.Nonces.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Local Open Scope Z_scope.

Module NoncesEquivalence.

  Import Nonces.

  (** ---- Abstract model of `_useCheckedNonce(owner, nonce); body` ----

      The Yul call-site expansion of a function using
      [_useCheckedNonce] (e.g. Governor.castVoteBySig) is:

        _useCheckedNonce(owner, nonce);   // revert if mismatch
        // ...user body executes against the post-increment map...

      Modelled in the Result monad: a revert in the nonce check
      short-circuits and the body never runs. On success, the body
      runs against the updated map. *)
  Definition with_useCheckedNonce {A : Set}
      (m : Map) (owner : Address) (nonce : Z)
      (body : Map -> Result.t (Map * A)) :
      Result.t (Map * A) :=
    match useCheckedNonce m owner nonce with
    | Result.Revert p q => Result.Revert p q
    | Result.Success m' => body m'
    end.

  (** ---- Body runs against incremented map on nonce match ----

      When the supplied [nonce] matches [m owner], the body is
      invoked with [m'] where [m' owner = m owner + 1]. This is the
      lift of [useCheckedNonce_increments] onto [with_useCheckedNonce]
      — the body sees the post-consume nonce state, which is the
      precondition every downstream call-site reasoning relies on. *)
  Lemma with_useCheckedNonce_match_runs_body
      {A : Set} (m : Map) (owner : Address) (nonce : Z)
      (body : Map -> Result.t (Map * A)) :
    m owner = nonce ->
    with_useCheckedNonce m owner nonce body
    = body (upd m owner (nonce + 1)).
  Proof.
    intro Hmatch.
    unfold with_useCheckedNonce, useCheckedNonce.
    rewrite Hmatch.
    rewrite Z.eqb_refl.
    reflexivity.
  Qed.

  (** ---- Replay-reverts: mismatched nonce short-circuits, body never runs ----

      When [m owner <> nonce], [_useCheckedNonce] reverts before the
      body executes. The body is opaque — passed as a function — so
      this lemma also witnesses that the body cannot observe the
      pre-check map under a failing precondition. Lift of
      [useCheckedNonce_success_iff_match] (contrapositive). *)
  Lemma with_useCheckedNonce_replay_reverts
      {A : Set} (m : Map) (owner : Address) (nonce : Z)
      (body : Map -> Result.t (Map * A)) :
    m owner <> nonce ->
    with_useCheckedNonce m owner nonce body = Result.Revert 0 64.
  Proof.
    intro Hne.
    unfold with_useCheckedNonce, useCheckedNonce.
    destruct (Z.eqb (m owner) nonce) eqn:Heqb.
    - apply Z.eqb_eq in Heqb. contradiction.
    - reflexivity.
  Qed.

  (** ---- Other accounts are untouched by a successful nonce consume ----

      Per-account isolation: when [with_useCheckedNonce] succeeds for
      [owner], any [other <> owner] sees its stored nonce unchanged in
      the map handed to the body. Stated as: if we run
      [with_useCheckedNonce m owner nonce body] with [body] capturing
      the map it sees as the success payload, the captured map equals
      [m] on every [other <> owner]. Lift of
      [useCheckedNonce_preserves_other_accounts] onto the wrapped
      form. *)
  Lemma with_useCheckedNonce_increments_target_account
      (m : Map) (owner other : Address) (nonce : Z) (m_seen : Map) :
    owner <> other ->
    m owner = nonce ->
    with_useCheckedNonce m owner nonce
      (fun m' => Result.Success (m', m')) = Result.Success (m_seen, m_seen) ->
    m_seen other = m other.
  Proof.
    intros Hne Hmatch Hrun.
    rewrite (with_useCheckedNonce_match_runs_body
               (A := Map) m owner nonce
               (fun m' => Result.Success (m', m')) Hmatch) in Hrun.
    injection Hrun as Hmseen _.
    subst m_seen.
    unfold upd.
    destruct (Z.eqb other owner) eqn:Heqb.
    - apply Z.eqb_eq in Heqb. subst other. contradiction.
    - reflexivity.
  Qed.

  (** ---- Monotonicity: nonce strictly increases across the check boundary ----

      The map handed to the body has a strictly larger [owner] entry
      than the pre-call map. Lift of [useCheckedNonce_monotone] onto
      the wrapped form — captures "a consumed nonce is gone forever,
      no body invocation can roll it back without an explicit further
      mutation". *)
  Lemma with_useCheckedNonce_monotone
      {A : Set} (m : Map) (owner : Address) (nonce : Z)
      (body : Map -> Result.t (Map * A)) :
    m owner = nonce ->
    let m' := upd m owner (nonce + 1) in
    with_useCheckedNonce m owner nonce body = body m' /\
    m owner < m' owner.
  Proof.
    intro Hmatch.
    simpl.
    split.
    - apply with_useCheckedNonce_match_runs_body. exact Hmatch.
    - unfold upd. rewrite Z.eqb_refl. lia.
  Qed.

  (** ---- Replay protection: second call with the same nonce reverts ----

      The headline replay-protection theorem: after a successful
      consume, calling [with_useCheckedNonce] again with the same
      [(owner, nonce)] pair reverts, regardless of the second body
      (which never runs). This is the structural form of OZ's
      [InvalidAccountNonce] guarantee.

      Lifted from [useCheckedNonce_replay_reverts] onto the
      [with_useCheckedNonce] form: a body wrapping a follow-up call
      with the SAME stale nonce always reverts in the inner check. *)
  Lemma with_useCheckedNonce_replay_protection
      (m : Map) (owner : Address) (nonce : Z) :
    m owner = nonce ->
    with_useCheckedNonce m owner nonce
      (fun m_after =>
         with_useCheckedNonce m_after owner nonce
           (fun m_final => Result.Success (m_final, tt)))
    = Result.Revert 0 64.
  Proof.
    intro Hmatch.
    rewrite with_useCheckedNonce_match_runs_body by exact Hmatch.
    apply with_useCheckedNonce_replay_reverts.
    unfold upd.
    rewrite Z.eqb_refl.
    lia.
  Qed.

End NoncesEquivalence.
