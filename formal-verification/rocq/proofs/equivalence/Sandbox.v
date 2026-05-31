(** Phase 0.5 (task #170) — toy equivalence proof.

    Validates that the rocq-of-solidity equivalence apparatus is
    plumbed end-to-end into our governor repo:

      - the upstream's [RocqOfSolidity], [simulations.RocqOfSolidity],
        and [proofs.RocqOfSolidity] libraries are reachable from our
        coqc invocation,
      - the [RunO.t] propositional Hoare triple and its abbreviated
        tactics ([l], [lu], [c], [cu], [p], [pe], [pr], [s]) work
        inside our build, and
      - a shallow-form contract definition can be referenced from a
        proof file rooted in our [proofs/equivalence/] tree.

    To avoid the work of running [shallow_embed.py] on our own
    [generated/] outputs (that wiring is a Phase 1 prerequisite),
    this toy proof piggybacks on the upstream's [contracts/tutorial/]
    shallow example. We state a small variant of the upstream's
    headline lemma to exercise the tactic vocabulary from scratch
    rather than just re-running their proof.

    Methodology decisions exercised (per notes/equivalence_proof_methodology.md):
      D1 (RunO Hoare triple for "exact result" claims),
      D4 (per-function equivalence lemma granularity),
      D5 (proof against the shallow form).

    The other decisions (storage projection D2, revert alignment
    D3, env constants D6, base-slot symbolic storage D7) don't
    apply here — the tutorial example is a pure arithmetic helper
    with no storage interaction. Phase 1.* will exercise those on
    ThrottleLib. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import RocqOfSolidity.simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import RocqOfSolidity.contracts.tutorial.shallow.

Import Stdlib.
Import RunO.

Module SandboxToyProof.

  (** The shallow form's [checked_add_t_uint256] body, condensed:

        let x := cleanup x in
        let y := cleanup y in
        let sum := add x y in
        if gt x sum then panic else ();
        return sum

      We prove that when [x + y] does not overflow uint256, the
      shallow body terminates with output [x + y] and the runtime
      state unchanged. This is the simplest non-trivial equivalence
      shape: no storage, no memory writes, just arithmetic + a
      conditional revert path that the precondition rules out. *)
  Lemma toy_equivalence codes environment state
      (x y : U256.t)
      (H_x  : 0 <= x < 2^256)
      (H_y  : 0 <= y < 2^256)
      (H_no_overflow : x + y < 2^256) :
    {{? codes, environment, Some state |
      Contract_16.Contract_16_deployed.checked_add_t_uint256 x y ⇓
      Result.Ok (x + y)
    | Some state ?}}.
  Proof.
    unfold Contract_16.Contract_16_deployed.checked_add_t_uint256.
    lu.
    repeat (lu || cu || p).
    s.
    unfold Pure.gt, Pure.add.
    destruct (_ >? _) eqn:Hgt; s.
    - (* Panic branch: ruled out by H_no_overflow + H_x + H_y. *)
      lia.
    - pe; f_equal. lia.
  Qed.

End SandboxToyProof.

(** ----- R020 verification: Stdlib.timestamp now has real semantics -----

    With the dev-clone of rocq-of-solidity (which we've now wired in
    via scripts/rocq-build pointing at
    ~/git/reserve/formal-verification/rocq-of-solidity), Stdlib.timestamp
    is defined as

      Definition timestamp : M.t U256.t :=
        LowM.Primitive Primitive.GetBlockTimestamp M.pure.

    and eval_primitive has a clause that returns state.(State.block_timestamp).

    Sanity-check that we can actually prove it returns the expected value
    from a state with a chosen block_timestamp. If this lemma closes, R020
    is operationally unblocked. *)

Module R020VerificationCheck.

  Lemma timestamp_returns_block_timestamp codes env state x :
    state.(State.block_timestamp) = x ->
    {{? codes, env, Some state |
      Stdlib.timestamp ⇓ Result.Ok x
    | Some state ?}}.
  Proof.
    intros H. unfold Stdlib.timestamp.
    eapply RunO.Primitive.
    - simpl. rewrite H. reflexivity.
    - apply RunO.Pure.
  Qed.

  Lemma number_returns_block_number codes env state x :
    state.(State.block_number) = x ->
    {{? codes, env, Some state |
      Stdlib.number ⇓ Result.Ok x
    | Some state ?}}.
  Proof.
    intros H. unfold Stdlib.number.
    eapply RunO.Primitive.
    - simpl. rewrite H. reflexivity.
    - apply RunO.Pure.
  Qed.

End R020VerificationCheck.

(** ----- R021 verification: RunO.CallContract now exists -----

    The upstream patch adds a CallContract constructor (and matching
    [cc] tactic) to [RunO.t]. It's intentionally permissive — the
    proof author picks [call_result] and [state_inter] freely — so
    soundness shifts to the proof-author level (the choice must be
    justified by a separate callee-spec axiom).

    The check below exercises the new constructor end-to-end: prove
    that *some* [(call_result, final_state)] discharges a CallContract
    followed by a Pure. This is the minimum bar — if it doesn't close,
    the constructor or the tactic is broken. *)

Module R021VerificationCheck.

  Lemma callcontract_can_be_discharged codes env state addr value input :
    {{? codes, env, Some state |
      LowM.CallContract addr value input false false (fun r => LowM.Pure r) ⇓ 0
    | Some state ?}}.
  Proof.
    cc. apply RunO.Pure.
  Qed.

End R021VerificationCheck.

(** ----- R050 verification: [staticcall] bridge composes -----

    [staticcall] is NOT a missing upstream primitive — it is already a
    composite of MLoad + CallContract + RLoad + MStore (see
    [simulations.RocqOfSolidity.Stdlib.staticcall]).
    [StaticCallBridge.run_staticcall_to_word] discharges the whole
    chain in one lemma given a precompile-disambiguation precondition
    and a proof-author-supplied [call_result].

    The check below exercises the bridge against an abstract non-
    precompile address. If the bridge ever stops composing, this fails
    and downstream R050-blocked proofs would too. *)
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.

Module R050VerificationCheck.

  Lemma staticcall_can_be_discharged
      codes env state
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (H_not_precompile : Stdlib.precompile_output addr [] = None) :
    exists state',
    {{? codes, env, Some state |
      Stdlib.staticcall g addr in_ insize out 32 ⇓
      Result.Ok call_result
    | state' ?}}.
  Proof.
    eexists.
    apply (StaticCallBridge.run_staticcall_to_word
             codes env state g addr in_ insize out
             call_result H_not_precompile).
  Qed.

  (** The bridge composes through the [LowM.Call (Stdlib.staticcall ...)
      LowM.Pure] shape that the shallow-form notation
      [[[ staticcall ~(| ... |) ]]] produces. This is the actual goal
      shape a walker arm sees inside a [let~ _24 := [[ staticcall ... ]]]. *)
  Lemma staticcall_composes_through_call
      codes env state
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (H_not_precompile : Stdlib.precompile_output addr [] = None) :
    exists state',
    {{? codes, env, Some state |
      LowM.Call (Stdlib.staticcall g addr in_ insize out 32) LowM.Pure ⇓
      Result.Ok call_result
    | state' ?}}.
  Proof.
    eexists.
    StaticCallBridge.sc_word call_result H_not_precompile.
    apply RunO.Pure.
  Qed.

  (** [iszero] post-bridge dispatches the canonical revert-on-zero
      branch trivially when the proof author picks a non-zero
      [call_result]. This exercises the [Pure.iszero] companion lemma. *)
  Lemma iszero_after_bridge_is_false
      (call_result : U256.t) :
    call_result <> 0 ->
    Pure.iszero call_result = 0.
  Proof.
    unfold Pure.iszero.
    destruct (call_result =? 0) eqn:E; intro Hne.
    - apply Z.eqb_eq in E. contradiction.
    - reflexivity.
  Qed.

End R050VerificationCheck.
