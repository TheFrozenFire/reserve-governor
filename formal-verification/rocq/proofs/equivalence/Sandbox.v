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
