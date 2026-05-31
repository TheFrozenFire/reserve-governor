(** * StaticCallBridge — composing [staticcall] from existing primitives

    R050 framework gap closure (task #268).

    The Yul-level [staticcall] is *not* a missing upstream primitive — it
    is already defined in
    [rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v]
    as a fixed composition of existing primitives:

    {[
      Definition staticcall (g a in_ insize out outsize : U256.t) : M.t U256.t :=
        match precompile_output a [] with
        | Some _ => call_precompile a in_ insize out outsize
        | None =>
          let* input := LowM.Primitive (Primitive.MLoad in_ insize) M.pure in
          let* result := LowM.CallContract a 0 input true false M.pure in
          let* output := LowM.Primitive Primitive.RLoad M.pure in
          LowM.Primitive (Primitive.MStore out (List.firstn (Z.to_nat outsize) output)) (fun _ =>
          M.pure result)
        end.
    ]}

    Closing R050 therefore needs only a *bridge lemma* + a tactic alias
    + walker arms — not new upstream primitives. The bridge composes
    onto:
      - [LowM.CallContract] / [RunO.CallContract] / [cc] tactic (R021).
      - [Primitive.MLoad] / [MStore] / [RLoad] memory primitives.

    The bridge is intentionally minimal: the proof author supplies a
    *callee specification* (output bytes / single-word return) tying
    the address+input to the chosen [call_result], and the bridge
    discharges the rest mechanically.

    See WISDOM R063 for the design rationale and the 3-step recipe for
    downstream consumers. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module StaticCallBridge.

  (** ----- Layer 1: Parametric callee specification -----

      A [CalleeSpec] is the proof-author's assertion about *what the
      called contract returns*. For VersionRegistry's
      [roleRegistry.isOwnerOrEmergencyCouncil(caller)], the spec says
      "when [is_owner_or_emergency caller = true], the call returns 1".

      The bridge is agnostic to the spec's content — it just takes the
      caller's chosen [call_result] (a [U256.t]) and the chosen output
      bytes (a [list Z] of length [outsize]) and threads them through.

      Two convenience forms below cover the common cases:
        - [run_staticcall_to_word] — single-word ABI return (bool /
          uint256 / address). Most VersionRegistry / Guardian /
          RewardTokenRegistry staticcalls fit this shape.
        - [run_staticcall_general] — arbitrary output-bytes return.
          Use for dynamic-string returns (ProposalLib's
          [Versioned.version()] staticcall).
  *)

  (** ----- Layer 2: The bridge lemmas -----

      The bridge unfolds [staticcall], dispatches MLoad via [pr], the
      CallContract via [cc] (choosing both [call_result] and
      [state_inter]), the RLoad via [pr] on the chosen [state_inter],
      then MStore via [pr] for the final memory write.

      Precondition: [precompile_output addr [] = None] — i.e., [addr]
      is not one of the 1..9 precompile addresses. For the governor's
      external-contract staticcalls (roleRegistry, deployer.version(),
      etc.) this holds trivially since the callee is a regular Solidity
      contract deployed at a non-precompile address. The proof author
      discharges it via [reflexivity] once [addr] is a concrete value,
      or carries it as a hypothesis when [addr] is abstract.

      State plumbing: the bridge picks
        state_inter := state <| State.return_data := output_bytes |>
      so that the downstream RLoad reads [output_bytes] back. The final
      state has [memory] updated with [List.firstn outsize output_bytes]
      written at [out], and [return_data := output_bytes].
  *)

  (** Generic bridge — proof author supplies the full output byte
      sequence and the result value. *)
  Lemma run_staticcall_general
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out outsize : U256.t)
      (call_result : U256.t)
      (output_bytes : list Z)
      (H_not_precompile : precompile_output addr [] = None) :
    let memory' :=
      Memory.update_bytes state.(State.memory) out
        (List.firstn (Z.to_nat outsize) output_bytes) in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.staticcall g addr in_ insize out outsize ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros memory' state'.
    unfold Stdlib.staticcall.
    rewrite H_not_precompile.
    (* After unfolding M.let_ + M.pure, the body desugars (via LowM.let_'s
       fixpoint) into a chain of nested LowM.Primitive / LowM.CallContract
       nodes terminating in LowM.Pure. We step through them with pr / cc. *)
    cbn [M.let_ generic_let LowM.let_].
    (* MLoad. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* CallContract — choose call_result and state_inter. *)
    eapply RunO.CallContract with
      (call_result := call_result)
      (state_inter := Some (state <| State.return_data := output_bytes |>)).
    cbn [M.let_ generic_let LowM.let_].
    (* RLoad. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* MStore. *)
    eapply RunO.Primitive; [reflexivity|].
    (* Final Pure. *)
    apply RunO.Pure.
  Qed.

  (** Single-word bridge — the most common case. The output bytes are
      the U256 ABI-encoding of [call_result] (32 bytes, big-endian).
      Used for staticcalls that return a single bool/uint256/address. *)
  Lemma run_staticcall_to_word
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (H_not_precompile : precompile_output addr [] = None) :
    let output_bytes := Memory.u256_as_bytes call_result in
    let memory' :=
      Memory.update_bytes state.(State.memory) out
        (List.firstn 32 output_bytes) in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.staticcall g addr in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros output_bytes memory' state'.
    pose proof (run_staticcall_general codes env state
                  g addr in_ insize out 32 call_result
                  output_bytes H_not_precompile) as H.
    cbv zeta in H.
    change (Z.to_nat 32) with 32%nat in H.
    exact H.
  Qed.

  (** ----- Layer 3: Tactic alias -----

      The [sc] tactic drives a walker arm. It expects:
        - [precompile_output addr [] = None] discharged via [reflexivity]
          or a context hypothesis.
        - A callee-spec axiom [H_callee] supplying the [call_result]
          witness.

      Typical use inside a walker:
      {[
        | |- {{? _, _, _ | Stdlib.staticcall _ _ _ _ _ 32 ⇓ _ | _ ?}} =>
            c; [ apply (run_staticcall_to_word _ _ _ _ _ _ _ _
                          chosen_result H_not_precompile) | ]
      ]}

      For walker integration the bridge is composed under [LowM.Call]
      because the shallow-embedded calls wrap [Stdlib.staticcall] in a
      [LowM.Call] node. The walker arm steps through the [c] then
      applies the bridge.
  *)
  Ltac sc_word call_result H_not_precompile :=
    eapply RunO.Call;
      [ apply (run_staticcall_to_word _ _ _ _ _ _ _ _ call_result H_not_precompile)
      | ].

  Ltac sc_general call_result output_bytes H_not_precompile :=
    eapply RunO.Call;
      [ apply (run_staticcall_general _ _ _ _ _ _ _ _ _
                  call_result output_bytes H_not_precompile)
      | ].

End StaticCallBridge.
