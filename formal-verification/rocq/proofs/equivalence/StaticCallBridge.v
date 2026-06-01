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

  (** ----- Convenience: the [staticcall + iszero + revert-on-zero]
      idiom.

      Every R050-blocked OZ-pattern mutator (VersionRegistry,
      Guardian, RewardTokenRegistry, ProposalLib) opens with the same
      shape:

      {[
        let~ _24 := [[ staticcall ~(| ... |) ]] in
        let_state~ 'tt := [[
          Shallow.if_ (|
            iszero ~(| _24 |),
            do~ [[ revert_forward_1 ~(||) ]] in
            M.pure (BlockUnit.Tt, tt),
            tt
          |)
        ]] default~ tt in
        ...
      ]}

      When the proof author picks [call_result = 1] (the role-check
      passes), [iszero call_result = 0] so [Shallow.if_] selects the
      default-pure branch. The lemma [staticcall_succeeds_iszero_false]
      packages this into a single step.

      The bridge expects the proof author to supply two pieces:
        - [H_not_precompile : precompile_output addr [] = None]
        - the choice that [call_result <> 0] (typically [call_result = 1]).

      The post-state is the same as [run_staticcall_to_word]'s: memory
      updated with the output bytes at [out], return_data set to
      [u256_as_bytes call_result]. *)

  Lemma run_staticcall_to_word_iszero_false
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (H_not_precompile : Stdlib.precompile_output addr [] = None)
      (H_call_result_nonzero : call_result <> 0) :
    let output_bytes := Memory.u256_as_bytes call_result in
    let memory' :=
      Memory.update_bytes state.(State.memory) out
        (List.firstn 32 output_bytes) in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    Pure.iszero call_result = 0 /\
    {{? codes, env, Some state |
      Stdlib.staticcall g addr in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros output_bytes memory' state'.
    split.
    - unfold Pure.iszero. destruct (call_result =? 0) eqn:E.
      + exfalso. apply Z.eqb_eq in E. apply H_call_result_nonzero. exact E.
      + reflexivity.
    - apply (run_staticcall_to_word codes env state g addr in_ insize out
               call_result H_not_precompile).
  Qed.

  (** ----- Companion leaf: loadimmutable -----

      The Yul prelude that flanks every external [staticcall] reads the
      callee's address out of an immutable slot via [loadimmutable].
      The upstream's [Stdlib.loadimmutable] reduces to a single
      [Primitive.LoadImmutable name] which [eval_primitive] dispatches
      against the current contract's [Account.immutables] dict. The
      proof author supplies the binding as a hypothesis. *)

  Lemma run_loadimmutable
      codes env state (name addr : U256.t)
      (account : Account.t)
      (H_account : Dict.get state.(State.accounts)
                     env.(Environment.address) = Some account)
      (H_immutable : Dict.get account.(Account.immutables) name = Some addr) :
    {{? codes, env, Some state |
      Stdlib.loadimmutable name ⇓ Result.Ok addr
    | Some state ?}}.
  Proof.
    unfold Stdlib.loadimmutable.
    eapply RunO.Primitive.
    - simpl. rewrite H_account, H_immutable. reflexivity.
    - apply RunO.Pure.
  Qed.

  (** ----- Companion leaf: returndatasize after the bridge -----

      After [run_staticcall_to_word] finishes, the state has
      [return_data = u256_as_bytes call_result], a 32-byte list. So
      [returndatasize] returns 32. This closes the R058 (R-returndatasize)
      residual that was flagged as "the most subtle" — the bridge fully
      pins down the post-staticcall state, so the value is concrete. *)

  Lemma length_u256_as_bytes (v : U256.t) :
    List.length (Memory.u256_as_bytes v) = 32%nat.
  Proof.
    unfold Memory.u256_as_bytes.
    rewrite List.length_map.
    rewrite List.length_seq.
    reflexivity.
  Qed.

  Lemma run_returndatasize_after_bridge
      codes env state v memory_post :
    let state_post :=
      state
        <| State.return_data := Memory.u256_as_bytes v |>
        <| State.memory := memory_post |> in
    {{? codes, env, Some state_post |
      Stdlib.returndatasize ⇓ Result.Ok 32
    | Some state_post ?}}.
  Proof.
    intros state_post.
    unfold Stdlib.returndatasize.
    eapply RunO.Primitive with (value := Memory.u256_as_bytes v).
    - reflexivity.
    - apply RunO.PureEq; [|reflexivity].
      rewrite length_u256_as_bytes. reflexivity.
  Qed.

  (** ----- Layer 4: Walker arm patterns -----

      Two canonical walker arms cover the two shapes of staticcall use:

      (1) Bare [staticcall] inside a [LowM.Call]:
      {[
        | |- {{? _, _, _ |
              LowM.Call (Stdlib.staticcall _ _ _ _ _ 32) _ ⇓ _ | _ ?}} =>
            sc_word chosen_result H_not_precompile
      ]}

      (2) Bare [staticcall] (post-unfold):
      {[
        | |- {{? _, _, _ |
              Stdlib.staticcall _ _ _ _ _ 32 ⇓ _ | _ ?}} =>
            apply (run_staticcall_to_word _ _ _ _ _ _ _ _ chosen_result H_not_precompile)
      ]}

      For the general (non-32-byte) case, substitute [sc_general]. *)

  (** ====================================================================
      Layer 5: delegatecall bridge — R091 framework primitive
      ====================================================================

      Sibling to [run_staticcall_general] / [run_staticcall_to_word] above,
      but for the [Stdlib.delegatecall] opcode.  The upstream definition
      mirrors [staticcall]'s shape exactly with two semantic differences:

        - The [is_delegate] flag on [LowM.CallContract] is [true]
          (instead of [is_static = true]).
        - There is NO precompile fast-path — the upstream's
          [Stdlib.delegatecall] does not guard on [precompile_output],
          so the bridge has no precompile precondition.

      The key SEMANTIC difference at the proof-rule level: the
      [RunO.CallContract] inference rule treats [is_static] /
      [is_delegate] uniformly (both flags are arguments but the
      proof-author is free to pick [call_result] and [state_inter]
      regardless of the flags).  The flag IS load-bearing for the
      [eval] interpreter (it changes which [Environment] gets built
      for the callee, and whether sstore is permitted), but the
      [RunO] rule pushes that load to the proof author via the
      callee-spec axiom.

      What the BRIDGE captures is the *shape* of the post-state in
      Yul terms: input bytes are mloaded; result is mstored; the
      delegatecall's storage-write side effect appears in the
      [state_inter] choice.  The base bridge below threads only the
      memory + return_data write effect; the [_absorbing] sibling
      in [AbiEncoding.v] threads the storage-write Skolem as well
      (mirroring R082's absorbing staticcall sibling).

      Soundness justification for treating delegatecall this way at
      the bridge layer:

        - [LowM.CallContract] is a single trust-based proof rule
          shared across call/staticcall/delegatecall (see upstream
          [RunO.CallContract] which is documented as a "trust-based
          proof rule" pending eval-soundness mechanization).
        - The proof author is required (by audit discipline) to
          discharge the choice of [call_result] and [state_inter]
          via a per-target callee-spec axiom.
        - For delegatecall, the callee-spec axiom commits to BOTH
          the [call_result] AND the storage-mutation effect.  The
          absorbing variant exposes this via the
          [delegatecall_post_storage] Skolem.

      The base lemma below is fully proved (modulo the underlying
      [RunO.CallContract] rule's own status). *)

  (** Generic delegatecall bridge — proof author supplies the full
      output byte sequence, the result value, and the post-state's
      [State.t] shape (which may carry a storage mutation).  Mirrors
      [run_staticcall_general] except:

        - No [H_not_precompile] precondition (delegatecall has no
          precompile guard).
        - The [state_inter] for the inner [LowM.CallContract] step
          is explicit, so the proof author can thread storage writes
          through.

      The post-state's [return_data] is set to [output_bytes] and
      its [memory] is updated with [List.firstn outsize output_bytes]
      at [out].  Storage writes (the delegatecall's side effect on
      the caller's storage) are encoded in the [callee_post_state]
      argument: the proof author passes the desired post-storage
      shape; the bridge threads it as the CallContract's
      [state_inter]. *)
  Lemma run_delegatecall_general
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out outsize : U256.t)
      (call_result : U256.t)
      (output_bytes : list Z)
      (callee_post_state : State.t) :
    let memory' :=
      Memory.update_bytes callee_post_state.(State.memory) out
        (List.firstn (Z.to_nat outsize) output_bytes) in
    let state' :=
      callee_post_state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.delegatecall g addr in_ insize out outsize ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros memory' state'.
    unfold Stdlib.delegatecall.
    cbn [M.let_ generic_let LowM.let_].
    (* MLoad of input bytes. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* CallContract — choose call_result and state_inter to carry the
       callee's storage-mutation effect. *)
    eapply RunO.CallContract with
      (call_result := call_result)
      (state_inter := Some (callee_post_state
                              <| State.return_data := output_bytes |>)).
    cbn [M.let_ generic_let LowM.let_].
    (* RLoad reads back [output_bytes]. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* MStore writes [List.firstn outsize output_bytes] at [out]. *)
    eapply RunO.Primitive; [reflexivity|].
    apply RunO.Pure.
  Qed.

  (** Single-word delegatecall bridge — the [outsize = 32] specialisation.
      Used for delegatecall targets that return a single bool/uint256
      (e.g. the `expr_4407_component_1` bool from
      [fun_functionDelegateCall_4416], or ProposalLib's
      delegate-target return shape).  Mirrors [run_staticcall_to_word]. *)
  Lemma run_delegatecall_to_word
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (callee_post_state : State.t) :
    let output_bytes := Memory.u256_as_bytes call_result in
    let memory' :=
      Memory.update_bytes callee_post_state.(State.memory) out
        (List.firstn 32 output_bytes) in
    let state' :=
      callee_post_state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.delegatecall g addr in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros output_bytes memory' state'.
    pose proof (run_delegatecall_general codes env state
                  g addr in_ insize out 32 call_result
                  output_bytes callee_post_state) as H.
    cbv zeta in H.
    change (Z.to_nat 32) with 32%nat in H.
    exact H.
  Qed.

  (** Zero-return delegatecall — [outsize = 0].  Used for
      delegatecalls whose return data is not consumed by the
      surrounding Yul (e.g. ROG's [fun_propose_389] delegatecall into
      ProposalLib.proposePessimistic which uses [outsize = 0] —
      the caller decodes via [returndatasize] / [returndatacopy] after).
      Same proof shape as [run_delegatecall_general] with [outsize = 0]
      forcing [List.firstn 0 output_bytes = []], leaving memory
      unchanged. *)
  Lemma run_delegatecall_to_nothing
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr in_ insize out : U256.t)
      (call_result : U256.t)
      (output_bytes : list Z)
      (callee_post_state : State.t) :
    let memory' :=
      Memory.update_bytes callee_post_state.(State.memory) out [] in
    let state' :=
      callee_post_state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.delegatecall g addr in_ insize out 0 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros memory' state'.
    pose proof (run_delegatecall_general codes env state
                  g addr in_ insize out 0 call_result
                  output_bytes callee_post_state) as H.
    cbv zeta in H.
    change (Z.to_nat 0) with 0%nat in H.
    change (List.firstn 0 output_bytes) with (@nil Z) in H.
    exact H.
  Qed.

  (** Tactic aliases mirroring [sc_word] / [sc_general] — drive a
      walker arm past a delegatecall by supplying the callee-spec
      witnesses (result + output bytes + post-state).  The post-state
      argument carries the callee's storage-mutation effect. *)
  Ltac dc_word call_result callee_post_state :=
    eapply RunO.Call;
      [ apply (run_delegatecall_to_word _ _ _ _ _ _ _ _ _
                  call_result callee_post_state)
      | ].

  Ltac dc_general call_result output_bytes callee_post_state :=
    eapply RunO.Call;
      [ apply (run_delegatecall_general _ _ _ _ _ _ _ _ _
                  call_result output_bytes callee_post_state)
      | ].

  Ltac dc_to_nothing call_result output_bytes callee_post_state :=
    eapply RunO.Call;
      [ apply (run_delegatecall_to_nothing _ _ _ _ _ _ _ _
                  call_result output_bytes callee_post_state)
      | ].

  (** ====================================================================
      Layer 6: low-level [call] bridge — R093 framework primitive
      ====================================================================

      Sibling to [run_staticcall_general] / [run_delegatecall_general]
      above, but for the [Stdlib.call] opcode.  Closes R086 — the
      SafeERC20 library-call gap that blocks the three
      UnstakingManager mutator walkers (createLock / cancelLock /
      claimLock) and the four StakingVaultExchange mutator walkers
      (deposit / mint / withdraw / redeem), all of which invoke
      [SafeERC20.{safeTransfer, safeTransferFrom, forceApprove}] via
      [using SafeERC20 for IERC20] and the solc-emitted [linkersymbol]
      + inlined library body shape.

      The library body itself is INLINED in the consuming Yul (no
      delegatecall — solc inlines internal library functions when
      possible).  What is NOT inlined is the actual external token
      [call(gas(), token, 0, in_, insize, 0, 32)] to the ERC20
      [transfer]/[transferFrom]/[approve] selector.  That low-level
      [call] is what this bridge primitive covers.

      Semantic difference vs [staticcall] / [delegatecall]:

        - [staticcall]: read-only callee context (cannot write
          storage).  Caller storage unchanged.  Has a precompile
          fast-path.
        - [delegatecall]: callee runs in CALLER's storage context
          (writes caller storage).  No precompile fast-path.  No
          [value] (ETH) transfer.
        - [call] (this bridge): callee runs in TARGET's storage
          context (writes only target storage from caller's POV;
          from the equivalence-projection's POV the target's
          storage is opaque).  Caller storage unchanged.  Has a
          precompile fast-path AND a [gas < 100 /\ v = 0]
          gas-fast-path that short-circuits to [RStore []] + [pure 0].

      The gas-fast-path is the only structural addition vs
      staticcall: the upstream [Stdlib.call] body is

      {[
        if andb (g <? 100) (v =? 0) then
          let* tt := LowM.Primitive (Primitive.RStore []) M.pure in
          M.pure 0
        else
          match precompile_output a [] with
          | Some _ => call_precompile ...
          | None => <same MLoad-CallContract-RLoad-MStore as staticcall>
          end.
      ]}

      For SafeERC20 token calls, [g = gas()] (full remaining gas,
      always >> 100) and [v = 0], so the andb test is FALSE — we
      always take the [else] branch.  The bridge below carries
      [H_not_fast_path : ~ (g < 100 /\ v = 0)] (or equivalently
      [(g <? 100) && (v =? 0) = false]) as a precondition, which is
      trivially discharged when [g = gas()] (a witness > 100) and
      [v = 0] (a literal).  The default-pure consumer case in OZ
      SafeERC20 always sets [v = 0] AND uses [g = gas()] so this
      branch is universally inhabited.

      What the BRIDGE captures is the *shape* of the post-state in
      Yul terms: input bytes are mloaded; result is mstored; the
      [call]'s storage-write side effect lives in TARGET's storage
      (NOT in the proof's [State.t] projection of the caller's
      [SimulatedStorage.t]).  From the caller's perspective the
      storage is unchanged at the projection level; the only
      observable mutation is [memory] (the return-data write at
      [out]) and [return_data].  This matches [staticcall]'s shape
      EXACTLY — storage unchanged at the caller's projection layer.

      Soundness justification:

        - [LowM.CallContract] is the shared trust-based proof rule
          across call/staticcall/delegatecall (the [is_static] /
          [is_delegate] flags are inputs but the [RunO.CallContract]
          rule treats them uniformly at the bridge layer; the eval
          interpreter consumes the flags to set the callee's
          [Environment]).
        - The base [call] bridge is provable from
          [RunO.CallContract] + [RunO.Primitive] in the same way
          [staticcall] is — the only structural difference is the
          gas-fast-path test, which the precondition rules out.
        - At the caller's projection layer storage is unchanged
          (the call's effects are on the target's storage, which is
          opaque from the caller's [SimulatedStorage.t] projection).
          This matches [staticcall]'s storage shape and differs from
          [delegatecall]'s shape.

      Net trust: ZERO new axioms at the base-bridge layer (three
      Qed lemmas).  The absorbing-Skolem variant in [AbiEncoding.v]
      adds +1 axiom (the [_absorbing] form) following the staticcall
      template, NOT the delegatecall template (since [call] does not
      mutate caller storage).

      Reference: [Stdlib.call] in
      [rocq-of-solidity/rocq/RocqOfSolidity/simulations/RocqOfSolidity.v]
      (line 1085). *)

  (** Generic [call] bridge — proof author supplies the full
      output byte sequence and the result value.  Mirrors
      [run_staticcall_general] with one additional precondition:
      the gas-fast-path is not taken.  The post-state's storage
      is UNCHANGED at the caller's projection level (the call's
      effects live in the target's opaque storage). *)
  Lemma run_call_general
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr v in_ insize out outsize : U256.t)
      (call_result : U256.t)
      (output_bytes : list Z)
      (H_not_fast_path : ((g <? 100) && (v =? 0))%bool = false)
      (H_not_precompile : Stdlib.precompile_output addr [] = None) :
    let memory' :=
      Memory.update_bytes state.(State.memory) out
        (List.firstn (Z.to_nat outsize) output_bytes) in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.call g addr v in_ insize out outsize ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros memory' state'.
    unfold Stdlib.call.
    rewrite H_not_fast_path.
    rewrite H_not_precompile.
    cbn [M.let_ generic_let LowM.let_].
    (* MLoad of input bytes. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* CallContract — choose call_result and state_inter.  Storage at
       the caller's projection level is unchanged. *)
    eapply RunO.CallContract with
      (call_result := call_result)
      (state_inter := Some (state <| State.return_data := output_bytes |>)).
    cbn [M.let_ generic_let LowM.let_].
    (* RLoad reads back [output_bytes]. *)
    eapply RunO.Primitive; [reflexivity|].
    cbn [M.let_ generic_let LowM.let_].
    (* MStore writes [List.firstn outsize output_bytes] at [out]. *)
    eapply RunO.Primitive; [reflexivity|].
    apply RunO.Pure.
  Qed.

  (** Single-word [call] bridge — the [outsize = 32] specialisation.
      Used for ERC20 [transfer]/[transferFrom]/[approve] returns,
      which decode as a single bool.  Mirrors
      [run_staticcall_to_word]. *)
  Lemma run_call_to_word
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr v in_ insize out : U256.t)
      (call_result : U256.t)
      (H_not_fast_path : ((g <? 100) && (v =? 0))%bool = false)
      (H_not_precompile : Stdlib.precompile_output addr [] = None) :
    let output_bytes := Memory.u256_as_bytes call_result in
    let memory' :=
      Memory.update_bytes state.(State.memory) out
        (List.firstn 32 output_bytes) in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.call g addr v in_ insize out 32 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros output_bytes memory' state'.
    pose proof (run_call_general codes env state
                  g addr v in_ insize out 32 call_result
                  output_bytes H_not_fast_path H_not_precompile) as H.
    cbv zeta in H.
    change (Z.to_nat 32) with 32%nat in H.
    exact H.
  Qed.

  (** Zero-return [call] — [outsize = 0].  Used when the caller
      ignores the return data (e.g. [callOptionalReturn]'s mload
      decode is gated on a returndatasize > 0 check).  Same proof
      shape as [run_call_general] with [outsize = 0] forcing
      [List.firstn 0 output_bytes = []], leaving memory unchanged. *)
  Lemma run_call_to_nothing
      (codes : Codes.t) (env : Environment.t) (state : State.t)
      (g addr v in_ insize out : U256.t)
      (call_result : U256.t)
      (output_bytes : list Z)
      (H_not_fast_path : ((g <? 100) && (v =? 0))%bool = false)
      (H_not_precompile : Stdlib.precompile_output addr [] = None) :
    let memory' :=
      Memory.update_bytes state.(State.memory) out [] in
    let state' :=
      state
        <| State.return_data := output_bytes |>
        <| State.memory := memory' |> in
    {{? codes, env, Some state |
      Stdlib.call g addr v in_ insize out 0 ⇓
      Result.Ok call_result
    | Some state' ?}}.
  Proof.
    intros memory' state'.
    pose proof (run_call_general codes env state
                  g addr v in_ insize out 0 call_result
                  output_bytes H_not_fast_path H_not_precompile) as H.
    cbv zeta in H.
    change (Z.to_nat 0) with 0%nat in H.
    change (List.firstn 0 output_bytes) with (@nil Z) in H.
    exact H.
  Qed.

  (** Tactic aliases mirroring [sc_word] / [dc_word] — drive a
      walker arm past a [call] by supplying the callee-spec
      witnesses.  The proof author also discharges the two
      preconditions (gas-fast-path and not-precompile). *)
  Ltac call_word call_result H_not_fast_path H_not_precompile :=
    eapply RunO.Call;
      [ apply (run_call_to_word _ _ _ _ _ _ _ _ _
                  call_result H_not_fast_path H_not_precompile)
      | ].

  Ltac call_general call_result output_bytes H_not_fast_path H_not_precompile :=
    eapply RunO.Call;
      [ apply (run_call_general _ _ _ _ _ _ _ _ _ _
                  call_result output_bytes
                  H_not_fast_path H_not_precompile)
      | ].

  Ltac call_to_nothing call_result output_bytes H_not_fast_path H_not_precompile :=
    eapply RunO.Call;
      [ apply (run_call_to_nothing _ _ _ _ _ _ _ _ _
                  call_result output_bytes
                  H_not_fast_path H_not_precompile)
      | ].

  (** ====================================================================
      Layer 7: [linkersymbol] companion leaf — R093 framework primitive
      ====================================================================

      Solidity LIBRARIES are referenced by [linkersymbol] in the
      compiled Yul.  At link time the linker substitutes a real
      library address; from the contract's POV the value is opaque.
      The upstream's [Stdlib.linkersymbol] models this as identity
      on the name argument:

      {[
        Definition linkersymbol (name : U256.t) : M.t U256.t :=
          M.pure name.
      ]}

      i.e. the "address" returned IS the symbol name.  This is
      sound because every consumer of the returned value either:

        - never uses the value (the [linkersymbol] read is a Yul
          artifact emitted alongside an inlined library call body —
          see UnstakingManager's [fun_claimLock_270] where
          [expr_255_address := linkersymbol(SafeERC20)] is computed
          but never referenced again), or
        - passes the value to an external [call]/[delegatecall]
          where the address-vs-name distinction is opaque from the
          [RunO.CallContract] proof rule's perspective (the rule
          accepts any [U256.t] as the callee address).

      The walker step for [linkersymbol] is trivially dischargeable
      via the standard [p.] (pure) tactic since the upstream
      definition is [M.pure name].  This companion lemma provides
      an ergonomic alias for downstream walker code.

      Soundness: the upstream definition fixes the return value to
      the name argument.  This bridge merely witnesses the [RunO.Pure]
      step.  No new axioms needed — fully Qed-proved. *)

  Lemma run_linkersymbol
      codes env state (name : U256.t) :
    {{? codes, env, Some state |
      Stdlib.linkersymbol name ⇓ Result.Ok name
    | Some state ?}}.
  Proof.
    unfold Stdlib.linkersymbol.
    apply RunO.Pure.
  Qed.

  (** Tactic alias: drive a walker arm past a [linkersymbol] read
      by deferring to the trivial pure step.  Inside a [let_step]
      this typically reduces to [l. { p. }] — see ProposalLib.v
      lines 1637, 1674 for the inline-tactic shape. *)
  Ltac ls := apply run_linkersymbol.

End StaticCallBridge.
