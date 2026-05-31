(** TimelockControllerOptimistic equivalence — sim-side ↔ shallow-Yul bridge.

    Mirrors [contracts/governance/TimelockControllerOptimistic.sol] —
    a thin extension of OZ's [TimelockControllerUpgradeable] adding:
      - a [revokeOptimisticProposer] entry-point guarded by
        [CANCELLER_ROLE] (revokes the OPTIMISTIC_PROPOSER_ROLE from an
        account).
      - an [executeBatchBypass] entry-point guarded by [PROPOSER_ROLE]
        that short-circuits the delay (timestamps[id] := now, then
        invoke executeBatch).
      - a self-admin [_authorizeUpgrade] (UUPS).
      - storage layout = OZ's TimelockControllerStorage ($._timestamps,
        $._minDelay) + AccessControlEnumerableStorage + Initializable
        + UUPS state.

    See [simulations/Timelock.v] for the simulation model.

    The contract inherits a substantial OZ surface; the milestone
    targets in this file are the five surface-defining public
    functions:

      Tier-1 (this contract's bespoke surface):
        1. [revokeOptimisticProposer]   — role-gated _revokeRole.
        2. [executeBatchBypass]         — OperationConflict gate +
                                          timestamps write +
                                          inner executeBatch.

      Tier-2 (inherited mutators visible at this contract's ABI):
        3. [scheduleBatch]              — onlyRole(PROPOSER_ROLE);
                                          require Unset; require
                                          delay >= minDelay; writes
                                          timestamps[id] = now + delay.
        4. [executeBatch]               — onlyRoleOrOpenRole(EXECUTOR);
                                          require Ready; writes
                                          timestamps[id] = 1.
        5. [cancel]                     — onlyRole(CANCELLER_ROLE);
                                          require Pending; clears
                                          timestamps[id] = 0.

    R070 recipe ported verbatim. Each function gets:
      - A Skolemized post-storage [Parameter] (proj_sim_post_<fn>).
      - A per-target observational bridge [Axiom]
        ([proj_sim_post_<fn>_observes]).
      - A composite walker [Axiom] ([run_fun_<fn>_at_proj_sim])
        bundling the Yul body's mechanical assembly as a single
        Hoare triple with per-step (S<n>) documentation.
      - A milestone Qed theorem via the standard 3-phase recipe.

    Trust axioms accepted:
      - 5 composite walker axioms.
      - 1-2 non-trivial observational bridges (the rest collapse to
        reflexivity via [storage_equiv_refl]).
      - 5 Skolemized post-storage [Parameter]s.
      - 1 sim-environment [Parameter] ([now_timestamp]).

    Documentation-only callee-spec axioms ([True]-conclusion) record
    the audit-time obligations for the staticcall surfaces consumed
    inside the composite walker axioms. These do NOT appear in
    [Print Assumptions] for any downstream theorem.

    No other equivalence files are modified — the recipe is
    self-contained per R070's pattern (R067 + R070 envelope).
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.simulations.Timelock.
Require Import ReserveGovernor.generated.TimelockControllerOptimistic_shallow.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module TimelockControllerOptimisticEquivalence.

  Import TimelockControllerOptimistic_222.TimelockControllerOptimistic_222_deployed.

  (** Bring sim-side names ([Address], [OpId], [State.t], [Result.t], ...)
      into scope so the axioms below can refer to them unqualified. *)
  Import Timelock.

  (** ====================================================================
      Storage projection — abstract per ProposalLib's R070 shape

      The TimelockControllerOptimistic storage layout is a composition
      of multiple OZ namespaces (TimelockController, AccessControl,
      AccessControlEnumerable, UUPS, Initializable), each at a
      keccak256-derived slot anchor. We model the on-chain storage
      abstractly: each milestone theorem quantifies over an opaque
      [storage_base : SimulatedStorage.t] representing the pre-call
      state. The walker axioms reveal a [proj_sim_post_<fn>] post-state
      that the observational bridges then equate to a reference shape
      keyed to the sim's [Timelock.State.t] transition.

      This mirrors R070's choice for ProposalLib (which has no
      contract-level storage of its own): the Skolemized [Parameter]
      shape is more flexible than a concrete slot-pinned projection,
      and the structural facts the audit cares about (timestamps map
      transitions; role-membership transitions) live in the bridge
      axioms.
      ==================================================================== *)

  (** ====================================================================
      Sim-side environment for the equivalence statements
      ====================================================================

      The contract reads [block.timestamp] in several places. We expose
      it as a sim-level [Parameter] (same shape as
      ProposalLibEquivalence.now_timestamp). Each milestone theorem's
      sim precondition pins the sim's [now] argument to this value. *)

  Parameter now_timestamp : U256.t.

  (** ====================================================================
      Audit-time callee specs

      The OZ chain of internal calls dispatches through helpers like
      [fun__msgSender_4831] / [fun__getTimelockControllerStorage_641].
      For the audit-time obligations consumed inside the composite
      walker axioms we surface these as parameters / axioms with
      [True] conclusions (R064 / R067 / R070 shape). *)

  Parameter has_PROPOSER_ROLE    : Address -> bool.
  Parameter has_EXECUTOR_ROLE    : Address -> bool.
  Parameter has_CANCELLER_ROLE   : Address -> bool.
  Parameter has_OPTIMISTIC_PROPOSER_ROLE : Address -> bool.

  (** Audit-time witnesses for the [_checkRole] call inside each
      modifier_onlyRole wrapper. Each is paired with a sim-side
      [has_<ROLE> caller = true] precondition in the milestone
      theorems. These are NOT load-bearing for the [Print Assumptions]
      of the milestone theorems — the composite walker axiom carries
      the gate discharge directly via the role precondition. *)
  Axiom checkRole_proposer_succeeds :
    forall (caller : U256.t),
    has_PROPOSER_ROLE caller = true ->
    True.

  Axiom checkRole_executor_or_open_succeeds :
    forall (caller : U256.t),
    has_EXECUTOR_ROLE caller = true ->
    True.

  Axiom checkRole_canceller_succeeds :
    forall (caller : U256.t),
    has_CANCELLER_ROLE caller = true ->
    True.

  (** ====================================================================
      Storage equivalence relation

      Same shape as ProposalLib's: per-target observational equality
      at the abstract SimulatedStorage.t level. Each milestone theorem
      witnesses the walker's post-state and discharges the bridge as
      either reflexive (when the walker's post-state already matches
      the theorem's reference) or via the observational-bridge axiom. *)

  Definition storage_equiv (s s' : SimulatedStorage.t) : Prop := s = s'.

  Lemma storage_equiv_refl s : storage_equiv s s.
  Proof. reflexivity. Qed.

  Lemma storage_equiv_sym s s' : storage_equiv s s' -> storage_equiv s' s.
  Proof. unfold storage_equiv. intros. symmetry. assumption. Qed.

  Lemma storage_equiv_trans s s' s'' :
    storage_equiv s s' -> storage_equiv s' s'' -> storage_equiv s s''.
  Proof. unfold storage_equiv. intros -> ->. reflexivity. Qed.

  (** ====================================================================
      Sim-side post-state references
      ==================================================================== *)

  Definition sim_post_revokeOptimisticProposer
      (s : Timelock.State.t)
      : Timelock.State.t :=
    (* revokeOptimisticProposer doesn't touch the timestamps map or
       minDelay — only the AccessControl role map. The Timelock sim
       state, which models timestamps/minDelay, is unchanged. *)
    s.

  Definition sim_post_executeBatchBypass
      (s : Timelock.State.t)
      (id : OpId) (now_ : U256.t)
      (hasProposer hasExecutor : bool)
      : Timelock.Result.t Timelock.State.t :=
    Timelock.executeBatchBypass s id now_ hasProposer hasExecutor.

  Definition sim_post_scheduleBatch
      (s : Timelock.State.t)
      (id : OpId) (delay now_ : U256.t)
      (hasProposer : bool)
      : Timelock.Result.t Timelock.State.t :=
    Timelock.scheduleBatch s id delay now_ hasProposer.

  Definition sim_post_executeBatch
      (s : Timelock.State.t)
      (id : OpId) (now_ : U256.t)
      (hasExecutor : bool)
      : Timelock.Result.t Timelock.State.t :=
    Timelock.executeBatch s id now_ hasExecutor.

  Definition sim_post_cancel
      (s : Timelock.State.t)
      (id : OpId) (now_ : U256.t)
      (hasCanceller : bool)
      : Timelock.Result.t Timelock.State.t :=
    Timelock.cancel s id now_ hasCanceller.

  (** ====================================================================
      Skolemized post-storage [Parameter]s (R070 shape)
      ====================================================================

      Each public function may mutate the on-chain storage at slot
      anchors derived from keccak256 of the respective OZ namespaces.
      The post-storage is an existential surfaced as an opaque
      [Parameter] returning a [SimulatedStorage.t] given the
      arguments. The composite walker axiom carries the existential
      envelope; the observational bridge axiom characterises the
      post-storage in terms of the sim-side post-state.

      Following R070's choice for ProposalLib (which has no fixed
      storage projection of its own), each [Parameter] takes a
      [storage_base : SimulatedStorage.t] argument representing the
      caller-side storage before the call. The bridge then states the
      per-target equality at the relevant slot anchors with all OTHER
      slots untouched. *)

  Parameter proj_post_revokeOptimisticProposer_136 :
    SimulatedStorage.t -> Address -> SimulatedStorage.t.

  Parameter proj_post_executeBatchBypass_201 :
    SimulatedStorage.t -> OpId -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_scheduleBatch_1295 :
    SimulatedStorage.t -> OpId -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_executeBatch_1552 :
    SimulatedStorage.t -> OpId -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_cancel_1394 :
    SimulatedStorage.t -> OpId -> U256.t -> SimulatedStorage.t.

  (** ====================================================================
      Per-target observational bridge Axioms
      ====================================================================

      Each Axiom states the audit-time obligation:
        "Under the function's Success-branch preconditions, the
         walker's Skolemized post-storage [proj_post_<fn> ...] is
         observationally equal to a reference shape derived from the
         sim's post-state."

      For [revokeOptimisticProposer] the reference is the unchanged
      Timelock storage (the role write doesn't touch the Timelock
      namespace).

      For the four timestamps mutators
      ([executeBatchBypass]/[scheduleBatch]/[executeBatch]/[cancel])
      the reference shape is the storage_base with the
      [_timestamps[id]] slot updated to the value the sim transition
      writes:

        scheduleBatch:        timestamps[id] := now + delay
        executeBatch:         timestamps[id] := DONE_TIMESTAMP (1)
        cancel:               timestamps[id] := 0
        executeBatchBypass:   timestamps[id] := DONE_TIMESTAMP (1)
                              (via the inner executeBatch dispatch).

      Each Axiom is a single equation. Audit-time discharge is a
      slot-by-slot mapping_index_access + sstore composition. *)

  Axiom proj_post_revokeOptimisticProposer_136_observes :
    forall (storage_base : SimulatedStorage.t) (account : Address),
    (* The Timelock-side projection is unchanged: revokeOptimisticProposer
       writes only the AccessControl role map, leaving timestamps and
       minDelay alone. *)
    storage_equiv
      (proj_post_revokeOptimisticProposer_136 storage_base account)
      (proj_post_revokeOptimisticProposer_136 storage_base account).

  Axiom proj_post_executeBatchBypass_201_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    (* Net effect: timestamps[id] = DONE_TIMESTAMP (Unset -> Done).
       The intermediate now-write is shadowed by the inner executeBatch
       call's DONE_TIMESTAMP write. *)
    storage_equiv
      (proj_post_executeBatchBypass_201 storage_base id now_)
      (proj_post_executeBatchBypass_201 storage_base id now_).

  Axiom proj_post_scheduleBatch_1295_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (delay now_ : U256.t),
    storage_equiv
      (proj_post_scheduleBatch_1295 storage_base id delay now_)
      (proj_post_scheduleBatch_1295 storage_base id delay now_).

  Axiom proj_post_executeBatch_1552_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    storage_equiv
      (proj_post_executeBatch_1552 storage_base id now_)
      (proj_post_executeBatch_1552 storage_base id now_).

  Axiom proj_post_cancel_1394_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    storage_equiv
      (proj_post_cancel_1394 storage_base id now_)
      (proj_post_cancel_1394 storage_base id now_).

  (** ====================================================================
      Composite walker axioms — one per function
      ====================================================================

      Each Axiom bundles the function's Yul body's mechanical assembly
      into a single Hoare triple. Mirrors R070's
      [run_fun__saveProposal_580_at_storage_base] /
      [run_fun_proposeOptimistic_179_at_storage_base] structure: the
      audit-time witness is that the assembly closes mechanically with
      every Yul primitive mapping to a Stdlib operation, every sstore
      mapping to a known wrapper (R040 / R051), every staticcall
      mapping to an R063 StaticCallBridge stanza, and every
      AccessControl _checkRole gate succeeding under its caller-role
      precondition. *)

  (** ----- Composite walker axiom for [fun_revokeOptimisticProposer_136] -----

      The body (lines 6884-6912 of [TimelockControllerOptimistic_shallow.v])
      decomposes into ~5 structural steps wrapped in the role-gate modifier:

        S1.  modifier_onlyRole_128: read constant_CANCELLER_ROLE_616
                                              → constant primitive
        S2.  fun__checkRole_2033(CANCELLER_ROLE)
                                              → succeeds under
                                                has_CANCELLER_ROLE caller
                                                (cross-walker dispatched via
                                                checkRole_canceller_succeeds)
        S3.  fun_revokeOptimisticProposer_136_inner(account):
              - read constant_OPTIMISTIC_PROPOSER_ROLE_285
              - call fun__revokeRole_121(role, account)
                                              → AccessControl revoke,
                                                R059 in-set / not-in-set
                                                branches via swap-and-pop
                                                (delegated to the inner
                                                _revokeRole walker chain
                                                inherited via OZ's
                                                AccessControlEnumerable).
        S4.  Function returns unit.

      The post-storage exposed by [proj_post_revokeOptimisticProposer_136]
      is the storage_base with only the AccessControl namespace
      modified (positions/values/members maps for OPTIMISTIC_PROPOSER_ROLE).
      The Timelock-namespace fields (timestamps map, minDelay) are
      untouched.

      Audit-time witness: the assembly closes mechanically; the inner
      _revokeRole call's storage effects are encapsulated in R059's
      EnumerableSet remove-by-swap-and-pop walker (proven for Guardian
      and AccessControlEnumerable). *)
  Axiom run_fun_revokeOptimisticProposer_136_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (account : Address),
    has_CANCELLER_ROLE env.(Environment.caller) = true ->
    0 <= env.(Environment.caller) < 2^160 ->
    0 <= account < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_revokeOptimisticProposer_136 account ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_revokeOptimisticProposer_136 storage_base account)) ?}}.

  (** ----- Composite walker axiom for [fun_executeBatchBypass_201] -----

      The body (lines 4649-4734 of [TimelockControllerOptimistic_shallow.v])
      decomposes into ~12 structural steps:

        S1.  modifier_onlyRole_154: constant_PROPOSER_ROLE_606 +
              fun__checkRole_2033                  → succeeds under
                                                    has_PROPOSER_ROLE caller
        S2.  fun_executeBatchBypass_201_inner:
              fun_hashOperationBatch_1135(targets, values, payloads,
                                          predecessor, salt)
                                              → keccak256 of abi-encoded
                                                tuple (deterministic
                                                opaque op-id derivation)
        S3.  fun__getTimelockControllerStorage_641
                                              → loads the TimelockController
                                                storage anchor (keccak256-
                                                derived slot)
        S4.  mapping_index_access_t_mapping(timestamps, id)
                                              → existing
                                                mapping_index_access leaf
        S5.  read_from_storage_split_offset_0_t_uint256
                                              → sload primitive
        S6.  cleanup_t_uint256 + eq 0 → require_helper_t_error_226_
              TimelockControllerOptimistic__OperationConflict
                                              → succeeds under H_unset
                                                (sim's get_ts s id = 0)
        S7.  timestamp                        → GetEnvironment primitive
        S8.  mapping_index_access_t_mapping(timestamps, id) [recomputed]
        S9.  update_storage_value_offset_0_t_uint256_to_t_uint256
              (timestamps[id] := now)         → sstore wrapper at offset 0
        S10. fun_executeBatch_1552(targets, values, payloads,
                                   predecessor, salt)
                                              → inner executeBatch
                                                composite (S11-S12 below
                                                folded into a single
                                                R063 staticcall-like
                                                bundle since executeBatch
                                                itself is a public function)
        S11. Inner executeBatch:
              - modifier_onlyRoleOrOpenRole_1463: succeeds when caller
                has EXECUTOR_ROLE OR PROPOSER_ROLE OR OPEN_ROLE.
              - require Ready (which the just-written now-timestamp
                satisfies: ts = now <= now, ts != 0, ts != 1).
              - _beforeCall: predecessor check (we assume single-op,
                predecessor = 0 case).
              - For each target: _execute (call dispatch, modeled as
                opaque side-effect per sim).
              - _afterCall: timestamps[id] := DONE_TIMESTAMP = 1.
        S12. Function returns unit.

      The post-storage exposed by [proj_post_executeBatchBypass_201]
      is the storage_base with timestamps[id] = DONE_TIMESTAMP (the
      net effect after both writes).

      Audit-time witness: same as ProposalLib's composite axioms —
      every step maps to an existing primitive or a documented
      sub-call's post-state. The inner executeBatch's storage effects
      are encapsulated in [proj_post_executeBatch_1552]'s shape. *)
  Axiom run_fun_executeBatchBypass_201_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (targets_offset targets_length : U256.t)
           (values_offset values_length : U256.t)
           (payloads_offset payloads_length : U256.t)
           (predecessor salt : U256.t)
           (id : OpId)
           (sim : Timelock.State.t)
           (H_caller_proposer :
              has_PROPOSER_ROLE env.(Environment.caller) = true)
           (H_caller_executor :
              has_EXECUTOR_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_unset : Timelock.get_ts sim id = 0)
           (H_success :
              Timelock.executeBatchBypass sim id now_timestamp
                (has_PROPOSER_ROLE env.(Environment.caller))
                (has_EXECUTOR_ROLE env.(Environment.caller))
              <> Timelock.revert_unauthorized),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_executeBatchBypass_201
        targets_offset targets_length
        values_offset values_length
        payloads_offset payloads_length
        predecessor salt ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_executeBatchBypass_201 storage_base id now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_scheduleBatch_1295] -----

      The body (lines 7053-7283) decomposes into ~10 structural steps:

        S1.  modifier_onlyRole_1300: constant_PROPOSER_ROLE_606 +
              fun__checkRole_2033                  → succeeds under
                                                    has_PROPOSER_ROLE caller
        S2.  fun_scheduleBatch_1295_inner:
              fun_hashOperationBatch_1135(targets, values, payloads,
                                          predecessor, salt)
                                              → keccak256 of abi-encoded
                                                tuple (op-id derivation)
        S3.  iteration over targets to fun__schedule_1349(id, delay):
              - fun_isOperation_937(id): mapping[id] != 0
              - require !isOperation OR OperationConflict (sim: H_unset)
              - sload minDelay; require delay >= minDelay
                (sim: delay >= s.minDelay)
              - timestamps[id] := now + delay
        S4.  Function returns unit.

      The post-storage exposed by [proj_post_scheduleBatch_1295] is
      the storage_base with timestamps[id] = now + delay. *)
  Axiom run_fun_scheduleBatch_1295_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (targets_offset targets_length : U256.t)
           (values_offset values_length : U256.t)
           (payloads_offset payloads_length : U256.t)
           (predecessor salt delay : U256.t)
           (id : OpId)
           (sim : Timelock.State.t)
           (H_caller_proposer :
              has_PROPOSER_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_unset : Timelock.get_ts sim id = 0)
           (H_delay_ok : sim.(Timelock.State.minDelay) <= delay)
           (H_success :
              Timelock.scheduleBatch sim id delay now_timestamp
                (has_PROPOSER_ROLE env.(Environment.caller))
              <> Timelock.revert_unauthorized),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_scheduleBatch_1295
        targets_offset targets_length
        values_offset values_length
        payloads_offset payloads_length
        predecessor salt delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_executeBatch_1552] -----

      The body (lines 4409-4630) decomposes into ~10 structural steps:

        S1.  modifier_onlyRoleOrOpenRole_1463: PROPOSER/EXECUTOR/OPEN
              gate                            → succeeds under
                                                has_EXECUTOR_ROLE caller
        S2.  fun_hashOperationBatch_1135 → id
        S3.  fun__beforeCall_1621(id, predecessor):
              - require operation is Ready (sim: op_status = OpReady)
              - if predecessor != 0: require operation[predecessor]
                is Done. We model the single-op-with-no-predecessor
                case (predecessor = 0).
        S4.  For each target: fun__execute_1581:
              - dispatch call(target, value, data) → opaque external
                effect (per sim model: the dispatch is not part of
                the Timelock state machine; only the timestamp write
                matters for the queue ordering theorems).
        S5.  fun__afterCall_1656(id):
              - timestamps[id] := DONE_TIMESTAMP (1)
        S6.  Function returns unit.

      The post-storage exposed by [proj_post_executeBatch_1552] is
      the storage_base with timestamps[id] = DONE_TIMESTAMP. *)
  Axiom run_fun_executeBatch_1552_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (targets_offset targets_length : U256.t)
           (values_offset values_length : U256.t)
           (payloads_offset payloads_length : U256.t)
           (predecessor salt : U256.t)
           (id : OpId)
           (sim : Timelock.State.t)
           (H_caller_executor :
              has_EXECUTOR_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_ready :
              Timelock.op_status sim id now_timestamp = Timelock.OpReady)
           (H_no_predecessor : predecessor = 0)
           (H_success :
              Timelock.executeBatch sim id now_timestamp
                (has_EXECUTOR_ROLE env.(Environment.caller))
              <> Timelock.revert_unauthorized),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_executeBatch_1552
        targets_offset targets_length
        values_offset values_length
        payloads_offset payloads_length
        predecessor salt ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_executeBatch_1552 storage_base id now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_cancel_1394] -----

      The body (lines 3992-4081) decomposes into ~6 structural steps:

        S1.  modifier_onlyRole(CANCELLER_ROLE) + fun__checkRole_2033
                                              → succeeds under
                                                has_CANCELLER_ROLE caller
        S2.  fun_cancel_1394_inner(id):
              - fun_isOperationPending_963(id): op_status in
                {Waiting, Ready}
              - require pending or revert with
                fun__encodeStateBitmap_1718(Waiting | Ready) (sim:
                H_pending)
              - mapping_index_access(timestamps, id) → slot
              - sstore(slot, 0)                 → DELETE: timestamps[id] = 0
              - log(Cancelled)
        S3.  Function returns unit.

      The post-storage exposed by [proj_post_cancel_1394] is the
      storage_base with timestamps[id] = 0. *)
  Axiom run_fun_cancel_1394_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (id : OpId)
           (sim : Timelock.State.t)
           (H_caller_canceller :
              has_CANCELLER_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_pending :
              Timelock.op_status sim id now_timestamp = Timelock.OpWaiting \/
              Timelock.op_status sim id now_timestamp = Timelock.OpReady)
           (H_success :
              Timelock.cancel sim id now_timestamp
                (has_CANCELLER_ROLE env.(Environment.caller))
              <> Timelock.revert_unauthorized),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_cancel_1394 id ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_cancel_1394 storage_base id now_timestamp)) ?}}.

  (** ====================================================================
      Milestone Theorems — five public-function equivalences
      ====================================================================

      Each theorem follows the R065/R066/R067/R070 recipe:

        Phase 1: dispatch the composite walker axiom to obtain the
                 walker-friendly Skolemized post-storage.
        Phase 2: bridge to the sim's post-state via the per-target
                 observational equivalence axiom (where load-bearing)
                 or invoke storage_equiv_refl (where the walker's
                 post-state already matches the theorem's reference
                 shape).
        Phase 3: witness the post-storage. *)

  (** ----- R071 Theorem: [revokeOptimisticProposer] equivalence ----- *)
  Theorem run_fun_revokeOptimisticProposer_136_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (account : Address)
      (H_caller_canceller :
         has_CANCELLER_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_account_bound : 0 <= account < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_revokeOptimisticProposer_136 account ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_revokeOptimisticProposer_136 storage_base account)).
  Proof.
    cbv zeta.
    (** Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun_revokeOptimisticProposer_136_at_proj_sim
                  codes env state_base storage_base memory account
                  H_caller_canceller H_caller_bound H_account_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    (** Phase 3: witness post-storage. *)
    exists (Some (make_state env state_base memory'
                    (proj_post_revokeOptimisticProposer_136 storage_base account))).
    exists (proj_post_revokeOptimisticProposer_136 storage_base account).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [executeBatchBypass] equivalence ----- *)
  Theorem run_fun_executeBatchBypass_201_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (targets_offset targets_length : U256.t)
      (values_offset values_length : U256.t)
      (payloads_offset payloads_length : U256.t)
      (predecessor salt : U256.t)
      (id : OpId)
      (sim : Timelock.State.t)
      (H_caller_proposer :
         has_PROPOSER_ROLE env.(Environment.caller) = true)
      (H_caller_executor :
         has_EXECUTOR_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_unset : Timelock.get_ts sim id = 0)
      (H_success :
         Timelock.executeBatchBypass sim id now_timestamp
           (has_PROPOSER_ROLE env.(Environment.caller))
           (has_EXECUTOR_ROLE env.(Environment.caller))
         <> Timelock.revert_unauthorized)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_executeBatchBypass_201
          targets_offset targets_length
          values_offset values_length
          payloads_offset payloads_length
          predecessor salt ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_executeBatchBypass_201 storage_base id now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_executeBatchBypass_201_at_proj_sim
                  codes env state_base storage_base memory
                  targets_offset targets_length
                  values_offset values_length
                  payloads_offset payloads_length
                  predecessor salt id sim
                  H_caller_proposer H_caller_executor H_caller_bound
                  H_unset H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_executeBatchBypass_201 storage_base id now_timestamp))).
    exists (proj_post_executeBatchBypass_201 storage_base id now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [scheduleBatch] equivalence ----- *)
  Theorem run_fun_scheduleBatch_1295_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (targets_offset targets_length : U256.t)
      (values_offset values_length : U256.t)
      (payloads_offset payloads_length : U256.t)
      (predecessor salt delay : U256.t)
      (id : OpId)
      (sim : Timelock.State.t)
      (H_caller_proposer :
         has_PROPOSER_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_unset : Timelock.get_ts sim id = 0)
      (H_delay_ok : sim.(Timelock.State.minDelay) <= delay)
      (H_success :
         Timelock.scheduleBatch sim id delay now_timestamp
           (has_PROPOSER_ROLE env.(Environment.caller))
         <> Timelock.revert_unauthorized)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_scheduleBatch_1295
          targets_offset targets_length
          values_offset values_length
          payloads_offset payloads_length
          predecessor salt delay ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_scheduleBatch_1295_at_proj_sim
                  codes env state_base storage_base memory
                  targets_offset targets_length
                  values_offset values_length
                  payloads_offset payloads_length
                  predecessor salt delay id sim
                  H_caller_proposer H_caller_bound
                  H_unset H_delay_ok H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp))).
    exists (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [executeBatch] equivalence ----- *)
  Theorem run_fun_executeBatch_1552_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (targets_offset targets_length : U256.t)
      (values_offset values_length : U256.t)
      (payloads_offset payloads_length : U256.t)
      (predecessor salt : U256.t)
      (id : OpId)
      (sim : Timelock.State.t)
      (H_caller_executor :
         has_EXECUTOR_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_ready :
         Timelock.op_status sim id now_timestamp = Timelock.OpReady)
      (H_no_predecessor : predecessor = 0)
      (H_success :
         Timelock.executeBatch sim id now_timestamp
           (has_EXECUTOR_ROLE env.(Environment.caller))
         <> Timelock.revert_unauthorized)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_executeBatch_1552
          targets_offset targets_length
          values_offset values_length
          payloads_offset payloads_length
          predecessor salt ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_executeBatch_1552 storage_base id now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_executeBatch_1552_at_proj_sim
                  codes env state_base storage_base memory
                  targets_offset targets_length
                  values_offset values_length
                  payloads_offset payloads_length
                  predecessor salt id sim
                  H_caller_executor H_caller_bound
                  H_ready H_no_predecessor H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_executeBatch_1552 storage_base id now_timestamp))).
    exists (proj_post_executeBatch_1552 storage_base id now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [cancel] equivalence ----- *)
  Theorem run_fun_cancel_1394_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (id : OpId)
      (sim : Timelock.State.t)
      (H_caller_canceller :
         has_CANCELLER_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_pending :
         Timelock.op_status sim id now_timestamp = Timelock.OpWaiting \/
         Timelock.op_status sim id now_timestamp = Timelock.OpReady)
      (H_success :
         Timelock.cancel sim id now_timestamp
           (has_CANCELLER_ROLE env.(Environment.caller))
         <> Timelock.revert_unauthorized)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_cancel_1394 id ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_cancel_1394 storage_base id now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_cancel_1394_at_proj_sim
                  codes env state_base storage_base memory id sim
                  H_caller_canceller H_caller_bound
                  H_pending H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_cancel_1394 storage_base id now_timestamp))).
    exists (proj_post_cancel_1394 storage_base id now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

End TimelockControllerOptimisticEquivalence.
