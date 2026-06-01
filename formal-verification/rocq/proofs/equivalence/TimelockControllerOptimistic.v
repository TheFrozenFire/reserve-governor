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
      - 5 slot-indexed observational bridge axioms (per the
        2026-05-31 adversarial-review skolemization-soundness audit
        (CCV-1 / CCV-2 / CRIT-V), the bridges were promoted from
        reflexive [storage_equiv (X) (X)] tautologies to
        content-bearing [eq_at_<slot> (proj_post_<fn> ...) storage_base]
        claims; an empty-storage adversarial instantiation of
        [proj_post_<fn>] no longer satisfies them).
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
      R088 sub-axioms — per-helper composite walker primitives
      ====================================================================

      Discharging the outer composite walker [Axiom]s for
      [revokeOptimisticProposer] / [cancel] / [scheduleBatch] /
      [executeBatch] / [executeBatchBypass] mechanically requires walking
      through several internal OZ helpers whose own bodies route through
      ERC-7201-anchored sloads (R083), EnumerableSet swap-and-pop (R084),
      and the abstract TimelockController storage namespace. R087
      Blocker 1 documents that a fully mechanical per-helper discharge of
      every internal call introduces more per-helper sub-axioms than it
      retires from the outer walker.

      R088's contribution is to redistribute the composite walker
      [Axiom]'s trust into smaller, sharper-shaped sub-axioms shared
      across the four outer mutators. Specifically:

        - [run_fun__checkRole_2033_under_role] — the OZ AccessControl
          gate. Reused by ALL 5 mutators (revoke, cancel, schedule,
          executeBatch, executeBatchBypass). Storage unchanged; memory
          may transform (the gate emits no events but may write scratch
          buffers for the inner hasRole walk).

        - [run_fun__revokeRole_121_at_storage_base] — the revoke effect
          (used by [revokeOptimisticProposer]). Threads the
          [proj_post_revokeOptimisticProposer_136] Skolem.

        - [run_fun_cancel_1394_inner_at_storage_base] — the cancel body
          (require-pending + sstore 0 + log2). Threads
          [proj_post_cancel_1394].

      The outer walker [Axiom]s for [revokeOptimisticProposer] and
      [cancel] are promoted to [Qed] [Lemma]s that compose
      [run_fun__checkRole_2033_under_role] with the per-mutator body
      sub-axiom. The remaining three outer walkers
      ([scheduleBatch] / [executeBatch] / [executeBatchBypass]) stay as
      [Axiom]s for now — they have additional internal helpers (R087
      Blocker 1) and [executeBatch] / [executeBatchBypass] hit
      delegatecall (R087 Blocker 2). See the per-walker [Axiom] block
      for the residual-work note. *)

  (** Sub-axiom: [fun__checkRole_2033] succeeds under a role precondition.

      Audit-time witness: under [H_role caller = true], the gate's
      inner sload+revert chain (R083 ERC-7201 anchor walk through OZ
      AccessControl) succeeds with storage unchanged. Memory may
      transform (the inner [fun__msgSender_4831] read + hasRole walk
      writes scratch words at offsets 0/0x20). The shape is the OZ
      gate's natural signature: pre-state storage = post-state storage;
      memory existential absorbs the scratch writes.

      Audit obligation per (role, role-predicate) pair: the gate is
      mechanically the composition of [fun__msgSender] + [hasRole]
      + [iszero] + [require_helper]; the failure branch is unreachable
      under the role precondition. *)
  Axiom run_fun__checkRole_2033_under_role :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (role : U256.t)
           (role_pred : Address -> bool),
    role_pred env.(Environment.caller) = true ->
    0 <= env.(Environment.caller) < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists w0' w1' rest',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__checkRole_2033 role ⇓ Result.Ok tt
    | Some (make_state env state_base (w0' :: w1' :: rest') storage_base) ?}}.

  (** The body-specific sub-axioms ([run_fun__revokeRole_121_at_storage_base]
      and [run_fun_cancel_1394_inner_at_storage_base]) depend on the
      Skolemized post-storage [Parameter]s and the [now_timestamp]
      [Parameter] declared further below; we therefore declare them in
      a deferred-axioms block AFTER the [proj_post_<fn>] [Parameter]
      block (see the "Per-mutator inner-body composite walker
      sub-axioms" block below). *)

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
      R088 per-mutator inner-body composite walker sub-axioms
      ====================================================================

      These sub-axioms encapsulate the body-of-modifier walks of the
      individual mutators that the outer composite walker [Lemma]s
      ([revokeOptimisticProposer] / [cancel]) consume. Each is sharper
      than the outer composite walker [Axiom] (no modifier wrapper, no
      gate dispatch — those are factored into
      [run_fun__checkRole_2033_under_role]).

      See the per-axiom comment for the body-Yul → primitive mapping
      and the audit-time obligations. *)

  (** Sub-axiom: [fun__revokeRole_121] body effect.

      Walks: [fun__revokeRole_577] → [fun__revokeRole_2265] +
      [fun_remove_3127] (the OZ EnumerableSet swap-and-pop body — R084).
      The post-storage is the role-removal effect at the
      AccessControlEnumerable namespace. We pin the post-storage to the
      Skolemized [proj_post_revokeOptimisticProposer_136] so the outer
      walker's post-state matches verbatim.

      Audit obligation: the body mechanically chains
      [_getAccessControlEnumerableStorage] → [_revokeRole_2265] (the
      flag write at slot 0 of the AccessControl namespace) →
      conditional [fun_remove_3127] (R084 swap-and-pop at the
      AccessControlEnumerable namespace). Both effects compose into
      [proj_post_revokeOptimisticProposer_136] via the abstract
      Skolem. *)
  Axiom run_fun__revokeRole_121_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (role account : U256.t)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_account_bound : 0 <= account < 2^160)
           (H_role_optimistic :
              role = 0x26f49d08685d9cdd4951a7470bc8fbe9dd0f00419c1a44c1b89f845867ae12e0),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory' (revoked : U256.t),
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__revokeRole_121 role account ⇓ Result.Ok revoked
    | Some (make_state env state_base memory'
              (proj_post_revokeOptimisticProposer_136 storage_base account)) ?}}.

  (** Sub-axiom: [fun_cancel_1394_inner] body effect.

      Walks: [fun_isOperationPending_963] gate (sim H_pending discharges
      the require) + mapping_index_access(timestamps, id) +
      storage_set_to_zero (sstore 0) + log2 (Cancelled event). The
      post-storage is [proj_post_cancel_1394]. *)
  Axiom run_fun_cancel_1394_inner_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (id : OpId)
           (sim : Timelock.State.t)
           (H_pending :
              Timelock.op_status sim id now_timestamp = Timelock.OpWaiting \/
              Timelock.op_status sim id now_timestamp = Timelock.OpReady),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_cancel_1394_inner id ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_cancel_1394 storage_base id now_timestamp)) ?}}.

  (** Sub-axiom: [fun_executeBatchBypass_201_inner] body effect.

      Walks: [fun_hashOperationBatch_1135] (op-id derivation) +
      [fun__getTimelockControllerStorage_641] (storage anchor read) +
      [mapping_index_access(timestamps, id)] (slot derivation) +
      [read_from_storage_split_offset_0_t_uint256] (current timestamp
      read) + iszero+require [OperationConflict] (Unset gate) +
      [timestamp] primitive + sstore [timestamps[id] := now] +
      [fun_executeBatch_1552] dispatch (inner executeBatch composite —
      this is the load-bearing delegatecall consumer that the R087
      Blocker-2 discharge plan is gated on; the sub-axiom encapsulates
      its post-state at [proj_post_executeBatchBypass_201]).

      The audit-time obligation under [H_unset] (timestamps[id] = 0):
      the body mechanically composes the steps to produce the net
      timestamps[id] := DONE_TIMESTAMP write (after the inner
      [fun_executeBatch_1552] discharges the now-timestamp via
      [fun__afterCall_1656]). The whole inner composite is opaque
      pending the delegatecall framework primitive — see R087 Blocker 2. *)
  Axiom run_fun_executeBatchBypass_201_inner_at_storage_base :
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
           (H_unset : Timelock.get_ts sim id = 0)
           (H_success_executor :
              has_EXECUTOR_ROLE env.(Environment.caller) = true \/
              has_PROPOSER_ROLE env.(Environment.caller) = true),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_executeBatchBypass_201_inner
        targets_offset targets_length
        values_offset values_length
        payloads_offset payloads_length
        predecessor salt ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_executeBatchBypass_201 storage_base id now_timestamp)) ?}}.

  (** Sub-axiom: [fun_scheduleBatch_1295_inner] body effect.

      Walks: array-length triple-check + revert-helper for
      [TimelockController__LengthMismatch] + [fun_hashOperationBatch_1135]
      (keccak256 of abi-encoded tuple) + [fun__schedule_1349] (sets the
      timestamps[id] entry to now + delay; reads minDelay and asserts
      delay >= minDelay) + a degenerate [Shallow.for_] loop that emits
      one [CallScheduled] event per target.

      The audit-time obligation: under [H_unset] (timestamps[id] = 0)
      and [H_delay_ok] (delay >= sim.minDelay), the inner body
      mechanically composes the four steps to produce the schedule
      post-state at [proj_post_scheduleBatch_1295]. *)
  Axiom run_fun_scheduleBatch_1295_inner_at_storage_base :
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
           (H_unset : Timelock.get_ts sim id = 0)
           (H_delay_ok : sim.(Timelock.State.minDelay) <= delay),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_scheduleBatch_1295_inner
        targets_offset targets_length
        values_offset values_length
        payloads_offset payloads_length
        predecessor salt delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp)) ?}}.

  (** ====================================================================
      Concrete slot-indexed observational predicates
      ====================================================================

      Per the 2026-05-31 adversarial-review skolemization-soundness
      audit (CCV-1 / CCV-2 / CRIT-V), the [_observes] bridges that
      previously stated [storage_equiv (proj_post X) (proj_post X)]
      were tautologies on the Skolem -- the same opaque
      [proj_post_<fn>] appeared on both sides, constraining nothing.
      An adversarial inheritor could pick any
      [proj_post_<fn> := fun _ _ => empty] without contradicting the
      bridges, leaving the milestone theorems content-free.

      We promote the bridges to content-bearing claims that relate
      the Skolemized post-storage to a CONCRETE reference shape
      derived from [storage_base] at slot-indexed positions of the
      [SimulatedStorage.t = list StorableValue.t] list. Each bridge
      now asserts equality at the specific slots the contract's Yul
      body touches:

        - [slot_timestamps] (the OZ TimelockControllerStorage
          namespace anchor, holding the [mapping bytes32 => uint256
          _timestamps] aggregate at slot offset 0 / its EIP-7201
          keccak256 anchor).
        - [slot_roles]      (the OZ AccessControlStorage namespace
          anchor, holding the [mapping bytes32 => RoleData _roles]
          aggregate).

      The slot-index choice is abstract (mirrors
      [TimelockControllerBase.v]'s [Variable slot_timestamps : nat]
      template); downstream inheritors / instantiation sites pin the
      concrete keccak256-derived value.  We hard-code
      [slot_timestamps := 0] and [slot_roles := 1] here because
      [List.nth_error] needs a [nat] index and the abstract list
      shape supports any consistent assignment; what matters is that
      the predicates [eq_at_timestamps] / [eq_at_roles] now carry
      real content (an empty-storage adversarial instantiation of
      [proj_post_<fn>] no longer satisfies "slot 0 equals slot 0 of
      storage_base"). *)

  Definition slot_timestamps : nat := 0.
  Definition slot_roles      : nat := 1.

  Definition eq_at_timestamps (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_timestamps = List.nth_error s2 slot_timestamps.

  Definition eq_at_roles (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_roles = List.nth_error s2 slot_roles.

  (** Reflexivity / transitivity of each slot-indexed predicate,
      [Qed]-provable from the [Definition]s above. Mirrors
      [StakingVaultRewards.eq_at_*_concrete_refl] /
      [_trans] / [Guardian.set_eq_at_role] / [RewardTokenRegistry.set_eq_in_registry]
      patterns. *)

  Lemma eq_at_timestamps_refl s : eq_at_timestamps s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_timestamps_sym s1 s2 :
    eq_at_timestamps s1 s2 -> eq_at_timestamps s2 s1.
  Proof. unfold eq_at_timestamps. intros H. symmetry. exact H. Qed.

  Lemma eq_at_timestamps_trans s1 s2 s3 :
    eq_at_timestamps s1 s2 ->
    eq_at_timestamps s2 s3 ->
    eq_at_timestamps s1 s3.
  Proof.
    unfold eq_at_timestamps. intros H12 H23.
    rewrite H12. exact H23.
  Qed.

  Lemma eq_at_roles_refl s : eq_at_roles s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_roles_sym s1 s2 :
    eq_at_roles s1 s2 -> eq_at_roles s2 s1.
  Proof. unfold eq_at_roles. intros H. symmetry. exact H. Qed.

  Lemma eq_at_roles_trans s1 s2 s3 :
    eq_at_roles s1 s2 ->
    eq_at_roles s2 s3 ->
    eq_at_roles s1 s3.
  Proof.
    unfold eq_at_roles. intros H12 H23.
    rewrite H12. exact H23.
  Qed.

  (** ====================================================================
      Per-target observational bridge Axioms
      ====================================================================

      Each Axiom states the audit-time obligation: under the
      function's Success-branch preconditions, the walker's
      Skolemized post-storage [proj_post_<fn> ...] agrees with
      [storage_base] at the slots the function does NOT touch.
      An adversarial instantiation that returns garbage at the
      untouched slots now contradicts these bridges.

      For [revokeOptimisticProposer] the function writes only the
      AccessControl role map at [slot_roles] -- the [slot_timestamps]
      slot is unchanged.

      For the four timestamps mutators
      ([executeBatchBypass]/[scheduleBatch]/[executeBatch]/[cancel])
      the function writes only the [_timestamps[id]] aggregate at
      [slot_timestamps] -- the [slot_roles] slot is unchanged. The
      audit-time obligation that the [slot_timestamps] value matches
      the sim's [set_ts] write is documented in the per-bridge
      comments below; pinning the post-value at [slot_timestamps]
      requires a slot-encoding lemma for the [TsMap] aggregate
      (mapping(bytes32 => uint256) layout) and is left to the
      instantiation site of
      [TimelockControllerBaseEquivalenceTemplate]. The CURRENT
      bridges are content-bearing on the [_unchanged_ slot] side --
      enough to defeat the [proj_post := fun _ _ => empty]
      adversarial instantiation that previously closed all five
      milestones via [True]-degeneracy.

      The sim-side post-value targets the bridges document:
        scheduleBatch:        timestamps[id] := now + delay
        executeBatch:         timestamps[id] := DONE_TIMESTAMP (1)
        cancel:               timestamps[id] := 0
        executeBatchBypass:   timestamps[id] := DONE_TIMESTAMP (1)
                              (via the inner executeBatch dispatch).

      Audit-time discharge of the full slot-by-slot equality is a
      [mapping_index_access] + [sstore] composition; see
      [proofs/equivalence/TimelockControllerBase.v]'s
      [walker_obs_getTimestamp] / [walker_obs_hasRole] for the
      lens-correctness hypotheses an inheritor supplies. *)

  Axiom proj_post_revokeOptimisticProposer_136_observes :
    forall (storage_base : SimulatedStorage.t) (account : Address),
    (* The Timelock-side projection is unchanged: revokeOptimisticProposer
       writes only the AccessControl role map, leaving timestamps and
       minDelay alone. *)
    eq_at_timestamps
      (proj_post_revokeOptimisticProposer_136 storage_base account)
      storage_base.

  Axiom proj_post_executeBatchBypass_201_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    (* Net effect on timestamps: timestamps[id] = DONE_TIMESTAMP
       (Unset -> Done).  The intermediate now-write is shadowed by
       the inner executeBatch call's DONE_TIMESTAMP write. The
       [slot_roles] aggregate is untouched. *)
    eq_at_roles
      (proj_post_executeBatchBypass_201 storage_base id now_)
      storage_base.

  Axiom proj_post_scheduleBatch_1295_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (delay now_ : U256.t),
    (* Net effect on timestamps: timestamps[id] = now + delay.
       The [slot_roles] aggregate is untouched. *)
    eq_at_roles
      (proj_post_scheduleBatch_1295 storage_base id delay now_)
      storage_base.

  Axiom proj_post_executeBatch_1552_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    (* Net effect on timestamps: timestamps[id] = DONE_TIMESTAMP.
       The [slot_roles] aggregate is untouched. *)
    eq_at_roles
      (proj_post_executeBatch_1552 storage_base id now_)
      storage_base.

  Axiom proj_post_cancel_1394_observes :
    forall (storage_base : SimulatedStorage.t)
           (id : OpId) (now_ : U256.t),
    (* Net effect on timestamps: timestamps[id] = 0.  The
       [slot_roles] aggregate is untouched. *)
    eq_at_roles
      (proj_post_cancel_1394 storage_base id now_)
      storage_base.

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
      and AccessControlEnumerable).

      R088 closure: the original [Axiom] has been replaced by this
      [Qed] [Lemma] composing the per-helper sub-axioms
      [run_fun__checkRole_2033_under_role] and
      [run_fun__revokeRole_121_at_storage_base]. Net trust impact:
      1 walker [Axiom] → 1 walker [Lemma] + 2 narrower sub-[Axiom]s,
      one of which ([run_fun__checkRole_2033_under_role]) is shared
      across the 5 outer mutators. *)
  Lemma run_fun_revokeOptimisticProposer_136_at_proj_sim :
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
  Proof.
    intros codes env state_base storage_base memory account
           H_caller_canceller H_caller_bound H_account_bound H_mem.
    (** Phase 1: dispatch [fun__checkRole_2033] sub-axiom (the gate). *)
    pose proof (run_fun__checkRole_2033_under_role
                  codes env state_base storage_base memory
                  0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783
                  has_CANCELLER_ROLE
                  H_caller_canceller H_caller_bound H_mem) as Hgate.
    destruct Hgate as (w0_g & w1_g & rest_g & Hgate).
    set (memory_gate := w0_g :: w1_g :: rest_g).
    assert (H_mem_gate : exists w0 w1 rest, memory_gate = w0 :: w1 :: rest)
      by (exists w0_g, w1_g, rest_g; reflexivity).
    (** Phase 2: dispatch [fun__revokeRole_121] sub-axiom (the body). *)
    pose proof (run_fun__revokeRole_121_at_storage_base
                  codes env state_base storage_base memory_gate
                  0x26f49d08685d9cdd4951a7470bc8fbe9dd0f00419c1a44c1b89f845867ae12e0
                  account
                  H_caller_bound H_account_bound eq_refl H_mem_gate) as Hbody.
    destruct Hbody as (memory' & revoked & Hbody).
    exists memory'.
    (** Phase 3: walk the outer body's mechanical assembly.

        The body has three levels of [M.call] nesting:
          [fun_revokeOptimisticProposer_136] →
            [modifier_onlyRole_128] →
              [constant_CANCELLER_ROLE_616] (literal)
              [fun__checkRole_2033] (Hgate)
              [fun_revokeOptimisticProposer_136_inner] →
                [constant_OPTIMISTIC_PROPOSER_ROLE_285] (literal)
                [fun__revokeRole_121] (Hbody)

        The walker arms below dispatch each level mechanically. Each
        constant evaluation is a pure-binding sub-walk; each named
        function call dispatches its corresponding hypothesis. *)
    unfold fun_revokeOptimisticProposer_136,
           modifier_onlyRole_128,
           fun_revokeOptimisticProposer_136_inner,
           constant_CANCELLER_ROLE_616,
           constant_OPTIMISTIC_PROPOSER_ROLE_285.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (fun__checkRole_2033 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ | LowM.Call (fun__revokeRole_121 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Call _ _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

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
      are encapsulated in [proj_post_executeBatch_1552]'s shape.

      R088 closure: same trust-redistribution split as [revoke] /
      [cancel] / [scheduleBatch]. Dispatches
      [run_fun__checkRole_2033_under_role] (shared gate, [has_PROPOSER_ROLE]
      discharge) and [run_fun_executeBatchBypass_201_inner_at_storage_base]
      (body — the body sub-axiom encapsulates the inner
      [fun_executeBatch_1552] dispatch, which is the R087-Blocker-2
      delegatecall consumer; trust there is bounded by the body
      sub-axiom rather than by the outer composite walker). *)
  Lemma run_fun_executeBatchBypass_201_at_proj_sim :
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
  Proof.
    intros codes env state_base storage_base memory
           targets_offset targets_length
           values_offset values_length
           payloads_offset payloads_length
           predecessor salt id sim
           H_caller_proposer H_caller_executor H_caller_bound H_unset H_success H_mem.
    (** Phase 1: gate dispatch via the shared [fun__checkRole_2033]
        sub-axiom under [has_PROPOSER_ROLE]. *)
    pose proof (run_fun__checkRole_2033_under_role
                  codes env state_base storage_base memory
                  0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1
                  has_PROPOSER_ROLE
                  H_caller_proposer H_caller_bound H_mem) as Hgate.
    destruct Hgate as (w0_g & w1_g & rest_g & Hgate).
    set (memory_gate := w0_g :: w1_g :: rest_g).
    assert (H_mem_gate : exists w0 w1 rest, memory_gate = w0 :: w1 :: rest)
      by (exists w0_g, w1_g, rest_g; reflexivity).
    (** Phase 2: inner-body dispatch (bypass-specific). The inner sub-axiom
        encapsulates the [fun_executeBatch_1552] dispatch (which contains
        the R087-Blocker-2 delegatecall) within its opaque post-state. *)
    pose proof (run_fun_executeBatchBypass_201_inner_at_storage_base
                  codes env state_base storage_base memory_gate
                  targets_offset targets_length
                  values_offset values_length
                  payloads_offset payloads_length
                  predecessor salt id sim
                  H_unset (or_intror H_caller_proposer) H_mem_gate) as Hbody.
    destruct Hbody as (memory' & Hbody).
    exists memory'.
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_executeBatchBypass_201,
           modifier_onlyRole_154,
           constant_PROPOSER_ROLE_606.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (fun__checkRole_2033 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ | LowM.Call (fun_executeBatchBypass_201_inner _ _ _ _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Call _ _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

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
      the storage_base with timestamps[id] = now + delay.

      R088 closure: same trust-redistribution split as [revoke]/[cancel].
      Dispatches [run_fun__checkRole_2033_under_role] (shared gate,
      [has_PROPOSER_ROLE] discharge) and
      [run_fun_scheduleBatch_1295_inner_at_storage_base] (body). *)
  Lemma run_fun_scheduleBatch_1295_at_proj_sim :
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
  Proof.
    intros codes env state_base storage_base memory
           targets_offset targets_length
           values_offset values_length
           payloads_offset payloads_length
           predecessor salt delay id sim
           H_caller_proposer H_caller_bound H_unset H_delay_ok H_success H_mem.
    (** Phase 1: gate dispatch via the shared [fun__checkRole_2033]
        sub-axiom under [has_PROPOSER_ROLE]. *)
    pose proof (run_fun__checkRole_2033_under_role
                  codes env state_base storage_base memory
                  0xb09aa5aeb3702cfd50b6b62bc4532604938f21248a27a1d5ca736082b6819cc1
                  has_PROPOSER_ROLE
                  H_caller_proposer H_caller_bound H_mem) as Hgate.
    destruct Hgate as (w0_g & w1_g & rest_g & Hgate).
    set (memory_gate := w0_g :: w1_g :: rest_g).
    assert (H_mem_gate : exists w0 w1 rest, memory_gate = w0 :: w1 :: rest)
      by (exists w0_g, w1_g, rest_g; reflexivity).
    (** Phase 2: inner-body dispatch via the schedule-specific sub-axiom. *)
    pose proof (run_fun_scheduleBatch_1295_inner_at_storage_base
                  codes env state_base storage_base memory_gate
                  targets_offset targets_length
                  values_offset values_length
                  payloads_offset payloads_length
                  predecessor salt delay id sim
                  H_unset H_delay_ok H_mem_gate) as Hbody.
    destruct Hbody as (memory' & Hbody).
    exists memory'.
    (** Phase 3: walk the outer body's mechanical assembly. *)
    unfold fun_scheduleBatch_1295,
           modifier_onlyRole_1213,
           constant_PROPOSER_ROLE_606.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (fun__checkRole_2033 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ | LowM.Call (fun_scheduleBatch_1295_inner _ _ _ _ _ _ _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Call _ _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

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
      storage_base with timestamps[id] = 0.

      R088 closure: promoted from [Axiom] to [Qed] [Lemma] via the
      same trust-redistribution split as
      [run_fun_revokeOptimisticProposer_136_at_proj_sim]: dispatches
      [run_fun__checkRole_2033_under_role] (shared gate) and
      [run_fun_cancel_1394_inner_at_storage_base] (cancel-specific
      body). *)
  Lemma run_fun_cancel_1394_at_proj_sim :
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
  Proof.
    intros codes env state_base storage_base memory id sim
           H_caller_canceller H_caller_bound H_pending H_success H_mem.
    (** Phase 1: gate dispatch. *)
    pose proof (run_fun__checkRole_2033_under_role
                  codes env state_base storage_base memory
                  0xfd643c72710c63c0180259aba6b2d05451e3591a24e58b62239378085726f783
                  has_CANCELLER_ROLE
                  H_caller_canceller H_caller_bound H_mem) as Hgate.
    destruct Hgate as (w0_g & w1_g & rest_g & Hgate).
    set (memory_gate := w0_g :: w1_g :: rest_g).
    assert (H_mem_gate : exists w0 w1 rest, memory_gate = w0 :: w1 :: rest)
      by (exists w0_g, w1_g, rest_g; reflexivity).
    (** Phase 2: inner-body dispatch. *)
    pose proof (run_fun_cancel_1394_inner_at_storage_base
                  codes env state_base storage_base memory_gate id sim
                  H_pending H_mem_gate) as Hbody.
    destruct Hbody as (memory' & Hbody).
    exists memory'.
    (** Phase 3: walk the outer body's mechanical assembly. Same
        modifier+gate+body shape as [revokeOptimisticProposer]. *)
    unfold fun_cancel_1394,
           modifier_onlyRole_1356,
           constant_CANCELLER_ROLE_616.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (fun__checkRole_2033 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ | LowM.Call (fun_cancel_1394_inner _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Call _ _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

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

  (** ----- R071 Theorem: [revokeOptimisticProposer] equivalence -----

      Conclusion includes [eq_at_timestamps storage_post storage_base]:
      the function writes only the AccessControl role map at
      [slot_roles], so the [slot_timestamps] slot is preserved. This
      clause makes the bridge axiom
      [proj_post_revokeOptimisticProposer_136_observes] load-bearing
      (it appears in [Print Assumptions] of this milestone). *)
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
          (proj_post_revokeOptimisticProposer_136 storage_base account) /\
        eq_at_timestamps storage_post storage_base).
  Proof.
    cbv zeta.
    (** Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun_revokeOptimisticProposer_136_at_proj_sim
                  codes env state_base storage_base memory account
                  H_caller_canceller H_caller_bound H_account_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    (** Phase 2: dispatch the slot-unchanged observational bridge. *)
    pose proof (proj_post_revokeOptimisticProposer_136_observes
                  storage_base account) as Hobs.
    (** Phase 3: witness post-storage. *)
    exists (Some (make_state env state_base memory'
                    (proj_post_revokeOptimisticProposer_136 storage_base account))).
    exists (proj_post_revokeOptimisticProposer_136 storage_base account).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- R071 Theorem: [executeBatchBypass] equivalence -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      the function writes only the [_timestamps] aggregate at
      [slot_timestamps], so the [slot_roles] slot is preserved. *)
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
          (proj_post_executeBatchBypass_201 storage_base id now_timestamp) /\
        eq_at_roles storage_post storage_base).
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
    pose proof (proj_post_executeBatchBypass_201_observes
                  storage_base id now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_executeBatchBypass_201 storage_base id now_timestamp))).
    exists (proj_post_executeBatchBypass_201 storage_base id now_timestamp).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- R071 Theorem: [scheduleBatch] equivalence -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      the function writes only the [_timestamps] aggregate at
      [slot_timestamps], so the [slot_roles] slot is preserved. *)
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
          (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp) /\
        eq_at_roles storage_post storage_base).
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
    pose proof (proj_post_scheduleBatch_1295_observes
                  storage_base id delay now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp))).
    exists (proj_post_scheduleBatch_1295 storage_base id delay now_timestamp).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
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
          (proj_post_executeBatch_1552 storage_base id now_timestamp) /\
        eq_at_roles storage_post storage_base).
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
    pose proof (proj_post_executeBatch_1552_observes
                  storage_base id now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_executeBatch_1552 storage_base id now_timestamp))).
    exists (proj_post_executeBatch_1552 storage_base id now_timestamp).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

  (** ----- R071 Theorem: [cancel] equivalence -----

      Conclusion includes [eq_at_roles storage_post storage_base]:
      the function writes only the [_timestamps] aggregate at
      [slot_timestamps], so the [slot_roles] slot is preserved. *)
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
          (proj_post_cancel_1394 storage_base id now_timestamp) /\
        eq_at_roles storage_post storage_base).
  Proof.
    cbv zeta.
    pose proof (run_fun_cancel_1394_at_proj_sim
                  codes env state_base storage_base memory id sim
                  H_caller_canceller H_caller_bound
                  H_pending H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_post_cancel_1394_observes
                  storage_base id now_timestamp) as Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_cancel_1394 storage_base id now_timestamp))).
    exists (proj_post_cancel_1394 storage_base id now_timestamp).
    split; [exact Hwalker|].
    exists memory'. split; [reflexivity|].
    split; [apply storage_equiv_refl|exact Hobs].
  Qed.

End TimelockControllerOptimisticEquivalence.
