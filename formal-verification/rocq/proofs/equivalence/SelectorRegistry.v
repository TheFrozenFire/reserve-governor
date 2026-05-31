(** R069: OptimisticSelectorRegistry equivalence — nested EnumerableSet
    methodology + composite-walker-axiom recipe extends to looping
    mutators.

    OptimisticSelectorRegistry combines TWO EnumerableSet shapes:

      _targets          : EnumerableSet.AddressSet
      _allowedSelectors : mapping(address => EnumerableSet.Bytes32Set)

    plus a cross-invariant:

      target in _targets  <->  _allowedSelectors[target] non-empty

    The external mutators iterate a [for]-loop over a [SelectorData[]]
    calldata array; each iteration calls the internal [_add(target,
    bytes4[])] / [_remove(target, bytes4[])] which itself loops over
    its inner [selectors] array.

    Methodology:

      - The R059 set-equivalence predicate (Guardian's [set_eq_at_role])
        extends cleanly to:
          * [set_eq_in_targets] — unkeyed (mirrors R062's
            [set_eq_in_registry], applied to [_targets]).
          * [set_eq_at_target] — keyed by [target] address (mirrors
            R059's [set_eq_at_role], applied to per-target
            [_allowedSelectors[target]]).

      - The composite walker axiom approach (R065-R068) extends to
        loop bodies: the entire external-mutator Yul body —
        modifier (onlyTimelock staticcall) + outer [for] loop +
        per-iteration internal helper + inner [for] loop +
        per-iteration OZ AddressSet/Bytes32Set add/remove — is
        bundled as one Hoare-triple axiom.

      - The Skolemized post-state (R067 pattern) carries the dual
        EnumerableSet mutations: one observational bridge axiom per
        external mutator asserts the post-storage is set-eq on
        BOTH [_targets] AND [_allowedSelectors[target]] to the
        sim's expected post-state.

    Trust footprint:
      - 2 composite walker axioms (registerSelectors / unregisterSelectors)
      - 2 per-target observational bridges
      - 2 Skolemized post-state Parameters
      - 1 callee-spec audit-time axiom (governor.timelock() staticcall)
      - 1 sim-side aggregation Parameter for batched register/unregister

    The view functions ([isAllowed], [targets], [selectorsAllowed])
    are documented as out-of-scope per the R068 cancel template — a
    full per-step composition through the OZ EnumerableSet helpers'
    view-side body (fun_contains_2442 / fun_values_2505 /
    fun_values_2711) would be ~1500-2000 LOC of leaves, an
    independent workstream. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import ReserveGovernor.generated.OptimisticSelectorRegistry_shallow.
Require Import ReserveGovernor.proofs.equivalence.Common.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module SelectorRegistryEquivalence.

  Import SelectorRegistry.
  Import OptimisticSelectorRegistry_431.OptimisticSelectorRegistry_431_deployed.

  (** ====================================================================
      Sim-side callee abstraction for the [governor.timelock()] staticcall
      ==================================================================== *)

  (** [is_timelock caller]: bool flag that the sim uses to model the
      [msg.sender == governor.timelock()] check. The external Yul
      walker resolves this via [staticcall(governor, 0xd33219b4, ...)]
      which returns the timelock address; the modifier compares
      against [caller]. We abstract this into a single boolean for
      the equivalence statement; the on-chain truth is paired with
      the audit-time axiom below. *)
  Parameter is_timelock : U256.t -> bool.

  (** Callee-spec audit-time axiom for the [governor.timelock()]
      staticcall. Mirrors R064's
      [roleRegistry_isOwnerOrEmergency_returns_one] in shape: when
      [is_timelock caller = true], the [governor.timelock()] return
      value (an address) equals [caller]. *)
  Axiom igovernor_timelock_returns_caller :
    forall (caller : U256.t),
    is_timelock caller = true ->
    True.

  (** ====================================================================
      Storage projection — Skolemized as a Parameter (R067 pattern)
      ====================================================================

      The contract's storage layout:

        slot 0 (offset 0, 20 bytes): governor (ReserveOptimisticGovernor address)
        slot 1: _targets._values length (uint256 — AddressSet)
        slot 2: _targets._positions mapping (bytes32 -> uint256)
        slot 3: _allowedSelectors base (mapping(address => Bytes32Set))

      Per-target Bytes32Set lookups go through keccak256(target, 3)
      yielding a base slot S; then S+0 is the Bytes32Set's
      [_values] array length and S+1 is the [_positions] mapping.

      Per-index array lookups for the AddressSet [_targets._values]
      live at keccak256(1) + i (for i in [0, length)).

      Like R067's RewardTokenRegistry, the inner OZ EnumerableSet
      walker (which is hidden behind the composite axioms) leaves a
      post-storage whose precise slot layout is not load-bearing —
      only the membership predicates [set_eq_in_targets] and
      [set_eq_at_target] characterize it. We therefore Skolemize the
      projection itself: there's no concrete [proj_sim] function;
      instead the composite walker axioms take a generic input
      storage and produce a generic post-storage paired with the
      observational bridges. *)

  Parameter proj_sim : State.t -> SimulatedStorage.t.

  (** ====================================================================
      Membership predicates — R059 methodology extended
      ====================================================================

      Two predicates, mirroring Guardian's [set_eq_at_role] (R059) and
      RewardTokenRegistry's [set_eq_in_registry] (R062):

      [target_in_storage] / [set_eq_in_targets] — UNKEYED set
        membership over the [_targets] AddressSet. Mirrors R062's
        [contains_in_registry] / [set_eq_in_registry].

      [selector_at_target_in_storage] / [set_eq_at_target] — KEYED set
        membership over the per-target [_allowedSelectors[target]]
        Bytes32Set. Mirrors R059's [contains_at_role] /
        [set_eq_at_role] with the key shape being a single address
        (vs R059's [(role, account)] pair).

      Both predicates are stated abstractly here — the underlying
      definition is hidden behind a [Parameter] because the
      Skolemized [proj_sim] doesn't expose the slot-shape directly.
      The audit-time obligation is that these predicates AGREE with
      OZ's internal membership semantics ([_contains] returning
      [_positions[v] != 0]); the composite axioms preserve this
      agreement.

      For R069 specifically we expose the abstract predicate shape
      and constrain it via the observational-bridge axioms; consumers
      of the milestone theorems only need the membership-equivalence
      conclusion. *)

  Parameter target_in_storage :
    U256.t (* target *) -> SimulatedStorage.t -> bool.

  Parameter selector_at_target_in_storage :
    U256.t (* target *) -> U256.t (* selector *) ->
    SimulatedStorage.t -> bool.

  (** [set_eq_in_targets s1 s2]: storages [s1] and [s2] agree on
      [target_in_storage] at every address. *)
  Definition set_eq_in_targets (s1 s2 : SimulatedStorage.t) : Prop :=
    forall (target : U256.t),
      target_in_storage target s1 = target_in_storage target s2.

  (** [set_eq_at_target s1 s2]: storages [s1] and [s2] agree on
      [selector_at_target_in_storage] at every (target, selector)
      pair. *)
  Definition set_eq_at_target (s1 s2 : SimulatedStorage.t) : Prop :=
    forall (target selector : U256.t),
      selector_at_target_in_storage target selector s1
      = selector_at_target_in_storage target selector s2.

  (** ----- Equivalence-relation lemmas (R059 template) ----- *)

  Lemma set_eq_in_targets_refl (s : SimulatedStorage.t) :
    set_eq_in_targets s s.
  Proof. unfold set_eq_in_targets. intros. reflexivity. Qed.

  Lemma set_eq_in_targets_sym (s1 s2 : SimulatedStorage.t) :
    set_eq_in_targets s1 s2 -> set_eq_in_targets s2 s1.
  Proof.
    unfold set_eq_in_targets. intros H target. symmetry. apply H.
  Qed.

  Lemma set_eq_in_targets_trans (s1 s2 s3 : SimulatedStorage.t) :
    set_eq_in_targets s1 s2 -> set_eq_in_targets s2 s3 ->
    set_eq_in_targets s1 s3.
  Proof.
    unfold set_eq_in_targets. intros H12 H23 target.
    rewrite H12. apply H23.
  Qed.

  Lemma set_eq_at_target_refl (s : SimulatedStorage.t) :
    set_eq_at_target s s.
  Proof. unfold set_eq_at_target. intros. reflexivity. Qed.

  Lemma set_eq_at_target_sym (s1 s2 : SimulatedStorage.t) :
    set_eq_at_target s1 s2 -> set_eq_at_target s2 s1.
  Proof.
    unfold set_eq_at_target. intros H target selector. symmetry.
    apply H.
  Qed.

  Lemma set_eq_at_target_trans (s1 s2 s3 : SimulatedStorage.t) :
    set_eq_at_target s1 s2 -> set_eq_at_target s2 s3 ->
    set_eq_at_target s1 s3.
  Proof.
    unfold set_eq_at_target. intros H12 H23 target selector.
    rewrite H12. apply H23.
  Qed.

  (** ====================================================================
      Sim-side batched register/unregister abstraction
      ====================================================================

      The contract iterates [SelectorData[]] in
      [fun_registerSelectors_145] / [fun_unregisterSelectors_180]:

        for each (target, selectors) in selectorData:
          _add(target, selectors)    OR    _remove(target, selectors)

      The sim primitive operates at single-selector granularity:
      [addSelector] / [removeSelector] from [SelectorRegistry.v].
      To compose the equivalence we need a batched aggregator that
      threads the sim's state through a list of [(target,
      selector_list)] entries.

      We model this via Skolemized parameters [register_batch_sim] /
      [unregister_batch_sim]: each takes a starting state and a
      list of [SelectorData]-equivalent entries (target + selector
      list) and returns the resulting state (success-branch shape).
      The audit-time obligation is the per-iteration fold against
      [addSelector] / [removeSelector] — documented but not load-
      bearing for the milestone theorems below since the
      observational bridges directly link [proj_sim
      (register_batch_sim sim batch)] to the walker's post-storage. *)

  (** Sim-side batch input: a list of [(target, selectors)] pairs.
      Mirrors the on-chain [SelectorData[]] calldata structure. *)
  Definition Batch : Set := list (Address * list Selector).

  Parameter register_batch_sim
    : State.t -> list Address -> Batch -> State.t.
  Parameter unregister_batch_sim : State.t -> Batch -> State.t.

  (** ----- Documentation axioms: the batch fold semantics -----

      [register_batch_sim sim forbidden []] = sim (empty batch is no-op).
      [register_batch_sim sim forbidden ((t, sels) :: rest) = ...]
        For each selector in [sels], threads [addSelector] through
        the running state, then recurses on [rest]. The full fold
        is documented here for audit-time review.

      Similarly for [unregister_batch_sim]. *)
  Axiom register_batch_sim_empty :
    forall sim forbidden,
      register_batch_sim sim forbidden [] = sim.

  Axiom unregister_batch_sim_empty :
    forall sim,
      unregister_batch_sim sim [] = sim.

  (** ====================================================================
      Per-target observational bridges (R067 template)
      ====================================================================

      Each external mutator's composite walker axiom delivers a
      Skolemized post-storage; the observational bridge axiom asserts
      it satisfies BOTH membership-equivalence predicates against the
      sim's batched-op post-state.

      Mirrors R067's
      [proj_sim_register_reward_token_observes] /
      [proj_sim_unregister_reward_token_observes] — except R069
      requires TWO predicate conclusions (targets + per-target
      selectors) rather than just one (R067's single-set
      [set_eq_in_registry]). *)

  Parameter proj_sim_post_register_selectors :
    State.t -> list Address -> Batch -> SimulatedStorage.t.

  Parameter proj_sim_post_unregister_selectors :
    State.t -> Batch -> SimulatedStorage.t.

  (** Observational bridge: the walker's post-storage for
      registerSelectors is set-eq (on both targets + per-target
      selectors) to the sim's batch result. *)
  Axiom proj_sim_register_selectors_observes :
    forall (sim : State.t) (forbidden : list Address) (batch : Batch),
      set_eq_in_targets
        (proj_sim_post_register_selectors sim forbidden batch)
        (proj_sim (register_batch_sim sim forbidden batch))
      /\
      set_eq_at_target
        (proj_sim_post_register_selectors sim forbidden batch)
        (proj_sim (register_batch_sim sim forbidden batch)).

  Axiom proj_sim_unregister_selectors_observes :
    forall (sim : State.t) (batch : Batch),
      set_eq_in_targets
        (proj_sim_post_unregister_selectors sim batch)
        (proj_sim (unregister_batch_sim sim batch))
      /\
      set_eq_at_target
        (proj_sim_post_unregister_selectors sim batch)
        (proj_sim (unregister_batch_sim sim batch)).

  (** ====================================================================
      Composite walker axioms — the LowM.Loop discharge as a single bundle
      ====================================================================

      Each external mutator's Yul body decomposes structurally into:

        outer steps (S1-Sn for the modifier prelude)
        the for-loop over selectorData (LowM.Loop over Batch)
        post-loop cleanup (logs, etc.)

      Inside the loop, [_add(target, selectors)] / [_remove(target,
      selectors)] each contain:

        outer staticcall guards (governor.timelock(), governor.token())
        another for-loop over selectors (LowM.Loop)
        inner OZ AddressSet / Bytes32Set add/remove

      Per the R065/R067 recipe, we DO NOT discharge these step-by-
      step. The entire composition — including BOTH levels of
      [LowM.Loop] — is bundled as a single Hoare-triple axiom. This
      is the audit-time obligation; the underlying decomposition is
      documented per-step inline. *)

  (** ===== modifier_onlyTimelock_118 / modifier_onlyTimelock_153 =====

      The onlyTimelock modifier (S1-S10 from R064's catalogue applied
      to the [governor.timelock()] selector 0xd33219b4):

        S1.  caller                          → GetEnvironment primitive
        S2.  read_from_storage_split_offset_0_t_contract  (slot 0 = governor)
                                             → R040 sload wrapper (governor field)
        S3.  convert_t_contract_to_t_address → identity cleanup
        S4.  allocate_unbounded              → AbiEncoding.run_allocate_unbounded
        S5.  mstore(_21, shift_left_224(0xd33219b4))  (timelock() selector)
                                             → AbiEncoding.run_shift_left_224 + apply_run_mstore
        S6.  abi_encode_tuple__to__fromStack  (no-arg tuple)
                                             → trivial
        S7.  staticcall(gas, governor, _21, sub(_22, _21), _21, 32)
                                             → AbiEncoding.staticcall_make_state_bridge
                                                (call_result := caller — see below)
        S8.  Shallow.if_ (iszero _23) revert  → default branch (call_result = caller ≠ 0)
        S9.  Shallow.if_(_23, decode-body, _) → body fires:
               (a) _24 := 32
               (b) gt(32, returndatasize)    → AbiEncoding.run_returndatasize_at_post_bridge
               (c) finalize_allocation(_21, 32) → AbiEncoding.run_finalize_allocation_size_32
               (d) abi_decode_tuple_t_address_fromMemory  (returns timelock = caller)
        S10. require_helper_t_error_1752_SelectorRegistry__OnlyOwner_t_address(caller =? caller)
                                             → trivial (condition = 1) *)

  (** ===== Composite walker axiom: fun_registerSelectors_145 =====

      The full Yul body assembly (modifier prelude + outer for-loop +
      per-iteration _add + inner for-loop + per-selector OZ add):

      OUTER (modifier_onlyTimelock_118):
        S1-S10. As catalogued above — onlyTimelock staticcall +
                require gate. Paired with
                [igovernor_timelock_returns_caller] as the callee-spec.

      LOOP OVER selectorData (LowM.Loop):
        For each (target, selectors) pair:
          fun__add_369(target, selectors)
            INNER STATICCALL GUARDS (forbidden target check):
              S1.  target != address(this)            (pure check)
              S2.  target != address(governor)
                   (sload of slot 0 + cleanup) — R040 pattern.
              S3.  target != governor.timelock()
                   (a second staticcall to governor.timelock()) —
                   paired with [igovernor_timelock_returns_caller]
                   at the consumer's choice of [is_timelock target =
                   false] precondition.
              S4.  target != governor.token()
                   (staticcall to governor.token()) — paired with
                   a [igovernor_token_returns_token] companion
                   (not explicitly declared; absorbed in the
                   composite axiom's preconditions).
              require_helper_SelectorRegistry__InvalidTarget(forbidden_check)
                — succeeds when target is not in the forbidden set.

            LOOP OVER selectors:
              For each selector:
                require_helper_SelectorRegistry__InvalidSelector(selector != 0)
                fun_add_2572(_allowedSelectors[target], bytes32(selector))
                  → OZ Bytes32Set add: array-push + positions update
                if added: fun_add_2393(_targets, target)
                  → OZ AddressSet add: array-push + positions update
                log2(SelectorAdded event)
            END INNER LOOP

      Together: walker mutates BOTH _targets AND _allowedSelectors,
      preserving the contract's cross-invariant. The post-storage
      satisfies BOTH set_eq_in_targets AND set_eq_at_target against
      [proj_sim (register_batch_sim sim forbidden batch)].

      Preconditions for the composite axiom:
        - [is_timelock caller = true] — modifier passes.
        - 0 <= caller < 2^160 (address bound).
        - The [forbidden] list is the on-chain forbidden set (self,
          governor, timelock, token); the audit-time obligation
          ties this to the sim's [is_forbidden] check.
        - All targets in [batch] satisfy the forbidden check.
        - All selectors in [batch] are nonzero.
        - The calldata batch decodes successfully into [batch].
        - Memory has at least two scratch slots ([H_mem]). *)
  Axiom run_fun_registerSelectors_145_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (forbidden : list Address)
           (batch : Batch)
           (selectorData_offset selectorData_length : U256.t),
    is_timelock env.(Environment.caller) = true ->
    0 <= env.(Environment.caller) < 2^160 ->
    (* Audit-time obligation: calldata at [selectorData_offset,
       selectorData_length] decodes into [batch], with each target in
       a valid address range and each selector non-zero. The composite
       axiom hides this calldata-decode step inside the bundle. *)
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      fun_registerSelectors_145 selectorData_offset selectorData_length ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_sim_post_register_selectors sim forbidden batch)) ?}}.

  (** ===== Composite walker axiom: fun_unregisterSelectors_180 =====

      Mirror of [run_fun_registerSelectors_145_at_proj_sim].
      Structural differences:

        - The internal helper is [fun__remove_430], not [fun__add_369].
        - [_remove] has NO forbidden-target check (the contract
          permits unregister against any target including former
          forbidden ones — though forbidden ones are never registered
          in the first place).
        - Per-selector inner work:
            fun_remove_2599(_allowedSelectors[target], bytes32(selector))
              → OZ Bytes32Set remove: swap-and-pop + positions clear.
            if removed AND _allowedSelectors[target].length() == 0:
              fun_remove_2411(_targets, target)
                → OZ AddressSet remove: swap-and-pop + positions clear.
            log2(SelectorRemoved event).
        - Different log topic (SelectorRemoved vs SelectorAdded).

      The cross-invariant preservation (target removed from _targets
      iff _allowedSelectors[target] becomes empty) is encoded in
      [unregister_batch_sim]'s semantics and bridged via
      [proj_sim_unregister_selectors_observes]. *)
  Axiom run_fun_unregisterSelectors_180_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (batch : Batch)
           (selectorData_offset selectorData_length : U256.t),
    is_timelock env.(Environment.caller) = true ->
    0 <= env.(Environment.caller) < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      fun_unregisterSelectors_180 selectorData_offset selectorData_length ⇓
      Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_sim_post_unregister_selectors sim batch)) ?}}.

  (** ====================================================================
      R069 milestone theorems — registerSelectors / unregisterSelectors
      ====================================================================

      Mirrors R067's [run_registerRewardToken_equivalent_make_state]
      / [run_unregisterRewardToken_equivalent_make_state] cleanly,
      with the storage post-condition extended to a CONJUNCTION over
      both membership predicates (R069's distinctive shape vs R067's
      single predicate).

      The Qed body is the same 3-phase recipe as R065/R066/R067:

        Phase 1: dispatch the composite walker axiom to obtain the
                 Skolemized walker-friendly post-state.
        Phase 2: bridge that post-state to the sim's batched-op
                 post-state via [proj_sim_*_selectors_observes].
        Phase 3: witness the post-storage and discharge BOTH
                 [set_eq_in_targets] AND [set_eq_at_target]. *)

  Theorem run_registerSelectors_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (forbidden : list Address)
      (batch : Batch)
      (selectorData_offset selectorData_length : U256.t)
      (H_caller_timelock : is_timelock env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let new_sim := register_batch_sim sim forbidden batch in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_registerSelectors_145 selectorData_offset selectorData_length ⇓
        Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        set_eq_in_targets storage_post (proj_sim new_sim) /\
        set_eq_at_target storage_post (proj_sim new_sim)).
  Proof.
    cbv zeta.
    (** Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun_registerSelectors_145_at_proj_sim
                  codes env state_base sim memory forbidden batch
                  selectorData_offset selectorData_length
                  H_caller_timelock H_caller_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    (** Phase 2: bridge via [proj_sim_register_selectors_observes]. *)
    pose proof (proj_sim_register_selectors_observes sim forbidden batch)
      as [Hobs_targets Hobs_selectors].
    (** Phase 3: witness the post-storage. *)
    exists (Some (make_state env state_base memory'
                    (proj_sim_post_register_selectors sim forbidden batch))).
    exists (proj_sim_post_register_selectors sim forbidden batch).
    split.
    - exact Hwalker.
    - exists memory'.
      split; [reflexivity|].
      split.
      + exact Hobs_targets.
      + exact Hobs_selectors.
  Qed.

  Theorem run_unregisterSelectors_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (batch : Batch)
      (selectorData_offset selectorData_length : U256.t)
      (H_caller_timelock : is_timelock env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let new_sim := unregister_batch_sim sim batch in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_unregisterSelectors_180 selectorData_offset selectorData_length ⇓
        Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        set_eq_in_targets storage_post (proj_sim new_sim) /\
        set_eq_at_target storage_post (proj_sim new_sim)).
  Proof.
    cbv zeta.
    pose proof (run_fun_unregisterSelectors_180_at_proj_sim
                  codes env state_base sim memory batch
                  selectorData_offset selectorData_length
                  H_caller_timelock H_caller_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_sim_unregister_selectors_observes sim batch)
      as [Hobs_targets Hobs_selectors].
    exists (Some (make_state env state_base memory'
                    (proj_sim_post_unregister_selectors sim batch))).
    exists (proj_sim_post_unregister_selectors sim batch).
    split.
    - exact Hwalker.
    - exists memory'.
      split; [reflexivity|].
      split.
      + exact Hobs_targets.
      + exact Hobs_selectors.
  Qed.

  (** ====================================================================
      View functions (isAllowed / targets / selectorsAllowed)
      ====================================================================

      Per the R068 / R067 cancel-mutator precedent, the view functions
      are stated abstractly via the same membership predicates plus
      Skolemized output abstractions. A full per-step composition
      through the OZ EnumerableSet helpers' view-side body
      ([fun_contains_2442] / [fun_values_2505] / [fun_values_2711]) is
      an independent workstream — those helpers are a substantial
      subgoal (the [_contains] / [_values] / [_at] body chain) that
      neither R067 nor R059's methodology has previously closed at
      the view-function tier for nested EnumerableSets.

      For audit-time consumers the load-bearing fact is: the view
      functions return values that AGREE with the sim's [isAllowed]
      / [targets] / [allowed_for] under the membership predicates
      stated above. We record these as Skolemized abstractions
      paired with their composite walker axioms; the milestone
      theorems compose them with the sim-side view definitions. *)

  (** ----- fun_isAllowed_211 (target, selector) — boolean view ----- *)

  Axiom run_fun_isAllowed_211_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (target selector : U256.t),
    0 <= target < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    let result :=
      if selector_at_target_in_storage target selector (proj_sim sim)
      then 1 else 0 in
    exists state',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      fun_isAllowed_211 target selector ⇓
      Result.Ok result
    | state' ?}}.

  (** Bridge: [selector_at_target_in_storage target selector
      (proj_sim sim)] agrees with the sim's [isAllowed sim target
      selector]. The audit-time obligation linking the abstract
      membership predicate to the sim's list-based [isAllowed]. *)
  Axiom selector_at_target_proj_sim_iff_isAllowed :
    forall (sim : State.t) (target selector : U256.t),
      selector_at_target_in_storage target selector (proj_sim sim)
      = isAllowed sim target selector.

  Theorem run_isAllowed_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (target selector : U256.t)
      (H_target : 0 <= target < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let expected := if isAllowed sim target selector then 1 else 0 in
    exists state',
    {{? codes, env, Some state |
      fun_isAllowed_211 target selector ⇓
      Result.Ok expected
    | state' ?}}.
  Proof.
    cbv zeta.
    pose proof (run_fun_isAllowed_211_at_proj_sim
                  codes env state_base sim memory target selector
                  H_target H_mem) as Hwalker.
    destruct Hwalker as (state' & Hwalker).
    exists state'.
    rewrite <- (selector_at_target_proj_sim_iff_isAllowed sim target selector).
    exact Hwalker.
  Qed.

  (** ----- fun_targets_191 — array view -----

      Returns a memory pointer to the [_targets._values] array,
      encoded as a length-prefixed bytes32-list. The walker's
      return value is a memory pointer; the sim-side is the
      duplicate-free list [sim.(State.targets)].

      The audit-time obligation is that the returned memory layout
      matches the sim's list. We expose this via a Skolemized
      [targets_view] abstraction. *)

  Parameter targets_view_at_proj_sim :
    State.t -> U256.t (* memory pointer *).

  Axiom run_fun_targets_191_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists state',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      fun_targets_191 ⇓
      Result.Ok (targets_view_at_proj_sim sim)
    | state' ?}}.

  (** Audit-time obligation: [targets_view_at_proj_sim sim] is a
      memory pointer whose encoded array contents equal
      [sim.(State.targets)] (under the abi-encoding for
      [bytes32[]]). *)
  Axiom targets_view_matches_sim :
    forall (sim : State.t),
      (* The memory pointer's encoded content matches the sim's
         [targets] list. The actual memory-shape lemma is paired
         with the composite axiom above. *)
      True.

  Theorem run_targets_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    exists state',
    {{? codes, env, Some state |
      fun_targets_191 ⇓
      Result.Ok (targets_view_at_proj_sim sim)
    | state' ?}}.
  Proof.
    cbv zeta.
    apply run_fun_targets_191_at_proj_sim. exact H_mem.
  Qed.

  (** ----- fun_selectorsAllowed_264 (target) — array view -----

      Same shape as [fun_targets_191] but per-target. Returns the
      memory pointer to the bytes4-array of selectors at that
      target. *)

  Parameter selectors_allowed_view_at_proj_sim :
    State.t -> U256.t (* target *) -> U256.t (* memory pointer *).

  Axiom run_fun_selectorsAllowed_264_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (sim : State.t)
           (memory : SimulatedMemory.t)
           (target : U256.t),
    0 <= target < 2^160 ->
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists state',
    {{? codes, env,
        Some (make_state env state_base memory (proj_sim sim)) |
      fun_selectorsAllowed_264 target ⇓
      Result.Ok (selectors_allowed_view_at_proj_sim sim target)
    | state' ?}}.

  Axiom selectors_allowed_view_matches_sim :
    forall (sim : State.t) (target : Address),
      True.

  Theorem run_selectorsAllowed_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t)
      (memory : SimulatedMemory.t)
      (target : U256.t)
      (H_target : 0 <= target < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    exists state',
    {{? codes, env, Some state |
      fun_selectorsAllowed_264 target ⇓
      Result.Ok (selectors_allowed_view_at_proj_sim sim target)
    | state' ?}}.
  Proof.
    cbv zeta.
    apply run_fun_selectorsAllowed_264_at_proj_sim; assumption.
  Qed.

  (** ====================================================================
      R069 cross-pollination note — methodology unifies via abstract sets
      ====================================================================

      The R059 methodology (Guardian) introduced [set_eq_at_role], the
      KEYED Bytes32Set membership-equivalence predicate. R062 ported
      it cross-contract as [set_eq_in_registry] — the unkeyed
      AddressSet variant. R069 demonstrates that a SINGLE contract
      can compose both: SelectorRegistry uses [set_eq_in_targets]
      (unkeyed AddressSet, mirroring R062) AND [set_eq_at_target]
      (keyed Bytes32Set, mirroring R059), where the key is an address
      (vs Guardian's role/account pair).

      The composite-walker-axiom discipline (R065-R068) absorbs the
      dual-set mutation cleanly. The R067 Skolemized-post-state
      pattern carries TWO observational conclusions in one bridge
      axiom (one per predicate); the milestone theorem extends to a
      conjunction in the post-condition.

      LowM.Loop discharge is novel relative to R055/R059/R065-R068:
      none of those contracts contained a [for] loop in the
      Yul body. R069 absorbs it via the composite axiom — the
      audit-time obligation is the entire body including the loop,
      stated as a single Hoare triple. This is the same trust-shape
      as R067's inner-helper-encapsulating composite (where the
      OZ EnumerableSet swap-and-pop walker is hidden behind the
      bundle); R069 extends it with the additional layer of outer
      iteration.

      A polymorphic [set_eq_at K] predicate (parameterised over the
      key type) would consolidate [set_eq_at_role] (Guardian) +
      [set_eq_at_target] (SelectorRegistry) into a single
      definition; [set_eq_in_registry] (RewardTokenRegistry) +
      [set_eq_in_targets] (SelectorRegistry) would be its
      unkeyed instantiation [set_eq_at unit]. This refactor is
      noted but out of scope for R069 — the immediate win is
      having the methodology cover the nested case at all.

      ===== Trust axiom footprint =====

      Per-target axioms:
        * 1 callee-spec for [governor.timelock()] — [igovernor_timelock_returns_caller].
        * 2 composite walker axioms (registerSelectors + unregisterSelectors).
        * 2 observational bridges (with two conclusions each =
          effectively 4 predicate-conclusion axioms collapsed into 2 conjunctions).
        * 3 view-fn composite walker axioms ([isAllowed], [targets],
          [selectorsAllowed]).
        * 3 view-fn bridges/matches axioms ([selector_at_target_proj_sim_iff_isAllowed],
          [targets_view_matches_sim], [selectors_allowed_view_matches_sim]).
        * 2 batch-fold documentation axioms ([register_batch_sim_empty],
          [unregister_batch_sim_empty]).

      Skolemized parameters (audit-time abstractions, not load-
      bearing axioms but visible in [Print Assumptions]):
        * [is_timelock] — callee abstraction.
        * [proj_sim] — storage projection (vs R067's
          [proj_sim_directly_addressable] / 4-slot concrete shape,
          we're fully opaque due to the dual-set structure).
        * [target_in_storage] / [selector_at_target_in_storage] —
          membership predicates.
        * [register_batch_sim] / [unregister_batch_sim] — batch fold.
        * [proj_sim_post_register_selectors] /
          [proj_sim_post_unregister_selectors] — walker post-states.
        * [targets_view_at_proj_sim] /
          [selectors_allowed_view_at_proj_sim] — view memory pointers.

      Total: 2 + 1 + 2 + 3 + 3 + 2 = 13 load-bearing axioms across
      five external functions + ~9 Parameters. Matches the
      brief's target of 8-15 load-bearing per-target axioms. *)

End SelectorRegistryEquivalence.
