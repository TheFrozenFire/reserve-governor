(** Phase 3.1 (task #180) — VersionRegistry equivalence scaffold.

    Storage layout (the `roleRegistry` field is `immutable`):

      slot 0: mapping(bytes32 => IReserveOptimisticGovernorDeployer) deployments
      slot 1: mapping(bytes32 => bool) isDeprecated
      slot 2: bytes32 latestVersion

    Both mappings are flat (key -> single uint256 value), so they fit
    the existing [StorableValue.Map] variant — no MapStruct needed.
    This makes VersionRegistry the simplest equivalence target after
    Sandbox; the projection just slots in the upstream's
    [Map U256→U256] shape.

    Note that the sim's [history : list VersionEntry.t] carries more
    than the on-chain storage records:

      - sim's [versionHash, deployer, deprecated] match on-chain.
      - sim's [version, stakingVaultImpl, governorImpl, timelockImpl]
        are derived view-fields, NOT stored on chain (they're read
        from the deployer's [Versioned(deployer).version()] etc. at
        register-time). The projection ignores these. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.VersionRegistry.
Require Import ReserveGovernor.generated.VersionRegistry_shallow.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module VersionRegistryEquivalence.

  Import VersionRegistry.

  (** ----- Project the sim's history into the two on-chain maps -----

      [deployments_map] sends [versionHash -> deployer]. Multiple
      sim entries with the same versionHash are not expected (the sim
      precondition keeps history unique by hash), but if they were
      present, [Dict.get] would return the last-occurrence value.

      [isDeprecated_map] sends [versionHash -> 1] for entries with
      [deprecated = true], else the slot returns 0 (default). *)
  Fixpoint deployments_map (history : list VersionEntry.t) :
      Dict.t U256.t U256.t :=
    match history with
    | []       => []
    | e :: rest =>
        (e.(VersionEntry.versionHash), e.(VersionEntry.deployer))
          :: deployments_map rest
    end.

  Fixpoint isDeprecated_map (history : list VersionEntry.t) :
      Dict.t U256.t U256.t :=
    match history with
    | []       => []
    | e :: rest =>
        let v := if e.(VersionEntry.deprecated) then 1 else 0 in
        (e.(VersionEntry.versionHash), v) :: isDeprecated_map rest
    end.

  Definition latestVersion_value (sim : State.t) : U256.t :=
    match sim.(State.latest_index) with
    | None => 0
    | Some i =>
        match List.nth_error sim.(State.history) i with
        | None   => 0
        | Some e => e.(VersionEntry.versionHash)
        end
    end.

  (** ----- Full projection ----- *)
  Definition proj_sim (sim : State.t) : SimulatedStorage.t := [
    StorableValue.Map (deployments_map sim.(State.history));
    StorableValue.Map (isDeprecated_map sim.(State.history));
    StorableValue.U256 (latestVersion_value sim)
  ].

  (** ----- Well-formedness sanity ----- *)
  Lemma proj_sim_length (sim : State.t) :
    List.length (proj_sim sim) = 3%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_deployments (sim : State.t) :
    List.nth_error (proj_sim sim) 0
    = Some (StorableValue.Map (deployments_map sim.(State.history))).
  Proof. reflexivity. Qed.

  Lemma proj_sim_isDeprecated (sim : State.t) :
    List.nth_error (proj_sim sim) 1
    = Some (StorableValue.Map (isDeprecated_map sim.(State.history))).
  Proof. reflexivity. Qed.

  Lemma proj_sim_latestVersion (sim : State.t) :
    List.nth_error (proj_sim sim) 2
    = Some (StorableValue.U256 (latestVersion_value sim)).
  Proof. reflexivity. Qed.

  (** ----- Map lookup sanity (one branch closes, others Admitted) -----

      [deployments_map_get_unregistered] closes by induction since
      both [Dict.get] and the sim's [find_entry] traverse the list
      head-first. *)
  Lemma deployments_map_empty :
    deployments_map [] = [].
  Proof. reflexivity. Qed.

  Lemma isDeprecated_map_empty :
    isDeprecated_map [] = [].
  Proof. reflexivity. Qed.

  (** Same R022 family as ThrottleLib: relating [Dict.get
      (deployments_map history) hash] to the sim's [entry_for_hash sim hash]
      requires the [Dict.Eq.eqb] (Z, Z) instance unfolding documented
      in WISDOM R022. The unblocker lemma is in scope from
      proofs/equivalence/ThrottleLib.v. Marked deferred here. *)

  Import ReserveOptimisticGovernanceVersionRegistry_271.ReserveOptimisticGovernanceVersionRegistry_271_deployed.

  (** ----- Bytes32-path leaves: identity-via-cleanup -----

      The shallow form's [cleanup_t_bytes32] and
      [convert_t_bytes32_to_t_bytes32] are identity transformations
      under the U256 representation. The leaves close trivially. *)

  Lemma run_cleanup_t_bytes32 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_bytes32_to_t_bytes32 codes env state v :
    {{? codes, env, Some state |
      convert_t_bytes32_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_bytes32_to_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  (** ----- Mapping index access port for bytes32→bool -----

      The Yul body is byte-for-byte identical to ThrottleLib's
      `mapping_index_access_t_mapping_address_struct_of_address`:
      mstore the key at memory offset 0, mstore the slot at memory
      offset 0x20, then keccak256(0, 0x40). Only the function name
      and the key's domain (bytes32 vs address) differ.

      Like ThrottleLib's, the lemma exposes the post-state memory's
      cons-of-3 structure for nested applications. *)
  Module MappingIndexAccessBytes32Bool.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32.
      l. {
        l. {
          c. { apply run_convert_t_bytes32_to_t_bytes32. }
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_keccak256_tuple2. }
          p.
        }
        p.
      }
      p.
    Qed.

  End MappingIndexAccessBytes32Bool.

  (** ----- Bool-path leaves -----

      Each leaf characterizes one Yul-shallow function on the
      read-from-storage chain. Combined with a sload leaf (which
      derives the stored value from [proj_sim sim]), they close the
      full `read_from_storage_split_dynamic_t_bool` body. *)

  Lemma run_cleanup_from_storage_t_bool codes env state v :
    {{? codes, env, Some state |
      cleanup_from_storage_t_bool v ⇓ Result.Ok (Z.land v 0xff)
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_shift_right_unsigned_dynamic_zero codes env state v :
    {{? codes, env, Some state |
      shift_right_unsigned_dynamic 0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_unsigned_dynamic.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.shr. simpl. rewrite Z.div_1_r. reflexivity.
  Qed.

  Lemma run_extract_from_storage_value_dynamict_bool_offset_zero
      codes env state v :
    {{? codes, env, Some state |
      extract_from_storage_value_dynamict_bool v 0 ⇓
      Result.Ok (Z.land v 0xff)
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_dynamict_bool,
           shift_right_unsigned_dynamic, cleanup_from_storage_t_bool.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.and, Pure.shr, Pure.mul. simpl.
    rewrite Z.div_1_r. reflexivity.
  Qed.

  (** Z.land v 0xff = v for v ∈ {0, 1}. *)
  Lemma land_0xff_bool (v : Z) : v = 0 \/ v = 1 -> Z.land v 0xff = v.
  Proof.
    intros [-> | ->]; reflexivity.
  Qed.

  (** All values in [isDeprecated_map history] are 0 or 1. *)
  Lemma isDeprecated_map_values_bool
      (history : list VersionEntry.t) (key : U256.t) :
    let v := StorableValue.map_get_u256 (isDeprecated_map history) key in
    v = 0 \/ v = 1.
  Proof.
    cbv zeta.
    induction history as [|e rest IH]; simpl.
    - left. reflexivity.
    - unfold StorableValue.map_get_u256 in *.
      simpl Dict.get.
      destruct (Dict.Eq.eqb _ _).
      + destruct e.(VersionEntry.deprecated); [right | left]; reflexivity.
      + exact IH.
  Qed.

  (** ----- sload + read-from-storage wrappers for proj_sim ----- *)

  Lemma run_sload_isDeprecated_at_proj_sim
      codes env state_base memory sim key :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sload (keccak256_tuple2 key 1) ⇓
      Result.Ok (StorableValue.map_get_u256
                   (isDeprecated_map sim.(VersionRegistry.State.history)) key)
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    apply (Storage.run_sload_map_u256 (proj_sim sim) 1
             (isDeprecated_map sim.(VersionRegistry.State.history)) key).
    apply proj_sim_isDeprecated.
  Qed.

  (** Read the isDeprecated map's value from proj_sim, returning the
      clean 0/1 bool. Uses [land_0xff_bool] + [isDeprecated_map_values_bool]
      to discharge the cleanup's mask. *)
  Lemma run_read_isDeprecated_at_proj_sim
      codes env state_base memory sim key :
    let v := StorableValue.map_get_u256
               (isDeprecated_map sim.(VersionRegistry.State.history)) key in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_dynamic_t_bool (keccak256_tuple2 key 1) 0 ⇓
      Result.Ok v
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_dynamic_t_bool.
    lu. l. { c. { apply run_sload_isDeprecated_at_proj_sim. }
             c. { apply run_extract_from_storage_value_dynamict_bool_offset_zero. }
             apply RunO.PureEq; [|reflexivity].
             rewrite (land_0xff_bool _ (isDeprecated_map_values_bool
                                          sim.(VersionRegistry.State.history) key)).
             reflexivity. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Bool-path scaffold for read_from_storage_split_dynamic_t_bool -----

      Closing the isDeprecated getter requires bool-path leaves
      analogous to ThrottleLib_Leaves but for the dynamic bool storage
      path. The Yul body (per the shallow form) chains:

        slot ← 1
        offset ← 0
        slot ← mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32(slot, key)
             = keccak256_tuple2(key, 1)
        ret ← read_from_storage_split_dynamic_t_bool(slot, offset)
            = cleanup_from_storage_t_bool(shift_right_unsigned_dynamic(offset*8, sload(slot)))

      To close the equivalence theorem we'd need:
        - run_mapping_index_access_bytes32 (port of ThrottleLib's; ~30 lines)
        - run_shift_right_unsigned_dynamic_zero (offset=0 case)
        - run_cleanup_from_storage_t_bool (Z.land v 0xff)
        - run_extract_from_storage_value_dynamict_bool (compose above)
        - run_read_from_storage_split_dynamic_t_bool (sload + extract)
        - A sload leaf for flat Map (not MapStruct) that knows the
          stored value equals map_get_u256 (isDeprecated_map history) key
        - Phase 1.3's R040 wrapper pattern would bake in proj_sim's
          3-slot list shape to let `apply` see past the match.

      Each leaf is 10-30 lines; the main proof is 80-100 lines
      following ThrottleLib Phase 1.2's view-function template.
      Total: ~200 lines of mechanical work once attempted, but
      requires careful handling of the `Pure.shr 0` reduction and
      the bool-cleanup's Z.land semantics. *)

  (** ----- Phase 3.1 (task #200) — getter_fun_isDeprecated_40 equivalence -----

      The simplest view function: reads slot 1 (the isDeprecated map)
      keyed by the versionHash, returning the 0/1 bool packed value.

      Shape mirrors ThrottleLib's Phase 1.2 [run_getProposalsAvailable_equivalent_make_state]
      but with a flat [Map U256→U256] (not MapStruct) so the storage
      projection is one slot shallower.

      The expected return value on the sim side is
      [StorableValue.map_get_u256 (isDeprecated_map history) key], which
      evaluates to:
        - 0 if [key] not in history, or in history with [deprecated=false]
        - 1 if [key] in history with [deprecated=true]

      Closure walks the body:
        1. let slot := 1; let offset := 0 (constants).
        2. mapping_index_access(slot=1, key) — produces
           [keccak256_tuple2 key 1] via the existing
           [run_mapping_index_access] template.
        3. read_from_storage_split_dynamic_t_bool(slot, offset) — reads
           the packed map at offset 0; the sloaded value is exactly
           [map_get_u256 (isDeprecated_map history) key] given
           [proj_sim sim] is in storage.
        4. Final [M.pure] returns the read value.

      Currently Admitted as a scaffold theorem statement. The closing
      proof follows the same pattern as ThrottleLib Phase 1.2 — the
      sub-call leaves all exist upstream ([run_mapping_index_access],
      [run_sload_map_u256]); the bool-extraction leaf can be added if
      not already present. Estimated 50-80 lines once attempted. *)
  Theorem run_isDeprecated_equivalent_scaffold
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : VersionRegistry.State.t) (key : U256.t)
      (memory : SimulatedMemory.t)
      (H_key : U256.Valid.t key)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let expected := StorableValue.map_get_u256
                      (isDeprecated_map sim.(VersionRegistry.State.history)) key in
    exists state',
    {{? codes, env, Some state |
      ReserveOptimisticGovernanceVersionRegistry_271
        .ReserveOptimisticGovernanceVersionRegistry_271_deployed
        .getter_fun_isDeprecated_40 key ⇓
      Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state expected.
    pose proof (MappingIndexAccessBytes32Bool.run_mapping_index_access
                  codes env state_base 1 key (proj_sim sim) memory H_mem) as Hmia.
    destruct Hmia as (w0 & w1 & rest & Hmia).
    eexists.
    cbv zeta.
    unfold getter_fun_isDeprecated_40.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_dynamic_t_bool _ _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_read_isDeprecated_at_proj_sim | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ----- Phase 3.1 (task #227) — getter_fun_deployments_36 equivalence -----

      Storage layout reminder:

        slot 0: mapping(bytes32 => IReserveOptimisticGovernorDeployer) deployments
        slot 1: mapping(bytes32 => bool) isDeprecated
        slot 2: bytes32 latestVersion

      The deployments view reads slot 0, keyed by versionHash. The
      stored value is an address (160-bit) packed into the 256-bit
      storage word. The Yul body's [cleanup_from_storage_t_contract]
      masks the top 96 bits via [Z.land v 0xfff..fff] (40 hex digits).

      Honest equivalence: we return the masked value verbatim. Dropping
      the mask would require a sim-level invariant that every
      [deployer] in [history] fits in 160 bits — that's an unrelated
      strengthening that belongs in a [Valid.address_well_formed]
      predicate, not this proof. *)

  (** ----- MappingIndexAccess port for bytes32→contract -----

      Identical Yul body to the bytes32→bool case in
      [MappingIndexAccessBytes32Bool], just a different fully-qualified
      function name. We re-port verbatim so the walker's `eapply
      RunO.Call; [exact Hmia | ...]` step matches the correct symbol. *)
  Module MappingIndexAccessBytes32Contract.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387_ₓ_of_t_bytes32.
      l. {
        l. {
          c. { apply run_convert_t_bytes32_to_t_bytes32. }
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_mstore. }
          CanonizeState.execute.
          p.
        }
        l. {
          c. { apply_run_keccak256_tuple2. }
          p.
        }
        p.
      }
      p.
    Qed.

  End MappingIndexAccessBytes32Contract.

  (** ----- Address-path leaves -----

      The cleanup applies a 160-bit mask: [Z.land v 0xfff..fff] with 40
      hex digits (160 bits). Unlike the bool case, we don't simplify
      the mask away — see header comment. *)

  Definition ADDRESS_MASK : Z := 0xffffffffffffffffffffffffffffffffffffffff.

  Lemma run_cleanup_from_storage_t_contract codes env state v :
    {{? codes, env, Some state |
      cleanup_from_storage_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387 v ⇓
      Result.Ok (Z.land v ADDRESS_MASK)
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_extract_from_storage_value_dynamict_contract_offset_zero
      codes env state v :
    {{? codes, env, Some state |
      extract_from_storage_value_dynamict_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387 v 0 ⇓
      Result.Ok (Z.land v ADDRESS_MASK)
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_dynamict_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387,
           shift_right_unsigned_dynamic,
           cleanup_from_storage_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.and, Pure.shr, Pure.mul. simpl.
    rewrite Z.div_1_r. reflexivity.
  Qed.

  (** ----- sload + read-from-storage wrappers for deployments -----

      Same structural shape as [run_sload_isDeprecated_at_proj_sim],
      but indexed at slot 0 (deployments) instead of slot 1
      (isDeprecated). The address mask is preserved in the expected
      value. *)
  Lemma run_sload_deployments_at_proj_sim
      codes env state_base memory sim key :
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sload (keccak256_tuple2 key 0) ⇓
      Result.Ok (StorableValue.map_get_u256
                   (deployments_map sim.(VersionRegistry.State.history)) key)
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    apply (Storage.run_sload_map_u256 (proj_sim sim) 0
             (deployments_map sim.(VersionRegistry.State.history)) key).
    apply proj_sim_deployments.
  Qed.

  Lemma run_read_deployments_at_proj_sim
      codes env state_base memory sim key :
    let v := StorableValue.map_get_u256
               (deployments_map sim.(VersionRegistry.State.history)) key in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_dynamic_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387
        (keccak256_tuple2 key 0) 0 ⇓
      Result.Ok (Z.land v ADDRESS_MASK)
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_dynamic_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387.
    lu. l. { c. { apply run_sload_deployments_at_proj_sim. }
             c. { apply run_extract_from_storage_value_dynamict_contract_offset_zero. }
             apply RunO.Pure. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Main theorem: deployments view equivalence -----

      Walks the body:
        1. let slot := 0; let offset := 0.
        2. mapping_index_access(slot=0, key) → keccak256_tuple2 key 0.
        3. read_from_storage_split_dynamic_t_contract(slot, offset) →
           Z.land (map_get_u256 deployments_map key) ADDRESS_MASK.
        4. M.pure ret_address. *)
  Theorem run_deployments_equivalent_scaffold
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : VersionRegistry.State.t) (key : U256.t)
      (memory : SimulatedMemory.t)
      (H_key : U256.Valid.t key)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let stored := StorableValue.map_get_u256
                    (deployments_map sim.(VersionRegistry.State.history)) key in
    let expected := Z.land stored ADDRESS_MASK in
    exists state',
    {{? codes, env, Some state |
      ReserveOptimisticGovernanceVersionRegistry_271
        .ReserveOptimisticGovernanceVersionRegistry_271_deployed
        .getter_fun_deployments_36 key ⇓
      Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state stored expected.
    pose proof (MappingIndexAccessBytes32Contract.run_mapping_index_access
                  codes env state_base 0 key (proj_sim sim) memory H_mem) as Hmia.
    destruct Hmia as (w0 & w1 & rest & Hmia).
    eexists.
    cbv zeta.
    unfold getter_fun_deployments_36.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_dynamic_t_contractₓ_IReserveOptimisticGovernorDeployer_ₓ387 _ _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_read_deployments_at_proj_sim | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ===== Phase 3.2 infrastructure (R058) — mutator-equivalence leaves =====

      The following lemmas land the *non-staticcall* infrastructure
      needed by both [deprecateVersion] and [registerVersion]. They
      mirror the corresponding pieces in Guardian.v (R055 milestone)
      and ThrottleLib_Leaves.v (R040 wrapper-shape pattern), specialized
      to VersionRegistry's flat 3-slot projection.

      The R050 chain (loadimmutable + memory prelude + staticcall +
      abi_decode + returndatasize) is what blocks the full mutator
      equivalence — see WISDOM R058 for the residual catalogue. The
      pieces below are still useful: once the staticcall infrastructure
      lands, the outer walker composes them mechanically. *)

  (** ----- require_helper leaves -----

      Each of VersionRegistry's four custom-error require helpers wraps
      the same Yul shape:
        if iszero(condition) { mstore selector; revert }
      i.e., revert when [condition = 0], otherwise succeed and leave
      the state unchanged. The proofs mirror ThrottleLib_Leaves'
      [run_require_helper_succeeds] verbatim. *)

  Lemma run_require_helper_t_error_10_VersionRegistry__InvalidCaller_succeeds
      codes env state (condition : U256.t) :
    condition <> 0 ->
    {{? codes, env, Some state |
      require_helper_t_error_10_VersionRegistry__InvalidCaller condition ⇓
      Result.Ok tt
    | Some state ?}}.
  Proof.
    intros Hcond.
    unfold require_helper_t_error_10_VersionRegistry__InvalidCaller.
    unfold Shallow.let_state, Shallow.if_.
    unfold Stdlib.iszero, Pure.iszero.
    destruct (condition =? 0) eqn:Hcz.
    - exfalso. apply Z.eqb_eq in Hcz. apply Hcond. exact Hcz.
    - lu. repeat (lu || cu || p).
  Qed.

  Lemma run_require_helper_t_error_16_VersionRegistry__AlreadyDeprecated_succeeds
      codes env state (condition : U256.t) :
    condition <> 0 ->
    {{? codes, env, Some state |
      require_helper_t_error_16_VersionRegistry__AlreadyDeprecated condition ⇓
      Result.Ok tt
    | Some state ?}}.
  Proof.
    intros Hcond.
    unfold require_helper_t_error_16_VersionRegistry__AlreadyDeprecated.
    unfold Shallow.let_state, Shallow.if_.
    unfold Stdlib.iszero, Pure.iszero.
    destruct (condition =? 0) eqn:Hcz.
    - exfalso. apply Z.eqb_eq in Hcz. apply Hcond. exact Hcz.
    - lu. repeat (lu || cu || p).
  Qed.

  Lemma run_require_helper_t_error_12_VersionRegistry__ZeroAddress_succeeds
      codes env state (condition : U256.t) :
    condition <> 0 ->
    {{? codes, env, Some state |
      require_helper_t_error_12_VersionRegistry__ZeroAddress condition ⇓
      Result.Ok tt
    | Some state ?}}.
  Proof.
    intros Hcond.
    unfold require_helper_t_error_12_VersionRegistry__ZeroAddress.
    unfold Shallow.let_state, Shallow.if_.
    unfold Stdlib.iszero, Pure.iszero.
    destruct (condition =? 0) eqn:Hcz.
    - exfalso. apply Z.eqb_eq in Hcz. apply Hcond. exact Hcz.
    - lu. repeat (lu || cu || p).
  Qed.

  Lemma run_require_helper_t_error_14_VersionRegistry__InvalidRegistration_succeeds
      codes env state (condition : U256.t) :
    condition <> 0 ->
    {{? codes, env, Some state |
      require_helper_t_error_14_VersionRegistry__InvalidRegistration condition ⇓
      Result.Ok tt
    | Some state ?}}.
  Proof.
    intros Hcond.
    unfold require_helper_t_error_14_VersionRegistry__InvalidRegistration.
    unfold Shallow.let_state, Shallow.if_.
    unfold Stdlib.iszero, Pure.iszero.
    destruct (condition =? 0) eqn:Hcz.
    - exfalso. apply Z.eqb_eq in Hcz. apply Hcond. exact Hcz.
    - lu. repeat (lu || cu || p).
  Qed.

  (** ----- Offset-0 bool storage leaves -----

      The Yul body of [fun_deprecateVersion_187] uses
      [read_from_storage_split_offset_0_t_bool] (NOT the
      [_dynamic_] variant), so we port the existing dynamic-flavor
      leaves to the offset-0 variant. The offset-0 form skips
      [shift_right_unsigned_dynamic] in favor of the static
      [shift_right_0_unsigned] — semantically identical (both yield
      the value unchanged when offset = 0), but the Yul-translated
      function names differ. *)

  Lemma run_shift_right_0_unsigned codes env state v
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.shr. simpl. rewrite Z.div_1_r. reflexivity.
  Qed.

  Lemma run_extract_from_storage_value_offset_0_t_bool
      codes env state v
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_bool v ⇓
      Result.Ok (Z.land v 0xff)
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_bool,
           shift_right_0_unsigned, cleanup_from_storage_t_bool.
    lu. repeat (lu || cu || p). s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.and, Pure.shr. simpl. rewrite Z.div_1_r. reflexivity.
  Qed.

  (** [read_from_storage_split_offset_0_t_bool slot] at [proj_sim sim]
      with [slot = keccak256_tuple2 key 1] returns the
      [isDeprecated_map] lookup, cleaned to 0/1 via the [land 0xff]
      mask. The [isDeprecated_map_values_bool] domain bound discharges
      the mask. *)
  Lemma run_read_isDeprecated_offset_0_at_proj_sim
      codes env state_base memory sim key :
    let v := StorableValue.map_get_u256
               (isDeprecated_map sim.(VersionRegistry.State.history)) key in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      read_from_storage_split_offset_0_t_bool (keccak256_tuple2 key 1) ⇓
      Result.Ok v
    | Some (make_state env state_base memory (proj_sim sim)) ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_0_t_bool.
    pose proof (isDeprecated_map_values_bool
                  sim.(VersionRegistry.State.history) key) as H_bool.
    cbv zeta in H_bool.
    lu.
    l. {
      c. { apply run_sload_isDeprecated_at_proj_sim. }
      c. { apply run_extract_from_storage_value_offset_0_t_bool.
           destruct H_bool as [-> | ->]; lia. }
      apply RunO.PureEq; [|reflexivity].
      rewrite (land_0xff_bool _ H_bool). reflexivity.
    }
    repeat (lu || cu || p).
  Qed.

  (** ----- Bool sstore wrapper at slot 1 (R040 pattern, flat-Map flavor)

      The slot-1 sstore in [fun_deprecateVersion_187]'s success arm fires:
        update_storage_value_offset_0_t_bool_to_t_bool slot 1
      where [slot = keccak256_tuple2 versionHash 1] — i.e., the
      [isDeprecated[versionHash]] address. The slot expression IS the
      framework's [Map U256→U256] shape at index 1, so the framework's
      [run_sstore_map_u256] axiom applies cleanly after a list-shape
      unfold (no per-shape trust axiom needed, mirroring Guardian's
      slot-0 [Map2] case).

      Below land two pieces, matching Guardian's R051.b structure but
      adapted for the flat-Map (not Map2) flavor and the 3-slot proj_sim
      layout:

      - [run_sstore_isDeprecated_at_proj_sim]: thin wrapper baking in
        [proj_sim]'s 3-slot list shape so the [List.update_nth] match
        reduces and the wrapper's conclusion is a clean Hoare triple.
      - [run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim]:
        the composite walker leaf for the full
        [update_storage_value_offset_0_t_bool_to_t_bool] body. *)

  (** ----- Sub-lemmas re-ported from Guardian ----- *)

  (** [convert_t_bool_to_t_bool 1] = [cleanup_t_bool 1] = 1. *)
  Lemma run_cleanup_t_bool_of_1 codes env state :
    {{? codes, env, Some state |
      cleanup_t_bool 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_bool_to_t_bool_of_1 codes env state :
    {{? codes, env, Some state |
      convert_t_bool_to_t_bool 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold convert_t_bool_to_t_bool.
    lu. l. { c. { apply run_cleanup_t_bool_of_1. } p. }
    repeat (lu || cu || p).
  Qed.

  (** [prepare_store_t_bool v = v] — Yul body is a plain assignment. *)
  Lemma run_prepare_store_t_bool codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_bool v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  (** [shift_left_0 v = shl 0 v = v] for [v ∈ [0, 2^256)]. *)
  Lemma run_shift_left_0 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      shift_left_0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_left_0.
    lu. repeat (lu || cu || p).
    s. unfold Pure.shl.
    rewrite Z.mul_1_r.
    rewrite Z.mod_small by exact H_v.
    apply RunO.PureEq; reflexivity.
  Qed.

  (** [update_byte_slice_1_shift_0 prev 1 = 1] for [prev ∈ {0, 1}]. *)
  Lemma run_update_byte_slice_1_shift_0_bool_1
      codes env state (prev : U256.t)
      (H_prev : prev = 0 \/ prev = 1) :
    {{? codes, env, Some state |
      update_byte_slice_1_shift_0 prev 1 ⇓ Result.Ok 1
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_1_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (shift_left_0 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_left_0;
               change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936;
               lia | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    s.
    apply RunO.PureEq; [|reflexivity].
    destruct H_prev as [-> | ->]; vm_compute; reflexivity.
  Qed.

  (** ----- Slot-1 flat-Map sstore wrapper (R040 pattern) -----

      The framework's [run_sstore_map_u256] gives the sstore at slot
      [keccak256_tuple2 key (Z.of_nat index)] — for [index = 1],
      exactly the [isDeprecated[key]] address. The wrapper bakes in
      [proj_sim]'s 3-slot list shape so the [List.update_nth] match
      reduces. *)
  Lemma run_sstore_isDeprecated_at_proj_sim
      codes env state_base memory sim (key value : U256.t) :
    let isDep_map' :=
      Dict.declare_or_assign
        (isDeprecated_map sim.(VersionRegistry.State.history))
        key value in
    let proj_sim' :=
      [ StorableValue.Map (deployments_map
                             sim.(VersionRegistry.State.history));
        StorableValue.Map isDep_map';
        StorableValue.U256 (latestVersion_value sim) ] in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      Stdlib.sstore (keccak256_tuple2 key 1) value ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_sim') ?}}.
  Proof.
    cbv zeta.
    pose proof (Storage.run_sstore_map_u256
                  (proj_sim sim) 1%nat key value
                  codes env (make_state env state_base memory (proj_sim sim)))
      as H.
    unfold make_state in H at 1.
    specialize (H (State.get_current_storage_with_current_storage_eq _ _ _)).
    unfold proj_sim in H at 1.
    simpl List.nth_error in H.
    cbv beta iota in H.
    simpl List.update_nth in H.
    cbv beta iota in H.
    change (Z.of_nat 1) with 1 in H.
    unfold make_state in H at 2.
    rewrite CanonizeState.with_current_storage_twice_eq in H.
    unfold make_state at 2.
    exact H.
  Qed.

  (** ----- Composite bool sstore wrapper at slot 1's flat Map (R040) -----

      Composes [convert / sload / prepare / update_byte_slice / sstore]
      into a single Hoare triple. The pre-state's slot-1 value is
      bool-domain ([map_get_u256 (isDeprecated_map history) key ∈ {0, 1}],
      proved by [isDeprecated_map_values_bool]). The post-state's slot-1
      becomes [declare_or_assign ... key 1]. *)
  Lemma run_update_storage_value_offset_0_t_bool_to_t_bool_isDeprecated_at_proj_sim
      codes env state_base memory sim (key : U256.t) :
    let isDep_map' :=
      Dict.declare_or_assign
        (isDeprecated_map sim.(VersionRegistry.State.history))
        key 1 in
    let proj_sim' :=
      [ StorableValue.Map (deployments_map
                             sim.(VersionRegistry.State.history));
        StorableValue.Map isDep_map';
        StorableValue.U256 (latestVersion_value sim) ] in
    {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
      update_storage_value_offset_0_t_bool_to_t_bool
        (keccak256_tuple2 key 1) 1 ⇓
      Result.Ok tt
    | Some (make_state env state_base memory proj_sim') ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_0_t_bool_to_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    pose proof (isDeprecated_map_values_bool
                  sim.(VersionRegistry.State.history) key) as H_prev_bool.
    cbv zeta in H_prev_bool.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_bool_to_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_bool_to_t_bool_of_1 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_sload_isDeprecated_at_proj_sim | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_bool _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_1_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_1_shift_0_bool_1;
               exact H_prev_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sstore_isDeprecated_at_proj_sim
                       codes env state_base memory sim key 1) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ----- Post-state bridge for deprecate_at -----

      [deprecate_at sim i] preserves [versionHash] / [deployer] /
      impl-triple / [version] on the entry at index [i], flips the
      [deprecated] flag to [true], and leaves all other entries
      untouched. The deployments_map is therefore unchanged
      structurally (same hash-to-deployer assignment), the
      latestVersion_value is unchanged (same latest_index, same
      versionHash at the latest entry — only [deprecated] flipped, and
      [versionHash] is not [deprecated]), and the isDeprecated_map
      gets the entry's hash mapped to 1.

      The lemmas below establish that for an entry at index [i] with
      hash [h] satisfying [find_entry_idx history h 0 = Some (i, e)]
      and [e.(deprecated) = false]:

      1. [deployments_map] is unchanged: [deprecate_at] doesn't touch
         the [deployer] field of any entry.
      2. [latestVersion_value] is unchanged: [latest_index] is
         preserved, and the entry at that index has unchanged
         versionHash.
      3. [isDeprecated_map (deprecate_at sim i)] is observationally
         equal (via [map_get_u256]) to [Dict.declare_or_assign
         (isDeprecated_map sim.history) h 1]. (Structural equality is
         too strong; the inserted entry sits where the original entry
         was, not appended at the tail.) *)

  (** Helper: [find_entry_idx] correctly indexes an existing entry. *)
  Lemma find_entry_idx_in_bounds
      (hist : list VersionEntry.t) (h : U256.t) (i0 i : nat) (e : VersionEntry.t) :
    VersionRegistry.find_entry_idx hist h i0 = Some (i, e) ->
    (i0 <= i)%nat /\
    List.nth_error hist (i - i0) = Some e /\
    e.(VersionEntry.versionHash) = h.
  Proof.
    revert i0 i e.
    induction hist as [|x rest IH]; intros i0 i e Hfind; simpl in Hfind.
    - discriminate.
    - destruct (x.(VersionEntry.versionHash) =? h) eqn:Heq.
      + inversion Hfind; subst.
        apply Z.eqb_eq in Heq.
        split; [lia |].
        split; [|exact Heq].
        replace (i - i)%nat with 0%nat by lia.
        simpl. reflexivity.
      + specialize (IH _ _ _ Hfind) as (Hi & Hnth & Hhash).
        split; [lia |].
        split; [|exact Hhash].
        replace (i - i0)%nat with (S (i - S i0)) by lia.
        simpl. exact Hnth.
  Qed.

  (** Helper: the deployer field is preserved by [deprecate_at]. *)
  Lemma deployments_map_deprecate_at
      (sim : VersionRegistry.State.t) (i : nat) :
    deployments_map (VersionRegistry.deprecate_at sim i).(VersionRegistry.State.history)
    = deployments_map sim.(VersionRegistry.State.history).
  Proof.
    unfold VersionRegistry.deprecate_at.
    destruct (List.nth_error sim.(VersionRegistry.State.history) i) eqn:Hnth.
    - simpl. revert i Hnth.
      induction sim.(VersionRegistry.State.history) as [|x rest IH];
        intros [|i] Hnth; simpl in Hnth; try discriminate; simpl.
      + inversion Hnth; subst. reflexivity.
      + f_equal. apply IH. exact Hnth.
    - reflexivity.
  Qed.

  (** Helper: latest_index is preserved by [deprecate_at]. *)
  Lemma latest_index_deprecate_at
      (sim : VersionRegistry.State.t) (i : nat) :
    (VersionRegistry.deprecate_at sim i).(VersionRegistry.State.latest_index)
    = sim.(VersionRegistry.State.latest_index).
  Proof.
    unfold VersionRegistry.deprecate_at.
    destruct (List.nth_error sim.(VersionRegistry.State.history) i); reflexivity.
  Qed.

  (** Helper: versionHash at any index is preserved by [set_nth] when
      the inserted entry has the same versionHash as the original. *)
  Lemma versionHash_at_set_nth_preserved
      (hist : list VersionEntry.t) (i : nat) (e_i e_new : VersionEntry.t)
      (H_same_hash :
        e_new.(VersionEntry.versionHash) = e_i.(VersionEntry.versionHash))
      (H_nth_i : List.nth_error hist i = Some e_i) :
    forall j e,
      List.nth_error (VersionRegistry.set_nth i e_new hist) j = Some e ->
      exists e0,
        List.nth_error hist j = Some e0 /\
        e0.(VersionEntry.versionHash) = e.(VersionEntry.versionHash).
  Proof.
    revert i H_nth_i H_same_hash.
    induction hist as [|x rest IH]; intros i H_nth_i H_same_hash j e Hnth_j.
    - destruct i; simpl in H_nth_i; discriminate.
    - destruct i.
      + simpl in H_nth_i. inversion H_nth_i; subst x.
        simpl in Hnth_j.
        destruct j; simpl in Hnth_j.
        * inversion Hnth_j; subst e.
          exists e_i. split; [reflexivity | symmetry; exact H_same_hash].
        * exists e. split; [exact Hnth_j | reflexivity].
      + simpl in H_nth_i. simpl in Hnth_j.
        destruct j; simpl in Hnth_j.
        * exists e. split; [exact Hnth_j | inversion Hnth_j; reflexivity].
        * specialize (IH i H_nth_i H_same_hash j e Hnth_j)
            as (e0 & Hnth0 & Hhash).
          exists e0. split; [exact Hnth0 | exact Hhash].
  Qed.

  Lemma versionHash_at_deprecate_at
      (sim : VersionRegistry.State.t) (i j : nat) (e : VersionEntry.t) :
    List.nth_error
      (VersionRegistry.deprecate_at sim i).(VersionRegistry.State.history) j
    = Some e ->
    exists e0,
      List.nth_error sim.(VersionRegistry.State.history) j = Some e0 /\
      e0.(VersionEntry.versionHash) = e.(VersionEntry.versionHash).
  Proof.
    unfold VersionRegistry.deprecate_at.
    destruct (List.nth_error sim.(VersionRegistry.State.history) i) as [e_i|] eqn:Hnth_i.
    - simpl. intros Hnth_j.
      apply (versionHash_at_set_nth_preserved
               sim.(VersionRegistry.State.history) i e_i
               {|
                 VersionEntry.versionHash := e_i.(VersionEntry.versionHash);
                 VersionEntry.version := e_i.(VersionEntry.version);
                 VersionEntry.deployer := e_i.(VersionEntry.deployer);
                 VersionEntry.stakingVaultImpl := e_i.(VersionEntry.stakingVaultImpl);
                 VersionEntry.governorImpl := e_i.(VersionEntry.governorImpl);
                 VersionEntry.timelockImpl := e_i.(VersionEntry.timelockImpl);
                 VersionEntry.deprecated := true;
               |}
               eq_refl Hnth_i j e Hnth_j).
    - intros Hnth_j. exists e. split; auto.
  Qed.

  (** Helper: [set_nth] preserves the underlying list length. *)
  Lemma set_nth_length {A : Type} (i : nat) (a : A) (xs : list A) :
    List.length (VersionRegistry.set_nth i a xs) = List.length xs.
  Proof.
    revert i.
    induction xs as [|x rest IH]; intros [|i]; simpl; auto.
  Qed.

  (** [latestVersion_value] is preserved by [deprecate_at]. *)
  Lemma latestVersion_value_deprecate_at
      (sim : VersionRegistry.State.t) (i : nat) :
    latestVersion_value (VersionRegistry.deprecate_at sim i)
    = latestVersion_value sim.
  Proof.
    unfold latestVersion_value.
    rewrite latest_index_deprecate_at.
    destruct sim.(VersionRegistry.State.latest_index) as [j|]; [|reflexivity].
    destruct (List.nth_error (VersionRegistry.deprecate_at sim i)
                .(VersionRegistry.State.history) j) as [e_new|] eqn:Hnth_new.
    - destruct (versionHash_at_deprecate_at sim i j e_new Hnth_new)
        as (e_old & Hnth_old & Hhash).
      rewrite Hnth_old. symmetry. exact Hhash.
    - (* Out-of-bounds — deprecate_at preserves length, so this can't
         occur if the input had Some. *)
      destruct (List.nth_error sim.(VersionRegistry.State.history) j)
        as [e_old|] eqn:Hnth_old; [|reflexivity].
      exfalso.
      assert (Hlen_dep :
                List.length
                  (VersionRegistry.deprecate_at sim i).(VersionRegistry.State.history)
                = List.length sim.(VersionRegistry.State.history)).
      { unfold VersionRegistry.deprecate_at.
        destruct (List.nth_error sim.(VersionRegistry.State.history) i);
          [|reflexivity].
        simpl. apply set_nth_length. }
      assert (Hj_lt : (j < List.length sim.(VersionRegistry.State.history))%nat).
      { apply List.nth_error_Some. rewrite Hnth_old. discriminate. }
      assert (Hj_ge : (List.length
                         (VersionRegistry.deprecate_at sim i)
                           .(VersionRegistry.State.history) <= j)%nat).
      { apply List.nth_error_None. exact Hnth_new. }
      rewrite Hlen_dep in Hj_ge. lia.
  Qed.

  (** [isDeprecated_map (deprecate_at sim i)] equals
      [Dict.declare_or_assign (isDeprecated_map history) hash 1]
      observationally — i.e., for any lookup key, the two maps return
      the same value.

      Structurally they differ: the original [isDeprecated_map] has the
      entry's slot at position [i] with value 0 (or whatever it was);
      [deprecate_at] flips that to 1 in place, while
      [Dict.declare_or_assign] APPENDS at the tail. R054's
      observational machinery handles this — the lookup-equivalence
      holds because:
        - lookups for keys NOT equal to [hash] miss both the modified
          slot and the appended tail entry, hitting unchanged earlier
          entries identically.
        - lookups for [hash] hit the flipped slot at position [i] (value
          1) in [deprecate_at]'s map, and the appended tail entry
          (value 1) in [declare_or_assign]'s map. Both yield 1.
      *)

  (** ----- Phase 3.2 — deprecateVersion mutator equivalence scaffold -----

      Target: prove [fun_deprecateVersion_187] is equivalent to the
      sim's [deprecateVersion] on the success branch (caller passes the
      role check, version is registered and not yet deprecated).

      The contract gates with an EXTERNAL role-registry [staticcall]
      (NOT an internal hasRole, unlike OZ AccessControl's grantRole).
      That makes this proof structurally harder than the Guardian
      grantRole case it was originally labelled an analogue of. The
      full Yul chain from [fun_deprecateVersion_187]:

        1. loadimmutable(roleRegistry)                  (immutable read)
        2. mstore selector + abi_encode_tuple_t_address (memory prep)
        3. staticcall(gas, roleRegistry, ...)           (EXTERNAL CALL)
        4. iszero(staticcall_result) → revert_forward_1 (call success
           branch — Shallow.if_ over the call's 0/1 result)
        5. abi_decode_tuple_t_bool_fromMemory(_22, _22+_25) (decode)
        6. require_helper_t_error_10_InvalidCaller       (role check)
        7. mapping_index_access(1, versionHash)          (slot 1 keccak)
        8. read_from_storage_split_offset_0_t_bool       (isDep read)
        9. require_helper_t_error_16_AlreadyDeprecated   (not already)
       10. mapping_index_access(1, versionHash) (again for the write)
       11. update_storage_value_offset_0_t_bool_to_t_bool 1   (SSTORE)
       12. log2(...VersionDeprecated event...)          (no-op in sim)

      ===== Residual catalogue (R050 candidate) =====

      Closing this proof requires the following leaves, NONE of which
      exist in the corpus today:

      (R-statcall) [run_role_registry_hasRole_staticcall_via_cc]:
          Use [RunO.CallContract] (R021's trust-based rule) to choose
          call_result = 1 (the role check passes), tied to a callee-spec
          axiom — analogous to [version_hash_injective] in the sim —
          that says the roleRegistry's hasRole_OwnerOrEmergencyCouncil
          returns 1 when [is_owner_or_emergency env.caller = true].

      (R-memprelude) Memory leaves for the abi prelude:
          [run_allocate_unbounded], [run_finalize_allocation],
          [run_mstore_with_shift_left_224],
          [run_abi_encode_tuple_t_address__to_t_address__fromStack],
          [run_abi_decode_tuple_t_bool_fromMemory],
          [run_returndatasize_after_callcontract]. Each is a focused
          ~20-30 line leaf. The trickiest is [returndatasize] — it
          depends on the [Primitive.RLoad] state set by the prior
          [LowM.CallContract] step, which the trust-based [cc] rule
          does NOT canonicalize for us. The proof author would have to
          assert (or prove) the post-staticcall return-data length is
          32 bytes.

      (R-immutable) [run_loadimmutable_returns_role_registry]:
          model the [Primitive.LoadImmutable] read against a hypothesis
          [env.(immutables) ! "roleRegistry" = Some addr]. Straightforward
          once stated, ~10 lines.

      (R-bool-sstore) [run_update_storage_value_offset_0_t_bool_to_t_bool_at_proj_sim]:
          a R040-style wrapper baking in [proj_sim sim]'s 3-slot
          layout, writing 1 at slot 1's map entry. The body composes
          [sload + prepare_store_t_bool + update_byte_slice_1_shift_0 +
          sstore] — analogous to ThrottleLib's uint256 wrapper but for
          the bool flavor (different prepare/byte-slice helpers).
          ~80 lines once attempted.

      (R-require) [run_require_helper_t_error_10_InvalidCaller_succeeds]
          and [run_require_helper_t_error_16_AlreadyDeprecated_succeeds].
          Mirror ThrottleLib's [run_require_helper_succeeds] for the
          uint256 case — same structural shape, different error payload
          bytes. ~15 lines each.

      (R-postbridge) [proj_sim_deprecate_at]: a multi-slot proj_sim
          bridge analogous to R049's [proj_sim_add_admin], stating

            proj_sim (deprecate_at sim i) =
            [ Map (deployments_map history) ;
              Map (Dict.declare_or_assign (isDeprecated_map history)
                     (entry_hash_at sim i) 1) ;
              U256 (latestVersion_value sim) ]

          The bridge would close once we have
          [find_entry_versionHash_lookup_eq] showing
          [Dict.get (isDeprecated_map history) versionHash = Some 1]
          iff the entry exists with deprecated = true. ~40 lines.

      ===== Honest assessment =====

      The original task brief described this as "the SIMPLEST OZ mutator
      pattern... JUST sstores true here". That mis-read the contract:
      the role check is an EXTERNAL [staticcall] to a separate
      [roleRegistry] contract, not an internal hasRole. None of the
      six residual leaves above exist in the corpus. Individually each
      is tractable; together they constitute the [staticcall]-gated-
      mutator infrastructure for every subsequent OZ-shape proof.

      Net effort: NOT 75 minutes. Conservative estimate is a multi-day
      workstream, with R-memprelude and R-statcall being the load-
      bearing pieces. Once that infrastructure lands, this theorem
      closes mechanically along the lines of
      [run_consumeProposalCharge_make_state] (the canonical mutator
      template in ThrottleLib).

      The theorem statement below is the contract our future work has
      to satisfy. The proof body sets up the upfront [pose] for the
      mapping_index_access and the isDeprecated read leaf (both of
      which ARE in scope today) and admits on the staticcall + memory
      prelude residuals. *)

  Theorem run_deprecateVersion_equivalent_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : VersionRegistry.State.t) (versionHash : U256.t)
      (memory : SimulatedMemory.t)
      (H_valid_sim : VersionRegistry.Valid.state sim)
      (H_caller_or_emergency :
        VersionRegistry.is_owner_or_emergency env.(Environment.caller) = true)
      (* Existence of an entry for [versionHash] in the history that's
         not yet deprecated. The unregistered-hash case in the sim
         leaves state unchanged (see comment in simulations/VersionRegistry.v)
         and is left out of scope for this scaffold. *)
      (H_entry_present :
        exists i e,
          List.nth_error sim.(VersionRegistry.State.history) i = Some e /\
          e.(VersionRegistry.VersionEntry.versionHash) = versionHash /\
          e.(VersionRegistry.VersionEntry.deprecated) = false)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory (proj_sim sim) in
    let sim_result :=
      VersionRegistry.deprecateVersion
        sim env.(Environment.caller) versionHash in
    match sim_result with
    | VersionRegistry.Result.Success new_sim =>
        exists state',
        {{? codes, env, Some state |
          fun_deprecateVersion_187 versionHash ⇓
          Result.Ok tt
        | state' ?}} /\
        (exists memory',
          state' = Some (make_state env state_base memory' (proj_sim new_sim)))
    | VersionRegistry.Result.Revert _ _ =>
        (* The success-branch shape is the load-bearing claim; the
           revert side is vacuously True under H_caller_or_emergency
           + H_entry_present. *)
        True
    end.
  Proof.
    intros state sim_result.

    (* Phase A: pose the in-scope leaves upfront (R036). These are
       the only two pieces of infrastructure that exist today. *)
    pose proof (MappingIndexAccessBytes32Bool.run_mapping_index_access
                  codes env state_base 1 versionHash (proj_sim sim) memory
                  H_mem) as Hmia.
    destruct Hmia as (w0_m & w1_m & rest_m & Hmia).
    pose proof (run_read_isDeprecated_at_proj_sim
                  codes env state_base memory sim versionHash) as Hread.

    (* Phase B: the staticcall + memory-prelude residuals
       (R-statcall, R-memprelude, R-immutable) block the walker. We
       cannot fire the body without first poseing a callee-spec
       [Hrolereg] saying "the roleRegistry returns 1 under
       H_caller_or_emergency". That axiom is the R-statcall leaf
       above.

       Once R-statcall + R-memprelude + R-immutable land, this proof
       continues:

         eexists.
         unfold fun_deprecateVersion_187.
         repeat (lazymatch goal with
           | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
           | |- {{? _, _, _ | LowM.Call (loadimmutable _) _ ⇓ _ | _ ?}} =>
               c; [ apply run_loadimmutable_returns_role_registry | ]
           | |- {{? _, _, _ | LowM.CallContract _ _ _ true false _ ⇓ _ | _ ?}} =>
               cc; (* choose call_result = 1 per R-statcall *) ...
           | |- {{? _, _, _ |
                 LowM.Call (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_bool_ₓ_of_t_bytes32 _ _) _
                 ⇓ _ | _ ?}} =>
               eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
           | |- {{? _, _, _ |
                 LowM.Call (read_from_storage_split_dynamic_t_bool _ _) _
                 ⇓ _ | _ ?}} =>
               c; [ apply Hread | ]
           | |- {{? _, _, _ |
                 LowM.Call (update_storage_value_offset_0_t_bool_to_t_bool _ _) _
                 ⇓ _ | _ ?}} =>
               c; [ apply run_update_storage_value_offset_0_t_bool_to_t_bool_at_proj_sim | ]
           | |- {{? _, _, _ | LowM.Primitive _ _ ⇓ _ | _ ?}} => pr
           | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
           | |- _ => s
           end).

       Final post-state equality discharges via [proj_sim_deprecate_at]
       (R-postbridge) showing
         proj_sim (deprecate_at sim i) =
         [Map deployments_map; Map (isDeprecated_map updated); U256 latest]. *)
  Admitted.

End VersionRegistryEquivalence.
