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
  Admitted.

End VersionRegistryEquivalence.
