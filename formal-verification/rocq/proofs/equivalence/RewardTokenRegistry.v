(** Phase 3.2 (task #181) — RewardTokenRegistry equivalence scaffold.

    Storage layout (the `roleRegistry` field is `immutable`):

      slot 0+: EnumerableSet.AddressSet _rewardTokens

    The on-chain layout is governed by OpenZeppelin's EnumerableSet:

      struct AddressSet {
        bytes32[] _values;                  (* uint256[] in memory *)
        mapping(bytes32 => uint256) _positions;  (* index+1, 0 = absent *)
      }

    Inlined into slot 0, this means:

      slot 0: length of _values array (uint256)
      slot keccak256(0) + i: _values[i] (one address per slot, lower 160 bits)
      slot 1: _positions mapping base

    Equivalence with OZ EnumerableSet is its own workstream — the OZ
    contract maintains an O(1) add/remove invariant via the
    [_positions] map, and the sim abstracts it as a duplicate-free
    [list Address.t]. Closing the equivalence requires:

      1. A projection of the sim's [rewardTokens : list Address.t] into
         BOTH on-chain shapes simultaneously (the [_values] array and
         the [_positions] map).
      2. Invariant preservation across [add] / [remove] (specifically
         the swap-and-pop pattern that OZ uses on remove).
      3. An equivalence proof for each of [registerRewardToken] /
         [unregisterRewardToken] that walks the OZ library code, not
         just the contract's wrapper.

    This file scaffolds the projection target and documents the gap.
    The full OZ-equivalence work is parked under Phase 4 (heavyweight
    contracts decision). *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.RewardTokenRegistry.
Require Import ReserveGovernor.generated.RewardTokenRegistry_shallow.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Import Stdlib.
Import RunO.

Module RewardTokenRegistryEquivalence.

  Import RewardTokenRegistry.

  (** ----- Per-shape projections of the sim's set -----

      [values_array_length] mirrors slot 0 (the array's length).
      [values_array_get] mirrors the i-th element slot.
      [positions_map] mirrors the [_positions] mapping.

      Convention: the sim's [rewardTokens] list stores tokens in
      registration order (most recent at the head). OZ EnumerableSet
      stores them in the [_values] array in the same order; the
      [_positions] map then sends each token to its index+1. *)

  Definition values_array_length (sim : State.t) : U256.t :=
    Z.of_nat (List.length sim.(State.rewardTokens)).

  Fixpoint values_array_get_aux
      (tokens : list Address) (i : nat) : option Address :=
    match tokens with
    | []          => None
    | t :: rest   =>
        match i with
        | O    => Some t
        | S i' => values_array_get_aux rest i'
        end
    end.

  Definition values_array_get (sim : State.t) (i : nat) : option Address :=
    values_array_get_aux sim.(State.rewardTokens) i.

  Fixpoint positions_map_aux
      (tokens : list Address) (i : nat) : Dict.t U256.t U256.t :=
    match tokens with
    | []          => []
    | t :: rest   => (t, Z.of_nat (S i)) :: positions_map_aux rest (S i)
    end.

  Definition positions_map (sim : State.t) : Dict.t U256.t U256.t :=
    positions_map_aux sim.(State.rewardTokens) 0.

  (** ----- Projection scaffold -----

      The full storage projection lives across multiple slots due to
      the [_values] array's keccak-based addressing. Since the array
      length and the positions map fit individual [StorableValue]
      variants, we expose them here; the per-index array reads need
      either a custom variant or per-slot hypotheses (similar to
      ThrottleLib's legacy [storage_slot_value] form).

      Slot 0: length of the [_values] array.
      Slot 1: [_positions] mapping.

      Per-index array slots:
        keccak256(0) + i: [_values[i]] = the i-th registered token.

      The projection below covers the directly-addressable slots; the
      per-index array slots get expressed as a separate hypothesis in
      any equivalence theorem. *)
  Definition proj_sim_directly_addressable (sim : State.t) : SimulatedStorage.t := [
    StorableValue.U256 (values_array_length sim);
    StorableValue.Map (positions_map sim)
  ].

  (** ----- Well-formedness sanity ----- *)
  Lemma proj_sim_length (sim : State.t) :
    List.length (proj_sim_directly_addressable sim) = 2%nat.
  Proof. reflexivity. Qed.

  Lemma values_array_length_empty :
    values_array_length empty_state = 0.
  Proof. reflexivity. Qed.

  Lemma positions_map_empty :
    positions_map empty_state = [].
  Proof. reflexivity. Qed.

  Import RewardTokenRegistry_156.RewardTokenRegistry_156_deployed.

  (** ----- Keccak bound axiom (same as Guardian/ThrottleLib) ----- *)
  Axiom keccak256_tuple2_offset_bound :
    forall (key index offset : U256.t),
      0 <= offset < 32 ->
      0 <= keccak256_tuple2 key index /\
      keccak256_tuple2 key index + offset < 2 ^ 256.

  Lemma Pure_add_keccak_offset (key index offset : U256.t) :
    0 <= offset < 32 ->
    Pure.add (keccak256_tuple2 key index) offset
    = keccak256_tuple2 key index + offset.
  Proof.
    intros H_off.
    pose proof (keccak256_tuple2_offset_bound key index offset H_off) as [Hnn Hb].
    unfold Pure.add. apply Z.mod_small. lia.
  Qed.

  (** ----- Conversion-chain leaves: address → uint160 → uint256 → bytes32 -----

      The Yul body's path from [address rewardToken] to a bytes32 used
      as a mapping key threads through several leaves, each of which
      is identity (modulo cleanup) under the 160-bit address bound. *)

  Lemma run_cleanup_t_uint160_on_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    lu. repeat (lu || cu || p). s.
    replace (Pure.and v 1461501637330902918203684832716283019655932542975) with v.
    - apply RunO.Pure.
    - unfold Pure.and.
      change 1461501637330902918203684832716283019655932542975 with (Z.ones 160).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
  Qed.

  Lemma run_cleanup_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_cleanup_t_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_bytes32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_bytes32_to_t_bytes32 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_bytes32_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_bytes32_to_t_bytes32.
    lu. l. { c. { apply run_cleanup_t_bytes32. } p. } p.
  Qed.

  Lemma run_identity codes env state (v : U256.t) :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold identity.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_shift_left_0 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      shift_left_0 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_left_0.
    lu. repeat (lu || cu || p). s.
    replace (Pure.shl 0 v) with v.
    - apply RunO.Pure.
    - unfold Pure.shl. simpl. rewrite Z.mul_1_r.
      rewrite Z.mod_small by exact H_v. reflexivity.
  Qed.

  Lemma run_convert_t_uint160_to_t_uint160 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             p. } p.
  Qed.

  Lemma run_convert_t_address_to_t_uint160 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_uint160.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160. exact H_v. } p. } p.
  Qed.

  Lemma run_convert_t_uint160_to_t_uint256 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address. exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint256. }
             p. } p.
  Qed.

  Lemma run_convert_t_uint256_to_t_bytes32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_bytes32.
    lu. l. { c. { apply run_cleanup_t_uint256. }
             c. { apply run_shift_left_0. exact H_v. }
             c. { apply run_cleanup_t_bytes32. }
             p. } p.
  Qed.

  (** [run_convert_t_address_to_t_bytes32_chain]: the composed
      address → uint160 → uint256 → bytes32 conversion preserves
      values within the 160-bit address range. Used inline by the
      main [run_isRegistered_equivalent] body; not exposed as a
      single chain lemma because the Yul body interleaves the steps
      via [let~] rather than [M.let_]. *)

  (** ----- Struct-ptr identity converters ----- *)
  Lemma run_convert_t_struct_AddressSet_storage_to_ptr
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_structₓ_AddressSet_ₓ684_storage_to_t_structₓ_AddressSet_ₓ684_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_structₓ_AddressSet_ₓ684_storage_to_t_structₓ_AddressSet_ₓ684_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_struct_Set_storage_to_ptr
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  (** ----- Mapping_index_access for bytes32 → uint256 (the positions map) ----- *)
  Module MappingIndexAccessBytes32Uint256.

    Lemma run_mapping_index_access codes env state_base
        (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
        (memory : SimulatedMemory.t)
        (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
      let st := make_state env state_base memory storage in
      exists w0' w1' rest',
      {{? codes, env, Some st |
        mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32 slot key ⇓
        Result.Ok (keccak256_tuple2 key slot)
      | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
    Proof.
      destruct H_mem as (w0 & w1 & rest & ->).
      do 3 eexists.
      unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32.
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

  End MappingIndexAccessBytes32Uint256.

  (** ----- sload at positions slot via Map projection ----- *)
  Lemma run_sload_positions_at_proj_sim
      codes env state_base memory sim (key : U256.t) :
    {{? codes, env, Some (make_state env state_base memory
                            (proj_sim_directly_addressable sim)) |
      Stdlib.sload (keccak256_tuple2 key 1) ⇓
      Result.Ok (StorableValue.map_get_u256 (positions_map sim) key)
    | Some (make_state env state_base memory
              (proj_sim_directly_addressable sim)) ?}}.
  Proof.
    apply (Storage.run_sload_map_u256
             (proj_sim_directly_addressable sim) 1
             (positions_map sim) key).
    reflexivity.
  Qed.

  (** ----- Equivalence-theorem scaffolds -----

      The [fun_isRegistered_155] view function reads
      [_positions[bytes32(token)]] from slot 1 of the AddressSet, then
      returns [iszero(eq(value, 0))] — i.e., 1 if the token is
      registered, 0 otherwise.

      The full equivalence proof would walk:
        - isRegistered_155 → convert_AddressSet_to_ptr (identity)
        - calls fun_contains_778(set_slot, token)
        - which converts token: address → uint160 → uint256 → bytes32
        - calls fun_contains_386(positions_slot, bytes32_token)
        - which does add(setBase, 1) = 1, mapping_index_access bytes32 1
        - sloads at keccak256(bytes32_token, 1)
        - returns iszero(eq(value, 0))

      Connecting to the sim's [isRegistered] requires the lemma:
        positions_map[bytes32(token)] ≠ 0  ↔  list_contains rewardTokens token
      which follows from positions_map_aux's construction (entries
      only for tokens in the list, with positive values [S i]).

      The substrate above (conversion leaves, mapping_index_access,
      sload lemma, Pure_add_keccak_offset) sets up the proof; the body
      is the mechanical composition. Estimated 80-120 lines once
      attempted. Tracked as task #215 for the next session. *)

  Theorem run_fun__contains_386_at_proj_sim_scaffold
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t) (bytes32_value : U256.t)
      (memory : SimulatedMemory.t)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory
                   (proj_sim_directly_addressable sim) in
    let positions_value := StorableValue.map_get_u256
                             (positions_map sim) bytes32_value in
    let expected := if positions_value =? 0 then 0 else 1 in
    exists state',
    {{? codes, env, Some state |
      fun__contains_386 0 bytes32_value ⇓ Result.Ok expected
    | Some state' ?}}.
  Proof.
  Admitted.

End RewardTokenRegistryEquivalence.
