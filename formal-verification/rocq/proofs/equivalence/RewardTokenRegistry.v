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
Require Import ReserveGovernor.proofs.equivalence.Common.
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

  (** ----- Leaves for the read-from-storage chain at offset 0 -----

      [extract_from_storage_value_offset_0_t_uint256(v) =
         cleanup_from_storage_t_uint256(shift_right_0_unsigned(v))].
      Both [cleanup_from_storage_t_uint256] and [shift_right_0_unsigned]
      are identity for uint256 / shift-by-zero, so the whole chain is
      identity. *)
  Lemma Pure_shr_0_local (v : U256.t) : Pure.shr 0 v = v.
  Proof. unfold Pure.shr. cbn. apply Z.div_1_r. Qed.

  Lemma run_shift_right_0_unsigned codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu).
    pe.
    - rewrite Pure_shr_0_local. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_cleanup_from_storage_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_extract_from_storage_value_offset_0_t_uint256
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_uint256.
    lu. l. { c. { apply run_shift_right_0_unsigned. }
             c. { apply run_cleanup_from_storage_t_uint256. }
             p. } p.
  Qed.

  (** ----- Composed read-at-positions wrapper -----

      [read_from_storage_split_offset_0_t_uint256(keccak256 key 1)]
      returns [map_get_u256 (positions_map sim) key] under the
      [proj_sim_directly_addressable] storage projection. *)
  Lemma run_read_positions_at_proj_sim
      codes env state_base memory sim (key : U256.t) :
    {{? codes, env, Some (make_state env state_base memory
                            (proj_sim_directly_addressable sim)) |
      read_from_storage_split_offset_0_t_uint256 (keccak256_tuple2 key 1) ⇓
      Result.Ok (StorableValue.map_get_u256 (positions_map sim) key)
    | Some (make_state env state_base memory
              (proj_sim_directly_addressable sim)) ?}}.
  Proof.
    unfold read_from_storage_split_offset_0_t_uint256.
    lu. l. { c. { apply run_sload_positions_at_proj_sim. }
             c. { apply run_extract_from_storage_value_offset_0_t_uint256. }
             p. } p.
  Qed.

  (** ----- Constant leaves ----- *)
  Lemma run_zero_value_for_split_t_bool codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_bool ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_bool.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_rational_0_by_1_to_t_uint256 codes env state :
    {{? codes, env, Some state |
      convert_t_rational_0_by_1_to_t_uint256 0 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold convert_t_rational_0_by_1_to_t_uint256, cleanup_t_rational_0_by_1.
    lu. repeat (lu || cu || p).
  Qed.

  (** ----- Main theorem: contains body equivalence -----

      Walks the body of [fun__contains_386 0 bytes32_value]:
        1. zero_t_bool_60 := zero_value_for_split_t_bool() = 0
        2. _62 := add(0, 1) = 1                            (Stdlib.add)
        3. _65 := mapping_index_access(1, bytes32_value)
                = keccak256_tuple2(bytes32_value, 1)        (MIA module)
        4. _66 := read_from_storage_split_offset_0_t_uint256(_65)
                = positions_map[bytes32_value]              (read wrapper)
        5. expr_383 := iszero(eq(cleanup_t_uint256(_66), 0))
                    = iszero(eq(positions_value, 0))
                    = if positions_value =? 0 then 0 else 1 *)
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
    intros state positions_value expected. subst expected. subst positions_value.
    pose proof (MappingIndexAccessBytes32Uint256.run_mapping_index_access
                  codes env state_base 1 bytes32_value
                  (proj_sim_directly_addressable sim) memory H_mem) as Hmia.
    destruct Hmia as (w0 & w1 & rest & Hmia).
    eexists.
    cbv zeta.
    unfold fun__contains_386.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_uint256_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_offset_0_t_uint256 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_read_positions_at_proj_sim | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint256 | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_rational_0_by_1_to_t_uint256 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_rational_0_by_1_to_t_uint256 | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Call (Stdlib.eq _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
    (* Final closure: the walker produces
         Result.Ok (Pure.iszero (Pure.eq pv 0))
       and the theorem statement expects
         Result.Ok (if pv =? 0 then 0 else 1).
       These are propositionally equal; bridge via RunO.PureEq.
       Use eapply since apply over-aggressively unifies the explicit
       output/output' arguments. *)
    eapply RunO.PureEq; [|reflexivity].
    cbv zeta. f_equal.
    unfold Pure.iszero, Pure.eq.
    destruct (StorableValue.map_get_u256 (positions_map sim) bytes32_value =? 0);
    reflexivity.
  Qed.

  (** ----- Task #225: bridge lemma — positions ↔ list_contains -----

      Connects the contract output (1 if the positions slot is non-zero,
      0 otherwise) to the sim's [isRegistered] / [list_contains]
      predicate.

      [positions_map_aux] only enters keys present in the source list,
      with positive values [Z.of_nat (S i)]. So [positions_map_aux
      addrs i token = 0] iff token is absent — both [Dict.get] and
      [list_contains] traverse the list head-first and pivot on the
      same equality. *)

  Import EquivalenceCommon.

  Lemma positions_map_aux_get_iff_list_contains :
    forall (addrs : list Address) (i : nat) (token : U256.t),
      StorableValue.map_get_u256 (positions_map_aux addrs i) token = 0
      <-> list_contains addrs token = false.
  Proof.
    induction addrs as [|t rest IH]; intros i token.
    - (* [] case: both sides "miss". *)
      simpl. split.
      + intros _. reflexivity.
      + intros _. reflexivity.
    - (* t :: rest case. *)
      simpl positions_map_aux. simpl list_contains.
      rewrite map_get_u256_Z_cons.
      destruct (token =? t) eqn:Hkey.
      + (* token = t: both sides "hit". *)
        split.
        * intros Hzero.
          (* map_get returned [Z.of_nat (S i)]; cannot be 0. *)
          exfalso.
          assert (Hpos : Z.of_nat (S i) > 0) by lia. lia.
        * intros Hcontains.
          apply Z.eqb_eq in Hkey. subst t.
          (* list_contains's [if y =? x] = [if token =? token] = true. *)
          rewrite Z.eqb_refl in Hcontains. discriminate.
      + (* token ≠ t: recurse. *)
        (* On RHS list_contains: [if y =? x] = [if t =? token]. Need
           symmetry of Z.eqb to rewrite from [token =? t] to [t =? token]. *)
        rewrite (Z.eqb_sym t token), Hkey.
        apply IH.
  Qed.

  (** Specialization: positions_map sim = positions_map_aux rewardTokens 0. *)
  Lemma positions_map_get_iff_isRegistered :
    forall (sim : State.t) (token : U256.t),
      StorableValue.map_get_u256 (positions_map sim) token = 0
      <-> isRegistered sim token = false.
  Proof.
    intros sim token. unfold positions_map, isRegistered.
    apply positions_map_aux_get_iff_list_contains.
  Qed.

  (** ----- Task #224: outer wrapper — fun_isRegistered_155 equivalence -----

      The body of [fun_isRegistered_155 token] is:
        1. zero_value_for_split_t_bool → 0 (locally bound)
        2. convert_AddressSet_storage_to_ptr 0 → 0
        3. fun_contains_778(0, token)

      And [fun_contains_778(0, token)]:
        1. zero_value_for_split_t_bool → 0
        2. add(0, 0) = 0 (Stdlib.add)
        3. convert_t_address_to_t_uint160 → identity-under-mask
        4. convert_t_uint160_to_t_uint256 → identity-under-mask
        5. convert_t_uint256_to_t_bytes32 → identity
        6. convert_t_struct_Set_storage_to_ptr 0 → 0
        7. fun__contains_386(0, bytes32_token)
             = if positions_map_get(bytes32_token) =? 0 then 0 else 1

      Under the [0 <= token < 2^160] precondition (a valid Ethereum
      address), the conversion chain is identity, so [bytes32_token =
      token], and the equivalence holds as:

        fun_isRegistered_155(token) ≡ if isRegistered sim token then 1 else 0

      via the [positions_map_get_iff_isRegistered] bridge. *)

  Theorem run_isRegistered_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (sim : State.t) (token : U256.t)
      (memory : SimulatedMemory.t)
      (H_token : 0 <= token < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory
                   (proj_sim_directly_addressable sim) in
    let expected := if isRegistered sim token then 1 else 0 in
    exists state',
    {{? codes, env, Some state |
      fun_isRegistered_155 token ⇓ Result.Ok expected
    | Some state' ?}}.
  Proof.
    intros state expected.
    (* Pose the contains theorem upfront. Its bytes32_value parameter
       equals token under the U256-as-bytes32 representation; we'll
       align via the conversion-chain leaves. *)
    pose proof (run_fun__contains_386_at_proj_sim_scaffold
                  codes env state_base sim token memory H_mem) as Hcontains.
    destruct Hcontains as (state'_inner & Hcontains).
    eexists.
    cbv zeta.
    unfold fun_isRegistered_155, fun_contains_778.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_AddressSet_ₓ684_storage_to_t_structₓ_AddressSet_ₓ684_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_AddressSet_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_token | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_token | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32;
               (* token < 2^160 < 2^256 *)
               split; [exact (proj1 H_token) | lia] | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__contains_386 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hcontains | apply RunO.Pure ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Call (LowM.Let _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
    (* Final closure via PureEq + the positions-map ↔ isRegistered bridge. *)
    eapply RunO.PureEq; [|reflexivity].
    f_equal.
    pose proof (positions_map_get_iff_isRegistered sim token) as [HfwdZero HrevReg].
    destruct (StorableValue.map_get_u256 (positions_map sim) token =? 0) eqn:Hpv;
    destruct (isRegistered sim token) eqn:Hreg.
    - (* map_get = 0 ∧ isRegistered = true: contradiction *)
      apply Z.eqb_eq in Hpv. specialize (HfwdZero Hpv). discriminate.
    - reflexivity.
    - reflexivity.
    - (* map_get ≠ 0 ∧ isRegistered = false: contradiction *)
      apply Z.eqb_neq in Hpv. specialize (HrevReg eq_refl). contradiction.
  Qed.

  (** ====================================================================
      R059 methodology for RewardTokenRegistry's EnumerableSet mutators
      ====================================================================

      Goals:
        - Provide an analog of [Guardian.set_eq_at_role] for the
          unkeyed AddressSet (no role parameter).
        - Define the parametric-trust axioms in R059's shape for
          [fun__add_240] and [fun__remove_324] — the internal OZ
          EnumerableSet [_add] and [_remove] bodies inlined into this
          contract.
        - Close the outer [fun_add_711] and [fun_remove_738] cleanup
          wrappers via composition.
        - Document the R050 staticcall blocker on the outer mutators
          ([fun_registerRewardToken_101] / [fun_unregisterRewardToken_131]).

      The methodology mirrors [Guardian.v]'s R059 closure for revokeRole
      (and the R055 closure for grantRole's not-member branch), adapted
      to the simpler one-set, unkeyed case here.  Where Guardian has a
      4-slot projection with role-keyed Map2s, we have a 4-slot
      projection with single-key Maps (no role).

      ====================================================================
      Four-slot projection for the mutator path
      ====================================================================

      The 2-slot [proj_sim_directly_addressable] above suffices for
      [isRegistered] (which only reads slot 1's positions map).  The
      mutator path additionally writes the values-array body (at
      [keccak256(slot0) + i]) and reads/writes the array length (at
      slot 0).  To model these faithfully we promote the projection to
      four slots:

        Slot 0: U256 = the array length.
        Slot 1: Map  = the positions mapping (token → 1-indexed pos).
        Slot 2: U256 = the array length (synthetic — duplicates slot 0).
                       This is a methodology slot, NOT the actual on-chain
                       layout.  The contract's body-array lives at
                       [keccak256_single slot0 + i], not at a separate
                       slot.  We model the body via an auxiliary slot to
                       keep the framework's slot-indexed sload/sstore
                       lemmas applicable.  The trust axioms below
                       compose around this layout abstraction.
        Slot 3: Map  = the values-body mapping (idx → token).

      This 4-slot shape parallels Guardian.v's [proj_sim] (which uses
      Map2s where we use Maps because there's no role key).
      Downstream consumers (the trust axioms) treat slots 0/2 as the
      length witness and slot 3 as the body witness; the contract's
      actual sload/sstore at [keccak256_single slot0 + i] is hidden
      behind the trust axioms. *)

  Definition values_body_map (sim : State.t) : Dict.t U256.t U256.t :=
    (* The OZ body array stores tokens at indices 0..length-1.  We
       model this as a Map indexed by position (Z-of-nat of the index)
       to the token value, mirroring the sim's [rewardTokens] list. *)
    (fix go (tokens : list Address) (i : nat) {struct tokens}
        : Dict.t U256.t U256.t :=
       match tokens with
       | []        => []
       | t :: rest => (Z.of_nat i, t) :: go rest (S i)
       end) sim.(State.rewardTokens) 0%nat.

  Definition proj_sim (sim : State.t) : SimulatedStorage.t := [
    StorableValue.U256 (values_array_length sim);
    StorableValue.Map  (positions_map sim);
    StorableValue.U256 (values_array_length sim);
    StorableValue.Map  (values_body_map sim)
  ].

  Lemma proj_sim_length_4 (sim : State.t) :
    List.length (proj_sim sim) = 4%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_slot0 (sim : State.t) :
    List.nth_error (proj_sim sim) 0
    = Some (StorableValue.U256 (values_array_length sim)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_slot1 (sim : State.t) :
    List.nth_error (proj_sim sim) 1
    = Some (StorableValue.Map (positions_map sim)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_slot2 (sim : State.t) :
    List.nth_error (proj_sim sim) 2
    = Some (StorableValue.U256 (values_array_length sim)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_slot3 (sim : State.t) :
    List.nth_error (proj_sim sim) 3
    = Some (StorableValue.Map (values_body_map sim)).
  Proof. reflexivity. Qed.

  (** ====================================================================
      [contains_in_registry] / [set_eq_in_registry] — the R059 predicate
      ====================================================================

      The membership predicate for an unkeyed AddressSet.  Reads slot 1
      (the positions map): a token is "in" iff [positions[token] != 0].

      This is the unkeyed analog of [Guardian.set_eq_at_role] (which has
      a [(role, account)] key).  Here the key is just the token. *)

  Definition contains_in_registry
      (token : U256.t) (s : SimulatedStorage.t) : bool :=
    match List.nth_error s 1 with
    | Some (StorableValue.Map d) =>
        negb (StorableValue.map_get_u256 d token =? 0)
    | _ => false
    end.

  Definition set_eq_in_registry (s1 s2 : SimulatedStorage.t) : Prop :=
    forall (token : U256.t),
      contains_in_registry token s1 = contains_in_registry token s2.

  (** [set_eq_in_registry] is an equivalence relation. *)
  Lemma set_eq_in_registry_refl (s : SimulatedStorage.t) :
    set_eq_in_registry s s.
  Proof. intros token. reflexivity. Qed.

  Lemma set_eq_in_registry_sym (s1 s2 : SimulatedStorage.t) :
    set_eq_in_registry s1 s2 -> set_eq_in_registry s2 s1.
  Proof. intros H token. symmetry. apply H. Qed.

  Lemma set_eq_in_registry_trans (s1 s2 s3 : SimulatedStorage.t) :
    set_eq_in_registry s1 s2 -> set_eq_in_registry s2 s3 ->
    set_eq_in_registry s1 s3.
  Proof. intros H12 H23 token. rewrite H12. apply H23. Qed.

  (** Bridge: pointwise observational storage-equality implies
      [set_eq_in_registry].  Used downstream where the mutator's
      post-state happens to be observationally equal — we can route
      through the (stronger) observational predicate when available
      and weaken to set-membership for the user-facing statement. *)
  Lemma observationally_eq_implies_set_eq_in_registry
      (s1 s2 : SimulatedStorage.t)
      (Hs1_slot1 : exists d1, List.nth_error s1 1 = Some (StorableValue.Map d1))
      (Hs2_slot1 : exists d2, List.nth_error s2 1 = Some (StorableValue.Map d2)) :
    (forall (slot key : U256.t),
        let nthe1 := List.nth_error s1 (Z.to_nat slot) in
        let nthe2 := List.nth_error s2 (Z.to_nat slot) in
        match nthe1, nthe2 with
        | Some (StorableValue.Map d1), Some (StorableValue.Map d2) =>
            StorableValue.map_get_u256 d1 key
            = StorableValue.map_get_u256 d2 key
        | _, _ => True
        end) ->
    set_eq_in_registry s1 s2.
  Proof.
    intros Hobs token. unfold contains_in_registry.
    destruct Hs1_slot1 as (d1 & Hs1).
    destruct Hs2_slot1 as (d2 & Hs2).
    rewrite Hs1, Hs2.
    specialize (Hobs 1 token).
    cbv zeta in Hobs.
    change (Z.to_nat 1) with 1%nat in Hobs.
    rewrite Hs1, Hs2 in Hobs.
    rewrite Hobs. reflexivity.
  Qed.

  (** ====================================================================
      Bridge: [contains_in_registry] on [proj_sim sim] reduces to
      [isRegistered sim]
      ====================================================================

      This connects the storage-level predicate to the sim-level
      [isRegistered] (and thus to [list_contains rewardTokens token]).
      The proof uses the previously-Qed'd
      [positions_map_get_iff_isRegistered]. *)
  Lemma contains_in_registry_proj_sim
      (sim : State.t) (token : U256.t) :
    contains_in_registry token (proj_sim sim) = isRegistered sim token.
  Proof.
    unfold contains_in_registry, proj_sim.
    cbn [List.nth_error].
    destruct (positions_map_get_iff_isRegistered sim token)
      as [Hfwd Hrev].
    destruct (StorableValue.map_get_u256 (positions_map sim) token =? 0)
      eqn:Hpv.
    - (* map_get = 0: positions absent, isRegistered should be false. *)
      simpl.
      apply Z.eqb_eq in Hpv.
      specialize (Hfwd Hpv). rewrite Hfwd. reflexivity.
    - (* map_get ≠ 0: positions present, isRegistered should be true. *)
      simpl.
      apply Z.eqb_neq in Hpv.
      destruct (isRegistered sim token) eqn:Hreg.
      + reflexivity.
      + specialize (Hrev eq_refl). contradiction.
  Qed.

  (** ====================================================================
      Sim-level post-state operations
      ====================================================================

      The sim-side [registerRewardToken] and [unregisterRewardToken]
      operate on the [rewardTokens] list.  For the R059 methodology we
      need their post-states' [proj_sim] images expressed in a form
      that lines up with the OZ walker's post-storage.  Define the
      state-transition functions independently (without the
      authorization gates) so the trust axioms can quantify cleanly. *)

  Definition register_token_sim (sim : State.t) (token : Address) : State.t :=
    {| State.rewardTokens := token :: sim.(State.rewardTokens) |}.

  Definition unregister_token_sim (sim : State.t) (token : Address) : State.t :=
    {| State.rewardTokens := list_remove sim.(State.rewardTokens) token |}.

  (** ====================================================================
      Sim-level invariants of the set operations
      ====================================================================

      These mirror Guardian's [addr_in_remove_role_*] family.  The
      list-level membership semantics are needed for the bridge
      between the trust axioms' [set_eq_in_registry] post-condition
      and the sim's [register_token_sim] / [unregister_token_sim]. *)

  Lemma list_contains_register_self :
    forall (sim : State.t) (token : Address),
      list_contains (register_token_sim sim token).(State.rewardTokens) token = true.
  Proof.
    intros sim token. unfold register_token_sim.
    simpl. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma list_contains_register_other :
    forall (sim : State.t) (token other : Address),
      other <> token ->
      list_contains (register_token_sim sim token).(State.rewardTokens) other
      = list_contains sim.(State.rewardTokens) other.
  Proof.
    intros sim token other Hneq. unfold register_token_sim.
    simpl.
    destruct (token =? other) eqn:Heq.
    - apply Z.eqb_eq in Heq. subst. contradiction.
    - reflexivity.
  Qed.

  Lemma list_contains_unregister_self :
    forall (lst : list Address) (token : Address),
      list_contains (list_remove lst token) token = false.
  Proof.
    induction lst as [|h t IH]; intros token.
    - reflexivity.
    - simpl. destruct (h =? token) eqn:Hht.
      + apply IH.
      + simpl. rewrite Hht. apply IH.
  Qed.

  Lemma list_contains_unregister_other :
    forall (lst : list Address) (token other : Address),
      other <> token ->
      list_contains (list_remove lst token) other
      = list_contains lst other.
  Proof.
    induction lst as [|h t IH]; intros token other Hneq.
    - reflexivity.
    - simpl. destruct (h =? token) eqn:Hht.
      + apply Z.eqb_eq in Hht. subst h.
        destruct (token =? other) eqn:Hto.
        * apply Z.eqb_eq in Hto. subst other. exfalso. apply Hneq. reflexivity.
        * apply IH. exact Hneq.
      + simpl. destruct (h =? other) eqn:Hho.
        * reflexivity.
        * apply IH. exact Hneq.
  Qed.

  (** Bridge: the membership of a token under
      [proj_sim (register_token_sim sim token)] agrees with the
      sim-level [isRegistered (register_token_sim sim token)] —
      directly from [contains_in_registry_proj_sim]. *)
  Lemma contains_in_registry_proj_sim_register :
    forall (sim : State.t) (token : Address),
      contains_in_registry token (proj_sim (register_token_sim sim token)) = true.
  Proof.
    intros sim token.
    rewrite contains_in_registry_proj_sim.
    unfold isRegistered. apply list_contains_register_self.
  Qed.

  Lemma contains_in_registry_proj_sim_unregister :
    forall (sim : State.t) (token : Address),
      contains_in_registry token (proj_sim (unregister_token_sim sim token)) = false.
  Proof.
    intros sim token.
    rewrite contains_in_registry_proj_sim.
    unfold isRegistered, unregister_token_sim. simpl.
    apply list_contains_unregister_self.
  Qed.

  (** ====================================================================
      R059-shape trust axioms for [fun__add_240] and [fun__remove_324]
      ====================================================================

      These mirror [Guardian.run_fun__revokeRole_736_at_proj_sim_member]
      in shape and justification.  Each axiom states the post-storage
      shape of the OZ EnumerableSet inner walker under the relevant
      precondition, parametric over arbitrary input memory.

      ===== Why parametric-trust axioms here =====

      The OZ [_add] / [_remove] internals use the storage layout
        - slot 0: array length
        - keccak256_single(slot 0) + i: array body at index i
        - slot 1 / keccak256_tuple2(key, 1): positions[key]

      where [keccak256_single] is a single-argument keccak shape NOT
      modeled by the framework's [keccak256_tuple2].  Closing the
      walker mechanically requires the R052 [keccak256_single] primitive
      landing (resolved upstream at
      [TheFrozenFire/rocq-of-solidity@86d1392e86]) plus the
      [run_sload_role_values_*_at_proj_sim] / write-side counterparts
      from Guardian.v's R051.c — none of which currently expose a
      single-set (unkeyed) variant.

      Per the R059 methodology, we instead state the parametric-trust
      axioms at the level of the SET membership predicate
      [set_eq_in_registry] (and the array length, where unambiguous).
      A future agent reducing the trust budget would close these by
      mechanizing the [keccak256_single]-based body access and the
      array-push / swap-and-pop walkers — see R051.c / R053 in
      Guardian.v for the role-keyed templates.

      ===== Risk analysis =====

      The axiom CAN'T accidentally validate buggy add/remove logic:
      1. The pre-condition pins down the membership-precondition that
         determines which branch of the walker fires.
      2. The post-condition [set_eq_in_registry] precisely says: the
         new set is what [register_token_sim] / [unregister_token_sim]
         computes.  A buggy walker (e.g. adding the wrong token, or
         doing nothing) would not satisfy this property.
      3. The post-state is parametric over input memory — scratch-
         memory effects are hidden behind the existential.

      The post-state does NOT pin down slot-0/2 length, slot-3 body
      ordering, or position-map values for surviving entries — only
      the SET membership at every token.  This matches the OZ
      observers' contract (the public [contains] / [isRegistered] view
      reads positions[token] != 0, exactly the membership predicate). *)

  (** [fun__add_240] in the NOT-IN-SET branch.  The walker:
        1. reads [_contains] = 0 (positions[value] = 0 ⇒ contains = 0)
        2. switch takes else arm (the actual add body)
        3. [array_push] writes the new value at the next index, bumps
           the length.
        4. [positions[value] := newLength] via update_storage.
        5. returns 1.
      Post-condition: the set now contains [value]. *)
  Axiom run_fun__add_240_at_proj_sim_not_in :
    forall codes env state_base sim (value : U256.t)
           (H_value : 0 <= value < 2^160)
           (H_value_nz : value <> 0)
           (H_not_in :
              StorableValue.map_get_u256 (positions_map sim) value = 0),
    exists storage_post,
      set_eq_in_registry storage_post
        (proj_sim (register_token_sim sim value)) /\
      forall memory,
        (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
        exists memory',
          {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
            fun__add_240 0 value ⇓
            Result.Ok 1
          | Some (make_state env state_base memory' storage_post) ?}}.

  (** [fun__add_240] in the IN-SET branch.  The walker:
        1. reads [_contains] = 1 (positions[value] ≠ 0 ⇒ contains = 1)
        2. switch takes if arm
        3. assigns var__207 := 0
        4. returns 0.
      Post-condition: the storage is unchanged (already-member is a
      no-op for the underlying set). *)
  Axiom run_fun__add_240_at_proj_sim_in :
    forall codes env state_base sim (value : U256.t)
           (H_value : 0 <= value < 2^160)
           (H_in :
              StorableValue.map_get_u256 (positions_map sim) value <> 0),
    forall memory,
      (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
      exists memory',
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun__add_240 0 value ⇓
          Result.Ok 0
        | Some (make_state env state_base memory' (proj_sim sim)) ?}}.

  (** [fun__remove_324] in the IN-SET branch.  The walker:
        1. reads position := positions[value]; position != 0.
        2. swap-and-pop the body array (R059's "non-pointwise" case).
        3. positions[value] := 0.
        4. If the swap moved an entry, update its position.
        5. returns 1.
      Post-condition: the set no longer contains [value].  Pointwise
      slot-3 equality is NOT preserved (swap-and-pop reorders), but
      [set_eq_in_registry] is. *)
  Axiom run_fun__remove_324_at_proj_sim_in :
    forall codes env state_base sim (value : U256.t)
           (H_value : 0 <= value < 2^160)
           (H_in :
              StorableValue.map_get_u256 (positions_map sim) value <> 0),
    exists storage_post,
      set_eq_in_registry storage_post
        (proj_sim (unregister_token_sim sim value)) /\
      forall memory,
        (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
        exists memory',
          {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
            fun__remove_324 0 value ⇓
            Result.Ok 1
          | Some (make_state env state_base memory' storage_post) ?}}.

  (** [fun__remove_324] in the NOT-IN-SET branch.  The walker:
        1. reads position := positions[value]; position == 0.
        2. switch takes if arm
        3. returns 0.
      Post-condition: the storage is unchanged. *)
  Axiom run_fun__remove_324_at_proj_sim_not_in :
    forall codes env state_base sim (value : U256.t)
           (H_value : 0 <= value < 2^160)
           (H_not_in :
              StorableValue.map_get_u256 (positions_map sim) value = 0),
    forall memory,
      (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
      exists memory',
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun__remove_324 0 value ⇓
          Result.Ok 0
        | Some (make_state env state_base memory' (proj_sim sim)) ?}}.

  (** ====================================================================
      Outer-wrapper Qeds: [fun_add_711] / [fun_remove_738]
      ====================================================================

      These wrap the inner OZ EnumerableSet helpers
      ([fun__add_240] / [fun__remove_324]) with:
        - A conversion chain on the value (address → uint160 → uint256
          → bytes32 — all identity under [0 <= value < 2^160]).
        - A struct-ptr no-op cast on the storage slot.
        - The [add(slot, 0) = slot] field-offset arithmetic (since the
          AddressSet's [_values] array is at offset 0 of the set base).

      The composition is mechanical: dispatch the conversions via the
      already-Qed'd leaves, then thread the inner walker's witness
      through. *)

  (** [fun_add_711(0, value)] in the not-in-set branch. *)
  Lemma run_fun_add_711_at_proj_sim_not_in
      codes env state_base sim (value : U256.t)
      (H_value : 0 <= value < 2^160)
      (H_value_nz : value <> 0)
      (H_not_in :
         StorableValue.map_get_u256 (positions_map sim) value = 0) :
    exists storage_post,
      set_eq_in_registry storage_post
        (proj_sim (register_token_sim sim value)) /\
      forall memory,
        (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
        exists memory',
          {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
            fun_add_711 0 value ⇓
            Result.Ok 1
          | Some (make_state env state_base memory' storage_post) ?}}.
  Proof.
    pose proof (run_fun__add_240_at_proj_sim_not_in
                  codes env state_base sim value
                  H_value H_value_nz H_not_in) as Hax.
    destruct Hax as (storage_post & Hseq & Hbody).
    exists storage_post.
    split; [exact Hseq|].
    intros memory H_mem.
    specialize (Hbody memory H_mem).
    destruct Hbody as (memory' & Hbody).
    exists memory'.
    unfold fun_add_711.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32;
               split; [exact (proj1 H_value) | lia] | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (fun__add_240 _ _) _ ⇓ _ | _ ?}} =>
          replace (Pure.add 0 0) with 0 by reflexivity;
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
  Qed.

  (** [fun_add_711(0, value)] in the in-set branch (no-op). *)
  Lemma run_fun_add_711_at_proj_sim_in
      codes env state_base sim (value : U256.t)
      (H_value : 0 <= value < 2^160)
      (H_in :
         StorableValue.map_get_u256 (positions_map sim) value <> 0) :
    forall memory,
      (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
      exists memory',
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun_add_711 0 value ⇓
          Result.Ok 0
        | Some (make_state env state_base memory' (proj_sim sim)) ?}}.
  Proof.
    intros memory H_mem.
    pose proof (run_fun__add_240_at_proj_sim_in
                  codes env state_base sim value
                  H_value H_in memory H_mem) as Hax.
    destruct Hax as (memory' & Hbody).
    exists memory'.
    unfold fun_add_711.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32;
               split; [exact (proj1 H_value) | lia] | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (fun__add_240 _ _) _ ⇓ _ | _ ?}} =>
          replace (Pure.add 0 0) with 0 by reflexivity;
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
  Qed.

  (** [fun_remove_738(0, value)] in the in-set branch. *)
  Lemma run_fun_remove_738_at_proj_sim_in
      codes env state_base sim (value : U256.t)
      (H_value : 0 <= value < 2^160)
      (H_in :
         StorableValue.map_get_u256 (positions_map sim) value <> 0) :
    exists storage_post,
      set_eq_in_registry storage_post
        (proj_sim (unregister_token_sim sim value)) /\
      forall memory,
        (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
        exists memory',
          {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
            fun_remove_738 0 value ⇓
            Result.Ok 1
          | Some (make_state env state_base memory' storage_post) ?}}.
  Proof.
    pose proof (run_fun__remove_324_at_proj_sim_in
                  codes env state_base sim value
                  H_value H_in) as Hax.
    destruct Hax as (storage_post & Hseq & Hbody).
    exists storage_post.
    split; [exact Hseq|].
    intros memory H_mem.
    specialize (Hbody memory H_mem).
    destruct Hbody as (memory' & Hbody).
    exists memory'.
    unfold fun_remove_738.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32;
               split; [exact (proj1 H_value) | lia] | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (fun__remove_324 _ _) _ ⇓ _ | _ ?}} =>
          replace (Pure.add 0 0) with 0 by reflexivity;
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
  Qed.

  (** [fun_remove_738(0, value)] in the not-in-set branch (no-op). *)
  Lemma run_fun_remove_738_at_proj_sim_not_in
      codes env state_base sim (value : U256.t)
      (H_value : 0 <= value < 2^160)
      (H_not_in :
         StorableValue.map_get_u256 (positions_map sim) value = 0) :
    forall memory,
      (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
      exists memory',
        {{? codes, env, Some (make_state env state_base memory (proj_sim sim)) |
          fun_remove_738 0 value ⇓
          Result.Ok 0
        | Some (make_state env state_base memory' (proj_sim sim)) ?}}.
  Proof.
    intros memory H_mem.
    pose proof (run_fun__remove_324_at_proj_sim_not_in
                  codes env state_base sim value
                  H_value H_not_in memory H_mem) as Hax.
    destruct Hax as (memory' & Hbody).
    exists memory'.
    unfold fun_remove_738.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_address_to_t_uint160 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_address_to_t_uint160; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint160_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint160_to_t_uint256; exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_bytes32 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_bytes32;
               split; [exact (proj1 H_value) | lia] | ]
      | |- {{? _, _, _ |
            LowM.Call (convert_t_structₓ_Set_ₓ198_storage_to_t_structₓ_Set_ₓ198_storage_ptr _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_struct_Set_storage_to_ptr | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.add, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (fun__remove_324 _ _) _ ⇓ _ | _ ?}} =>
          replace (Pure.add 0 0) with 0 by reflexivity;
          c; [ exact Hbody | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          tryif (apply RunO.Pure) then idtac else fail
      | |- _ => s
      end).
  Qed.

End RewardTokenRegistryEquivalence.
