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

End RewardTokenRegistryEquivalence.
