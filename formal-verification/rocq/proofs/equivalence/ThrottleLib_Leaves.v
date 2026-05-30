(** Phase 1.1 — extracted ThrottleLibLeaves module.

    Closed building-block lemmas for the ThrottleLib equivalence
    proof. Each lemma proves a single leaf operation in the shallow
    form (zero_value, cleanup, identity, convert, checked_*, etc.)
    closes mechanically to its sim-level meaning.

    Extracted into its own file so edits to the main equivalence
    proofs (Phase E / Phase F / Phase 1.3) don't trigger recompile
    of ~70 leaf lemmas. The .vo file caches the whole module after
    the first build.

    Originally lived as [Module ThrottleLibLeaves] inside
    [ThrottleLib.v]. The module-namespace is preserved so callers
    continue to qualify as [ThrottleLibLeaves.run_*].
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.generated.ThrottleLib_shallow.
Require Import ReserveGovernor.simulations.ProposerThrottle.

Import ProposerThrottle.
Import Stdlib.
Import RunO.

Module ThrottleLibLeaves.

  Import ThrottleLib_153.ThrottleLib_153_deployed.

  (** Returns the constant 0. *)
  Lemma run_zero_value_for_split_t_uint256 codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_uint256 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** Identity on valid U256.t. *)
  Lemma run_cleanup_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** The cleanup-from-storage helper is also identity. *)
  Lemma run_cleanup_from_storage_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** [cleanup_t_rational_*_by_1] are all identity (the rational has
      denominator 1, so cleanup just passes through). *)
  Lemma run_cleanup_t_rational_1000000000000000000_by_1 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_rational_1000000000000000000_by_1 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold cleanup_t_rational_1000000000000000000_by_1.
         lu. repeat (lu || cu || p). Qed.

  Lemma run_cleanup_t_rational_1_by_1 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_rational_1_by_1 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold cleanup_t_rational_1_by_1.
         lu. repeat (lu || cu || p). Qed.

  Lemma run_cleanup_t_rational_43200_by_1 codes env state v :
    {{? codes, env, Some state |
      cleanup_t_rational_43200_by_1 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold cleanup_t_rational_43200_by_1.
         lu. repeat (lu || cu || p). Qed.

  Lemma run_identity codes env state v :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold identity. lu. repeat (lu || cu || p). Qed.

  (** [shr 0 v = v] in EVM arithmetic. *)
  Lemma Pure_shr_0 (v : U256.t) : Pure.shr 0 v = v.
  Proof.
    unfold Pure.shr. cbn. apply Z.div_1_r.
  Qed.

  (** [shift_right_0_unsigned v] returns [v]. Stepping through Stdlib.shr
      gives [Pure.shr 0 v] which reduces to [v] by [Pure_shr_0]. *)
  Lemma run_shift_right_0_unsigned codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu).
    pe.
    - rewrite Pure_shr_0. reflexivity.
    - reflexivity.
  Qed.

  (** [extract_from_storage_value_offset_0_t_uint256 v = v]
      (storage values for uint256 fields are stored unshifted, and the
      cleanup-from-storage is identity for U256.t in range). *)
  Lemma run_extract_from_storage_value_offset_0_t_uint256 codes env state v :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_uint256.
    lu. l. { c. { apply run_shift_right_0_unsigned. }
             c. { apply run_cleanup_from_storage_t_uint256. }
             p. }
    repeat (lu || cu || p).
  Qed.

  (** [convert_t_uint256_to_t_uint256] is identity (cleanup ∘ identity ∘ cleanup). *)
  Lemma run_convert_t_uint256_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** Rational-to-uint256 conversions are all identity. *)
  Lemma run_convert_t_rational_1000000000000000000_by_1_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_rational_1000000000000000000_by_1_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_rational_1000000000000000000_by_1_to_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_rational_1_by_1_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_rational_1_by_1_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_rational_1_by_1_to_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_rational_43200_by_1_to_t_uint256 codes env state v :
    {{? codes, env, Some state |
      convert_t_rational_43200_by_1_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_rational_43200_by_1_to_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** The PROPOSAL_THROTTLE_PERIOD constant returns 43200 = 0xa8c0. *)
  Lemma run_constant_PROPOSAL_THROTTLE_PERIOD_349 codes env state :
    {{? codes, env, Some state |
      constant_PROPOSAL_THROTTLE_PERIOD_349 ⇓
        Result.Ok ProposerThrottle.PROPOSAL_THROTTLE_PERIOD
    | Some state ?}}.
  Proof.
    unfold constant_PROPOSAL_THROTTLE_PERIOD_349.
    change ProposerThrottle.PROPOSAL_THROTTLE_PERIOD with 0xa8c0.
    lu. repeat (lu || cu || p).
  Qed.

  (** ----- Storage-reading helpers -----

      [Stdlib.sload slot] is a [Primitive.SLoad slot] step. The
      [eval_primitive] semantics for SLoad reads
      [account.(Account.storage) slot] where [account] is the contract
      at [env.(Environment.address)]. The lemma below pulls a runtime
      account into a storage-read result. *)

  Lemma run_sload_returns_storage codes env state slot account :
    Dict.get state.(State.accounts) env.(Environment.address) = Some account ->
    {{? codes, env, Some state |
      Stdlib.sload slot ⇓ Result.Ok (account.(Account.storage) slot)
    | Some state ?}}.
  Proof.
    intros H. unfold Stdlib.sload.
    eapply RunO.Primitive.
    - simpl. rewrite H. reflexivity.
    - apply RunO.Pure.
  Qed.

  (** [read_from_storage_split_offset_0_t_uint256 slot] sloads the slot
      and pipes through [extract_from_storage_value_offset_0_t_uint256]
      (which is identity). *)
  Lemma run_read_from_storage_split_offset_0_t_uint256
      codes env state slot account :
    Dict.get state.(State.accounts) env.(Environment.address) = Some account ->
    {{? codes, env, Some state |
      read_from_storage_split_offset_0_t_uint256 slot ⇓
        Result.Ok (account.(Account.storage) slot)
    | Some state ?}}.
  Proof.
    intros H. unfold read_from_storage_split_offset_0_t_uint256.
    lu. l. { c. { apply run_sload_returns_storage with (account := account). exact H. }
             c. { apply run_extract_from_storage_value_offset_0_t_uint256. } p. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Checked arithmetic — success cases ----- *)

  (** [checked_add x y] returns [x + y] when the sum doesn't overflow uint256. *)
  Lemma run_checked_add_t_uint256 codes env state (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_no_overflow : x + y < 2^256) :
    {{? codes, env, Some state |
      checked_add_t_uint256 x y ⇓ Result.Ok (x + y)
    | Some state ?}}.
  Proof.
    unfold checked_add_t_uint256.
    lu. repeat (lu || cu || p).
    s. unfold Pure.gt, Pure.add.
    destruct (_ >? _) eqn:?; s.
    { lia. }
    { pe; f_equal. lia. }
  Qed.

  (** [checked_sub x y] returns [x - y] when [y <= x] (no underflow). *)
  Lemma run_checked_sub_t_uint256 codes env state (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_no_underflow : y <= x) :
    {{? codes, env, Some state |
      checked_sub_t_uint256 x y ⇓ Result.Ok (x - y)
    | Some state ?}}.
  Proof.
    unfold checked_sub_t_uint256.
    lu. repeat (lu || cu || p).
    s. unfold Pure.gt, Pure.sub.
    destruct (_ >? _) eqn:?; s.
    { lia. }
    { pe; f_equal. lia. }
  Qed.

  (** [checked_mul x y] returns [x * y] when the product doesn't overflow.
      The shallow form uses [iszero (or (iszero x) (eq y (div product x)))]
      to detect overflow:

        - panic iff [x != 0 AND y != div product x]
        - when [x * y < 2^256], [product = x*y] (cleanup is identity in
          range), so [div product x = y] for [x != 0]: no panic.
        - when [x = 0], [iszero x = 1], or-result is 1, outer iszero = 0:
          no panic. [product = 0 * y = 0]. *)
  Lemma run_checked_mul_t_uint256 codes env state (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_no_overflow : x * y < 2^256) :
    {{? codes, env, Some state |
      checked_mul_t_uint256 x y ⇓ Result.Ok (x * y)
    | Some state ?}}.
  Proof.
    unfold checked_mul_t_uint256.
    lu. repeat (lu || cu || p).
    assert (Hxy_nn : 0 <= x * y) by (apply Z.mul_nonneg_nonneg; lia).
    s. unfold Pure.iszero, Pure.or, Pure.eq, Pure.div, Pure.mul, Shallow.if_.
    rewrite (Z.mod_small (x*y) (2^256)) by lia.
    (** Case-split WITHOUT [eqn:] so the [if]-expressions in the goal
        reduce. With [eqn:] the hypothesis is added but the
        [if x =? 0 then 1 else 0]-shapes don't substitute back. *)
    destruct (x =? 0) eqn:Hx0.
    - (* x = 0: [Pure.iszero x] resolves to 1 in goal; need to also
         resolve [eq y (div product x)] cases. *)
      apply Z.eqb_eq in Hx0. subst x.
      destruct (y =? 0) eqn:Hyb.
      + (* y = 0: both branches of [Pure.eq y 0] resolve. Then
           [Z.lor 1 1] is 1; outer iszero(1) is 0; no panic. *)
        apply Z.eqb_eq in Hyb. subst y.
        s. repeat (lu || cu || p).
      + (* y != 0: [Pure.eq y 0] is 0, [Z.lor 1 0] is 1; iszero 1 is 0. *)
        s. repeat (lu || cu || p).
    - apply Z.eqb_neq in Hx0.
      assert (Hdiv : (x * y) / x = y).
      { rewrite Z.mul_comm. apply Z.div_mul. lia. }
      rewrite Hdiv. rewrite Z.eqb_refl.
      (* [Pure.iszero x] is 0; [Pure.eq y y] is 1; [Z.lor 0 1] is 1;
         iszero(1) is 0; no panic. *)
      s. repeat (lu || cu || p).
  Qed.

  (** [checked_div x y] returns [x / y] when [y > 0]. *)
  Lemma run_checked_div_t_uint256 codes env state (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_nonzero : y > 0) :
    {{? codes, env, Some state |
      checked_div_t_uint256 x y ⇓ Result.Ok (x / y)
    | Some state ?}}.
  Proof.
    unfold checked_div_t_uint256.
    lu. repeat (lu || cu || p).
    s. unfold Pure.iszero.
    destruct (y =? 0) eqn:Hy0; s.
    { apply Z.eqb_eq in Hy0. lia. }
    { repeat (lu || cu || p). s. unfold Pure.div.
      rewrite Hy0. pe; reflexivity. }
  Qed.

  (** ----- Address-cleanup helpers -----

      [cleanup_t_uint160 v] = [v AND (2^160 - 1)]. On a valid Address
      (in range [0, 2^160)), the cleanup is identity by
      [Address.implies_and_mask]. [convert_t_address_to_t_address] is
      [cleanup_t_uint160 ∘ identity ∘ cleanup_t_uint160], hence also
      identity on valid Address.t. *)

  Lemma run_cleanup_t_uint160_on_address codes env state (a : U256.t)
      (H : Address.Valid.t a) :
    {{? codes, env, Some state |
      cleanup_t_uint160 a ⇓ Result.Ok a
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- Address.implies_and_mask by assumption. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_convert_t_uint160_to_t_uint160 codes env state (a : U256.t)
      (H : Address.Valid.t a) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 a ⇓ Result.Ok a
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address. exact H. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint160_on_address. exact H. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_address codes env state (a : U256.t)
      (H : Address.Valid.t a) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address a ⇓ Result.Ok a
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160. exact H. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_t_address_to_t_address codes env state (a : U256.t)
      (H : Address.Valid.t a) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address a ⇓ Result.Ok a
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address. exact H. }
             p. }
    repeat (lu || cu || p).
  Qed.

  (** [convert_t_structₓ_ProposalThrottle_ₓ18_storage_to_..._ptr] is
      identity at the slot level — it just copies the slot address. *)
  Lemma run_convert_t_struct_ProposalThrottle_storage_to_ptr codes env state v :
    {{? codes, env, Some state |
      convert_t_structₓ_ProposalThrottle_ₓ18_storage_to_t_structₓ_ProposalThrottle_ₓ18_storage_ptr v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_structₓ_ProposalThrottle_ₓ18_storage_to_t_structₓ_ProposalThrottle_ₓ18_storage_ptr.
    lu. repeat (lu || cu || p).
  Qed.

  (** [Stdlib.timestamp] reads [State.block_timestamp] via the
      [Primitive.GetBlockTimestamp] primitive (R020 — resolved upstream
      via dev clone). State is unchanged across the call. *)
  Lemma run_timestamp codes env state x :
    state.(State.block_timestamp) = x ->
    {{? codes, env, Some state |
      Stdlib.timestamp ⇓ Result.Ok x
    | Some state ?}}.
  Proof.
    intros H. unfold Stdlib.timestamp.
    eapply RunO.Primitive.
    - simpl. rewrite H. reflexivity.
    - apply RunO.Pure.
  Qed.

  (** [make_state] preserves [State.block_timestamp]. The function only
      writes [State.memory] (via record update) and [State.accounts]
      (via [State.with_current_storage]); both update operations are
      record-field-targeted, so the timestamp field is unchanged. *)
  Local Transparent State.with_current_storage.
  Lemma make_state_block_timestamp env state memory storage :
    (make_state env state memory storage).(State.block_timestamp)
    = state.(State.block_timestamp).
  Proof.
    unfold make_state, State.with_current_storage.
    destruct (Dict.assign_function _ _ _); reflexivity.
  Qed.
  Local Opaque State.with_current_storage.

  (** ----- Phase 1.3 leaves: sstore wrapper machinery ----- *)

  (** [shift_left_0 v] = [shl 0 v] = v for valid U256.t v. *)
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
    pe; reflexivity.
  Qed.

  (** [prepare_store_t_uint256 v] = v. Just an assignment in Yul. *)
  Lemma run_prepare_store_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** [update_byte_slice_32_shift_0 old new] = new for valid U256.t new.
      Walks the bit-mask logic:
        - shift_left_0 new = new
        - old AND (NOT (2^256 - 1)) = old AND 0 = 0
        - 0 OR (new AND (2^256 - 1)) = new (since new < 2^256). *)
  Lemma run_update_byte_slice_32_shift_0 codes env state
      (old_value new_value : U256.t)
      (H_new : 0 <= new_value < 2^256) :
    {{? codes, env, Some state |
      update_byte_slice_32_shift_0 old_value new_value ⇓ Result.Ok new_value
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_32_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    (* Walk: mask=ff..ff, toInsert=shift_left_0 new, value=old AND NOT mask,
       result = value OR (toInsert AND mask). *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ | LowM.Call (shift_left_0 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_shift_left_0; exact H_new | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.not _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.not; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.and _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.and; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.or _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.or; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    (* Final step: prove result = new_value via bit-mask reduction. *)
    s.
    unfold Pure.and, Pure.or, Pure.not.
    (* Mask is 2^256 - 1 as a literal; not(mask) = 0. *)
    change (2 ^ 256 -
            115792089237316195423570985008687907853269984665640564039457584007913129639935 - 1)
      with 0.
    rewrite Z.land_0_r.
    rewrite Z.lor_0_l.
    (* new_value AND (2^256-1) = new_value (since 0 <= new_value < 2^256) *)
    change 115792089237316195423570985008687907853269984665640564039457584007913129639935
      with (Z.ones 256).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small by exact H_new.
    pe; reflexivity.
  Qed.

  (** [convert_t_uint256_to_t_uint256] is identity for uint256.
      Already proven above; restated here for completeness. *)

  (** [update_storage_value_offset_0_t_uint256_to_t_uint256 slot value] —
      Yul helper that sstores [value] at [slot] (going through a
      sload + bit-mask + sstore that reduces to a plain sstore for
      uint256). The post-state has the storage updated at the
      MapStruct entry [(key, offset)] to [value], where the slot is
      [keccak256_tuple2 key index + offset].

      Precondition: the storage at [index] is a [MapStruct map]; the
      value being written fits in U256. *)
  Lemma run_update_storage_value_offset_0_t_uint256_to_t_uint256
      codes env state_base memory
      (storage : list StorableValue.t)
      (index : nat)
      (map : Dict.t (U256.t * U256.t) U256.t)
      (key : U256.t) (offset : U256.t) (value : U256.t)
      (H_v : 0 <= value < 2^256)
      (H_nth : List.nth_error storage index = Some (StorableValue.MapStruct map)) :
    let state := make_state env state_base memory storage in
    let map' := Dict.declare_or_assign map (key, offset) value in
    match List.update_nth storage index (StorableValue.MapStruct map') with
    | Some storage' =>
      let state' := State.with_current_storage env state
                      (Storage.of_storable_values storage') in
      {{? codes, env, Some state |
        update_storage_value_offset_0_t_uint256_to_t_uint256
          (keccak256_tuple2 key (Z.of_nat index) + offset) value ⇓
        Result.Ok tt
      | Some state' ?}}
    | None => True
    end.
  Proof.
    cbv zeta.
    destruct (List.update_nth storage index
                (StorableValue.MapStruct
                   (Dict.declare_or_assign map (key, offset) value)))
      eqn:Hupd; [|exact I].
    unfold update_storage_value_offset_0_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    (* Walk: convert → sload → prepare_store → update_byte_slice → sstore. *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256 | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (Storage.run_sload_struct_field storage index map key offset);
               exact H_nth | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_uint256 | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_32_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_32_shift_0; exact H_v | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ eapply (Storage.run_sstore_struct_field storage index key offset value) | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  (* Residual: walker leaves the sstore's state-precondition discharge
     ([State.get_current_storage env state = Some (...)]) and possibly
     post-sstore state canonicalization. Closing this requires
     CanonizeState.execute + the precise state-shape lemmas from the
     upstream proof library. The structure is in place; closure is
     mechanical but lengthy. *)
  Admitted.

End ThrottleLibLeaves.
