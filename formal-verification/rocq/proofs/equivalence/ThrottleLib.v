(** Phase 1.1 (task #171) — storage projection for ThrottleLib.

    Sim-side ↔ Yul-side glue for the equivalence proofs in Phase 1.2
    ([_getProposalsAvailable] view) and Phase 1.3 ([consumeProposalCharge]
    mutator). Defines:

      - [ProposalThrottleStorage.t]: the full Solidity-side storage
        shape ([capacity] + [mapping(address => ProposalThrottle)]),
        promoting our existing [ProposerThrottle.Throttle.t] (one
        account's slot) into the full mapping context.

      - Slot-address helpers ([slot_capacity], [slot_currentCharge],
        [slot_lastUpdated]): the U256 slot keys at which each storage
        field lives, parameterised by the library's [base_slot]
        argument and (for per-account fields) the account address.

      - [storage_slot_value]: a Gallina function mapping a [SlotKind.t]
        + sim state to the U256 word the runtime should observe at the
        corresponding slot. The equivalence lemma in 1.2 / 1.3 takes
        the conjunction of [forall account, sload <slot_X account> =
        storage_slot_value sim (SlotKind.X account)] as a precondition.

      - Sanity lemmas verifying the projection respects the sim-side
        operations (set-then-get returns the set value; an update on
        account [a] leaves account [b ≠ a] alone).

    Methodology note (refinement of D2 in
    notes/equivalence_proof_methodology.md):

      The upstream's [StorableValue.t] inductive supports
      [U256 | Map U256→U256 | Map (U256*U256)→U256] only. ThrottleLib's
      [mapping(address => struct{currentCharge, lastUpdated})] does
      not fit any variant — the two struct fields live at
      [keccak256(account, mapBase) + 0] and [+ 1], i.e., adjacent slots
      under the same hash. Rather than extend [StorableValue.t]
      upstream, this file takes the per-slot-hypothesis route: the
      equivalence lemma's precondition is a family of [sload <expr> =
      <sim_field>] hypotheses, not a single
      [storage = of_storable_values (proj_sim sim)] equation. The
      [storage_slot_value] function is the projection at the per-slot
      level; aggregating it into a [SimulatedStorage.t] list would
      require the struct-aware variant we deliberately don't add.

      Phase 1.5 will update Audit.v Caveat-5 to document this trust
      path. Library-style contracts with struct-valued mappings get
      the per-slot-hypothesis shape; future contracts whose storage
      is expressible in plain [StorableValue.t] (e.g.,
      VersionRegistry, RewardTokenRegistry) may use the
      [of_storable_values] shape from Phase 3 onwards.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.ProposerThrottle.

Import ProposerThrottle.

Module ThrottleLibStorage.

  (** ----- Full Solidity-side storage shape -----

      Mirrors [ThrottleLib.ProposalThrottleStorage]:

        struct ProposalThrottleStorage {
            uint256 capacity;
            mapping(address account => ProposalThrottle) throttles;
        }

      [throttles] is a finite map by account; [Dict.t] is the upstream's
      abstract finite-map shape (no operational semantics — just
      [get], [declare_or_assign], [Valid.t]). The simulation's existing
      [ProposerThrottle.Throttle.t] is the inner-struct shape. *)
  Record t : Set := {
    capacity  : U256.t;
    throttles : Dict.t Address.t Throttle.t;
  }.

  (** Default throttle returned on a missing key. Matches Solidity's
      "uninitialised storage reads as zero" semantics: a fresh account
      starts with zero currentCharge and zero lastUpdated. *)
  Definition default_throttle : Throttle.t := {|
    Throttle.currentCharge := 0;
    Throttle.lastUpdated   := 0;
  |}.

  Definition get_throttle (s : t) (account : Address.t) : Throttle.t :=
    match Dict.get s.(throttles) account with
    | Some throttle => throttle
    | None          => default_throttle
    end.

  Definition set_throttle (s : t) (account : Address.t) (t' : Throttle.t) : t := {|
    capacity  := s.(capacity);
    throttles := Dict.declare_or_assign s.(throttles) account t';
  |}.

  Definition init (cap : U256.t) : t := {|
    capacity  := cap;
    throttles := [];
  |}.

End ThrottleLibStorage.

(** ----- Solidity storage-slot addresses, parameterised by base_slot -----

    The library's Yul-side function takes [var_proposalThrottle_slot] as
    its first argument; that's the [base_slot] here. Storage layout:

      base_slot + 0:  capacity (uint256, single slot)
      base_slot + 1:  throttles mapping base
      keccak256(account, base_slot + 1) + 0:  ProposalThrottle.currentCharge
      keccak256(account, base_slot + 1) + 1:  ProposalThrottle.lastUpdated

    [keccak256_tuple2] is the upstream's 2-word keccak helper, axiomatised
    in [proofs.RocqOfSolidity]. *)

Definition slot_capacity (base_slot : U256.t) : U256.t :=
  base_slot.

Definition slot_throttles_base (base_slot : U256.t) : U256.t :=
  base_slot + 1.

Definition slot_currentCharge (base_slot : U256.t) (account : Address.t) : U256.t :=
  keccak256_tuple2 account (slot_throttles_base base_slot).

Definition slot_lastUpdated (base_slot : U256.t) (account : Address.t) : U256.t :=
  (keccak256_tuple2 account (slot_throttles_base base_slot)) + 1.

(** ----- The per-slot projection: which sim field lives where ----- *)

Module SlotKind.
  Inductive t : Set :=
  | Capacity
  | CurrentCharge (account : Address.t)
  | LastUpdated   (account : Address.t).
End SlotKind.

(** Address of a [SlotKind.t] under the given [base_slot]. *)
Definition slot_address (base_slot : U256.t) (k : SlotKind.t) : U256.t :=
  match k with
  | SlotKind.Capacity              => slot_capacity base_slot
  | SlotKind.CurrentCharge account => slot_currentCharge base_slot account
  | SlotKind.LastUpdated   account => slot_lastUpdated   base_slot account
  end.

(** Value the runtime should observe at a given slot, given a sim state.
    This is the forward projection at the per-slot level. *)
Definition storage_slot_value
    (s : ThrottleLibStorage.t) (k : SlotKind.t) : U256.t :=
  match k with
  | SlotKind.Capacity              => s.(ThrottleLibStorage.capacity)
  | SlotKind.CurrentCharge account =>
      (ThrottleLibStorage.get_throttle s account).(Throttle.currentCharge)
  | SlotKind.LastUpdated   account =>
      (ThrottleLibStorage.get_throttle s account).(Throttle.lastUpdated)
  end.

(** ----- Sanity lemmas -----

    These lemmas verify the projection's algebraic behaviour against
    the sim's [set_throttle] and [get_throttle]. They give the
    equivalence-proof author the building blocks to rewrite
    [storage_slot_value (set_throttle s a t') k] into a case-split on
    [k] without re-deriving the [Dict] axioms each time.

    Required for the Phase 1.3 [consumeProposalCharge] proof: after
    [sstore <slot_currentCharge a>], the post-state's
    [storage_slot_value] for [CurrentCharge a] must equal the new
    value, and for any other slot kind must equal the pre-state's. *)

Lemma storage_slot_value_capacity_independent
    (s : ThrottleLibStorage.t) (account : Address.t) (t' : Throttle.t) :
  storage_slot_value (ThrottleLibStorage.set_throttle s account t') SlotKind.Capacity
  = storage_slot_value s SlotKind.Capacity.
Proof. reflexivity. Qed.

(** Helper: a get-after-declare-or-assign lemma. The upstream's
    [Dict] doesn't provide one, so we prove it inline against the
    concrete [Z]-keyed instance ([Address.t = U256.t = Z]). *)
Lemma dict_get_declare_or_assign_eq
    {V : Set} (dict : Dict.t Address.t V)
    (key : Address.t) (value : V) :
  Dict.get (Dict.declare_or_assign dict key value) key = Some value.
Proof.
  unfold Dict.declare_or_assign.
  induction dict as [|[k v] dict IH]; hauto lq: on use: Z.eqb_refl, Z.eqb_eq, Z.eqb_neq.
Qed.

Lemma storage_slot_value_currentCharge_set_same
    (s : ThrottleLibStorage.t) (account : Address.t) (t' : Throttle.t) :
  storage_slot_value
    (ThrottleLibStorage.set_throttle s account t')
    (SlotKind.CurrentCharge account)
  = t'.(Throttle.currentCharge).
Proof.
  unfold storage_slot_value, ThrottleLibStorage.set_throttle,
         ThrottleLibStorage.get_throttle. simpl.
  rewrite dict_get_declare_or_assign_eq. reflexivity.
Qed.

Lemma storage_slot_value_lastUpdated_set_same
    (s : ThrottleLibStorage.t) (account : Address.t) (t' : Throttle.t) :
  storage_slot_value
    (ThrottleLibStorage.set_throttle s account t')
    (SlotKind.LastUpdated account)
  = t'.(Throttle.lastUpdated).
Proof.
  unfold storage_slot_value, ThrottleLibStorage.set_throttle,
         ThrottleLibStorage.get_throttle. simpl.
  rewrite dict_get_declare_or_assign_eq. reflexivity.
Qed.

(** ----- Validity ----- *)

Module Valid.
  Record state (s : ThrottleLibStorage.t) : Prop := {
    capacity_pos     : ProposerThrottle.Valid.capacity s.(ThrottleLibStorage.capacity);
    throttles_valid  : Dict.Valid.t
                         Address.Valid.t
                         ProposerThrottle.Valid.throttle
                         s.(ThrottleLibStorage.throttles);
  }.

  (** Initial storage with any positive capacity satisfies validity. *)
  Lemma init_is_valid (cap : U256.t)
      (H_cap : ProposerThrottle.Valid.capacity cap) :
    state (ThrottleLibStorage.init cap).
  Proof. constructor; [exact H_cap | constructor]. Qed.
End Valid.

(** ----- Phase 1.2: equivalence of [_getProposalsAvailable] (view) -----

    States the per-function equivalence between the shallow Yul body
    [ThrottleLib_153.deployed.fun__getProposalsAvailable_152] (generated
    by [bash formal-verification/scripts/shallow-embed-sweep]) and the
    sim's [ProposerThrottle.proposalsAvailable] + [readCharge].

    The theorem statement is the deliverable for this phase. The proof
    body is [Admitted] — the closing tactic dance walks through ~30
    primitive steps ([sload]/[keccak256]/[checked_*]/[Shallow.if_])
    and is mechanical but lengthy. It will close as a side-effect of
    Phase 1.3, which needs all of the same apparatus for the mutator.

    Per the methodology doc's D2 refinement (per-slot hypotheses
    rather than [SimulatedStorage.t] encoding), the preconditions
    parameterise over the relevant sloads instead of asserting a
    [storage = of_storable_values …] equation. The
    [storage_slot_value] projection (defined above) names the
    expected [sload] result for each [SlotKind.t].

    Two design choices deliberately taken in the statement:

      1. The theorem targets the *private* [fun__getProposalsAvailable_152]
         (note double underscore) which returns the tuple
         [(proposalsAvailable, charge)]. The public-facing
         [fun_getProposalsAvailable_91] is a thin wrapper returning
         just the first component; once 1.2 closes, the public-facing
         lemma falls out in ~5 lines.

      2. The post-state's memory is existentially quantified — the
         function writes to memory slots 0 and 0x20 to compute the
         [keccak256(account, baseSlot+1)] mapping-derivation, then
         leaves that scratch behind. No caller cares about it; the
         sim is memory-free; we don't constrain the post-memory.
         (Matches the upstream's [Erc20_403.run_body] pattern.) *)

Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.generated.ThrottleLib_shallow.

Import Stdlib.
Import RunO.

(** Aggregated per-slot equivalence — the shape every storage-touching
    equivalence lemma in this file will take as a hypothesis. Says:
    "the runtime's storage at each kind-relevant slot returns the
    [storage_slot_value sim] projection at that slot." *)
Definition storage_matches_sim
    (codes : Codes.t) (env : Environment.t) (state : State.t)
    (base_slot : U256.t) (sim : ThrottleLibStorage.t) : Prop :=
  forall (k : SlotKind.t),
    {{? codes, env, Some state |
      Stdlib.sload (slot_address base_slot k) ⇓
      Result.Ok (storage_slot_value sim k)
    | Some state ?}}.

(** Memory layout precondition. The mapping-index-access helper writes
    [account] at memory[0..0x20] and [base_slot+1] at memory[0x20..0x40],
    then keccaks those 64 bytes. We require enough scratch in the
    pre-state's memory (32-byte word at indices 0 and 1) to model this
    cleanly. *)
Definition memory_has_scratch
    (memory : SimulatedMemory.t) : Prop :=
  exists w0 w1 rest, memory = w0 :: w1 :: rest.

(** Block-timestamp pinning hypothesis. R020 is now resolved — the
    dev-clone runtime defines [Stdlib.timestamp] as
    [LowM.Primitive Primitive.GetBlockTimestamp M.pure] with
    [eval_primitive] reading from [State.block_timestamp]. So
    "block.timestamp returns now" is just [state.(State.block_timestamp) = now]. *)

(** ----- Closed building-block lemmas -----

    Small leaves of the [_getProposalsAvailable] call tree. Each one
    closes mechanically — they accumulate the workflow patterns we
    need for the larger proof body below. *)

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
      to detect overflow.

      The proof needs deeper EVM-boolean-arithmetic reduction (nested
      iszero/or/eq with the (if then 1 else 0)-style branching that the
      shallow form bakes in). Admitted pending a more involved tactic
      development. *)
  Lemma run_checked_mul_t_uint256 codes env state (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_no_overflow : x * y < 2^256) :
    {{? codes, env, Some state |
      checked_mul_t_uint256 x y ⇓ Result.Ok (x * y)
    | Some state ?}}.
  Admitted.

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

End ThrottleLibLeaves.

(** ----- Phase C: mapping_index_access (memory + keccak) -----

    The function writes [convert_t_address_to_t_address key] at mem[0],
    [slot] at mem[0x20], then keccaks 64 bytes from mem[0] and returns
    the result. On a valid Address, the cleanup is identity, so the
    result is precisely [keccak256_tuple2 key slot].

    Precondition: the state must be in [make_state env state_base memory storage]
    form with at least two memory slots available for the scratch
    writes. [storage] is unconstrained — this helper doesn't touch
    storage. *)

Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Module MappingIndexAccess.

  Import ThrottleLib_153.ThrottleLib_153_deployed.
  Import ThrottleLibLeaves.

  (** The function name in the generated shallow file contains unicode
      subscripts (ₓ) to encode the original Yul mangling. We bind it to
      a Coq-level name for readability. *)
  Notation mapping_index_access_t_mapping_address_struct_of_address :=
    mapping_index_access_t_mappingₓ_t_address_ₓ_t_structₓ_ProposalThrottle_ₓ18_storage_ₓ_of_t_address.

  Lemma run_mapping_index_access codes env state_base
      (slot : U256.t) (key : U256.t) (storage : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (H_key : Address.Valid.t key)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let st := make_state env state_base memory storage in
    exists memory_post,
    {{? codes, env, Some st |
      mapping_index_access_t_mapping_address_struct_of_address slot key ⇓
      Result.Ok (keccak256_tuple2 key slot)
    | Some (make_state env state_base memory_post storage) ?}}.
  Proof.
    destruct H_mem as (w0 & w1 & rest & ->).
    eexists.
    unfold mapping_index_access_t_mapping_address_struct_of_address.
    l. {
      (* do~ mstore(0, convert_t_address_to_t_address key) *)
      l. {
        c. { apply run_convert_t_t_address_to_t_address. exact H_key. }
        c. { apply_run_mstore. }
        CanonizeState.execute.
        p.
      }
      (* do~ mstore(0x20, slot) *)
      l. {
        c. { apply_run_mstore. }
        CanonizeState.execute.
        p.
      }
      (* let~ dataSlot := keccak256(0, 0x40) *)
      l. {
        c. { apply_run_keccak256_tuple2. }
        p.
      }
      p.
    }
    p.
  Qed.

End MappingIndexAccess.

(** ----- The main equivalence theorem (Admitted; see header note) ----- *)

Theorem run_getProposalsAvailable_equivalent
    (codes : Codes.t) (env : Environment.t) (state : State.t)
    (base_slot : U256.t) (account : Address.t)
    (sim : ThrottleLibStorage.t) (now : U256.t)
    (memory : SimulatedMemory.t)
    (H_valid_sim     : Valid.state sim)
    (H_valid_account : Address.Valid.t account)
    (H_valid_now     : U256.Valid.t now)
    (H_storage       : storage_matches_sim codes env state base_slot sim)
    (H_timestamp     : state.(State.block_timestamp) = now)
    (H_memory        : state.(State.memory) = Memory.of_u256_list memory)
    (H_scratch       : memory_has_scratch memory)
    (H_no_overflow   : (** charge computation does not revert via checked_*: *)
       let throttle := ThrottleLibStorage.get_throttle sim account in
       now >= throttle.(Throttle.lastUpdated) /\
       throttle.(Throttle.currentCharge)
         + ((now - throttle.(Throttle.lastUpdated)) * ProposerThrottle.FIX_ONE)
           / ProposerThrottle.PROPOSAL_THROTTLE_PERIOD < 2 ^ 256 /\
       sim.(ThrottleLibStorage.capacity) * ProposerThrottle.FIX_ONE < 2 ^ 256) :
  let throttle  := ThrottleLibStorage.get_throttle sim account in
  let charge    := ProposerThrottle.readCharge throttle now in
  let available := ProposerThrottle.proposalsAvailable
                     throttle sim.(ThrottleLibStorage.capacity) now in
  exists memory',
  {{? codes, env, Some state |
    ThrottleLib_153.ThrottleLib_153_deployed.fun__getProposalsAvailable_152
      base_slot account ⇓
    Result.Ok (available, charge)
  | Some (state <| State.memory := Memory.of_u256_list memory' |>) ?}}.
Proof.
  (** Proof body: walks the shallow body of
      [fun__getProposalsAvailable_152] (445 lines into
      [generated/ThrottleLib_shallow.v]) with the named tactics:

        unfold fun__getProposalsAvailable_152.
        repeat (l || c || cu).
        - The [_27 := mapping_index_access_*] call writes to memory
          and keccaks; discharge via [apply_run_mstore],
          [apply_run_mstore], [apply_run_keccak256_tuple2], then
          [CanonizeState.execute].
        - The [_31 := read_from_storage_split_offset_0_t_uint256] call
          unfolds to [sload] composed with [cleanup_*]; discharge via
          [H_storage (SlotKind.LastUpdated account)] etc.
        - The [checked_sub_t_uint256] and [checked_mul_*] calls reduce
          to [Z] arithmetic guarded by [H_no_overflow]; each path
          terminates with [p] in the no-revert branch and [lia] in
          the revert branch.
        - The [Shallow.if_] at the clamp branch case-splits on whether
          the raw charge exceeds [FIX_ONE]; the sim's [Z.min FIX_ONE
          raw] matches by case analysis.

      Estimated ~200 lines of mechanical proof. Land as part of
      Phase 1.3 since [consumeProposalCharge] reuses the same body. *)
Admitted.

(** ----- Phase B: [make_state] form (task #187) -----

    The legacy [storage_matches_sim] precondition above takes a family
    of [sload <slot> = <value>] hypotheses keyed by [SlotKind.t]. Each
    storage-touching subproof has to invoke the hypothesis with the
    right [SlotKind.t] tag — readable, but it doesn't compose with the
    upstream's [apply_run_sload_*] Ltacs which expect a
    [make_state env state memory storage] state shape.

    With Phase A's new [StorableValue.MapStruct] variant (in the
    rocq-of-solidity fork at commit 2b66701431), we can now project
    the sim's [ThrottleLibStorage.t] into a [SimulatedStorage.t] list
    of length 2 and re-state the main theorem against
    [make_state env state_base memory (proj_sim sim)]. Subsequent
    storage reads then dispatch via [apply_run_sload_u256] (capacity)
    and [apply_run_sload_struct_field] (per-throttle fields).

    The legacy [storage_matches_sim] form is left in place for the
    leaf lemmas that reference it; new lemmas in Phases C-F prefer
    the [make_state] form. *)

Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Module MakeStateForm.

  (** Pack a sim's [throttles] dict into the flat (account, offset)-keyed
      map shape that [StorableValue.MapStruct] uses. Each non-zero
      throttle contributes two entries: (account, 0) -> currentCharge
      and (account, 1) -> lastUpdated. Accounts not in the sim's dict
      project to no entries, so [map_get_u256] returns 0 at those
      keys — matching Solidity's "uninitialised storage is zero". *)
  Definition throttles_packed (sim : ThrottleLibStorage.t) :
      Dict.t (U256.t * U256.t) U256.t :=
    List.flat_map (fun (entry : Address.t * Throttle.t) =>
      let (account, t) := entry in
      [((account, 0), t.(Throttle.currentCharge));
       ((account, 1), t.(Throttle.lastUpdated))])
      sim.(ThrottleLibStorage.throttles).

  (** The full sim ↔ Yul-storage projection. Two top-level slots:

        slot 0: capacity (uint256)
        slot 1: throttles mapping (MapStruct; field offset 0 =
                currentCharge, field offset 1 = lastUpdated)

      With this projection, [make_state env state_base memory (proj_sim sim)]
      is a [State.t] whose storage agrees with the sim and whose memory
      is freely chosen — the shape every Phase C-F lemma will take as
      its precondition. *)
  Definition proj_sim (sim : ThrottleLibStorage.t) : SimulatedStorage.t := [
    StorableValue.U256 sim.(ThrottleLibStorage.capacity);
    StorableValue.MapStruct (throttles_packed sim)
  ].

  (** Sanity: the [proj_sim] entries' lookup keys match the slot-address
      helpers above. The MapStruct sload uses
      [keccak256_tuple2 account (Z.of_nat 1) + offset], and [slot_currentCharge]
      is [keccak256_tuple2 account (base_slot + 1)], so they agree when
      [base_slot = 0] (which is the convention used by every governor
      contract's ThrottleLib instance — the throttle storage is at the
      contract's slot 0 + 1).

      The cross-check below verifies the projection is well-formed at
      the capacity slot. The per-field checks for MapStruct sloads
      land in Phase C alongside the [apply_run_sload_struct_field]
      tactic usage. *)
  Lemma proj_sim_well_formed (sim : ThrottleLibStorage.t) :
    List.length (proj_sim sim) = 2%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_capacity (sim : ThrottleLibStorage.t) :
    List.nth_error (proj_sim sim) 0
    = Some (StorableValue.U256 sim.(ThrottleLibStorage.capacity)).
  Proof. reflexivity. Qed.

  Lemma proj_sim_throttles (sim : ThrottleLibStorage.t) :
    List.nth_error (proj_sim sim) 1
    = Some (StorableValue.MapStruct (throttles_packed sim)).
  Proof. reflexivity. Qed.

  (** [throttles_packed] lookup: when the sim contains an entry for
      [account], the packed map returns the requested field's value.
      When the sim has no entry, the lookup defaults to 0 (matching
      [ThrottleLibStorage.default_throttle], which is also zero in both
      fields). *)
  (** ----- Projection sanity lemmas (Admitted — WISDOM R022) -----

      These two lemmas relate the [throttles_packed] map's offset-0 /
      offset-1 lookups to the sim's [Throttle.currentCharge] /
      [Throttle.lastUpdated] field accessors. Phase C uses them as the
      rewrite rules after [apply_run_sload_struct_field] surfaces a
      [map_get_u256 (throttles_packed sim) (account, offset)] in the
      goal.

      They are mathematically trivial — the [throttles_packed] flat_map
      lays out [(account, 0) -> currentCharge] and [(account, 1) -> lastUpdated]
      for each sim throttle, and the [map_get_u256] lookup
      sequentially scans for the matching key. Mechanizing the proof
      in Coq 8.20.1 hits a typeclass-projection anomaly: [Dict.Eq.eqb]
      on tuple keys dispatches through [Dict.Eq.ITuple2], and both
      [simpl] / [cbn] / [hauto] anomaly on the unfolded body with
      "Conversion test raised an anomaly: Uncaught exception Not_found".
      Manual [change] tactics also fail because [change] requires
      syntactic identity through the typeclass projection, which Coq
      doesn't reduce.

      WISDOM.md R022 captures this trap; the upstream-side workaround
      would be to expose a [Dict.Eq.eqb_pair_unfold] lemma in the
      rocq-of-solidity simulation. Tracked as task #185 (WISDOM
      updates) — the lemma will close once that helper lands.

      Their use is non-defeating: Phases C-F use them as oracle
      rewrites; treat them as sound on inspection of the
      [throttles_packed] body, which is a pure function. *)
  Lemma throttles_packed_currentCharge (sim : ThrottleLibStorage.t) (account : Address.t) :
    StorableValue.map_get_u256 (throttles_packed sim) (account, 0)
    = (ThrottleLibStorage.get_throttle sim account).(Throttle.currentCharge).
  Proof.
  Admitted.

  Lemma throttles_packed_lastUpdated (sim : ThrottleLibStorage.t) (account : Address.t) :
    StorableValue.map_get_u256 (throttles_packed sim) (account, 1)
    = (ThrottleLibStorage.get_throttle sim account).(Throttle.lastUpdated).
  Proof.
  Admitted.

  (** ----- Restated main theorem (still Admitted) -----

      Replaces the [storage_matches_sim] precondition with the
      canonical [make_state] form. The state-skeleton [state_base]
      carries everything except memory and storage; [memory] is the
      scratch memory the function uses internally; [proj_sim sim] is
      the projected storage. *)
  Theorem run_getProposalsAvailable_equivalent_make_state
      (codes : Codes.t) (env : Environment.t) (state_base : State.t)
      (account : Address.t)
      (sim : ThrottleLibStorage.t) (now : U256.t)
      (memory : SimulatedMemory.t)
      (H_valid_sim     : Valid.state sim)
      (H_valid_account : Address.Valid.t account)
      (H_valid_now     : U256.Valid.t now)
      (H_timestamp     : state_base.(State.block_timestamp) = now)
      (H_no_overflow   : (** charge computation does not revert via checked_*: *)
         let throttle := ThrottleLibStorage.get_throttle sim account in
         now >= throttle.(Throttle.lastUpdated) /\
         throttle.(Throttle.currentCharge)
           + ((now - throttle.(Throttle.lastUpdated)) * ProposerThrottle.FIX_ONE)
             / ProposerThrottle.PROPOSAL_THROTTLE_PERIOD < 2 ^ 256 /\
         sim.(ThrottleLibStorage.capacity) * ProposerThrottle.FIX_ONE < 2 ^ 256) :
    let state    := make_state env state_base memory (proj_sim sim) in
    let throttle  := ThrottleLibStorage.get_throttle sim account in
    let charge    := ProposerThrottle.readCharge throttle now in
    let available := ProposerThrottle.proposalsAvailable
                       throttle sim.(ThrottleLibStorage.capacity) now in
    exists memory',
    {{? codes, env, Some state |
      ThrottleLib_153.ThrottleLib_153_deployed.fun__getProposalsAvailable_152
        0 (** base_slot *) account ⇓
      Result.Ok (available, charge)
    | Some (state <| State.memory := Memory.of_u256_list memory' |>) ?}}.
  Proof.
  (** Discharged in Phases C-F via apply_run_sload_struct_field,
      apply_run_mstore, apply_run_keccak256_tuple2, CanonizeState.execute. *)
  Admitted.

End MakeStateForm.
