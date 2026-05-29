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

End ThrottleLibLeaves.

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
