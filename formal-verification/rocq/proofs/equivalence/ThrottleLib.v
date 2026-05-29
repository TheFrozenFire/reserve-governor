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
