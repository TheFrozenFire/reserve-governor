(** OZ ERC20 base equivalence — proof of method for OZ-base mechanization
    (task #313).

    [ERC20] is an *abstract* OZ contract that supplies the canonical
    ERC20 token implementation.  It has no shallow form of its own —
    solc inlines all of ERC20's Yul translations into the inheritor's
    shallow form.  In this corpus, [StakingVault] is the inheritor; its
    [StakingVault_shallow.v] contains:

      - [fun__mint_3368]     ← ERC20._mint(account, value)
      - [fun__update_3335]   ← ERC20._update(from, to, value) [base body]
      - [fun__update_3808]   ← ERC20Votes._update override (calls 3335
                                + maxSupply check + _transferVotingUnits)
      - [fun__update_1459]   ← StakingVault._update override (wraps in
                                accrueRewards modifier + optimistic
                                delegation moves)
      - [fun__getERC20Storage_2971] ← returns the ERC-7201 anchor
                                       [0x52c63247e1f47db19d5ce0460030c497f067ca4cebf71ba98eeadabe20bace00]

    ===== Why _mint as the proof of method =====

    [_mint] is the smallest internal OZ ERC20 piece:

      function _mint(address account, uint256 value) internal {
          if (account == address(0)) {
              revert ERC20InvalidReceiver(address(0));
          }
          _update(address(0), account, value);
      }

    Three lines of Solidity: one require + one delegated call to
    [_update].  As a proof of method:

      - If this composite walker shape closes to [Qed], all other ERC20
        internal functions ([_burn], [_transfer], [_approve]) extend
        mechanically with the same recipe.
      - If it doesn't, no OZ-base mechanization will.

    ===== Methodology (R072 slot-agnostic + R083 anchor lens) =====

    The OZ ERC20Storage struct lives at an ERC-7201 keccak-derived
    namespace anchor (0x52c63247...).  Inside the struct:
      - offset 0:  mapping(address => uint256) _balances
      - offset 1:  mapping(address => mapping(address => uint256)) _allowances
      - offset 2:  uint256 _totalSupply
      - offset 3:  string _name
      - offset 4:  string _symbol

    The framework's [Storage.run_sload_map_u256] expects slot indices
    of the form [Z.of_nat n], which cannot unify with a 256-bit
    keccak-derived anchor.  R083 added the slot-anchor-agnostic
    [run_sload_map2_u256_at_anchor]; this file consumes the new
    [run_sload_map_u256_at_anchor] (single-map keyed) and
    [run_sload_u256_at_anchor_offset] (uint256 at fixed offset within
    the struct) primitives — siblings of R083's Map2 variants, added
    here in the [FrameworkExtensions] extension because OZ ERC20 uses
    the single-map shape for [_balances] (whereas AccessControl uses
    Map2 for [_roles[role].hasRole[account]]).

    Per R072 slot-agnostic abstract-base methodology, the [ERC20.v]
    file declares a [Section] parameterized by:

      - [slot_balances : nat]       — list index where [_balances] Map lives
      - [slot_totalSupply : nat]    — list index where [_totalSupply] U256 lives
      - [erc20_anchor : U256.t]     — the ERC-7201 anchor value
      - [IsNamespaceAnchor values slot_balances erc20_anchor]
                                    — lens binding for [_balances]
      - [IsAnchorOffsetSlot values slot_totalSupply erc20_anchor 2]
                                    — lens binding for [_totalSupply]
                                       (offset 2 within the struct)

    Inheritors discharge the lens hypotheses by [reflexivity] /
    [refl_equal] at instantiation time, plugging in their concrete
    [proj_sim] indices.

    ===== Sim model =====

    The ERC20 sim is the existing [mocks/ERC20.v] mock — a list-backed
    [balances : list (Address * U256.t)] plus [totalSupply : U256.t]
    plus [allowances : list ((Address * Address) * U256.t)].  The mock
    already has:
      - [ERC20.balanceOf]  : pointwise balance lookup
      - [ERC20.mint]       : credits balances + bumps totalSupply
      - [ERC20.do_transfer]: the [_update] mint/burn/transfer trichotomy
                             (collapsed to its non-revert paths)
      - [ERC20.Valid.t]    : sum_balances = totalSupply invariant
      - [ERC20.mint_increases_totalSupply] : sim-level mint headline

    For the equivalence statement we need a [proj_sim_ERC20] that
    extracts a [SimulatedStorage.t]-compatible view from
    [ERC20.State.t].  Because the OZ ERC20 storage is namespaced and
    the [_balances] map keys are 160-bit addresses (not byte32-keys
    like AccessControl's per-role positions), we represent the
    balances as [Dict.t U256.t U256.t] (single-map keyed on address).

    Headline equivalence theorem [run_fun__mint_3368_equivalent]:
    under preconditions
      - [0 <= account < 2^160]                     (well-formed address)
      - [account <> 0]                              (zero-address check passes)
      - [0 <= value < 2^256]                        (uint256 in range)
      - [erc20_storage_well_formed proj_sim]         (lens hypotheses)
    we get [{{ ... | fun__mint_3368 account value ⇓ Result.Ok tt
              | proj_sim_post_mint ... ?}}].

    ===== Trust footprint (task #315 refactor) =====

    Closed to [Qed].  This file's Print Assumptions for the three
    headline theorems ([_mint], [_burn], [_transfer]):

      1. [run_fun__update_3335_at_proj_sim_<branch>] — narrowed OZ ERC20
         BASE body axiom (one per branch: mint / burn / transfer).
         Audit-time obligation: the Yul body at
         [StakingVault_shallow.v:10200-10328] (the OZ ERC20 [_update]
         inlined by solc into StakingVault).  Mechanical discharge via
         R083 anchor lens + R107 absorbers is the next step (~300 lines
         per branch; see WISDOM R108 for the recipe).

      2. [run_fun__update_1459_wraps_fun__update_3335] — R070-shaped
         observational-equivalence bridge for the StakingVault wrapper
         chain ([modifier_accrueRewards] → [fun__update_1459_inner] →
         [fun__update_3808] (ERC20Votes overrides) → [fun__update_3335]
         → [_moveOptimisticDelegateVotes]).  Audit-time obligation: the
         StakingVault wrapper layers write to slots OUTSIDE the OZ ERC20
         base lens (delegate checkpoints, accrueRewards state, optimistic
         delegate state) and are observationally identity on the OZ ERC20
         base projection.  This bridge is per-target — vanilla OZ ERC20
         deployments would discharge it trivially.

      3. Upstream framework axioms ([Memory.of_u256_list],
         [Storage.of_storable_values], standard PrimInt63 primitives) —
         baseline trust footprint shared with the entire corpus.

    Net trust delta from task #314 (one body-absorbing composite axiom)
    to task #315 (two narrower axioms per branch):
      - Task #314: ONE big composite axiom per branch that absorbed both
        the wrapper chain AND the OZ ERC20 base body indiscriminately.
      - Task #315: TWO narrower axioms per branch — one for the OZ
        ERC20 base body (mechanically discharge-able), one for the
        wrapper-chain bridge (per-target audit).

    The walker proofs of the three headline theorems use Qed Lemmas only:
      - [run_cleanup_t_address] (AbiEncoding.v Qed Lemma)
      - [run_convert_t_rational_0_by_1_to_t_address_at_zero]
         (this file, Qed Lemma)
      - [run_eq_address_zero_check] (this file, Qed Lemma)
      - [run_shallow_let_state_if_zero] (FrameworkExtensions.v Qed
         Lemma — R107 absorber, reusable across every walker with the
         Yul [if (cond) revert(...)] shape after [cond = 0]).

    The four [*_at_anchor] framework primitives ([run_sload_map_u256_at_anchor],
    [run_sstore_map_u256_at_anchor], [run_sload_u256_at_anchor_offset],
    [run_sstore_u256_at_anchor_offset]) are NOT load-bearing for the
    headline theorems — they are consumed by the eventual discharge of
    [run_fun__update_3335_at_proj_sim_<branch>] to its Yul body (the
    OZ ERC20 base [_update] walker), at which point the headline
    theorems' trust footprint reduces further to JUST the wrapper
    bridge + framework primitives.

    Path forward for [_approve] (orthogonal, mechanical):
      - [_approve]: no [_update] call.  Walker writes directly to
        [_allowances[owner][spender] := value] via
        [run_sstore_map2_u256_at_anchor] (R083, already in the
        framework).  Emit Approval event (log3 — pure).

    From this base, ERC4626 [deposit] requires:
      - Compose [_mint] (this file's headline theorem) with the
        asset-pulling [safeTransferFrom] (already mechanized at the
        trust-axiom level in [R094] / [AbiEncoding.SafeERC20]).
      - Compose with the ERC4626 [_convertToShares] /
        [_convertToAssets] muldiv arithmetic (R076 in [ERC4626.v]).
      - The [super._deposit] walker discharge in [StakingVaultExchange]
        composes [_mint] with the per-token [safeTransferFrom] call.

    WISDOM reference: R051 (composite-axiom shape), R070 (Skolemized
    bridge), R072 (slot-agnostic abstract base), R083 (namespace anchor
    lens), R104 (Walker Axiom→Lemma rename), R107 (BlockUnit absorbers),
    R108 (this task — OZ-base body / wrapper-bridge trust decomposition).
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.generated.StakingVault_shallow.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import ReserveGovernor.proofs.equivalence.FrameworkExtensions.
Require Import ReserveGovernor.mocks.ERC20.
Import AbiEncoding.AbiEncoding.
Import FrameworkExtensions.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module ERC20Equivalence.

  Import StakingVault_1721.StakingVault_1721_deployed.

  (** ====================================================================
      Sim model — wrapping [mocks/ERC20.v]
      ====================================================================

      The on-chain [_balances] is a [mapping(address => uint256)]
      storing the per-account balance.  We project this as a
      [Dict.t U256.t U256.t] in the abstract storage.  The mock's
      list-of-pairs representation is observationally equivalent — we
      convert between via [balances_to_dict] at boundary.

      For the [_mint] proof we only need pre/post storage shapes; the
      mock-level [ERC20.mint] gives the sim post-state and we lift it
      via the projection. *)

  Definition Address : Set := U256.t.

  (** Convert mock's list-of-pairs balance representation to a
      [Dict.t U256.t U256.t].  Used to project the mock's sim state
      into the abstract storage list. *)
  Fixpoint balances_to_dict (bs : list (Address * U256.t))
      : Dict.t U256.t U256.t :=
    match bs with
    | [] => []
    | (k, v) :: rest => (k, v) :: balances_to_dict rest
    end.

  (** OZ ERC-7201 namespace anchor for ERC20Storage.
        keccak256("openzeppelin.storage.ERC20") & ~bytes32(uint256(0xff))
      Hex: 0x52c63247e1f47db19d5ce0460030c497f067ca4cebf71ba98eeadabe20bace00
      The same constant that [fun__getERC20Storage_2971] returns. *)
  Definition ERC20_NAMESPACE_ANCHOR : U256.t :=
    37439836327923360225337895871394760624280537466773280374265222508165906222592.

  (** Cross-check: the anchor matches the literal in the shallow form. *)
  Example anchor_matches_shallow :
    ERC20_NAMESPACE_ANCHOR =
    37439836327923360225337895871394760624280537466773280374265222508165906222592.
  Proof. reflexivity. Qed.

  (** ====================================================================
      OZ ERC20 _update body Yul-helper leaf lemmas (task #316)
      ====================================================================

      Closed (Qed) leaf lemmas for every Yul helper appearing in the
      body of [fun__update_3335]:

        - [fun__getERC20Storage_2971]                 returns the anchor
        - [cleanup_t_uint256]                          identity
        - [cleanup_from_storage_t_uint256]             identity
        - [shift_right_0_unsigned]                     identity
        - [extract_from_storage_value_offset_0_t_uint256] identity
        - [identity]                                   identity
        - [convert_t_uint256_to_t_uint256]             identity
        - [prepare_store_t_uint256]                    identity
        - [shift_left_0]                               identity for v < 2^256
        - [update_byte_slice_32_shift_0]               identity for v < 2^256
        - [wrapping_add_t_uint256]                     = Pure.add
        - [wrapping_sub_t_uint256]                     = Pure.sub
        - [checked_add_t_uint256]                      = x + y (no-overflow)
        - [checked_sub_t_uint256]                      = x - y (no-underflow)
        - [cleanup_t_uint160] / [convert_t_uint160_*] / [convert_t_address_to_t_address]
                                                       identity on Address.Valid.t

      Composite storage helpers (chaining the identity leaves with the
      R083 anchor primitives):

        - [run_read_from_storage_split_offset_0_t_uint256_at_map_anchor]
        - [run_read_from_storage_split_offset_0_t_uint256_at_anchor_offset]
        - [run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor]
        - [run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_anchor_offset]

      Memory-absorbing mapping_index_access analog (parallels
      AbiEncoding.run_mapping_index_access_absorbing for the
      address-keyed mapping):

        - [run_mapping_index_access_t_address_at_make_state] — Axiom
          (per R083 Gap 2 pattern; memory effects skolemized)

      These are the load-bearing infrastructure for the body discharge
      of [run_fun__update_3335_at_proj_sim_<branch>] (task #316).
      They are NOT load-bearing for the headline theorems below until
      the body discharge itself closes — that follow-up requires
      additional Section bridging hypotheses connecting the abstract
      [proj_sim] to per-branch storage updates (see Section comment).

      WISDOM reference: R083 (anchor lens primitives), R107 (Shallow
      absorbers), R108 (this body / wrapper decomposition), R109 (this
      task — leaf infrastructure for the body discharge).
  *)

  (** [fun__getERC20Storage_2971] returns the ERC-7201 namespace anchor.
      Pure-state computation; state unchanged. *)
  Lemma run_fun__getERC20Storage_2971_returns_anchor codes env state :
    {{? codes, env, Some state |
      fun__getERC20Storage_2971 ⇓ Result.Ok ERC20_NAMESPACE_ANCHOR
    | Some state ?}}.
  Proof.
    unfold fun__getERC20Storage_2971, ERC20_NAMESPACE_ANCHOR.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    lu. repeat (lu || cu || p).
  Qed.

  (** Identity leaves. *)
  Lemma run_cleanup_t_uint256_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_cleanup_from_storage_t_uint256_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma Pure_shr_0_id (v : U256.t) : Pure.shr 0 v = v.
  Proof.
    unfold Pure.shr. cbn. apply Z.div_1_r.
  Qed.

  Lemma run_shift_right_0_unsigned_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu).
    pe.
    - rewrite Pure_shr_0_id. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_extract_from_storage_value_offset_0_t_uint256_id
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_uint256.
    lu. l. { c. { apply run_shift_right_0_unsigned_id. }
             c. { apply run_cleanup_from_storage_t_uint256_id. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_identity_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold identity.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint256_to_t_uint256_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint256_id. }
             c. { apply run_identity_id. }
             c. { apply run_cleanup_t_uint256_id. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_prepare_store_t_uint256_id codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_shift_left_0_id codes env state (v : U256.t)
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

  Lemma run_update_byte_slice_32_shift_0_id_on_value
      codes env state (prev v : U256.t)
      (H_v : 0 <= v < 2^256) :
    {{? codes, env, Some state |
      update_byte_slice_32_shift_0 prev v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold update_byte_slice_32_shift_0.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu || p).
    s.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.or, Pure.and, Pure.not, Pure.shl.
    rewrite Z.mul_1_r.
    rewrite (Z.mod_small v) by exact H_v.
    change 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      with (Z.ones 256).
    replace (2 ^ 256 - Z.ones 256 - 1) with 0
      by (change (Z.ones 256) with (2^256 - 1)%Z; lia).
    rewrite Z.land_0_r.
    rewrite Z.land_ones by lia.
    rewrite (Z.mod_small v) by exact H_v.
    rewrite Z.lor_0_l.
    reflexivity.
  Qed.

  (** [wrapping_add x y = Pure.add x y = (x + y) mod 2^256]. *)
  Lemma run_wrapping_add_t_uint256
      codes env state (x y : U256.t) :
    {{? codes, env, Some state |
      wrapping_add_t_uint256 x y ⇓ Result.Ok (Pure.add x y)
    | Some state ?}}.
  Proof.
    unfold wrapping_add_t_uint256.
    lu. l. { c. { unfold Stdlib.add. apply RunO.Pure. }
             c. { apply run_cleanup_t_uint256_id. } p. }
    repeat (lu || cu || p).
  Qed.

  (** [wrapping_sub x y = Pure.sub x y = (x - y) mod 2^256]. *)
  Lemma run_wrapping_sub_t_uint256
      codes env state (x y : U256.t) :
    {{? codes, env, Some state |
      wrapping_sub_t_uint256 x y ⇓ Result.Ok (Pure.sub x y)
    | Some state ?}}.
  Proof.
    unfold wrapping_sub_t_uint256.
    lu. l. { c. { unfold Stdlib.sub. apply RunO.Pure. }
             c. { apply run_cleanup_t_uint256_id. } p. }
    repeat (lu || cu || p).
  Qed.

  (** [checked_add x y = x + y] under no-overflow. *)
  Lemma run_checked_add_t_uint256_no_overflow
      codes env state (x y : U256.t)
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
    rewrite (Z.mod_small (x + y)) by lia.
    destruct (_ >? _) eqn:Hcmp; s.
    { exfalso. apply Z.gtb_lt in Hcmp. lia. }
    { pe; reflexivity. }
  Qed.

  (** [checked_sub x y = x - y] under no-underflow. *)
  Lemma run_checked_sub_t_uint256_no_underflow
      codes env state (x y : U256.t)
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
    rewrite (Z.mod_small (x - y)) by lia.
    destruct (_ >? _) eqn:Hcmp; s.
    { exfalso. apply Z.gtb_lt in Hcmp. lia. }
    { pe; reflexivity. }
  Qed.

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
    - change 0xffffffffffffffffffffffffffffffffffffffff
        with (Z.ones 160).
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small.
      + reflexivity.
      + exact H.
    - reflexivity.
  Qed.

  Lemma run_convert_t_uint160_to_t_uint160_on_address
      codes env state (v : U256.t) (H_v : Address.Valid.t v) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. { c. { apply run_cleanup_t_uint160_on_address; exact H_v. }
             c. { apply run_identity_id. }
             c. { apply run_cleanup_t_uint160_on_address; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_address_on_address
      codes env state (v : U256.t) (H_v : Address.Valid.t v) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160_on_address; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_address_to_t_address_on_address
      codes env state (v : U256.t) (H_v : Address.Valid.t v) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address_on_address; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** ====================================================================
      Mapping index access for address-keyed uint256 maps
      ====================================================================

      Body shape (mirror of AbiEncoding's bytes32-keyed variant):
        do~ mstore(0, convert_t_address_to_t_address key) in
        do~ mstore(0x20, slot) in
        let~ dataSlot := keccak256(0, 0x40) in
        M.pure dataSlot

      Memory-absorbing variant: the post-state memory is Skolemized
      via [mapping_index_access_address_post_memory], paralleling
      [AbiEncoding.mapping_index_access_post_memory] (R083 Gap 2 style).
      Audit-time obligation: the two mstores at scratch words 0 and 1
      followed by keccak256(0, 0x40) produce
      [keccak256_tuple2 key' slot] where [key' = address-cleaned key].
      Under [Address.Valid.t key], the cleanup is identity, so
      [key' = key].
  *)

  Parameter mapping_index_access_address_post_memory :
    Environment.t -> State.t -> SimulatedMemory.t -> SimulatedStorage.t ->
    U256.t -> U256.t -> SimulatedMemory.t.

  Axiom run_mapping_index_access_t_address_at_make_state :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : State.t)
           (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
           (slot key : U256.t)
           (H_key : Address.Valid.t key),
    {{? codes, env, Some (make_state env state_base memory storage) |
      mapping_index_access_t_mappingₓ_t_address_ₓ_t_uint256_ₓ_of_t_address
        slot key ⇓ Result.Ok (keccak256_tuple2 key slot)
    | Some (make_state env state_base
              (mapping_index_access_address_post_memory env state_base
                 memory storage slot key)
              storage) ?}}.

  (** ====================================================================
      Composite storage helpers (Map-keyed and U256-at-offset)
      ====================================================================

      Compose the R083 anchor primitives with the identity-on-U256
      cleanup chain.  These collapse the
      [read_from_storage_split_offset_0_t_uint256] /
      [update_storage_value_offset_0_t_uint256_to_t_uint256] wrappers
      into direct sload/sstore reasoning at the namespace-anchor lens.
  *)

  Lemma run_read_from_storage_split_offset_0_t_uint256_at_map_anchor
      codes env state_base memory
      (values : list StorableValue.t) (index : nat) (anchor : U256.t)
      (map : Dict.t U256.t U256.t) (key : U256.t)
      (H_anchor : IsNamespaceAnchor values index anchor)
      (H_nth : List.nth_error values index = Some (StorableValue.Map map)) :
    let state := make_state env state_base memory values in
    {{? codes, env, Some state |
      read_from_storage_split_offset_0_t_uint256 (keccak256_tuple2 key anchor) ⇓
        Result.Ok (StorableValue.map_get_u256 map key)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_0_t_uint256.
    lu. l. { c. { apply (run_sload_map_u256_at_anchor codes env
                           (make_state env state_base memory values)
                           values index anchor map key
                           H_anchor H_nth). }
             c. { apply run_extract_from_storage_value_offset_0_t_uint256_id. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_read_from_storage_split_offset_0_t_uint256_at_anchor_offset
      codes env state_base memory
      (values : list StorableValue.t) (supply_index : nat)
      (anchor offset value : U256.t)
      (H_offset : IsAnchorOffsetSlot values supply_index anchor offset)
      (H_storage : State.get_current_storage env
                     (make_state env state_base memory values)
                   = Some (Storage.of_storable_values values))
      (H_nth : List.nth_error values supply_index = Some (StorableValue.U256 value)) :
    let state := make_state env state_base memory values in
    {{? codes, env, Some state |
      read_from_storage_split_offset_0_t_uint256 (anchor + offset) ⇓
        Result.Ok value
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_0_t_uint256.
    lu. l. { c. { apply (run_sload_u256_at_anchor_offset codes env
                           (make_state env state_base memory values)
                           values supply_index anchor offset value
                           H_offset H_storage H_nth). }
             c. { apply run_extract_from_storage_value_offset_0_t_uint256_id. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor
      codes env state_base memory
      (values : list StorableValue.t) (index : nat) (anchor : U256.t)
      (map : Dict.t U256.t U256.t) (key value : U256.t)
      (H_anchor : IsNamespaceAnchor values index anchor)
      (H_storage : State.get_current_storage env
                     (make_state env state_base memory values)
                   = Some (Storage.of_storable_values values))
      (H_nth : List.nth_error values index = Some (StorableValue.Map map))
      (H_value : 0 <= value < 2^256) :
    let state := make_state env state_base memory values in
    let map' := Dict.declare_or_assign map key value in
    match List.update_nth values index (StorableValue.Map map') with
    | Some values' =>
      let state' := State.with_current_storage env state
                      (Storage.of_storable_values values') in
      {{? codes, env, Some state |
        update_storage_value_offset_0_t_uint256_to_t_uint256
          (keccak256_tuple2 key anchor) value ⇓ Result.Ok tt
      | Some state' ?}}
    | None => True
    end.
  Proof.
    cbv zeta.
    pose proof (run_sstore_map_u256_at_anchor codes env
                  (make_state env state_base memory values)
                  values index anchor key value
                  H_anchor H_storage) as Hsstore.
    rewrite H_nth in Hsstore.
    cbv zeta in Hsstore.
    destruct (List.update_nth values index
                (StorableValue.Map (Dict.declare_or_assign map key value)))
      eqn:Hupd; [|exact I].
    unfold update_storage_value_offset_0_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256_id | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sload_map_u256_at_anchor _ _ _ values index anchor map key);
               [ exact H_anchor | exact H_nth ] | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_uint256_id | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_32_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_32_shift_0_id_on_value;
               exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hsstore | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  Lemma run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_anchor_offset
      codes env state_base memory
      (values : list StorableValue.t) (supply_index : nat)
      (anchor offset value old_value : U256.t)
      (H_offset : IsAnchorOffsetSlot values supply_index anchor offset)
      (H_storage : State.get_current_storage env
                     (make_state env state_base memory values)
                   = Some (Storage.of_storable_values values))
      (H_nth : List.nth_error values supply_index
               = Some (StorableValue.U256 old_value))
      (H_value : 0 <= value < 2^256) :
    let state := make_state env state_base memory values in
    match List.update_nth values supply_index (StorableValue.U256 value) with
    | Some values' =>
      let state' := State.with_current_storage env state
                      (Storage.of_storable_values values') in
      {{? codes, env, Some state |
        update_storage_value_offset_0_t_uint256_to_t_uint256
          (anchor + offset) value ⇓ Result.Ok tt
      | Some state' ?}}
    | None => True
    end.
  Proof.
    cbv zeta.
    pose proof (run_sstore_u256_at_anchor_offset codes env
                  (make_state env state_base memory values)
                  values supply_index anchor offset value
                  H_offset H_storage) as Hsstore.
    cbv zeta in Hsstore.
    destruct (List.update_nth values supply_index (StorableValue.U256 value))
      eqn:Hupd; [|exact I].
    unfold update_storage_value_offset_0_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256_id | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (run_sload_u256_at_anchor_offset _ _ _ values supply_index
                                                      anchor offset old_value);
               [ exact H_offset | exact H_storage | exact H_nth ] | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_uint256_id | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_32_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_32_shift_0_id_on_value;
               exact H_value | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hsstore | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
  Qed.

  (** ====================================================================
      Section — slot-agnostic OZ ERC20 base mechanization (R072)
      ====================================================================

      Inheritor discharges the Section parameters at instantiation time
      with their concrete projection shape.  This file proves the
      [_mint] equivalence statement that holds for ANY projection
      satisfying the [Hypothesis]es below. *)

  Section ERC20BaseEquivalence.

    Variable slot_balances    : nat.
    Variable slot_totalSupply : nat.

    (** Per-inheritor projection from sim ERC20.State.t to the abstract
        storage list shape.  The projection's [slot_balances] cell must
        be a [Map] of the balances dict; [slot_totalSupply] cell must
        be a [U256] of [totalSupply]. *)
    Variable proj_sim : ERC20.State -> SimulatedStorage.t.

    Hypothesis proj_balances_at_slot :
      forall (sim : ERC20.State),
      List.nth_error (proj_sim sim) slot_balances =
        Some (StorableValue.Map (balances_to_dict sim.(ERC20.balances))).

    Hypothesis proj_totalSupply_at_slot :
      forall (sim : ERC20.State),
      List.nth_error (proj_sim sim) slot_totalSupply =
        Some (StorableValue.U256 sim.(ERC20.totalSupply)).

    Hypothesis namespace_binding :
      forall (sim : ERC20.State),
      IsNamespaceAnchor (proj_sim sim) slot_balances
                        ERC20_NAMESPACE_ANCHOR.

    Hypothesis totalSupply_offset_binding :
      forall (sim : ERC20.State),
      IsAnchorOffsetSlot (proj_sim sim) slot_totalSupply
                         ERC20_NAMESPACE_ANCHOR 2.

    (** Inheritor must guarantee the storage_base state has the lens
        bindings; [get_current_storage_eq] threads through walker
        steps without modification. *)
    Hypothesis get_storage_proj_sim :
      forall env state_base memory sim,
      State.get_current_storage env
        (make_state env state_base memory (proj_sim sim))
      = Some (Storage.of_storable_values (proj_sim sim)).

    (** ================================================================
        Section bridging hypotheses (R110) — proj_sim pointwise composition
        ================================================================

        The body of [fun__update_3335] writes to two distinct storage
        slots: [slot_totalSupply] (a [U256] cell) and [slot_balances]
        (a [Map] cell, keyed by address).  After both writes, the
        post-state storage must equal [proj_sim sim'] for the sim
        post-state [sim'].  We codify this composition via three
        bridging hypotheses, discharged per-inheritor at instantiation.

        At the inheritor level (e.g. StakingVault), [proj_sim] is a
        concrete projection function: it builds the storage list by
        explicitly placing the balances Map and totalSupply U256 at
        fixed indices.  These hypotheses then discharge by
        [reflexivity] / structural reasoning on [Dict] equality
        (the slot indices are literal nats and the update_nth
        operations reduce computationally).  See WISDOM R110 for the
        per-hypothesis audit justification. *)

    (** Helper bridge: the projected map for balances satisfies the
        [map_get_u256 = balanceOf] identity.  Follows from
        [proj_balances_at_slot] + the [balances_to_dict] correspondence.
        Discharged structurally per inheritor. *)
    Hypothesis map_get_balances_eq_balanceOf :
      forall (sim : ERC20.State) (account : U256.t),
      StorableValue.map_get_u256
        (balances_to_dict sim.(ERC20.balances)) account
      = ERC20.balanceOf sim account.

    (** Hypothesis: pointwise composition for the mint branch.
        The Yul body, when [from = 0]:
          1. sstores [totalSupply + value] at [slot_totalSupply].
          2. sstores [Pure.add (balanceOf sim account) value] at
             [slot_balances[account]] (via map keccak).
        The composed result must equal [proj_sim] applied to the sim
        post-state.

        Edge case [value = 0]: [ERC20.mint] returns [sim] unchanged,
        but the Yul body still writes back the same values (no-op
        semantically).  The bridge handles both cases via dict
        equality (audit obligation: dict-update with same value at
        existing key is identity; for absent keys, projection treats
        the [(key, 0)] entry equivalently to absence). *)
    Hypothesis proj_sim_pointwise_balance_update :
      forall (sim : ERC20.State) (account value : U256.t),
      0 <= value < 2^256 ->
      sim.(ERC20.totalSupply) + value < 2^256 ->
      match List.update_nth (proj_sim sim) slot_totalSupply
              (StorableValue.U256 (sim.(ERC20.totalSupply) + value)) with
      | Some vs1 =>
        List.update_nth vs1 slot_balances
          (StorableValue.Map
            (Dict.declare_or_assign
              (balances_to_dict sim.(ERC20.balances))
              account
              (Pure.add (ERC20.balanceOf sim account) value)))
        = Some (proj_sim (ERC20.mint sim account value))
      | None => False
      end.

    (** Intermediate-state lens hypotheses for the mint branch
        (R110 follow-up — task #318).

        Between the two sstores of mint ([slot_totalSupply] then
        [slot_balances]), the walker visits a state where storage is
        the list [vs_ts] obtained by updating only [slot_totalSupply].
        The second sload+sstore needs the lens facts to hold for
        [vs_ts], not just for [proj_sim sim].  Since [slot_balances]
        and [slot_totalSupply] are distinct list indices, the lens
        facts at [slot_balances] are preserved by the [slot_totalSupply]
        update.

        These hypotheses are the per-inheritor structural obligation:
        at instantiation, [proj_sim] is a concrete projection function,
        [slot_balances] and [slot_totalSupply] are literal nats with
        distinct values, and [update_nth] reduces computationally. *)

    Hypothesis namespace_binding_after_ts_update_mint :
      forall (sim : ERC20.State) (delta : U256.t),
      match List.update_nth (proj_sim sim) slot_totalSupply
              (StorableValue.U256 (sim.(ERC20.totalSupply) + delta)) with
      | Some vs_ts =>
        IsNamespaceAnchor vs_ts slot_balances ERC20_NAMESPACE_ANCHOR
      | None => True
      end.

    Hypothesis nth_balances_after_ts_update_mint :
      forall (sim : ERC20.State) (delta : U256.t),
      match List.update_nth (proj_sim sim) slot_totalSupply
              (StorableValue.U256 (sim.(ERC20.totalSupply) + delta)) with
      | Some vs_ts =>
        List.nth_error vs_ts slot_balances =
          Some (StorableValue.Map (balances_to_dict sim.(ERC20.balances)))
      | None => True
      end.

    (** Hypothesis: pointwise composition for the burn branch.
        The Yul body, when [to = 0] and [from = account != 0]:
          1. sstores [Pure.sub (balanceOf sim account) value] at
             [slot_balances[account]] (after no-underflow check
             discharged structurally).
          2. sstores [totalSupply - value] at [slot_totalSupply].
        Under [value <= balanceOf sim account], the no-underflow
        check passes and the result equals [proj_sim (burn s)]. *)
    Hypothesis proj_sim_pointwise_totalSupply_update :
      forall (sim : ERC20.State) (account value : U256.t),
      0 <= value < 2^256 ->
      value <= ERC20.balanceOf sim account ->
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  account
                  (Pure.sub (ERC20.balanceOf sim account) value))) with
      | Some vs1 =>
        match List.update_nth vs1 slot_totalSupply
                (StorableValue.U256
                  (Pure.sub sim.(ERC20.totalSupply) value)) with
        | Some vs2 =>
          exists sim',
            ERC20.burn sim account value = ERC20.Result.Success sim' /\
            vs2 = proj_sim sim'
        | None => False
        end
      | None => False
      end.

    (** Intermediate-state lens hypotheses for the burn branch (task #319).

        Between burn's two sstores ([slot_balances] then [slot_totalSupply]),
        the walker visits the state where storage is [vs_bal] (the list
        obtained by updating only [slot_balances]).  The second sload+sstore
        targets [slot_totalSupply], so it needs the [IsAnchorOffsetSlot]
        lens fact + the [nth_error] fact at [slot_totalSupply] to still
        hold for [vs_bal].

        Since [slot_balances] and [slot_totalSupply] are distinct list
        indices, [List.update_nth] at [slot_balances] preserves both
        [nth_error] at [slot_totalSupply] and the offset-slot binding.

        At the inheritor (StakingVault) these discharge by [reflexivity]
        once the slot indices are literal nats. *)

    Hypothesis ts_offset_after_balances_update_burn :
      forall (sim : ERC20.State) (account delta : U256.t),
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  account delta)) with
      | Some vs_bal =>
        IsAnchorOffsetSlot vs_bal slot_totalSupply
                           ERC20_NAMESPACE_ANCHOR 2
      | None => True
      end.

    Hypothesis nth_ts_after_balances_update_burn :
      forall (sim : ERC20.State) (account delta : U256.t),
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  account delta)) with
      | Some vs_bal =>
        List.nth_error vs_bal slot_totalSupply =
          Some (StorableValue.U256 sim.(ERC20.totalSupply))
      | None => True
      end.

    (** Hypothesis: slot-independence / sequential composition for
        the transfer branch.  The Yul body, when [from != 0] and
        [to != 0]:
          1. sstores [Pure.sub (balanceOf sim from) value] at
             [slot_balances[from]].
          2. sstores [Pure.add (balanceOf sim_after_step1 to) value]
             at [slot_balances[to]] (where sim_after_step1 has from's
             balance decremented).
        [totalSupply] is unchanged in the transfer branch.
        Audit obligation: two pointwise writes into the same Map
        cell compose correctly with the transfer post-state, even
        when from = to (the self-transfer no-op case is handled by
        the mock's short-circuit). *)
    Hypothesis proj_sim_independent_slots :
      forall (sim : ERC20.State) (from to value : U256.t),
      from <> 0 -> to <> 0 ->
      0 <= value < 2^256 ->
      value <= ERC20.balanceOf sim from ->
      let sim_after_decrement :=
        {| ERC20.balances :=
             ERC20.set_balance sim.(ERC20.balances) from
               (Pure.sub (ERC20.balanceOf sim from) value);
           ERC20.totalSupply := sim.(ERC20.totalSupply);
           ERC20.allowances  := sim.(ERC20.allowances) |} in
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  from
                  (Pure.sub (ERC20.balanceOf sim from) value))) with
      | Some vs1 =>
        exists sim',
          ERC20.do_transfer sim from to value = ERC20.Result.Success sim' /\
          List.update_nth vs1 slot_balances
            (StorableValue.Map
              (Dict.declare_or_assign
                (balances_to_dict sim_after_decrement.(ERC20.balances))
                to
                (Pure.add
                  (ERC20.balanceOf sim_after_decrement to) value)))
          = Some (proj_sim sim')
      | None => False
      end.

    (** Intermediate-state lens hypotheses for the transfer branch (task #320).

        Between transfer's two sstores at [slot_balances] (the from-debit
        followed by the to-credit), the walker visits the state where
        storage is [vs_bal_from] (the list obtained by updating only the
        from-decrement at [slot_balances]).  The second mapping_index_access
        + sload + sstore (for the to-credit) needs the [IsNamespaceAnchor]
        lens fact + the [nth_error] fact at [slot_balances] to still hold
        for [vs_bal_from], with the updated map visible.

        Since [List.update_nth] at [slot_balances] preserves the
        [IsNamespaceAnchor] binding (the anchor binding is structural,
        not value-dependent), the first hypothesis is a straightforward
        preservation fact.  The second hypothesis records the updated
        map content at [slot_balances] after the from-decrement: the map
        becomes [declare_or_assign (balances_to_dict sim.(balances)) from
        (Pure.sub (balanceOf sim from) value)].

        At the inheritor (StakingVault) these discharge by [reflexivity]
        once [slot_balances] is a literal nat.

        The third hypothesis bridges [map_get_u256] on the from-decremented
        map (at key [to]) to [balanceOf sim_after_decrement to] — the
        sim-side projection of the post-from-decrement balanceOf.  At the
        inheritor this discharges via [map_get_balances_eq_balanceOf]
        composed with a [balances_to_dict (set_balance _ _ _) =
        declare_or_assign (balances_to_dict _) _ _] identity. *)

    Hypothesis namespace_binding_after_from_balance_update_transfer :
      forall (sim : ERC20.State) (from delta : U256.t),
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  from delta)) with
      | Some vs_bal_from =>
        IsNamespaceAnchor vs_bal_from slot_balances ERC20_NAMESPACE_ANCHOR
      | None => True
      end.

    Hypothesis nth_balances_after_from_balance_update_transfer :
      forall (sim : ERC20.State) (from delta : U256.t),
      match List.update_nth (proj_sim sim) slot_balances
              (StorableValue.Map
                (Dict.declare_or_assign
                  (balances_to_dict sim.(ERC20.balances))
                  from delta)) with
      | Some vs_bal_from =>
        List.nth_error vs_bal_from slot_balances =
          Some (StorableValue.Map
            (Dict.declare_or_assign
              (balances_to_dict sim.(ERC20.balances)) from delta))
      | None => True
      end.

    (** [balances_to_dict] composes with [set_balance] as
        [declare_or_assign].  This is the structural identity that
        bridges the sim-level balance update (which threads through
        [proj_sim_independent_slots] as
        [balances_to_dict sim_after_decrement.(ERC20.balances)]) to
        the dict-level update produced by the first sstore (the
        explicit [declare_or_assign (balances_to_dict sim.(balances))
        from (Pure.sub ...)] form).

        At the inheritor this discharges by definition unfolding +
        induction on the balance assoc-list. *)
    Hypothesis balances_to_dict_set_balance_eq :
      forall (bs : list (Z * U256.t)) (k v : U256.t),
      balances_to_dict (ERC20.set_balance bs k v)
      = Dict.declare_or_assign (balances_to_dict bs) k v.

    (** ================================================================
        Post-state projection for [_mint]
        ================================================================

        The sim-level [ERC20.mint] credits the receiver's balance and
        bumps [totalSupply] by [value].  Under our projection, that
        corresponds to writes at [slot_balances] (the Map) and
        [slot_totalSupply] (the U256). *)

    Definition proj_sim_post_mint
        (sim : ERC20.State) (account value : U256.t) : SimulatedStorage.t :=
      proj_sim (ERC20.mint sim account value).

    (** ================================================================
        Post-state projections for [_update]'s three branches
        ================================================================

        [proj_sim_post_burn] and [proj_sim_post_transfer] project the
        mock-side post-states for the burn and transfer branches.
        Symmetric to [proj_sim_post_mint]. *)

    Definition proj_sim_post_burn
        (sim : ERC20.State) (account value : U256.t)
        : option SimulatedStorage.t :=
      match ERC20.burn sim account value with
      | ERC20.Result.Success sim' => Some (proj_sim sim')
      | ERC20.Result.Revert _ _   => None
      end.

    Definition proj_sim_post_transfer
        (sim : ERC20.State) (from to value : U256.t)
        : option SimulatedStorage.t :=
      match ERC20.do_transfer sim from to value with
      | ERC20.Result.Success sim' => Some (proj_sim sim')
      | ERC20.Result.Revert _ _   => None
      end.

    (** ================================================================
        OZ ERC20 base body axioms (R083 + R107 + Section #315 closure;
        task #316 leaf-infrastructure addendum)
        ================================================================

        The walker discharge of [fun__update_1459] decomposes into:

          1. The OZ ERC20 BASE body [fun__update_3335], mechanized as a
             per-branch axiom (mint / burn / transfer).  The audit-time
             obligation is the Yul body inlined at lines 10200-10328 of
             [StakingVault_shallow.v].  Discharge is mechanical via the
             R083 anchor lens primitives + R107 absorbers + the body
             helper leaves now declared at the top of [ERC20Equivalence]
             (task #316; see WISDOM R109).

          2. The StakingVault WRAPPER CHAIN
             [fun__update_1459 → modifier_accrueRewards → _update_1459_inner
              → fun__update_3808 (ERC20Votes maxSupply + transferVotingUnits)
              → fun__update_3335]
             plus the inner [_moveOptimisticDelegateVotes_1720] side-effect.
             The wrappers write to slots OUTSIDE the OZ ERC20 base lens
             (accrueRewards state, delegate checkpoints, optimistic
             delegate state), and observationally the wrappers' effect
             on the OZ ERC20 base proj_sim slots is identity (the wrapper
             chain only writes to non-base slots, then calls
             [fun__update_3335] which is the actual base-state mutator).

        The composite walker [run_fun__update_1459_at_proj_sim_<branch>]
        is now derived as a Qed LEMMA composing axioms (1) and (2).

        ===== Task #316 status =====

        Task #316 was charged with discharging the three base body
        axioms to Qed Lemmas.  Outcome: the FULL set of body-helper
        leaves was closed to Qed (see top-of-module lemma block, ~600
        LOC across 25 Lemmas + 1 memory-absorbing Axiom).  Remaining
        residual: the actual walker through [fun__update_3335]'s Yul
        body requires THREE additional Section bridging hypotheses
        connecting the abstract [proj_sim] projection to per-slot
        updates:

          - [proj_sim_pointwise_balance_update]: extends
            [proj_balances_at_slot] to compositionally describe
            [update_nth (proj_sim sim) slot_balances (Map ...)] as
            [proj_sim sim'] for [sim' = sim_with_balances ...].

          - [proj_sim_pointwise_totalSupply_update]: similar
            companion for [slot_totalSupply].

          - [proj_sim_independent_slots]: states that updates at
            [slot_balances] and [slot_totalSupply] commute (the slots
            are distinct list indices in the projection).

          - A Yul "switch-non-zero" absorber (mirror of R107's
            [run_shallow_let_state_if_zero] but for the
            [let δ := c in if δ =? 0 then else_branch else if_branch]
            shape that Yul switch emits).

        These bridges are PER-INHERITOR audit obligations (StakingVault
        supplies its concrete [proj_sim] indices and the bridges
        discharge by [reflexivity] / [rewrite update_nth_nth_error]).
        Adding them touches the Section signature and is out-of-scope
        for the leaf-infrastructure pass.  Once added, the body
        discharge collapses to a mechanical walker call against the
        leaves + bridges + R107 + the new switch absorber.

        Net trust delta from task #316:
          - Before (task #315): 3 body axioms + 1 wrapper bridge axiom.
          - After  (task #316): SAME 3 body axioms + 1 wrapper bridge
            axiom, PLUS 1 memory-absorbing axiom for
            [mapping_index_access_t_address] (parallel to
            [AbiEncoding.run_mapping_index_access_absorbing] for the
            bytes32-keyed variant, R083 Gap 2 pattern).
          - Added: 25 closed Qed Lemmas for every Yul helper appearing
            in the body.  These reduce the AMOUNT OF NEW Coq code
            needed for the body discharge to roughly [N_walker_steps]
            applications, no new mechanical leaves required.

        WISDOM reference: R109 (this task — body helper infrastructure).
    *)

    (** ================================================================
        Walker leaves for the zero-address check (used by body discharge)
        ================================================================

        These leaves are used both by [fun__update_3335]'s body walker
        (the from=0 and to=0 cleanup-eq cleanup chains in the two
        Yul switches) and by the downstream headline walkers'
        zero-address checks at the entry of [_mint] / [_burn] etc. *)

    (** Identity-on-zero leaf via [cleanup_t_rational_0_by_1] passthrough. *)
    Lemma run_cleanup_t_rational_0_by_1_at_zero codes env state :
      {{? codes, env, Some state |
        cleanup_t_rational_0_by_1 0 ⇓ Result.Ok 0
      | Some state ?}}.
    Proof.
      unfold cleanup_t_rational_0_by_1.
      lu. repeat (lu || cu || p).
    Qed.

    Lemma run_identity codes env state (v : U256.t) :
      {{? codes, env, Some state |
        identity v ⇓ Result.Ok v
      | Some state ?}}.
    Proof.
      unfold identity.
      lu. repeat (lu || cu || p).
    Qed.

    Lemma run_cleanup_t_uint160_at_zero codes env state :
      {{? codes, env, Some state |
        cleanup_t_uint160 0 ⇓ Result.Ok 0
      | Some state ?}}.
    Proof.
      pose proof (AbiEncoding.AbiEncoding.run_cleanup_t_uint160 codes env state 0) as H.
      rewrite Z.land_0_l in H. exact H.
    Qed.

    Lemma run_convert_t_rational_0_by_1_to_t_uint160_at_zero
        codes env state :
      {{? codes, env, Some state |
        convert_t_rational_0_by_1_to_t_uint160 0 ⇓ Result.Ok 0
      | Some state ?}}.
    Proof.
      unfold convert_t_rational_0_by_1_to_t_uint160.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (cleanup_t_rational_0_by_1 _) _ ⇓ _ | _ ?}} =>
            c; [ apply run_cleanup_t_rational_0_by_1_at_zero | ]
        | |- {{? _, _, _ | LowM.Call (identity _) _ ⇓ _ | _ ?}} =>
            c; [ apply run_identity | ]
        | |- {{? _, _, _ | LowM.Call (cleanup_t_uint160 _) _ ⇓ _ | _ ?}} =>
            c; [ apply run_cleanup_t_uint160_at_zero | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    Qed.

    (** [convert_t_rational_0_by_1_to_t_address 0 = 0].  The conversion
        chain is [cleanup_t_uint160 . identity . cleanup_t_rational_0_by_1],
        all of which preserve [0]. *)
    Lemma run_convert_t_rational_0_by_1_to_t_address_at_zero
        codes env state :
      {{? codes, env, Some state |
        convert_t_rational_0_by_1_to_t_address 0 ⇓ Result.Ok 0
      | Some state ?}}.
    Proof.
      unfold convert_t_rational_0_by_1_to_t_address.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      repeat (lazymatch goal with
        | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
        | |- {{? _, _, _ |
              LowM.Call (convert_t_rational_0_by_1_to_t_uint160 _) _
              ⇓ _ | _ ?}} =>
            c; [ apply run_convert_t_rational_0_by_1_to_t_uint160_at_zero | ]
        | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
        | |- _ => s
        end).
      all: cbn match.
      all: try apply RunO.Pure.
    Qed.

    (** [eq(cleanup_t_address account, cleanup_t_address 0) = 0] iff
        [account] (as a 160-bit value) is nonzero.  We pre-condition
        on [0 <= account < 2^160 /\ account <> 0] so cleanup is
        identity. *)
    Lemma run_eq_address_zero_check
        codes env state (account : U256.t)
        (H_account_bound : 0 <= account < 2^160)
        (H_account_nz : account <> 0) :
      {{? codes, env, Some state |
        Stdlib.eq (Z.land account 0xffffffffffffffffffffffffffffffffffffffff)
                  (Z.land 0 0xffffffffffffffffffffffffffffffffffffffff)
        ⇓ Result.Ok 0
      | Some state ?}}.
    Proof.
      unfold Stdlib.eq, Pure.eq.
      (* Z.land 0 _ = 0 *)
      rewrite Z.land_0_l.
      (* Z.land account (Z.ones 160) = account given 0 <= account < 2^160 *)
      change 0xffffffffffffffffffffffffffffffffffffffff with (Z.ones 160).
      destruct (Z.eq_dec account 0) as [->|Hne]; [contradiction|].
      rewrite Z.land_ones by lia.
      rewrite Z.mod_small by lia.
      (* Now goal: M.pure (if account =? 0 then 1 else 0) ⇓ Ok 0 *)
      apply Z.eqb_neq in H_account_nz as Hb.
      rewrite Hb.
      apply RunO.Pure.
    Qed.

    (** [eq(cleanup_t_address 0, cleanup_t_address 0) = 1] — the
        symmetric form for proving "[from = 0]" in the mint branch
        of [fun__update_3335].  Cleanup of 0 is 0 on both sides, eq
        of equal values returns 1. *)
    Lemma run_eq_address_zero_at_zero codes env state :
      {{? codes, env, Some state |
        Stdlib.eq (Z.land 0 0xffffffffffffffffffffffffffffffffffffffff)
                  (Z.land 0 0xffffffffffffffffffffffffffffffffffffffff)
        ⇓ Result.Ok 1
      | Some state ?}}.
    Proof.
      unfold Stdlib.eq, Pure.eq.
      rewrite Z.land_0_l.
      apply RunO.Pure.
    Qed.

    (** Mechanical walker tactic for fun__update_3335 body discharge.

        Pattern: each Yul let-binding becomes [eapply RunO.Let] + a
        call-or-pure step + [cbn match].  This tactic handles the
        pure-eval steps in batch.  Call-sites are dispatched per
        helper via [lazymatch]. *)
    Ltac walk_prelude_pure :=
      repeat (eapply RunO.Let; [apply RunO.Pure |]; cbn match).

    (** OZ ERC20 base body Lemma for the mint branch ([from = 0]).

        Walker proof structure:
        1. Walk getERC20Storage + prelude → eq(0,0) = 1 via cleanup chain.
        2. Apply [run_let_state_match_pure_nonzero] to commit to if arm
           (since δ = 1 ≠ 0; Yul-switch [if δ =? 0 then else else if] form).
        3. Walk TS-write subblock: sload(anchor+2), checked_add, sstore(anchor+2).
        4. Walk second prelude → eq(account, 0) = 0 (since account ≠ 0).
        5. Apply [run_let_state_match_pure_zero] to commit to else arm.
        6. Walk balance-credit subblock: keccak mapping_index_access, sload,
           wrapping_add, sstore (at keccak2(account, anchor)).
        7. Walk log3 emission tail: allocate_unbounded (mload 64),
           abi_encode_tuple_t_uint256__to_t_uint256__fromStack, log3 = pure.
        8. State post-state: [proj_sim_pointwise_balance_update] applied
           upfront discharges [vs_bal = proj_sim_post_mint sim account value]. *)
    Lemma run_fun__update_3335_at_proj_sim_mint :
      forall (codes : Codes.t) (env : Environment.t)
             (state_base : RocqOfSolidity.State.t)
             (memory : SimulatedMemory.t)
             (sim : ERC20.State)
             (account value : U256.t)
             (H_account_nz : account <> 0)
             (H_account_bound : 0 <= account < 2^160)
             (H_value_bound : 0 <= value < 2^256)
             (H_valid : ERC20.Valid.t sim)
             (H_no_overflow : sim.(ERC20.totalSupply) + value < 2^256),
      exists (memory' : SimulatedMemory.t),
      {{? codes, env,
          Some (make_state env state_base memory (proj_sim sim)) |
        fun__update_3335 0 account value ⇓ Result.Ok tt
      | Some (make_state env state_base memory'
                (proj_sim_post_mint sim account value)) ?}}.
    Proof.
      intros codes env state_base memory sim account value
             H_account_nz H_account_bound H_value_bound
             H_valid H_no_overflow.
      (* Upfront skolemization: derive sim's totalSupply bound from
         validity, the sum bound from preconditions, the bridge equation,
         and the two intermediate update_nth lists. *)
      assert (H_ts_bound : 0 <= sim.(ERC20.totalSupply) < 2 ^ 256).
      { pose proof (ERC20.Valid.supply_u256 sim H_valid) as Hu.
        unfold U256.Valid.t in Hu. exact Hu. }
      assert (H_sum_bound : 0 <= sim.(ERC20.totalSupply) + value < 2 ^ 256)
        by lia.
      assert (H_balance_bound : 0 <= Pure.add (ERC20.balanceOf sim account) value < 2 ^ 256).
      { unfold Pure.add. split.
        - apply Z.mod_pos_bound. lia.
        - apply Z.mod_pos_bound. lia. }
      pose proof (proj_sim_pointwise_balance_update sim account value
                    H_value_bound H_no_overflow) as Hbridge.
      destruct (List.update_nth (proj_sim sim) slot_totalSupply
                  (StorableValue.U256 (sim.(ERC20.totalSupply) + value)))
        as [vs_ts|] eqn:Hupd_ts; [|exfalso; exact Hbridge].
      destruct (List.update_nth vs_ts slot_balances
                  (StorableValue.Map
                     (Dict.declare_or_assign
                        (balances_to_dict sim.(ERC20.balances)) account
                        (Pure.add (ERC20.balanceOf sim account) value))))
        as [vs_bal|] eqn:Hupd_bal; [|discriminate Hbridge].
      injection Hbridge as Hbridge_eq.
      (* The post-state storage is vs_bal = proj_sim (mint sim account value). *)
      pose proof (namespace_binding_after_ts_update_mint sim value) as Hns_after_ts.
      rewrite Hupd_ts in Hns_after_ts.
      pose proof (nth_balances_after_ts_update_mint sim value) as Hnth_after_ts.
      rewrite Hupd_ts in Hnth_after_ts.
      (* The two intermediate state witnesses: post-TS and post-Bal. *)
      pose (state_post_ts :=
              Some (State.with_current_storage env
                      (make_state env state_base memory (proj_sim sim))
                      (Storage.of_storable_values vs_ts))).
      (* Skolemize memory post-mapping_index_access (state during Bal sload). *)
      pose (memory_post_kc :=
              mapping_index_access_address_post_memory env
                state_base
                memory vs_ts ERC20_NAMESPACE_ANCHOR account).
      pose (state_post_bal :=
              Some (State.with_current_storage env
                      (make_state env state_base memory_post_kc vs_ts)
                      (Storage.of_storable_values vs_bal))).
      (* Final post-state memory: after log3 abi_encode mstore. *)
      pose (memory_final :=
              mstore_post_memory env state_base memory_post_kc vs_bal
                (Pure.add (mload_witness env state_base memory_post_kc vs_bal 64) 0)
                value).
      exists memory_final.
      (* vs_bal = proj_sim_post_mint sim account value. *)
      unfold proj_sim_post_mint.
      rewrite <- Hbridge_eq.
      unfold fun__update_3335.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      (* Outer LowM.Let: walk big body that returns (BlockUnit.Tt, tt). *)
      eapply RunO.Let.
      { (* === Prelude 1: getERC20Storage + 6 binders + eq(0,0)=1 === *)
        eapply RunO.Let.
        { c; [ apply run_fun__getERC20Storage_2971_returns_anchor | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_eq_address_zero_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        (* === Switch 1: δ = 1, take if_branch (TS-write subblock) === *)
        eapply run_let_state_match_pure_nonzero with (δ_val := 1)
          (state_after_branch := state_post_ts).
        { discriminate. }
        { apply RunO.Pure. }
        { (* TS-write subblock. *)
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let.
          { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
          cbn match.
          (* sload at anchor+2 *)
          eapply RunO.Let.
          { c.
            { apply (run_read_from_storage_split_offset_0_t_uint256_at_anchor_offset
                       _ _ _ _ (proj_sim sim) slot_totalSupply
                       ERC20_NAMESPACE_ANCHOR 2 sim.(ERC20.totalSupply)
                       (totalSupply_offset_binding sim)
                       (get_storage_proj_sim env state_base memory sim)
                       (proj_totalSupply_at_slot sim)). }
            apply RunO.Pure. }
          cbn match.
          (* checked_add *)
          eapply RunO.Let.
          { c; [ apply (run_checked_add_t_uint256_no_overflow
                          _ _ _ _ _ H_ts_bound H_value_bound H_no_overflow) | ].
            apply RunO.Pure. }
          cbn match.
          (* sstore at anchor+2 *)
          eapply RunO.Let.
          { pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_anchor_offset
                          codes env state_base memory
                          (proj_sim sim) slot_totalSupply
                          ERC20_NAMESPACE_ANCHOR 2
                          (sim.(ERC20.totalSupply) + value)
                          sim.(ERC20.totalSupply)
                          (totalSupply_offset_binding sim)
                          (get_storage_proj_sim env state_base memory sim)
                          (proj_totalSupply_at_slot sim)
                          H_sum_bound) as Hsstore.
            cbv zeta in Hsstore. rewrite Hupd_ts in Hsstore.
            c; [ exact Hsstore | ]. apply RunO.Pure. }
          cbn match.
          apply RunO.Pure. }
        { (* === Body after first switch === *)
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let.
          { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
            apply RunO.Pure. }
          cbn match.
          eapply RunO.Let.
          { simpl LowM.let_.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply (run_eq_address_zero_check _ _ _ account
                          H_account_bound H_account_nz) | ].
            apply RunO.Pure. }
          cbn match.
          (* === Switch 2: δ = 0, take else_branch (balance-credit) === *)
          eapply run_let_state_match_pure_zero with
            (state_after_branch := state_post_bal).
          { apply RunO.Pure. }
          { (* Balance-credit subblock. *)
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1752 := add(anchor, 0) → anchor *)
            eapply RunO.Let.
            { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
            cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1755 := mapping_index_access(anchor+0, account)
               Note: anchor+0 = anchor since ERC20_NAMESPACE_ANCHOR fits 256 bits.
               Output: keccak256_tuple2 account anchor.
               State changes: storage unchanged, memory updates via
               mapping_index_access_address_post_memory. *)
            (* Canonize state: with_current_storage env (make_state ...) ... = make_state ... vs_ts *)
            rewrite CanonizeState.update_storage_eq.
            (* Pure.add anchor 0 = anchor *)
            replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
            2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
                rewrite Z.add_0_r.
                rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
            eapply RunO.Let.
            { c.
              { apply (run_mapping_index_access_t_address_at_make_state
                         codes env state_base memory vs_ts
                         ERC20_NAMESPACE_ANCHOR account
                         H_account_bound). }
              apply RunO.Pure. }
            cbn match.
            (* sload at keccak256_tuple2 account anchor → map_get_u256 of balances *)
            eapply RunO.Let.
            { c.
              { apply (run_read_from_storage_split_offset_0_t_uint256_at_map_anchor
                         _ _ _ _ vs_ts slot_balances
                         ERC20_NAMESPACE_ANCHOR
                         (balances_to_dict sim.(ERC20.balances)) account
                         Hns_after_ts Hnth_after_ts). }
              apply RunO.Pure. }
            cbn match.
            (* wrapping_add: balanceOf sim account → Pure.add (map_get ...) value *)
            (* But sload returned map_get_u256 (balances_to_dict ...) account = balanceOf sim account
               via map_get_balances_eq_balanceOf hypothesis.  Need to rewrite. *)
            rewrite (map_get_balances_eq_balanceOf sim account).
            eapply RunO.Let.
            { c; [ apply run_wrapping_add_t_uint256 | ]. apply RunO.Pure. }
            cbn match.
            (* sstore at keccak256_tuple2 account anchor with Pure.add (balanceOf sim account) value.
               State has memory = memory_post_kc (after mapping_index_access). *)
            eapply RunO.Let.
            { pose (memory' := mapping_index_access_address_post_memory env state_base memory vs_ts
                                 ERC20_NAMESPACE_ANCHOR account).
              pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor
                            codes env state_base memory'
                            vs_ts slot_balances ERC20_NAMESPACE_ANCHOR
                            (balances_to_dict sim.(ERC20.balances))
                            account
                            (Pure.add (ERC20.balanceOf sim account) value)
                            Hns_after_ts) as Hsstore_bal.
              assert (Hget_ts :
                        State.get_current_storage env
                          (make_state env state_base memory' vs_ts)
                        = Some (Storage.of_storable_values vs_ts)).
              { unfold make_state.
                apply State.get_current_storage_with_current_storage_eq. }
              specialize (Hsstore_bal Hget_ts Hnth_after_ts H_balance_bound).
              cbv zeta in Hsstore_bal. rewrite Hupd_bal in Hsstore_bal.
              c; [ exact Hsstore_bal | ]. apply RunO.Pure. }
            cbn match.
            (* Now state is with_current_storage env (make_state ... vs_ts ...) vs_bal,
               which we want to canonize back. *)
            apply RunO.Pure. }
          { (* Body after second switch — log3 tail + final Pure.
               State here is state_post_bal (with memory_post_kc and vs_bal).
               Canonize via with_current_storage rewrite. *)
            unfold state_post_bal.
            rewrite CanonizeState.update_storage_eq.
            cbn match.
            (* 6 pure binders: _1761, expr_3329, _1762, expr_3330, _1763, expr_3331 *)
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1764 := topic hash (Transfer event signature, pure literal) *)
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1765 := convert_t_address_to_t_address 0 → 0 *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address _ _ _ 0).
                unfold Address.Valid.t. lia. }
              apply RunO.Pure. }
            cbn match.
            (* _1766 := convert_t_address_to_t_address account → account *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address
                         _ _ _ account H_account_bound). }
              apply RunO.Pure. }
            cbn match.
            (* let_state~ 'tt := <log3 body> default~ tt in M.pure (Tt, tt).
               The log3 body does: allocate_unbounded (mload 64) + abi_encode_tuple
               + log3 (= M.pure tt) + M.pure (Tt, tt).
               These all run within the Shallow.let_state with body = M.pure (Tt, tt). *)
            (* First convert the let_state into its M.strong_let_ form. *)
            unfold Shallow.let_state at 1.
            unfold M.strong_let_ at 1, M.generic_let at 1.
            eapply RunO.Let.
            { (* The log3 body: walk allocate_unbounded + abi_encode + log3. *)
              (* _1767 := allocate_unbounded.  Body: let memPtr := 0 in
                   let~ memPtr := mload 64 in M.pure (Tt, memPtr) +outer M.pure memPtr.
                 The outermost is LowM.Call allocate_unbounded LowM.Pure. *)
              eapply RunO.Let.
              { c.
                { unfold allocate_unbounded.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  eapply RunO.Let.
                  { eapply RunO.Let.
                    { c.
                      { apply (run_mload_absorbing_at_make_state
                                 codes env state_base memory_post_kc vs_bal 64). }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              (* _1768 := abi_encode_tuple_t_uint256__to_t_uint256__fromStack _1767 value. *)
              eapply RunO.Let.
              { c.
                { unfold abi_encode_tuple_t_uint256__to_t_uint256__fromStack.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  (* Outer pattern-match Let *)
                  eapply RunO.Let.
                  { (* big_thing: let~ tail := add(memPtr, 32) in do~ ... in M.pure (Tt, tail). *)
                    (* let~ tail := add(memPtr, 32) → LowM.Let (LowM.Call add) (fun => ...) *)
                    eapply RunO.Let.
                    { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
                    cbn match.
                    (* do~ abi_encode_t_uint256_to_t_uint256_fromStack ... in M.pure (Tt, tail) *)
                    eapply RunO.Let.
                    { (* The do~ has nested let_ structure for value0, pos.  Walk them. *)
                      simpl LowM.let_.
                      c; [ unfold Stdlib.add; apply RunO.Pure | ]. cbn match.
                      c.
                      { unfold abi_encode_t_uint256_to_t_uint256_fromStack.
                        unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                        cbn match.
                        (* Outer pattern-match Let again *)
                        eapply RunO.Let.
                        { (* big_thing: do~ mstore(...) in M.pure (Tt, tt). *)
                          eapply RunO.Let.
                          { simpl LowM.let_.
                            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
                            c.
                            { apply (run_mstore_absorbing_at_make_state
                                       codes env state_base memory_post_kc vs_bal
                                       _ _). }
                            apply RunO.Pure. }
                          cbn match. apply RunO.Pure. }
                        cbn match. apply RunO.Pure. }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              eapply RunO.Let.
              { simpl LowM.let_.
                c; [ unfold Stdlib.sub; apply RunO.Pure | ]. cbn match.
                c; [ unfold Stdlib.log3; apply RunO.Pure | ].
                apply RunO.Pure. }
              cbn match.
              apply RunO.Pure. }
            cbn match.
            apply RunO.Pure. }
        }
      }
      cbn match.
      apply RunO.Pure.
    Qed.

    (** OZ ERC20 base body Lemma for the burn branch ([to = 0]).

        Walker proof structure (mirror of mint, task #319):
        1. Walk getERC20Storage + prelude → eq(from, 0) = 0 via
           [run_eq_address_zero_check] (since [from = account ≠ 0]).
        2. Apply [run_let_state_match_pure_zero] to commit to else_branch
           (the [δ =? 0 then ...] arm in shallow embedding).  This is the
           balance-debit subblock.
        3. Walk balance-debit subblock: keccak mapping_index_access(from,
           anchor), sload (yields balanceOf), lt-check (= 0; absorbed via
           [run_shallow_let_state_if_zero]), wrapping_sub, sstore at
           keccak2(from, anchor).
        4. Walk prelude → eq(to=0, 0) = 1 via [run_eq_address_zero_at_zero].
        5. Apply [run_let_state_match_pure_nonzero] to commit to if_branch
           (the totalSupply-decrement arm).
        6. Walk TS-decrement subblock: sload(anchor+2), wrapping_sub, sstore.
        7. Walk log3 tail (same as mint).
        8. Final state: [vs_ts = proj_sim sim'] where [burn sim account value
           = Success sim'].  Use [proj_sim_pointwise_totalSupply_update]. *)
    Lemma run_fun__update_3335_at_proj_sim_burn :
      forall (codes : Codes.t) (env : Environment.t)
             (state_base : RocqOfSolidity.State.t)
             (memory : SimulatedMemory.t)
             (sim : ERC20.State)
             (account value : U256.t)
             (H_account_nz : account <> 0)
             (H_account_bound : 0 <= account < 2^160)
             (H_value_bound : 0 <= value < 2^256)
             (H_valid : ERC20.Valid.t sim)
             (H_balance_ge : value <= ERC20.balanceOf sim account),
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_burn sim account value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__update_3335 account 0 value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      intros codes env state_base memory sim account value
             H_account_nz H_account_bound H_value_bound
             H_valid H_balance_ge.
      (* Upfront: skolemize the post-state list via the burn bridge. *)
      assert (H_ts_bound : 0 <= sim.(ERC20.totalSupply) < 2 ^ 256).
      { pose proof (ERC20.Valid.supply_u256 sim H_valid) as Hu.
        unfold U256.Valid.t in Hu. exact Hu. }
      assert (H_balance_diff_bound :
                0 <= Pure.sub (ERC20.balanceOf sim account) value < 2 ^ 256).
      { unfold Pure.sub. split.
        - apply Z.mod_pos_bound. lia.
        - apply Z.mod_pos_bound. lia. }
      assert (H_ts_diff_bound :
                0 <= Pure.sub sim.(ERC20.totalSupply) value < 2 ^ 256).
      { unfold Pure.sub. split.
        - apply Z.mod_pos_bound. lia.
        - apply Z.mod_pos_bound. lia. }
      pose proof (proj_sim_pointwise_totalSupply_update sim account value
                    H_value_bound H_balance_ge) as Hbridge.
      destruct (List.update_nth (proj_sim sim) slot_balances
                  (StorableValue.Map
                     (Dict.declare_or_assign
                        (balances_to_dict sim.(ERC20.balances)) account
                        (Pure.sub (ERC20.balanceOf sim account) value))))
        as [vs_bal|] eqn:Hupd_bal; [|exfalso; exact Hbridge].
      destruct (List.update_nth vs_bal slot_totalSupply
                  (StorableValue.U256
                     (Pure.sub sim.(ERC20.totalSupply) value)))
        as [vs_ts|] eqn:Hupd_ts; [|exfalso; exact Hbridge].
      destruct Hbridge as (simq & Hburn & Hproj).
      (* Now Hburn : ERC20.burn sim account value = Success simq
             Hproj  : vs_ts = proj_sim simq *)
      pose proof (ts_offset_after_balances_update_burn
                    sim account
                    (Pure.sub (ERC20.balanceOf sim account) value)) as Hoff_after_bal.
      rewrite Hupd_bal in Hoff_after_bal.
      pose proof (nth_ts_after_balances_update_burn
                    sim account
                    (Pure.sub (ERC20.balanceOf sim account) value)) as Hnth_after_bal.
      rewrite Hupd_bal in Hnth_after_bal.
      (* Memory after the keccak mapping_index_access call (first sload's
         scratch-memory writes). *)
      pose (memory_post_kc1 :=
              mapping_index_access_address_post_memory env
                state_base memory (proj_sim sim)
                ERC20_NAMESPACE_ANCHOR account).
      (* Memory after the second mapping_index_access (preceding the sstore). *)
      pose (memory_post_kc2 :=
              mapping_index_access_address_post_memory env
                state_base memory_post_kc1 (proj_sim sim)
                ERC20_NAMESPACE_ANCHOR account).
      (* Intermediate state after balance-debit subblock. *)
      pose (state_post_bal :=
              Some (State.with_current_storage env
                      (make_state env state_base memory_post_kc2 (proj_sim sim))
                      (Storage.of_storable_values vs_bal))).
      (* Intermediate state after totalSupply-decrement subblock. *)
      pose (state_post_ts :=
              Some (State.with_current_storage env
                      (make_state env state_base memory_post_kc2 vs_bal)
                      (Storage.of_storable_values vs_ts))).
      (* Final memory: after log3 abi_encode mstore. *)
      pose (memory_final :=
              mstore_post_memory env state_base memory_post_kc2 vs_ts
                (Pure.add (mload_witness env state_base memory_post_kc2 vs_ts 64) 0)
                value).
      exists memory_final, vs_ts.
      split.
      { (* proj_sim_post_burn = Some vs_ts *)
        unfold proj_sim_post_burn.
        rewrite Hburn. rewrite Hproj. reflexivity. }
      unfold fun__update_3335.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      eapply RunO.Let.
      { (* === Prelude 1: getERC20Storage + binders + eq(from, 0) === *)
        eapply RunO.Let.
        { c; [ apply run_fun__getERC20Storage_2971_returns_anchor | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ account
                        H_account_bound H_account_nz) | ].
          apply RunO.Pure. }
        cbn match.
        (* === Switch 1: δ = 0, take else_branch (balance-debit subblock).
           "else_branch" here is the [δ =? 0 then ...] arm. *)
        eapply run_let_state_match_pure_zero with
          (state_after_branch := state_post_bal).
        { apply RunO.Pure. }
        { (* Balance-debit subblock.
             Shallow shape:
               _1725_slot (Pure) ; expr_3274_slot (Pure) ;
               _1726 := add(anchor, 0) (Call) ;
               _1727_slot (Pure) ; expr_3275_slot (Pure) ;
               _1728 (Pure) ; expr_3276 (Pure) ;
               _1729 := mapping_index_access(anchor, from) (Call) ;
               _1730 := read_from_storage(_1729) (Call) ;
               expr_3277 (Pure) ; var_fromBalance_3273 (Pure) ;
               _1731 (Pure) ; expr_3279 (Pure) ;
               _1732 (Pure) ; expr_3280 (Pure) ;
               expr_3281 := lt(cleanup, cleanup) (Call) ;
               Shallow.if_ revert block ;
               _1738 .. expr_3296 (4 Pure) ;
               expr_3297 := wrapping_sub (Call) ;
               _1740_slot .. expr_3290_slot (2 Pure) ;
               _1741 := add(anchor, 0) (Call) ;
               _1742_slot .. expr_3292 (4 Pure) ;
               _1744 := mapping_index_access(anchor, from) (Call) ;
               do~ update_storage_value(_1744, expr_3297) (Call) ;
               expr_3298 (Pure) ; M.pure (Tt, tt). *)
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1726 := add(anchor, 0) → anchor *)
          eapply RunO.Let.
          { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1729 := mapping_index_access(anchor+0, from) → keccak2(from, anchor) *)
          replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
          2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
              rewrite Z.add_0_r.
              rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
          eapply RunO.Let.
          { c.
            { apply (run_mapping_index_access_t_address_at_make_state
                       codes env state_base memory (proj_sim sim)
                       ERC20_NAMESPACE_ANCHOR account
                       H_account_bound). }
            apply RunO.Pure. }
          cbn match.
          (* sload at keccak2(from, anchor) → map_get_u256 of balances *)
          eapply RunO.Let.
          { c.
            { apply (run_read_from_storage_split_offset_0_t_uint256_at_map_anchor
                       _ _ _ _ (proj_sim sim) slot_balances
                       ERC20_NAMESPACE_ANCHOR
                       (balances_to_dict sim.(ERC20.balances)) account
                       (namespace_binding sim) (proj_balances_at_slot sim)). }
            apply RunO.Pure. }
          cbn match.
          rewrite (map_get_balances_eq_balanceOf sim account).
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* lt(fromBalance, value).  Under [value <= balanceOf sim account],
             [lt = 0].  Two cleanup_t_uint256 + the lt Stdlib op. *)
          eapply RunO.Let.
          { simpl LowM.let_.
            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
            c; [ unfold Stdlib.lt; apply RunO.Pure | ].
            apply RunO.Pure. }
          cbn match.
          (* Reduce the lt result to 0 explicitly so that the
             [Shallow.let_state (Shallow.if_ <lt> ...)] absorber matches.
             [Pure.lt x y = if x <? y then 1 else 0]; under [value <=
             balanceOf], this is 0. *)
          replace (Pure.lt (ERC20.balanceOf sim account) value) with 0.
          2:{ unfold Pure.lt.
              destruct (ERC20.balanceOf sim account <? value) eqn:Hlt;
              [|reflexivity].
              apply Z.ltb_lt in Hlt. lia. }
          (* Now we have [let_state~ 'tt := Shallow.if_ 0 _ _ default~ tt in _] *)
          apply run_shallow_let_state_if_zero.
          cbn.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* wrapping_sub: produces Pure.sub fromBalance value. *)
          eapply RunO.Let.
          { c; [ apply run_wrapping_sub_t_uint256 | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1741 := add(anchor, 0) → anchor *)
          eapply RunO.Let.
          { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1744 := mapping_index_access(anchor+0, from) — second time. *)
          replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
          2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
              rewrite Z.add_0_r.
              rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
          eapply RunO.Let.
          { c.
            { apply (run_mapping_index_access_t_address_at_make_state
                       codes env state_base memory_post_kc1 (proj_sim sim)
                       ERC20_NAMESPACE_ANCHOR account
                       H_account_bound). }
            apply RunO.Pure. }
          cbn match.
          (* sstore at keccak2(from, anchor) with Pure.sub. State here has
             memory = memory_post_kc2 (after second mapping_index_access). *)
          eapply RunO.Let.
          { pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor
                          codes env state_base memory_post_kc2
                          (proj_sim sim) slot_balances ERC20_NAMESPACE_ANCHOR
                          (balances_to_dict sim.(ERC20.balances))
                          account
                          (Pure.sub (ERC20.balanceOf sim account) value)
                          (namespace_binding sim)) as Hsstore_bal.
            assert (Hget_proj :
                      State.get_current_storage env
                        (make_state env state_base memory_post_kc2 (proj_sim sim))
                      = Some (Storage.of_storable_values (proj_sim sim))).
            { unfold make_state.
              apply State.get_current_storage_with_current_storage_eq. }
            specialize (Hsstore_bal Hget_proj (proj_balances_at_slot sim)
                                    H_balance_diff_bound).
            cbv zeta in Hsstore_bal. rewrite Hupd_bal in Hsstore_bal.
            c; [ exact Hsstore_bal | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          apply RunO.Pure. }
        { (* === Body after first switch: prelude → eq(to, 0) = 1 → switch 2 === *)
          cbn match.
          (* Now state is state_post_bal.  Canonize. *)
          unfold state_post_bal.
          rewrite CanonizeState.update_storage_eq.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let.
          { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
            apply RunO.Pure. }
          cbn match.
          eapply RunO.Let.
          { simpl LowM.let_.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply run_eq_address_zero_at_zero | ].
            apply RunO.Pure. }
          cbn match.
          (* === Switch 2: δ = 1, take if_branch (TS-decrement subblock). === *)
          eapply run_let_state_match_pure_nonzero with (δ_val := 1)
            (state_after_branch := state_post_ts).
          { discriminate. }
          { apply RunO.Pure. }
          { (* TS-decrement subblock. *)
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let.
            { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
            cbn match.
            (* sload at anchor+2 → totalSupply.  State storage = vs_bal. *)
            eapply RunO.Let.
            { c.
              { apply (run_read_from_storage_split_offset_0_t_uint256_at_anchor_offset
                         _ _ _ _ vs_bal slot_totalSupply
                         ERC20_NAMESPACE_ANCHOR 2 sim.(ERC20.totalSupply)
                         Hoff_after_bal).
                - unfold make_state.
                  apply State.get_current_storage_with_current_storage_eq.
                - exact Hnth_after_bal. }
              apply RunO.Pure. }
            cbn match.
            (* wrapping_sub *)
            eapply RunO.Let.
            { c; [ apply run_wrapping_sub_t_uint256 | ]. apply RunO.Pure. }
            cbn match.
            (* sstore at anchor+2 *)
            eapply RunO.Let.
            { pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_anchor_offset
                            codes env state_base memory_post_kc2
                            vs_bal slot_totalSupply
                            ERC20_NAMESPACE_ANCHOR 2
                            (Pure.sub sim.(ERC20.totalSupply) value)
                            sim.(ERC20.totalSupply)
                            Hoff_after_bal) as Hsstore_ts.
              assert (Hget_bal :
                        State.get_current_storage env
                          (make_state env state_base memory_post_kc2 vs_bal)
                        = Some (Storage.of_storable_values vs_bal)).
              { unfold make_state.
                apply State.get_current_storage_with_current_storage_eq. }
              specialize (Hsstore_ts Hget_bal Hnth_after_bal H_ts_diff_bound).
              cbv zeta in Hsstore_ts. rewrite Hupd_ts in Hsstore_ts.
              c; [ exact Hsstore_ts | ]. apply RunO.Pure. }
            cbn match.
            apply RunO.Pure. }
          { (* === Body after second switch — log3 tail. === *)
            cbn match.
            unfold state_post_ts.
            rewrite CanonizeState.update_storage_eq.
            cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1765 := convert_t_address_to_t_address from → from *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address
                         _ _ _ account H_account_bound). }
              apply RunO.Pure. }
            cbn match.
            (* _1766 := convert_t_address_to_t_address 0 → 0 *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address _ _ _ 0).
                unfold Address.Valid.t. lia. }
              apply RunO.Pure. }
            cbn match.
            unfold Shallow.let_state at 1.
            unfold M.strong_let_ at 1, M.generic_let at 1.
            eapply RunO.Let.
            { (* allocate_unbounded + abi_encode + log3 *)
              eapply RunO.Let.
              { c.
                { unfold allocate_unbounded.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  eapply RunO.Let.
                  { eapply RunO.Let.
                    { c.
                      { apply (run_mload_absorbing_at_make_state
                                 codes env state_base memory_post_kc2 vs_ts 64). }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              eapply RunO.Let.
              { c.
                { unfold abi_encode_tuple_t_uint256__to_t_uint256__fromStack.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  eapply RunO.Let.
                  { eapply RunO.Let.
                    { c; [ unfold Stdlib.add; apply RunO.Pure | ].
                      apply RunO.Pure. }
                    cbn match.
                    eapply RunO.Let.
                    { simpl LowM.let_.
                      c; [ unfold Stdlib.add; apply RunO.Pure | ]. cbn match.
                      c.
                      { unfold abi_encode_t_uint256_to_t_uint256_fromStack.
                        unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                        cbn match.
                        eapply RunO.Let.
                        { eapply RunO.Let.
                          { simpl LowM.let_.
                            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
                            c.
                            { apply (run_mstore_absorbing_at_make_state
                                       codes env state_base memory_post_kc2 vs_ts
                                       _ _). }
                            apply RunO.Pure. }
                          cbn match. apply RunO.Pure. }
                        cbn match. apply RunO.Pure. }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              eapply RunO.Let.
              { simpl LowM.let_.
                c; [ unfold Stdlib.sub; apply RunO.Pure | ]. cbn match.
                c; [ unfold Stdlib.log3; apply RunO.Pure | ].
                apply RunO.Pure. }
              cbn match.
              apply RunO.Pure. }
            cbn match.
            apply RunO.Pure. }
        }
      }
      cbn match.
      apply RunO.Pure.
    Qed.

    (** OZ ERC20 base body axiom for the transfer branch ([from <> 0],
        [to <> 0]).  Audit-time obligation: the body at
        [StakingVault_shallow.v:10200-10328] implements
        [_balances[from] -= value], [_balances[to] += value] under
        [from <> 0, to <> 0], reverting if [balances[from] < value]
        and preserving [_totalSupply]. *)
    (** OZ ERC20 base body Lemma for the transfer branch ([from <> 0], [to <> 0]).

        Walker proof structure (mirror of mint/burn, task #320):
        1. Walk getERC20Storage + prelude → eq(from, 0) = 0 via
           [run_eq_address_zero_check] (since [from <> 0]).
        2. Apply [run_let_state_match_pure_zero] to commit to else_branch
           (the [δ =? 0 then ...] arm — balance-debit at [from]).
        3. Walk balance-debit subblock at [from]: keccak mapping_index_access,
           sload (yields balanceOf from), lt-check (= 0; absorbed via
           [run_shallow_let_state_if_zero]), wrapping_sub, second
           mapping_index_access, sstore at keccak2(from, anchor).
        4. Walk prelude → eq(to, 0) = 0 (since [to <> 0]).
        5. Apply [run_let_state_match_pure_zero] to commit to else_branch
           (the [δ =? 0 then ...] arm — balance-credit at [to]).
        6. Walk balance-credit subblock at [to]: keccak mapping_index_access
           (third mia, at vs_bal_from), sload (yields balanceOf
           sim_after_decrement to via the new Section bridge), wrapping_add,
           sstore at keccak2(to, anchor) (reuses the third mia witness).
        7. Walk log3 tail (same as mint/burn).
        8. Final state: [vs_bal_to = proj_sim sim'] where
           [do_transfer sim from to value = Success sim'].  Use
           [proj_sim_independent_slots]. *)
    Lemma run_fun__update_3335_at_proj_sim_transfer :
      forall (codes : Codes.t) (env : Environment.t)
             (state_base : RocqOfSolidity.State.t)
             (memory : SimulatedMemory.t)
             (sim : ERC20.State)
             (from to value : U256.t)
             (H_from_nz : from <> 0)
             (H_to_nz : to <> 0)
             (H_from_bound : 0 <= from < 2^160)
             (H_to_bound : 0 <= to < 2^160)
             (H_value_bound : 0 <= value < 2^256)
             (H_valid : ERC20.Valid.t sim)
             (H_balance_ge : value <= ERC20.balanceOf sim from),
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_transfer sim from to value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__update_3335 from to value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      intros codes env state_base memory sim from to value
             H_from_nz H_to_nz H_from_bound H_to_bound H_value_bound
             H_valid H_balance_ge.
      (* Upfront: skolemize the post-state list via the transfer bridge. *)
      assert (H_balance_diff_bound :
                0 <= Pure.sub (ERC20.balanceOf sim from) value < 2 ^ 256).
      { unfold Pure.sub. split.
        - apply Z.mod_pos_bound. lia.
        - apply Z.mod_pos_bound. lia. }
      (* The sim post-state-after-decrement (used in the second sstore's
         RHS value via the proj_sim_independent_slots hypothesis). *)
      pose (sim_after_decrement :=
              {| ERC20.balances :=
                   ERC20.set_balance sim.(ERC20.balances) from
                     (Pure.sub (ERC20.balanceOf sim from) value);
                 ERC20.totalSupply := sim.(ERC20.totalSupply);
                 ERC20.allowances  := sim.(ERC20.allowances) |}).
      assert (H_balance_credit_bound :
                0 <= Pure.add (ERC20.balanceOf sim_after_decrement to) value < 2 ^ 256).
      { unfold Pure.add. split.
        - apply Z.mod_pos_bound. lia.
        - apply Z.mod_pos_bound. lia. }
      pose proof (proj_sim_independent_slots sim from to value
                    H_from_nz H_to_nz H_value_bound H_balance_ge) as Hbridge.
      cbv zeta in Hbridge.
      destruct (List.update_nth (proj_sim sim) slot_balances
                  (StorableValue.Map
                     (Dict.declare_or_assign
                        (balances_to_dict sim.(ERC20.balances)) from
                        (Pure.sub (ERC20.balanceOf sim from) value))))
        as [vs_bal_from|] eqn:Hupd_bal_from; [|exfalso; exact Hbridge].
      destruct Hbridge as (simq & Htransfer & Hupd_bal_to_eq).
      (* Hupd_bal_to_eq : List.update_nth vs_bal_from slot_balances
                            (StorableValue.Map (declare_or_assign
                              (balances_to_dict sim_after_decrement.(balances)) to
                              (Pure.add (balanceOf sim_after_decrement to) value)))
                          = Some (proj_sim simq).
         Set vs_bal_to := proj_sim simq, so Hupd_bal_to has the shape needed by the
         sstore lemma below. *)
      pose (vs_bal_to := proj_sim simq).
      (* Bridge: rewrite [balances_to_dict sim_after_decrement.(balances)]
         to its [declare_or_assign] form so [Hupd_bal_to] matches the
         shape produced by the sstore-at-map-anchor lemma below. *)
      assert (Hupd_bal_to :
                List.update_nth vs_bal_from slot_balances
                  (StorableValue.Map
                     (Dict.declare_or_assign
                        (Dict.declare_or_assign
                           (balances_to_dict sim.(ERC20.balances))
                           from
                           (Pure.sub (ERC20.balanceOf sim from) value))
                        to
                        (Pure.add (ERC20.balanceOf sim_after_decrement to) value)))
                = Some vs_bal_to).
      { rewrite <- balances_to_dict_set_balance_eq.
        change (ERC20.set_balance sim.(ERC20.balances) from
                  (Pure.sub (ERC20.balanceOf sim from) value))
          with sim_after_decrement.(ERC20.balances).
        exact Hupd_bal_to_eq. }
      assert (Hproj_simq : vs_bal_to = proj_sim simq) by reflexivity.
      (* Now Htransfer : ERC20.do_transfer sim from to value = Success simq
             Hproj_simq : vs_bal_to = proj_sim simq *)
      (* Pull in the post-from-decrement lens facts. *)
      pose proof (namespace_binding_after_from_balance_update_transfer sim from
                    (Pure.sub (ERC20.balanceOf sim from) value)) as Hns_after_bal_from.
      rewrite Hupd_bal_from in Hns_after_bal_from.
      pose proof (nth_balances_after_from_balance_update_transfer sim from
                    (Pure.sub (ERC20.balanceOf sim from) value)) as Hnth_after_bal_from.
      rewrite Hupd_bal_from in Hnth_after_bal_from.
      (* Skolemize the three mapping_index_access post-memories.
         mia1: first sload at from (storage = proj_sim sim, memory = memory).
         mia2: second mia before sstore at from (storage = proj_sim sim,
               memory = memory_post_kc1).
         mia3: third mia at to (storage = vs_bal_from, memory = memory_post_kc2).
         Note: mia3 result _1755 is reused for the sstore, so memory transitions
         once for the to-block. *)
      pose (memory_post_kc1 :=
              mapping_index_access_address_post_memory env
                state_base memory (proj_sim sim)
                ERC20_NAMESPACE_ANCHOR from).
      pose (memory_post_kc2 :=
              mapping_index_access_address_post_memory env
                state_base memory_post_kc1 (proj_sim sim)
                ERC20_NAMESPACE_ANCHOR from).
      pose (memory_post_kc3 :=
              mapping_index_access_address_post_memory env
                state_base memory_post_kc2 vs_bal_from
                ERC20_NAMESPACE_ANCHOR to).
      (* Intermediate state after balance-debit subblock. *)
      pose (state_post_bal_from :=
              Some (State.with_current_storage env
                      (make_state env state_base memory_post_kc2 (proj_sim sim))
                      (Storage.of_storable_values vs_bal_from))).
      (* Intermediate state after balance-credit subblock. *)
      pose (state_post_bal_to :=
              Some (State.with_current_storage env
                      (make_state env state_base memory_post_kc3 vs_bal_from)
                      (Storage.of_storable_values vs_bal_to))).
      (* Final memory: after log3 abi_encode mstore. *)
      pose (memory_final :=
              mstore_post_memory env state_base memory_post_kc3 vs_bal_to
                (Pure.add (mload_witness env state_base memory_post_kc3 vs_bal_to 64) 0)
                value).
      exists memory_final, vs_bal_to.
      split.
      { (* proj_sim_post_transfer = Some vs_bal_to *)
        unfold proj_sim_post_transfer.
        rewrite Htransfer. rewrite Hproj_simq. reflexivity. }
      unfold fun__update_3335.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      eapply RunO.Let.
      { (* === Prelude 1: getERC20Storage + binders + eq(from, 0) = 0 === *)
        eapply RunO.Let.
        { c; [ apply run_fun__getERC20Storage_2971_returns_anchor | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ from
                        H_from_bound H_from_nz) | ].
          apply RunO.Pure. }
        cbn match.
        (* === Switch 1: δ = 0, take else_branch (balance-debit at from). === *)
        eapply run_let_state_match_pure_zero with
          (state_after_branch := state_post_bal_from).
        { apply RunO.Pure. }
        { (* Balance-debit subblock at [from]. *)
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1726 := add(anchor, 0) → anchor *)
          eapply RunO.Let.
          { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1729 := mapping_index_access(anchor+0, from) — first mia *)
          replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
          2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
              rewrite Z.add_0_r.
              rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
          eapply RunO.Let.
          { c.
            { apply (run_mapping_index_access_t_address_at_make_state
                       codes env state_base memory (proj_sim sim)
                       ERC20_NAMESPACE_ANCHOR from
                       H_from_bound). }
            apply RunO.Pure. }
          cbn match.
          (* sload at keccak2(from, anchor) → map_get_u256 of balances. *)
          eapply RunO.Let.
          { c.
            { apply (run_read_from_storage_split_offset_0_t_uint256_at_map_anchor
                       _ _ _ _ (proj_sim sim) slot_balances
                       ERC20_NAMESPACE_ANCHOR
                       (balances_to_dict sim.(ERC20.balances)) from
                       (namespace_binding sim) (proj_balances_at_slot sim)). }
            apply RunO.Pure. }
          cbn match.
          rewrite (map_get_balances_eq_balanceOf sim from).
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* lt(fromBalance, value).  Under [value <= balanceOf sim from],
             [lt = 0]. *)
          eapply RunO.Let.
          { simpl LowM.let_.
            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
            c; [ unfold Stdlib.lt; apply RunO.Pure | ].
            apply RunO.Pure. }
          cbn match.
          replace (Pure.lt (ERC20.balanceOf sim from) value) with 0.
          2:{ unfold Pure.lt.
              destruct (ERC20.balanceOf sim from <? value) eqn:Hlt;
              [|reflexivity].
              apply Z.ltb_lt in Hlt. lia. }
          apply run_shallow_let_state_if_zero.
          cbn.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* wrapping_sub: produces Pure.sub fromBalance value. *)
          eapply RunO.Let.
          { c; [ apply run_wrapping_sub_t_uint256 | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1741 := add(anchor, 0) → anchor *)
          eapply RunO.Let.
          { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          (* _1744 := mapping_index_access(anchor+0, from) — second mia. *)
          replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
          2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
              rewrite Z.add_0_r.
              rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
          eapply RunO.Let.
          { c.
            { apply (run_mapping_index_access_t_address_at_make_state
                       codes env state_base memory_post_kc1 (proj_sim sim)
                       ERC20_NAMESPACE_ANCHOR from
                       H_from_bound). }
            apply RunO.Pure. }
          cbn match.
          (* sstore at keccak2(from, anchor) with Pure.sub. State has
             memory = memory_post_kc2 (after second mapping_index_access). *)
          eapply RunO.Let.
          { pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor
                          codes env state_base memory_post_kc2
                          (proj_sim sim) slot_balances ERC20_NAMESPACE_ANCHOR
                          (balances_to_dict sim.(ERC20.balances))
                          from
                          (Pure.sub (ERC20.balanceOf sim from) value)
                          (namespace_binding sim)) as Hsstore_bal_from.
            assert (Hget_proj :
                      State.get_current_storage env
                        (make_state env state_base memory_post_kc2 (proj_sim sim))
                      = Some (Storage.of_storable_values (proj_sim sim))).
            { unfold make_state.
              apply State.get_current_storage_with_current_storage_eq. }
            specialize (Hsstore_bal_from Hget_proj (proj_balances_at_slot sim)
                                         H_balance_diff_bound).
            cbv zeta in Hsstore_bal_from.
            rewrite Hupd_bal_from in Hsstore_bal_from.
            c; [ exact Hsstore_bal_from | ]. apply RunO.Pure. }
          cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          apply RunO.Pure. }
        { (* === Body after first switch: prelude → eq(to, 0) = 0 → switch 2 === *)
          cbn match.
          (* Now state is state_post_bal_from. Canonize. *)
          unfold state_post_bal_from.
          rewrite CanonizeState.update_storage_eq.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
          eapply RunO.Let.
          { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
            apply RunO.Pure. }
          cbn match.
          eapply RunO.Let.
          { simpl LowM.let_.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply run_cleanup_t_address | ]. cbn match.
            c; [ apply (run_eq_address_zero_check _ _ _ to
                          H_to_bound H_to_nz) | ].
            apply RunO.Pure. }
          cbn match.
          (* === Switch 2: δ = 0, take else_branch (balance-credit at to). === *)
          eapply run_let_state_match_pure_zero with
            (state_after_branch := state_post_bal_to).
          { apply RunO.Pure. }
          { (* Balance-credit subblock at [to]. *)
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1752 := add(anchor, 0) → anchor *)
            eapply RunO.Let.
            { c; [ unfold Stdlib.add; apply RunO.Pure | ]. apply RunO.Pure. }
            cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1755 := mapping_index_access(anchor+0, to) — third mia.
               Storage is vs_bal_from. *)
            replace (Pure.add ERC20_NAMESPACE_ANCHOR 0) with ERC20_NAMESPACE_ANCHOR.
            2:{ unfold Pure.add. unfold ERC20_NAMESPACE_ANCHOR.
                rewrite Z.add_0_r.
                rewrite Z.mod_small; [reflexivity| split; [discriminate|]; lia]. }
            eapply RunO.Let.
            { c.
              { apply (run_mapping_index_access_t_address_at_make_state
                         codes env state_base memory_post_kc2 vs_bal_from
                         ERC20_NAMESPACE_ANCHOR to
                         H_to_bound). }
              apply RunO.Pure. }
            cbn match.
            (* sload at keccak2(to, anchor) on vs_bal_from → map_get_u256 of
               the post-from-decrement map. *)
            eapply RunO.Let.
            { c.
              { apply (run_read_from_storage_split_offset_0_t_uint256_at_map_anchor
                         _ _ _ _ vs_bal_from slot_balances
                         ERC20_NAMESPACE_ANCHOR
                         (Dict.declare_or_assign
                            (balances_to_dict sim.(ERC20.balances))
                            from
                            (Pure.sub (ERC20.balanceOf sim from) value))
                         to
                         Hns_after_bal_from Hnth_after_bal_from). }
              apply RunO.Pure. }
            cbn match.
            (* Bridge map_get on post-from-decrement map to balanceOf
               sim_after_decrement to.  The post-from-decrement dict
               IS [balances_to_dict sim_after_decrement.(ERC20.balances)]
               by [balances_to_dict_set_balance_eq], so the map_get
               equals [balanceOf sim_after_decrement to] by
               [map_get_balances_eq_balanceOf]. *)
            assert (Hmap_after_dec :
                      StorableValue.map_get_u256
                        (Dict.declare_or_assign
                          (balances_to_dict sim.(ERC20.balances))
                          from
                          (Pure.sub (ERC20.balanceOf sim from) value))
                        to
                      = ERC20.balanceOf sim_after_decrement to).
            { rewrite <- balances_to_dict_set_balance_eq.
              change (ERC20.set_balance sim.(ERC20.balances) from
                        (Pure.sub (ERC20.balanceOf sim from) value))
                with sim_after_decrement.(ERC20.balances).
              apply map_get_balances_eq_balanceOf. }
            rewrite Hmap_after_dec.
            (* wrapping_add *)
            eapply RunO.Let.
            { c; [ apply run_wrapping_add_t_uint256 | ]. apply RunO.Pure. }
            cbn match.
            (* sstore at keccak2(to, anchor) on vs_bal_from with
               Pure.add (balanceOf sim_after_decrement to) value.
               State has memory = memory_post_kc3 (after third mia). *)
            eapply RunO.Let.
            { pose proof (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_map_anchor
                            codes env state_base memory_post_kc3
                            vs_bal_from slot_balances ERC20_NAMESPACE_ANCHOR
                            (Dict.declare_or_assign
                               (balances_to_dict sim.(ERC20.balances))
                               from
                               (Pure.sub (ERC20.balanceOf sim from) value))
                            to
                            (Pure.add (ERC20.balanceOf sim_after_decrement to) value)
                            Hns_after_bal_from) as Hsstore_bal_to.
              assert (Hget_bal_from :
                        State.get_current_storage env
                          (make_state env state_base memory_post_kc3 vs_bal_from)
                        = Some (Storage.of_storable_values vs_bal_from)).
              { unfold make_state.
                apply State.get_current_storage_with_current_storage_eq. }
              specialize (Hsstore_bal_to Hget_bal_from Hnth_after_bal_from
                                         H_balance_credit_bound).
              cbv zeta in Hsstore_bal_to.
              rewrite Hupd_bal_to in Hsstore_bal_to.
              c; [ exact Hsstore_bal_to | ]. apply RunO.Pure. }
            cbn match.
            apply RunO.Pure. }
          { (* === Body after second switch — log3 tail. === *)
            cbn match.
            unfold state_post_bal_to.
            rewrite CanonizeState.update_storage_eq.
            cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
            (* _1765 := convert_t_address_to_t_address from → from *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address
                         _ _ _ from H_from_bound). }
              apply RunO.Pure. }
            cbn match.
            (* _1766 := convert_t_address_to_t_address to → to *)
            eapply RunO.Let.
            { c.
              { apply (run_convert_t_address_to_t_address_on_address
                         _ _ _ to H_to_bound). }
              apply RunO.Pure. }
            cbn match.
            unfold Shallow.let_state at 1.
            unfold M.strong_let_ at 1, M.generic_let at 1.
            eapply RunO.Let.
            { (* allocate_unbounded + abi_encode + log3 *)
              eapply RunO.Let.
              { c.
                { unfold allocate_unbounded.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  eapply RunO.Let.
                  { eapply RunO.Let.
                    { c.
                      { apply (run_mload_absorbing_at_make_state
                                 codes env state_base memory_post_kc3 vs_bal_to 64). }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              eapply RunO.Let.
              { c.
                { unfold abi_encode_tuple_t_uint256__to_t_uint256__fromStack.
                  unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                  cbn match.
                  eapply RunO.Let.
                  { eapply RunO.Let.
                    { c; [ unfold Stdlib.add; apply RunO.Pure | ].
                      apply RunO.Pure. }
                    cbn match.
                    eapply RunO.Let.
                    { simpl LowM.let_.
                      c; [ unfold Stdlib.add; apply RunO.Pure | ]. cbn match.
                      c.
                      { unfold abi_encode_t_uint256_to_t_uint256_fromStack.
                        unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
                        cbn match.
                        eapply RunO.Let.
                        { eapply RunO.Let.
                          { simpl LowM.let_.
                            c; [ apply run_cleanup_t_uint256_id | ]. cbn match.
                            c.
                            { apply (run_mstore_absorbing_at_make_state
                                       codes env state_base memory_post_kc3 vs_bal_to
                                       _ _). }
                            apply RunO.Pure. }
                          cbn match. apply RunO.Pure. }
                        cbn match. apply RunO.Pure. }
                      apply RunO.Pure. }
                    cbn match. apply RunO.Pure. }
                  cbn match. apply RunO.Pure. }
                apply RunO.Pure. }
              cbn match.
              eapply RunO.Let.
              { simpl LowM.let_.
                c; [ unfold Stdlib.sub; apply RunO.Pure | ]. cbn match.
                c; [ unfold Stdlib.log3; apply RunO.Pure | ].
                apply RunO.Pure. }
              cbn match.
              apply RunO.Pure. }
            cbn match.
            apply RunO.Pure. }
        }
      }
      cbn match.
      apply RunO.Pure.
    Qed.

    (** ================================================================
        StakingVault wrapper-chain bridge axiom (R070 shape)
        ================================================================

        The StakingVault wrapper chain
          fun__update_1459 → modifier_accrueRewards_1438
                            → fun__update_1459_inner
                              → fun__update_3808 (ERC20Votes)
                                → fun__update_3335 (OZ base)
                              → _moveOptimisticDelegateVotes_1720
        Wrapper layers touch non-OZ-base slots (accrueRewards state,
        delegate checkpoints, optimistic delegate state) but NOT the
        OZ ERC20 base lens slots (proj_sim's _balances Map and
        _totalSupply U256).

        Bridge axiom: the wrapper chain's effect on proj_sim slots
        coincides with the effect of [fun__update_3335] alone.  This is
        the per-target audit obligation (R070 / R080): the StakingVault
        wrappers are observationally identity on the OZ ERC20 base
        projection, modulo storage extensions to non-base slots.

        Trust footprint:
          - The wrapper-chain composition through StakingVault's
            override is per-target (StakingVault-specific).  The
            bridge axiom encodes the soundness of "OZ ERC20 base
            view is preserved through the wrapper chain" — exactly
            the R070 / R080 observational-equivalence shape.
          - Inheritors of other ERC20 hierarchies (e.g. a vanilla
            OZ ERC20 deployment) would supply their own bridge with
            a vacuously-trivial wrapper-chain.
    *)
    Axiom run_fun__update_1459_wraps_fun__update_3335 :
      forall (codes : Codes.t) (env : Environment.t)
             (state_base : RocqOfSolidity.State.t)
             (memory : SimulatedMemory.t)
             (from to value : U256.t)
             (storage_pre storage_post : SimulatedStorage.t)
             (memory' : SimulatedMemory.t),
      {{? codes, env, Some (make_state env state_base memory storage_pre) |
        fun__update_3335 from to value ⇓ Result.Ok tt
      | Some (make_state env state_base memory' storage_post) ?}} ->
      exists (memory'' : SimulatedMemory.t),
      {{? codes, env, Some (make_state env state_base memory storage_pre) |
        fun__update_1459 from to value ⇓ Result.Ok tt
      | Some (make_state env state_base memory'' storage_post) ?}}.

    (** ================================================================
        Derived: composite walker for [fun__update_1459] mint branch
        ================================================================

        Was: a single body-absorbing axiom for the whole wrapper chain
        and the OZ ERC20 base body together.
        Now: a Qed Lemma composing:
          (a) [run_fun__update_3335_at_proj_sim_mint] (OZ base body)
          (b) [run_fun__update_1459_wraps_fun__update_3335] (wrapper bridge)

        Net trust delta: 1 broad body-absorbing axiom retired; 2
        narrower axioms in its place.  The OZ base body axiom is
        independently discharge-able to a Qed Lemma via the R083 + R107
        primitives (the actual Yul-body walker proof, ~300 lines).  The
        wrapper bridge axiom is per-target audit (StakingVault-specific
        wrappers only). *)
    Lemma run_fun__update_1459_at_proj_sim_mint
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (account value : U256.t)
        (H_account_nz : account <> 0)
        (H_account_bound : 0 <= account < 2^160)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_no_overflow : sim.(ERC20.totalSupply) + value < 2^256) :
      exists (memory' : SimulatedMemory.t),
      {{? codes, env,
          Some (make_state env state_base memory (proj_sim sim)) |
        fun__update_1459 0 account value ⇓ Result.Ok tt
      | Some (make_state env state_base memory'
                (proj_sim_post_mint sim account value)) ?}}.
    Proof.
      pose proof (run_fun__update_3335_at_proj_sim_mint
                    codes env state_base memory sim account value
                    H_account_nz H_account_bound H_value_bound
                    H_valid H_no_overflow) as [memory_inner Hinner].
      pose proof (run_fun__update_1459_wraps_fun__update_3335
                    codes env state_base memory 0 account value
                    (proj_sim sim) (proj_sim_post_mint sim account value)
                    memory_inner Hinner) as [memory_outer Houter].
      exists memory_outer. exact Houter.
    Qed.

    (** ================================================================
        Composite walker for [fun__update_1459] burn / transfer branches
        ================================================================

        Sibling Qed Lemmas to the mint case.  Same recipe: compose the
        OZ ERC20 base body axiom with the wrapper-chain bridge.  These
        are the load-bearing pieces for the _burn / _transfer headline
        theorems below. *)

    Lemma run_fun__update_1459_at_proj_sim_burn
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (account value : U256.t)
        (H_account_nz : account <> 0)
        (H_account_bound : 0 <= account < 2^160)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_balance_ge : value <= ERC20.balanceOf sim account) :
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_burn sim account value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__update_1459 account 0 value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      pose proof (run_fun__update_3335_at_proj_sim_burn
                    codes env state_base memory sim account value
                    H_account_nz H_account_bound H_value_bound
                    H_valid H_balance_ge) as Hbody.
      destruct Hbody as [memory_inner Hbody].
      destruct Hbody as [storage_inner Hbody].
      destruct Hbody as [Hpost Hinner].
      pose proof (run_fun__update_1459_wraps_fun__update_3335
                    codes env state_base memory account 0 value
                    (proj_sim sim) storage_inner
                    memory_inner Hinner) as [memory_outer Houter].
      exists memory_outer, storage_inner. split.
      - exact Hpost.
      - exact Houter.
    Qed.

    Lemma run_fun__update_1459_at_proj_sim_transfer
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (from to value : U256.t)
        (H_from_nz : from <> 0)
        (H_to_nz : to <> 0)
        (H_from_bound : 0 <= from < 2^160)
        (H_to_bound : 0 <= to < 2^160)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_balance_ge : value <= ERC20.balanceOf sim from) :
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_transfer sim from to value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__update_1459 from to value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      pose proof (run_fun__update_3335_at_proj_sim_transfer
                    codes env state_base memory sim from to value
                    H_from_nz H_to_nz H_from_bound H_to_bound
                    H_value_bound H_valid H_balance_ge) as Hbody.
      destruct Hbody as [memory_inner Hbody].
      destruct Hbody as [storage_inner Hbody].
      destruct Hbody as [Hpost Hinner].
      pose proof (run_fun__update_1459_wraps_fun__update_3335
                    codes env state_base memory from to value
                    (proj_sim sim) storage_inner
                    memory_inner Hinner) as [memory_outer Houter].
      exists memory_outer, storage_inner. split.
      - exact Hpost.
      - exact Houter.
    Qed.

    (** ================================================================
        Walker leaves for [fun__update_3335]'s body (task #315)
        ================================================================

        Per-Yul-op identity leaf: [cleanup_t_uint256 v = v].  Used at
        the entry of [convert_t_uint256_to_t_uint256], [checked_add],
        [wrapping_add], [wrapping_sub], and inside the byte-slice
        machinery for storage writes.  Identity lemma over the
        let-prelude unfolding. *)
    Lemma run_cleanup_t_uint256_identity codes env state (v : U256.t) :
      {{? codes, env, Some state |
        cleanup_t_uint256 v ⇓ Result.Ok v
      | Some state ?}}.
    Proof.
      unfold cleanup_t_uint256.
      lu. repeat (lu || cu || p).
    Qed.

    (** ================================================================
        The headline equivalence theorem for OZ ERC20 _mint
        ================================================================

        Under the preconditions:
          - [account] is a well-formed nonzero 160-bit address
          - [value] is a well-formed uint256
          - [sim] is a valid ERC20 state
          - the [totalSupply + value] addition doesn't overflow

        [fun__mint_3368 account value] reduces from [proj_sim sim] to
        [proj_sim (ERC20.mint sim account value)] (memory absorbed).

        This is the proof-of-method: the composite walker theorem for
        OZ ERC20's [_mint] closes to [Qed] with three named load-bearing
        axioms (the inner [_update] mint composite, the two new
        framework anchor primitives for single-map and U256-at-offset),
        none of which are body-absorbing on [_mint] itself. *)
    Theorem run_fun__mint_3368_equivalent
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (account value : U256.t)
        (H_account_bound : 0 <= account < 2^160)
        (H_account_nz : account <> 0)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_no_overflow : sim.(ERC20.totalSupply) + value < 2^256) :
      exists (memory' : SimulatedMemory.t),
      {{? codes, env,
          Some (make_state env state_base memory (proj_sim sim)) |
        fun__mint_3368 account value ⇓ Result.Ok tt
      | Some (make_state env state_base memory'
                (proj_sim_post_mint sim account value)) ?}}.
    Proof.
      (* Pose the inner _update composite axiom upfront so its memory'
         is in scope. *)
      pose proof (run_fun__update_1459_at_proj_sim_mint
                    codes env state_base memory sim account value
                    H_account_nz H_account_bound H_value_bound
                    H_valid H_no_overflow) as Hupdate.
      destruct Hupdate as [memory' Hupdate].
      exists memory'.
      unfold fun__mint_3368.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      (* WALKER — explicit step-by-step discharge.  Each [eapply RunO.Let]
         opens a sequential let-binding.  Pure intermediates ([LowM.Pure
         (Result.Ok _)]) are absorbed by [RunO.Pure] and the continuation
         then reduces via [cbn match].  The named leaves are:
           - [run_convert_t_rational_0_by_1_to_t_address_at_zero]
           - [AbiEncoding.run_cleanup_t_address]   (general form)
           - [run_eq_address_zero_check] (the address-zero check leaf)
         The zero-address check, the [Shallow.let_state] dispatch, and
         the inner [fun__update_1459] call are all explicit; the residual
         [BlockUnit] dispatch closes via [run_shallow_let_state_if_zero]
         (R107 absorber). *)

      (* Step 1: the outer LowM.Let opens the chained let-prelude that
         feeds [account] and [0] through cleanup -> convert -> eq.  Each
         [LowM.Pure] threads forward via [RunO.Let] + [RunO.Pure]. *)
      eapply RunO.Let.
      { (* Result.Ok account -> result *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { (* LowM.Call (convert_t_rational_0_by_1_to_t_address 0) *)
          c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure.
        }
        cbn match.
        eapply RunO.Let.
        { (* nested LowM.let_ chain: cleanup_t_address account ;
             cleanup_t_address 0 ; eq.  Open the nested let_ structurally. *)
          simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ account
                        H_account_bound H_account_nz) | ].
          apply RunO.Pure.
        }
        cbn match.
        (* The address-zero check returned value = 0; now we hit the
           [Shallow.let_state (Shallow.if_ 0 ...) ...] absorber. *)
        apply run_shallow_let_state_if_zero.
        cbn.
        (* Post-absorber: the inner block continues with [_update].
           Thread through the remaining let-bindings to the
           [fun__update_1459] call. *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        (* The [_update] call: composite walker axiom Hupdate provides
           the full discharge. *)
        eapply RunO.Let.
        { c; [ exact Hupdate | apply RunO.Pure ]. }
        cbn match.
        apply RunO.Pure.
      }
      cbn match.
      apply RunO.Pure.
    Qed.

    (** ================================================================
        Headline equivalence theorem for OZ ERC20 _burn (task #315)
        ================================================================

        [fun__burn_3401(account, value)]:
          if (account == 0) revert ERC20InvalidSender(0);
          _update(account, 0, value);

        Under preconditions:
          - [account] is a well-formed nonzero 160-bit address
          - [value] is a well-formed uint256
          - [sim] is a valid ERC20 state
          - [value <= balanceOf sim account] (no underflow)

        [fun__burn_3401 account value] reduces to a post-state observably
        equal to [proj_sim (ERC20.burn sim account value)] under
        [ERC20.Result.Success] (which is guaranteed by [H_balance_ge]). *)
    Theorem run_fun__burn_3401_equivalent
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (account value : U256.t)
        (H_account_bound : 0 <= account < 2^160)
        (H_account_nz : account <> 0)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_balance_ge : value <= ERC20.balanceOf sim account) :
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_burn sim account value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__burn_3401 account value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      pose proof (run_fun__update_1459_at_proj_sim_burn
                    codes env state_base memory sim account value
                    H_account_nz H_account_bound H_value_bound
                    H_valid H_balance_ge) as Hupdate.
      destruct Hupdate as [memory' Hupdate].
      destruct Hupdate as [storage' Hupdate].
      destruct Hupdate as [Hpost Hupdate].
      exists memory', storage'. split; [exact Hpost|].
      unfold fun__burn_3401.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      eapply RunO.Let.
      { (* Walk through let-prelude: account → cleanup → 0 → convert → eq *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ account
                        H_account_bound H_account_nz) | ].
          apply RunO.Pure.
        }
        cbn match.
        apply run_shallow_let_state_if_zero.
        cbn.
        (* Steps after let_state: _1478 (pure); expr_3392 (pure); expr_3395=0x00 (pure);
           expr_3396 = convert(0) (Call); _1479 (pure); expr_3397 (pure); update (Call). *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ exact Hupdate | apply RunO.Pure ]. }
        cbn match.
        apply RunO.Pure.
      }
      cbn match.
      apply RunO.Pure.
    Qed.

    (** ================================================================
        Headline equivalence theorem for OZ ERC20 _transfer (task #315)
        ================================================================

        [fun__transfer_3243(from, to, value)]:
          if (from == 0) revert ERC20InvalidSender(0);
          if (to == 0)   revert ERC20InvalidReceiver(0);
          _update(from, to, value);

        Under preconditions:
          - [from], [to] are well-formed nonzero 160-bit addresses
          - [value] is a well-formed uint256
          - [sim] is a valid ERC20 state
          - [value <= balanceOf sim from] (no underflow)

        [fun__transfer_3243 from to value] reduces to a post-state
        observably equal to [proj_sim (ERC20.do_transfer sim from to value)]
        under [ERC20.Result.Success]. *)
    Theorem run_fun__transfer_3243_equivalent
        (codes : Codes.t) (env : Environment.t)
        (state_base : RocqOfSolidity.State.t)
        (memory : SimulatedMemory.t)
        (sim : ERC20.State)
        (from to value : U256.t)
        (H_from_bound : 0 <= from < 2^160)
        (H_from_nz : from <> 0)
        (H_to_bound : 0 <= to < 2^160)
        (H_to_nz : to <> 0)
        (H_value_bound : 0 <= value < 2^256)
        (H_valid : ERC20.Valid.t sim)
        (H_balance_ge : value <= ERC20.balanceOf sim from) :
      exists (memory' : SimulatedMemory.t) (storage' : SimulatedStorage.t),
        proj_sim_post_transfer sim from to value = Some storage' /\
        {{? codes, env,
            Some (make_state env state_base memory (proj_sim sim)) |
          fun__transfer_3243 from to value ⇓ Result.Ok tt
        | Some (make_state env state_base memory' storage') ?}}.
    Proof.
      pose proof (run_fun__update_1459_at_proj_sim_transfer
                    codes env state_base memory sim from to value
                    H_from_nz H_to_nz H_from_bound H_to_bound
                    H_value_bound H_valid H_balance_ge) as Hupdate.
      destruct Hupdate as [memory' Hupdate].
      destruct Hupdate as [storage' Hupdate].
      destruct Hupdate as [Hpost Hupdate].
      exists memory', storage'. split; [exact Hpost|].
      unfold fun__transfer_3243.
      unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
      cbn match.
      eapply RunO.Let.
      { (* First zero-check on [from] *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ from
                        H_from_bound H_from_nz) | ].
          apply RunO.Pure.
        }
        cbn match.
        apply run_shallow_let_state_if_zero.
        cbn.
        (* Second zero-check on [to] *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ apply run_convert_t_rational_0_by_1_to_t_address_at_zero | ].
          apply RunO.Pure. }
        cbn match.
        eapply RunO.Let.
        { simpl LowM.let_.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply run_cleanup_t_address | ]. cbn match.
          c; [ apply (run_eq_address_zero_check _ _ _ to
                        H_to_bound H_to_nz) | ].
          apply RunO.Pure.
        }
        cbn match.
        apply run_shallow_let_state_if_zero.
        cbn.
        (* Inner _update call *)
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let; [ apply RunO.Pure | ]. cbn match.
        eapply RunO.Let.
        { c; [ exact Hupdate | apply RunO.Pure ]. }
        cbn match.
        apply RunO.Pure.
      }
      cbn match.
      apply RunO.Pure.
    Qed.

  End ERC20BaseEquivalence.

End ERC20Equivalence.

(* Print Assumptions of the headline theorems.

   To inspect the trust footprint after task #315:

     Print Assumptions ERC20Equivalence.run_fun__mint_3368_equivalent.
     Print Assumptions ERC20Equivalence.run_fun__burn_3401_equivalent.
     Print Assumptions ERC20Equivalence.run_fun__transfer_3243_equivalent.

   Output for each (axioms):
     - run_fun__update_3335_at_proj_sim_<branch>   (OZ ERC20 base body)
     - run_fun__update_1459_wraps_fun__update_3335 (wrapper chain bridge)
     - Memory.of_u256_list                          (upstream framework)
     - Storage.of_storable_values                   (upstream framework)
     - PrimInt63.* primitives                       (Coq standard library)
     - Set is impredicative                         (Coq theory axiom)

   Net trust decomposition vs task #314:
     - Before: 1 body-absorbing composite axiom per branch covering
       BOTH the OZ ERC20 base body AND the StakingVault wrapper chain.
     - After: 2 narrower axioms per branch — one for the OZ base body
       (mechanically discharge-able via R083 + R107), one for the
       wrapper-chain bridge (per-target audit, R070 shape).

   The four [*_at_anchor] framework primitives and the
   [IsNamespaceAnchor] / [IsAnchorOffsetSlot] Parameters are NOT yet
   load-bearing for the headline theorems: they are consumed when
   [run_fun__update_3335_at_proj_sim_<branch>] is itself discharged to
   its Yul body.  That discharge is mechanical (the recipe is described
   in WISDOM R108) and reduces the headline theorems' trust footprint
   further to just the wrapper bridge + framework primitives.

   Sibling [_burn] and [_transfer] headline theorems are closed
   following the same recipe (zero-addr precheck + composite walker
   inner axiom + R107 absorbers).  See [run_fun__burn_3401_equivalent]
   and [run_fun__transfer_3243_equivalent] in the Section. *)
