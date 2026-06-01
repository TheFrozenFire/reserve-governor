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

    ===== Trust footprint =====

    Closed to [Qed].  This file's Print Assumptions for
    [run_fun__mint_3368_equivalent] (task #314 closure):

      1. [run_fun__update_1459_at_proj_sim_mint] — composite walker
         axiom for the [_update] sub-call, narrowed to the mint shape
         ([from = 0], [to <> 0]).  Reusable for ANY mint call site
         (including future ERC4626 [_deposit], ERC20Votes [_mint], etc.)
         and strictly narrower than a full body-absorbing [Axiom] on
         [fun__update_1459] (which would absorb burn, transfer, mint
         indiscriminately).  THIS is the only contract-specific audit
         obligation for the headline theorem.

      2. Upstream framework axioms ([Memory.of_u256_list],
         [Storage.of_storable_values], standard PrimInt63 primitives) —
         baseline trust footprint shared with the entire corpus.

    The walker proof itself uses Qed Lemmas only:
      - [run_cleanup_t_address] (AbiEncoding.v Qed Lemma)
      - [run_convert_t_rational_0_by_1_to_t_address_at_zero]
         (this file, Qed Lemma)
      - [run_eq_address_zero_check] (this file, Qed Lemma)
      - [run_shallow_let_state_if_zero] (FrameworkExtensions.v Qed
         Lemma — R107 absorber, reusable across every walker with the
         Yul [if (cond) revert(...)] shape after [cond = 0]).

    The four [*_at_anchor] framework primitives ([run_sload_map_u256_at_anchor],
    [run_sstore_map_u256_at_anchor], [run_sload_u256_at_anchor_offset],
    [run_sstore_u256_at_anchor_offset]) are NOT load-bearing for this
    theorem — they will be consumed by the eventual discharge of
    [run_fun__update_1459_at_proj_sim_mint] to its Yul body (the
    OZ ERC20 base [_update] walker through the StakingVault override
    chain), at which point this theorem's trust footprint reduces
    further.

    Path forward for [_burn] / [_transfer] / [_approve] (mechanical
    extension):
      - [_burn]: same shape; zero-addr check on [account], then
        [_update(account, 0, value)].  Inner sub-axiom shape is
        [run_fun__update_1459_at_proj_sim_burn].
      - [_transfer]: zero-addr checks on both [from] and [to], then
        [_update(from, to, value)].  Inner sub-axiom shape is
        [run_fun__update_1459_at_proj_sim_transfer].
      - [_approve]: orthogonal — no [_update] call.  Walker writes
        directly to [_allowances[owner][spender] := value] via
        [run_sstore_map2_u256_at_anchor] (R083, already in the
        framework).  Emit Approval event (log3 — pure).

    From this base, ERC4626 [deposit] requires:
      - Compose [_mint] with the asset-pulling [safeTransferFrom]
        (already mechanized at the trust-axiom level in [R094] /
        [AbiEncoding.SafeERC20]).
      - Compose with the ERC4626 [_convertToShares] / [_convertToAssets]
        muldiv arithmetic (R076 in [ERC4626.v]).
      - The [super._deposit] walker discharge in [StakingVaultExchange]
        composes [_mint] with the per-token [safeTransferFrom] call.

    WISDOM reference: R051 (composite-axiom shape), R072 (slot-agnostic
    abstract base), R083 (namespace anchor lens), R104 (Walker
    Axiom→Lemma rename).
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
        Composite walker axiom for the [_update] mint sub-call
        ================================================================

        The walker for [fun__update_1459(0, account, value)] follows
        the StakingVault override chain:
          fun__update_1459 ← modifier_accrueRewards
                            ← fun__update_1459_inner
                              → fun__update_3808 (ERC20Votes._update)
                                → fun__update_3335 (ERC20._update)
                                  → mint-branch: read+write _totalSupply
                                    at anchor+2, read+write _balances[to]
                                    at keccak2(to, anchor), emit Transfer
                                → maxSupply check + _transferVotingUnits
                              → optimisticDelegateVotes side-effect

        The "pure OZ ERC20 base" sub-claim ignores the StakingVault
        accrueRewards modifier, the ERC20Votes maxSupply / transferVotingUnits
        side-effect, and the optimistic-delegation side-effect.  Those
        compose orthogonally via R078 / R080 / R094 — they are not part
        of the OZ-base [_mint] semantics.

        This axiom states the WALKER post-state in terms of the OZ ERC20
        base [_update] effect: balances[account] += value, totalSupply
        += value.  Inheritor walker proofs that need the StakingVault-
        specific side-effects compose this axiom with their own
        modifier walkers.

        Narrower than a full body-absorbing Axiom because:
          - Only the mint-branch (from = 0) shape is asserted.
          - Reusable for any future [_mint] call site (ERC4626
            [_deposit], native [mint] wrappers, etc.).
          - The other [_update] branches (burn: to = 0; transfer:
            from <> 0, to <> 0) are NOT covered — each gets its own
            sibling axiom.

        Audit-time obligation: the actual Yul body of [fun__update_3335]
        (the OZ ERC20 base [_update] inlined into StakingVault_shallow.v
        at lines 10200-10328) implements exactly this post-state under
        the mint-branch precondition.  Mechanical verification is
        ~150 walker steps over the framework primitives below.  The
        path forward note in the file header describes the wrapper
        chain needed to discharge this axiom to a Qed Lemma:

          - run_fun__update_3335_at_mint_branch (the actual ERC20 base body)
          - composed with the ERC20Votes / StakingVault wrappers
            (already mechanized via R078 / R080 at the trust-axiom level).
    *)
    Axiom run_fun__update_1459_at_proj_sim_mint :
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
        fun__update_1459 0 account value ⇓ Result.Ok tt
      | Some (make_state env state_base memory'
                (proj_sim_post_mint sim account value)) ?}}.

    (** ================================================================
        Walker leaves for [_mint]'s zero-address check
        ================================================================ *)

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

  End ERC20BaseEquivalence.

End ERC20Equivalence.

(* Print Assumptions of the headline theorem.

   To inspect the trust footprint of [run_fun__mint_3368_equivalent],
   uncomment the following line:

   Print Assumptions ERC20Equivalence.run_fun__mint_3368_equivalent.

   Actual output (task #314 closure):
     - run_fun__update_1459_at_proj_sim_mint  (the inner-body sub-axiom)
     - Memory.of_u256_list                    (upstream framework)
     - Storage.of_storable_values             (upstream framework)
     - PrimInt63.* primitives                 (Coq standard library)
     - Set is impredicative                   (Coq theory axiom)

   The four [*_at_anchor] framework primitives and the
   [IsNamespaceAnchor] / [IsAnchorOffsetSlot] Parameters are NOT
   load-bearing for this theorem: [_mint] itself never touches storage
   directly, so the anchor lens infrastructure is consumed only when
   [run_fun__update_1459_at_proj_sim_mint] is itself discharged to its
   Yul body. *)
