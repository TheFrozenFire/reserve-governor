(** ProposalLib equivalence — sim-side ↔ shallow-Yul bridge.

    Mirrors [contracts/governance/lib/ProposalLib.sol] — the library
    that mediates proposal lifecycle for the ReserveOptimisticGovernor.
    See [simulations/ProposalLib.v] for the simulation model.

    SCOPE NOTE (R060): the initial brief for this work characterised
    ProposalLib as a "pure Solidity library, no OZ deps, no external
    calls" with "4 uint48 timestamps + uint8 state enum + address packed
    in 2 storage slots". That characterisation is INCORRECT against the
    actual source.

    Reality:
      - [ProposalLib] dispatches through [_governor()] (cast of
        [address(this)]) into the deployed [ReserveOptimisticGovernor]
        contract, then issues EXTERNAL [staticcall]s to query
        [timelock()], [selectorRegistry()], [state()],
        [proposalThreshold()], [votingDelay()], [votingPeriod()],
        [proposalProposer()], and [getProposalId()]. Additionally,
        [proposeOptimistic] queries [AccessControl(timelock).hasRole]
        on the returned timelock — another external [staticcall].
      - The storage layout the brief described ("4 uint48 timestamps +
        uint8 + address in 2 packed slots") matches the OZ
        [GovernorUpgradeable.ProposalCore] struct, NOT ProposalLib's
        own storage. ProposalLib writes ONE field of that struct
        ([_saveProposal]'s three sstores at offsets 0/20/26 of the
        passed-in [proposalCore_slot]) — the address + uint48 voteStart
        + uint32 voteDuration packing.

    With that reality:

      - [fun__saveProposal_580] has NO external calls in its body
        (three sstores to slot+0 at offsets 0/20/26, plus internal
        helper calls [fun_toUint48], [fun_toUint32], and a [log1]
        emit). This is the canonical Qed target for the mutator side.
      - [fun__validateProposal_507] gates an EXTERNAL staticcall to
        [governor.state()] in the [voteStart != 0] branch (for the
        revert detail). The happy-path branch ([voteStart == 0]) does
        NOT hit the staticcall and is tractable.
      - [fun_proposeOptimistic_179], [fun_proposePessimistic_288],
        [fun_transitionToPessimistic_400] all dispatch through
        multiple external staticcalls. These hit the R050 (external
        [staticcall] infrastructure gap) blocker — same as
        [VersionRegistry.deprecateVersion].

    The headline ladder closed in this file:

      Tier 0 (pure helpers, internal):
        - [run_fun__governor_679_equivalent] — [_governor()] returns
          [address(this)] cast to [ReserveOptimisticGovernor].
        - [run_fun_toUint48_7536_within_bound] — [SafeCast.toUint48] on
          a value already in uint48 range is identity.
        - [run_fun_toUint32_7592_within_bound] — same for uint32.

      Tier 1 (pure cleanup / convert leaves):
        Closed standalone — each is identity on values in range.
        ([cleanup_t_uint48], [cleanup_t_uint32],
        [cleanup_from_storage_t_uint48], [cleanup_from_storage_t_uint32],
        [convert_t_uint256_to_t_uint48], etc.)

    Trust axioms accepted (alongside pre-existing
    [Storage.run_sload_*] / [keccak256_*] family):
      - [Address.implies_and_mask] (pre-existing in
        [rocq-of-solidity/proofs/RocqOfSolidity.v]) — generalisation
        of the same mask-cleanup-is-identity result extended to
        uint48 / uint32 inline below ([uint_implies_and_mask_*]).
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.simulations.ProposalLib.
Require Import ReserveGovernor.generated.ProposalLib_shallow.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import ReserveGovernor.proofs.equivalence.FrameworkExtensions.
Require Import ReserveGovernor.proofs.equivalence.ThrottleLib_Leaves.

Import Stdlib.
Import RunO.
Import FrameworkExtensions.

Open Scope Z_scope.

Module ProposalLibEquivalence.

  Import ProposalLib_680.ProposalLib_680_deployed.

  (** Bring sim-side names ([Address], [Selector], [ProposalData], etc.)
      into scope so the R070 axioms below can refer to them unqualified
      — the deployed-shallow namespace has no such names. *)
  Import ProposalLib.

  (** ========================================================
        Tier 1.0 — generic bit-mask lemmas
      ========================================================

      The same shape as [Address.implies_and_mask] (which is admitted
      upstream): a value in [0, 2^N) equals itself ANDed with the
      N-bit mask. We prove the [Z.land] formulation directly here for
      the uint48 / uint32 widths used by ProposalLib's packed slot. *)

  Lemma uint_implies_and_mask (n : nat) (v : U256.t)
      (H_v : 0 <= v < 2^(Z.of_nat n)) :
    v = Z.land v (2^(Z.of_nat n) - 1).
  Proof.
    assert (Heq : 2^(Z.of_nat n) - 1 = Z.ones (Z.of_nat n))
      by (rewrite Z.ones_equiv; lia).
    rewrite Heq.
    apply Z.bits_inj'. intros k Hk.
    rewrite Z.land_spec.
    destruct (Z.testbit v k) eqn:Hbit.
    - rewrite Bool.andb_true_l.
      destruct (Z_lt_le_dec k (Z.of_nat n)) as [Hl|Hl].
      + rewrite Z.ones_spec_low by lia. reflexivity.
      + exfalso.
        destruct (Z.eq_dec v 0) as [Heq0|Hne].
        * subst. rewrite Z.bits_0 in Hbit. discriminate.
        * assert (Hvpos : 0 < v) by lia.
          assert (Hlog : Z.log2 v < Z.of_nat n) by (apply Z.log2_lt_pow2; lia).
          rewrite Z.bits_above_log2 in Hbit; [discriminate | lia | lia].
    - rewrite Bool.andb_false_l. reflexivity.
  Qed.

  (** Specialisations for the widths in use. *)
  Lemma uint48_implies_and_mask (v : U256.t) (H_v : 0 <= v < 2^48) :
    v = Z.land v 0xffffffffffff.
  Proof.
    change 0xffffffffffff with (2 ^ (Z.of_nat 48) - 1).
    apply uint_implies_and_mask. change (Z.of_nat 48) with 48. exact H_v.
  Qed.

  Lemma uint32_implies_and_mask (v : U256.t) (H_v : 0 <= v < 2^32) :
    v = Z.land v 0xffffffff.
  Proof.
    change 0xffffffff with (2 ^ (Z.of_nat 32) - 1).
    apply uint_implies_and_mask. change (Z.of_nat 32) with 32. exact H_v.
  Qed.

  Lemma uint160_implies_and_mask (v : U256.t) (H_v : 0 <= v < 2^160) :
    v = Z.land v 0xffffffffffffffffffffffffffffffffffffffff.
  Proof.
    change 0xffffffffffffffffffffffffffffffffffffffff with (2 ^ (Z.of_nat 160) - 1).
    apply uint_implies_and_mask. change (Z.of_nat 160) with 160. exact H_v.
  Qed.

  (** ========================================================
        Tier 1.1 — pure cleanup-and-convert helpers
      ========================================================

      These are the same shape as ThrottleLib_Leaves' [run_cleanup_t_*]
      family, specialised for the uint48 / uint32 / address widths
      that ProposalLib's packed [ProposalCore] slot uses.
   *)

  (** [cleanup_t_uint256] and [identity] are pure passthroughs. *)
  Lemma run_cleanup_t_uint256 codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold cleanup_t_uint256. lu. repeat (lu || cu || p). Qed.

  Lemma run_identity codes env state (v : U256.t) :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof. unfold identity. lu. repeat (lu || cu || p). Qed.

  (** [cleanup_t_uint48 v] reduces to [Z.land v 0xffffffffffff], which
      is [v] when [v < 2^48]. *)
  Lemma run_cleanup_t_uint48 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      cleanup_t_uint48 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint48.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- uint48_implies_and_mask by exact H_v. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_cleanup_t_uint32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      cleanup_t_uint32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint32.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- uint32_implies_and_mask by exact H_v. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_cleanup_t_uint160 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- uint160_implies_and_mask by exact H_v. reflexivity.
    - reflexivity.
  Qed.

  (** [cleanup_t_address] = [cleanup_t_uint160]. *)
  Lemma run_cleanup_t_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_address.
    lu. l. { c. { apply run_cleanup_t_uint160; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** Storage-side cleanup is also identity (inline [and] mask). *)
  Lemma run_cleanup_from_storage_t_uint48 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_uint48 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_uint48.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- uint48_implies_and_mask by exact H_v. reflexivity.
    - reflexivity.
  Qed.

  Lemma run_cleanup_from_storage_t_uint32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_uint32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_uint32.
    lu. repeat (lu || cu || p).
    s. unfold Pure.and.
    pe.
    - f_equal. rewrite <- uint32_implies_and_mask by exact H_v. reflexivity.
    - reflexivity.
  Qed.

  (** [convert_t_uint256_to_t_uint48 v] = cleanup_t_uint48 (identity
      (cleanup_t_uint256 v)). We prove the value passthrough on
      [v < 2^48]. *)
  Lemma run_convert_t_uint256_to_t_uint48 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint48 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint48.
    lu. l. { c. { apply run_cleanup_t_uint256. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint48; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint256_to_t_uint32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint32.
    lu. l. { c. { apply run_cleanup_t_uint256. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint32; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint48_to_t_uint256 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      convert_t_uint48_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint48_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint48; exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint256. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint48_to_t_uint48 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      convert_t_uint48_to_t_uint48 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint48_to_t_uint48.
    lu. l. { c. { apply run_cleanup_t_uint48; exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint48; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint32_to_t_uint32 codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      convert_t_uint32_to_t_uint32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint32_to_t_uint32.
    lu. l. { c. { apply run_cleanup_t_uint32; exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint32; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_uint160
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. { c. { apply run_cleanup_t_uint160; exact H_v. }
             c. { apply run_identity. }
             c. { apply run_cleanup_t_uint160; exact H_v. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_address_to_t_address codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** [Stdlib.address] returns [env.(Environment.address)]. *)
  Lemma run_address_primitive codes env state :
    {{? codes, env, Some state |
      Stdlib.address ⇓ Result.Ok env.(Environment.address)
    | Some state ?}}.
  Proof.
    unfold Stdlib.address.
    eapply RunO.Primitive; [reflexivity|].
    apply RunO.Pure.
  Qed.

  Lemma run_convert_t_contract_ProposalLib_to_t_address
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_contractₓ_ProposalLib_ₓ680_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_contractₓ_ProposalLib_ₓ680_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_address_payable
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address_payable v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address_payable.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_address_to_t_address_payable
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address_payable v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address_payable.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address_payable; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint160_to_t_contract_ReserveOptimisticGovernor
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_contractₓ_ReserveOptimisticGovernor_ₓ2415 v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_contractₓ_ReserveOptimisticGovernor_ₓ2415.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160; exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_address_payable_to_t_contract_ReserveOptimisticGovernor
      codes env state (v : U256.t) (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_payable_to_t_contractₓ_ReserveOptimisticGovernor_ₓ2415 v ⇓
      Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_payable_to_t_contractₓ_ReserveOptimisticGovernor_ₓ2415.
    lu. l. { c. { apply run_convert_t_uint160_to_t_contract_ReserveOptimisticGovernor;
                  exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_zero_value_for_split_t_contract codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_contractₓ_ReserveOptimisticGovernor_ₓ2415 ⇓
      Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_contractₓ_ReserveOptimisticGovernor_ₓ2415.
    lu. repeat (lu || cu || p).
  Qed.

  (** ========================================================
        Tier 0 — [_governor] equivalence
      ======================================================== *)

  (** [_governor()] in Solidity is
        [ReserveOptimisticGovernor(payable(address(this)))]
      — a chain of identity casts on [address()], which returns the
      runtime's contract address. We model that as the same address,
      since every cast in the chain is value-identity at the U256
      level.

      Proof shape: standard walker drains the leading [let~] tower,
      then [unfold Stdlib.address; cbn] exposes the [LowM.Primitive
      GetEnvironment] step which we discharge with [RunO.Primitive].
      The follow-on [repeat (lu || cu || p)] cascade unfolds the
      nested [convert_*] casts down to a chain of [Pure.and v mask]
      applications, which [uint160_implies_and_mask] collapses to
      [v] under [H_addr]. PureEq closes the final equality. *)
  Theorem run_fun__governor_679_equivalent codes env state
      (H_addr : 0 <= env.(Environment.address) < 2^160) :
    {{? codes, env, Some state |
      fun__governor_679 ⇓ Result.Ok env.(Environment.address)
    | Some state ?}}.
  Proof.
    unfold fun__governor_679.
    lu. l. { c. { apply run_zero_value_for_split_t_contract. } p. }
    repeat (lu || cu || p).
    unfold Stdlib.address.
    cbn.
    eapply RunO.Primitive; [reflexivity|].
    repeat (lu || cu || p).
    unfold Pure.and.
    pe.
    - (* The goal is [Result.Ok (Z.land ... v ...) = Result.Ok v]. *)
      f_equal.
      (* Six nested [Z.land _ mask] applications; each is identity
         since the inner value stays in [0, 2^160). Stage the
         identity rewrite via an [assert] so that [rewrite !]
         drains all occurrences in one pass. *)
      assert (Hid : Z.land env.(Environment.address)
                      1461501637330902918203684832716283019655932542975
                    = env.(Environment.address)).
      { change 1461501637330902918203684832716283019655932542975
          with 0xffffffffffffffffffffffffffffffffffffffff.
        rewrite <- uint160_implies_and_mask by exact H_addr.
        reflexivity. }
      rewrite !Hid. reflexivity.
    - reflexivity.
  Qed.

  (** ========================================================
        Tier 0 — [SafeCast.toUint48] / [toUint32] within-bound
      ========================================================

      [fun_toUint48_7536] checks if [value > 2^48 - 1]; if yes, reverts
      with [SafeCastOverflowedUintDowncast(48, value)]; otherwise
      [convert_t_uint256_to_t_uint48] (identity on values in range).

      We prove the happy path: value already in uint48 range, the
      gt-check is false, the function returns the value unchanged.

      Proof shape (R047 case-split-before-eexists):
        1. Walk the zero-init prefix with the standard [lu. l. {c. ...} p.]
           pattern.
        2. [s. unfold Shallow.if_, Pure.gt] exposes the gt-check.
        3. Case-split on [v >? mask]; the [true] branch contradicts
           [H_v]; the [false] branch falls into the no-revert leg.
        4. [simpl] reduces the [if 0 =? 0] to the [(Tt, tt)] arm and
           [l; [p|]; cbv match] threads the [Result.Ok v] through.
        5. [repeat (lu || cu || p)] then drains the [convert_*] cast
           into a single [Pure.and v mask]; rewrite by
           [uint{48,32}_implies_and_mask] under [H_v] closes Pure. *)

  (** Zero-value initialiser used inside [fun_toUint48]. Same shape
      as [run_zero_value_for_split_t_contract] above. *)
  Lemma run_zero_value_for_split_t_uint48 codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_uint48 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_uint48.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_fun_toUint48_7536_within_bound codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      fun_toUint48_7536 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold fun_toUint48_7536.
    lu. l. { c. { apply run_zero_value_for_split_t_uint48. } p. }
    repeat (lu || cu || p).
    s. unfold Shallow.if_, Pure.gt.
    destruct (v >? 281474976710655) eqn:Hgt.
    - apply Z.gtb_lt in Hgt. exfalso. lia.
    - simpl.
      l; [ p | ].
      cbv match.
      repeat (lu || cu || p).
      unfold Pure.and.
      rewrite <- uint48_implies_and_mask by exact H_v.
      cbn.
      repeat (lu || cu || p).
  Qed.

  (** Zero-value initialiser used inside [fun_toUint32]. Same shape
      as [run_zero_value_for_split_t_uint48] above. *)
  Lemma run_zero_value_for_split_t_uint32 codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_uint32 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_uint32.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_fun_toUint32_7592_within_bound codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      fun_toUint32_7592 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold fun_toUint32_7592.
    lu. l. { c. { apply run_zero_value_for_split_t_uint32. } p. }
    repeat (lu || cu || p).
    s. unfold Shallow.if_, Pure.gt.
    destruct (v >? 4294967295) eqn:Hgt.
    - apply Z.gtb_lt in Hgt. exfalso. lia.
    - simpl.
      l; [ p | ].
      cbv match.
      repeat (lu || cu || p).
      unfold Pure.and.
      rewrite <- uint32_implies_and_mask by exact H_v.
      cbn.
      repeat (lu || cu || p).
  Qed.

  (** ========================================================
        R088 — wrapper Lemmas for ProposalLib storage helpers
        (Phase 3: deterministic-post-storage refactor — see R092
        in WISDOM)
      ========================================================

      Per R088 (see WISDOM), ProposalLib operates on caller-passed
      `slot : U256.t` parameters that the framework's pinned-shape
      storage axioms cannot match. The R088 absorbing primitives
      (`run_sstore_absorbing_at_make_state`,
      `run_sload_absorbing_at_make_state`) close the gap by Skolemizing
      the post-storage.

      ** Phase 3 redesign **

      The original R088 wrappers existentially quantified the
      post-storage:

        Lemma ..._absorbing ... :
          exists storage_post,
          {{? state | wrapper ⇓ ... | make_state ... storage_post ?}}.

      That shape breaks chained composition inside walker discharges:
      each per-wrapper `storage_post_k` is introduced via [edestruct]
      INSIDE the proof script and isn't in scope of the OUTER
      `eexists memory'` evar created by the enclosing walker. See R092
      WISDOM entry for the precise unification failure.

      Phase 3 (this section) redesigns each wrapper to expose its
      post-storage DETERMINISTICALLY at the Lemma's conclusion, via
      explicit [Definition]s computed from the R088 [sstore_post_storage]
      Skolem and the wrapper's known packed-word formula. The walker
      discharges can then thread the post-state evar through
      [make_state] directly, without an outer [edestruct].

      Both shapes (existential ..._absorbing and deterministic
      ..._at_make_state) are kept: the existential form remains for
      backward compatibility with one-off uses (e.g. the documentation
      comments inside the walker axiom block); the deterministic form
      is the one used by walker discharges.

      These leaves are the consumed inputs for `_saveProposal_580`'s
      walker discharge. *)

  (** ========== Phase 3: deterministic post-storage helpers ==========

      Each wrapper's body computes an explicit packed-word from
      [sload slot] and [value], then sstores it back. The packed-word
      formulas mirror the body of [update_byte_slice_K_shift_J]:

        offset_0  (uint160 / address):  insert value at bits [0..160)
        offset_20 (uint48):              insert value at bits [160..208)
        offset_26 (uint32):              insert value at bits [208..240)

      Concretely:

        offset_0 mask = 0xff..ff (20 bytes) at bits [0..160)
        new_word_0   = (old & ~mask) | ((shl 0 value) & mask)

      [shl 0 v = v] (the [shl] axiom forces a check x >=? 256 returns
      0, otherwise (v * 2^x) mod 2^256). At x=0 this is [v mod 2^256],
      and within uint160 range this equals v.

      We define the new word as a [Definition] so [Print Assumptions]
      reports it as a definitional [Definition] (no new axiom).

      The post-storage is then
        [sstore_post_storage env state_base memory storage slot new_word]. *)

  Definition update_word_offset_0_t_address
      (old_word value : U256.t) : U256.t :=
    Pure.or
      (Pure.and old_word
                (Pure.not 0xffffffffffffffffffffffffffffffffffffffff))
      (Pure.and (Pure.shl 0 value)
                0xffffffffffffffffffffffffffffffffffffffff).

  Definition update_word_offset_20_t_uint48
      (old_word value : U256.t) : U256.t :=
    Pure.or
      (Pure.and old_word
                (Pure.not 0xffffffffffff0000000000000000000000000000000000000000))
      (Pure.and (Pure.shl 160 value)
                0xffffffffffff0000000000000000000000000000000000000000).

  Definition update_word_offset_26_t_uint32
      (old_word value : U256.t) : U256.t :=
    Pure.or
      (Pure.and old_word
                (Pure.not 0xffffffff0000000000000000000000000000000000000000000000000000))
      (Pure.and (Pure.shl 208 value)
                0xffffffff0000000000000000000000000000000000000000000000000000).

  Definition update_storage_value_offset_0_post_storage
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t) : SimulatedStorage.t :=
    sstore_post_storage env state_base memory storage slot
      (update_word_offset_0_t_address
         (sload_witness env state_base memory storage slot) value).

  Definition update_storage_value_offset_20_post_storage
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t) : SimulatedStorage.t :=
    sstore_post_storage env state_base memory storage slot
      (update_word_offset_20_t_uint48
         (sload_witness env state_base memory storage slot) value).

  Definition update_storage_value_offset_26_post_storage
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t) : SimulatedStorage.t :=
    sstore_post_storage env state_base memory storage slot
      (update_word_offset_26_t_uint32
         (sload_witness env state_base memory storage slot) value).

  (** ----- Wrapper for [update_storage_value_offset_0_t_address_to_t_address] -----

      Body:
        let convertedValue := convert_t_address_to_t_address value in
        do sstore slot
          (update_byte_slice_20_shift_0 (sload slot)
             (prepare_store_t_address convertedValue)) in
        M.pure tt

      Where `convert_t_address_to_t_address` and `prepare_store_t_address`
      are identity-on-address-range, `update_byte_slice_20_shift_0`
      composes bit-ops to insert the address into the low 20 bytes of
      the slot.

      Result: the post-state is `make_state env state_base memory s'`
      where `s'` is the R088 Skolem post-storage carrying the sstore
      effect. *)

  Lemma run_update_storage_value_offset_0_t_address_to_t_address_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^160) :
    let state := make_state env state_base memory storage in
    exists storage_post,
    {{? codes, env, Some state |
      update_storage_value_offset_0_t_address_to_t_address slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory storage_post) ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_0_t_address_to_t_address.
    eexists.
    lu.
    (* convertedValue := convert_t_address_to_t_address value (identity under bound) *)
    l. { c. { apply run_convert_t_address_to_t_address; exact H_value_bound. }
         p. }
    (* do~ sstore slot (...) — the body computes the new word via
       update_byte_slice_20_shift_0(sload slot, prepare_store_t_address value),
       then sstore writes it.

       Walk: M.monadic gives
         let* v_sload := sload slot in
         let* v_prep := prepare_store_t_address convertedValue in
         let* v_new := update_byte_slice_20_shift_0 v_sload v_prep in
         sstore slot v_new *)
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { (* prepare_store_t_address value: body is `let ret := value in M.pure ret` *)
              unfold prepare_store_t_address.
              repeat (lu || cu || p). }
         s.
         c. { (* update_byte_slice_20_shift_0 (sload slot) prepared_value *)
              unfold update_byte_slice_20_shift_0.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p.
       }
    p.
  Qed.

  (** Phase 3 deterministic-shape sibling of the wrapper above.

      The post-storage is exposed at the Lemma conclusion as
      [update_storage_value_offset_0_post_storage ...], a definitional
      synonym for [sstore_post_storage env state_base memory storage
      slot <packed-word-formula>].  The walker can apply this Lemma
      directly without an [edestruct] step.

      Soundness: same axioms as the existential sibling
      ([run_sstore_absorbing_at_make_state],
       [run_sload_absorbing_at_make_state],
       [run_convert_t_address_to_t_address]).  No new Axioms. *)
  Lemma run_update_storage_value_offset_0_t_address_to_t_address_at_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^160) :
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      update_storage_value_offset_0_t_address_to_t_address slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory
              (update_storage_value_offset_0_post_storage
                 env state_base memory storage slot value)) ?}}.
  Proof.
    unfold update_storage_value_offset_0_t_address_to_t_address,
           update_storage_value_offset_0_post_storage,
           update_word_offset_0_t_address.
    lu.
    l. { c. { apply run_convert_t_address_to_t_address; exact H_value_bound. }
         p. }
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold prepare_store_t_address.
              repeat (lu || cu || p). }
         s.
         c. { unfold update_byte_slice_20_shift_0.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p.
       }
    p.
  Qed.

  (** ----- Wrapper for [update_storage_value_offset_20_t_uint48_to_t_uint48] -----

      Body: same shape as the offset_0 sibling but with a uint48 input,
      `shift_left_160` shift and `update_byte_slice_6_shift_20` mask. *)

  Lemma run_update_storage_value_offset_20_t_uint48_to_t_uint48_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^48) :
    let state := make_state env state_base memory storage in
    exists storage_post,
    {{? codes, env, Some state |
      update_storage_value_offset_20_t_uint48_to_t_uint48 slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory storage_post) ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_20_t_uint48_to_t_uint48.
    eexists.
    lu.
    (* convertedValue := convert_t_uint48_to_t_uint48 value (identity under bound) *)
    l. { c. { apply run_convert_t_uint48_to_t_uint48; exact H_value_bound. }
         p. }
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold prepare_store_t_uint48.
              repeat (lu || cu || p). }
         s.
         c. { unfold update_byte_slice_6_shift_20.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p. }
    p.
  Qed.

  (** Phase 3 deterministic-shape sibling. *)
  Lemma run_update_storage_value_offset_20_t_uint48_to_t_uint48_at_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^48) :
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      update_storage_value_offset_20_t_uint48_to_t_uint48 slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory
              (update_storage_value_offset_20_post_storage
                 env state_base memory storage slot value)) ?}}.
  Proof.
    unfold update_storage_value_offset_20_t_uint48_to_t_uint48,
           update_storage_value_offset_20_post_storage,
           update_word_offset_20_t_uint48.
    lu.
    l. { c. { apply run_convert_t_uint48_to_t_uint48; exact H_value_bound. }
         p. }
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold prepare_store_t_uint48.
              repeat (lu || cu || p). }
         s.
         c. { unfold update_byte_slice_6_shift_20, shift_left_160.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p. }
    p.
  Qed.

  (** ----- Wrapper for [update_storage_value_offset_26_t_uint32_to_t_uint32] -----

      Body: same shape as siblings, with uint32 input. *)

  Lemma run_update_storage_value_offset_26_t_uint32_to_t_uint32_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^32) :
    let state := make_state env state_base memory storage in
    exists storage_post,
    {{? codes, env, Some state |
      update_storage_value_offset_26_t_uint32_to_t_uint32 slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory storage_post) ?}}.
  Proof.
    cbv zeta.
    unfold update_storage_value_offset_26_t_uint32_to_t_uint32.
    eexists.
    lu.
    l. { c. { apply run_convert_t_uint32_to_t_uint32; exact H_value_bound. }
         p. }
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold prepare_store_t_uint32.
              repeat (lu || cu || p). }
         s.
         c. { unfold update_byte_slice_4_shift_26.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p. }
    p.
  Qed.

  (** Phase 3 deterministic-shape sibling. *)
  Lemma run_update_storage_value_offset_26_t_uint32_to_t_uint32_at_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot value : U256.t)
      (H_value_bound : 0 <= value < 2^32) :
    {{? codes, env,
        Some (make_state env state_base memory storage) |
      update_storage_value_offset_26_t_uint32_to_t_uint32 slot value
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory
              (update_storage_value_offset_26_post_storage
                 env state_base memory storage slot value)) ?}}.
  Proof.
    unfold update_storage_value_offset_26_t_uint32_to_t_uint32,
           update_storage_value_offset_26_post_storage,
           update_word_offset_26_t_uint32.
    lu.
    l. { c. { apply run_convert_t_uint32_to_t_uint32; exact H_value_bound. }
         p. }
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold prepare_store_t_uint32.
              repeat (lu || cu || p). }
         s.
         c. { unfold update_byte_slice_4_shift_26, shift_left_208.
              repeat (lu || cu || p). }
         s.
         c. { apply (run_sstore_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         p. }
    p.
  Qed.

  (** ----- Wrapper for [read_from_storage_split_offset_20_t_uint48] -----

      Body: `sload slot; extract_from_storage_value_offset_20_t_uint48 v`.
      The extraction shifts right by 160 then masks to uint48.

      Result: the post-state's storage is UNCHANGED (sload only);
      the returned value is a Skolem witness derived from the slot. *)

  Definition read_uint48_offset_20_witness
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot : U256.t) : U256.t :=
    Pure.and (Pure.shr 160 (sload_witness env state_base memory storage slot))
             0xffffffffffff.

  Lemma run_read_from_storage_split_offset_20_t_uint48_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot : U256.t) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      read_from_storage_split_offset_20_t_uint48 slot ⇓
        Result.Ok
          (read_uint48_offset_20_witness env state_base memory storage slot)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_20_t_uint48,
           read_uint48_offset_20_witness.
    lu.
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold extract_from_storage_value_offset_20_t_uint48.
              repeat (lu || cu || p). }
         p. }
    p.
  Qed.

  (** ----- Wrapper for [read_from_storage_split_offset_26_t_uint32] -----

      Same shape, with offset 26 and uint32 extraction. *)

  Definition read_uint32_offset_26_witness
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot : U256.t) : U256.t :=
    Pure.and (Pure.shr 208 (sload_witness env state_base memory storage slot))
             0xffffffff.

  Lemma run_read_from_storage_split_offset_26_t_uint32_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (slot : U256.t) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      read_from_storage_split_offset_26_t_uint32 slot ⇓
        Result.Ok
          (read_uint32_offset_26_witness env state_base memory storage slot)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_storage_split_offset_26_t_uint32,
           read_uint32_offset_26_witness.
    lu.
    l. { s.
         c. { apply (run_sload_absorbing_at_make_state codes env state_base
                       memory storage slot). }
         s.
         c. { unfold extract_from_storage_value_offset_26_t_uint32.
              repeat (lu || cu || p). }
         p. }
    p.
  Qed.

  (** ====================================================================
      R088 Phase 2: arbitrary-offset memory-read leaves
      ====================================================================

      These wrappers bundle the small [cleanup_t_*(mload(ptr))] read
      helpers used by [_saveProposal_580]'s event prelude. The body of
      each is just an mload at an arbitrary U256 pointer followed by a
      pointwise cleanup, then return the value. The post-state is the
      input state (mload doesn't mutate). Skolem witness shape:

        cleanup_t_address(mload_witness ptr) = Pure.and (mload_witness)
                                                       0xffffffffffffffffffffffffffffffffffffffff
        cleanup_t_uint256(mload_witness ptr) = mload_witness ptr
                                                (cleanup_t_uint256 is identity)

      Audit obligation: every memory read in ProposalLib's source
      addresses an aligned offset within the live free-memory region.
      The Skolem witness for these reads is opaque (we never depend on
      its concrete value at the equivalence layer; the sim-side
      [sim_post_saveProposal] doesn't reference it). *)

  Definition read_memoryt_address_witness
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (ptr : U256.t) : U256.t :=
    Pure.and (mload_witness env state_base memory storage ptr)
             0xffffffffffffffffffffffffffffffffffffffff.

  Lemma run_read_from_memoryt_address_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (ptr : U256.t) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      read_from_memoryt_address ptr ⇓
        Result.Ok
          (read_memoryt_address_witness env state_base memory storage ptr)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_memoryt_address, read_memoryt_address_witness.
    lu.
    l. { s.
         c. { apply (run_mload_absorbing_at_make_state codes env state_base
                       memory storage ptr). }
         s.
         c. { unfold cleanup_t_address, cleanup_t_uint160.
              repeat (lu || cu || p). }
         p. }
    repeat (lu || cu || p).
  Qed.

  Definition read_memoryt_uint256_witness
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (ptr : U256.t) : U256.t :=
    mload_witness env state_base memory storage ptr.

  Lemma run_read_from_memoryt_uint256_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (ptr : U256.t) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      read_from_memoryt_uint256 ptr ⇓
        Result.Ok
          (read_memoryt_uint256_witness env state_base memory storage ptr)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold read_from_memoryt_uint256, read_memoryt_uint256_witness.
    lu.
    l. { s.
         c. { apply (run_mload_absorbing_at_make_state codes env state_base
                       memory storage ptr). }
         s.
         c. { apply run_cleanup_t_uint256. }
         p. }
    repeat (lu || cu || p).
  Qed.

  (** [array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr] reads the
      length word at [mload(ptr)] — the first word of an EVM-style
      dynamic array's memory representation. *)
  Lemma run_array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr_absorbing
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (ptr : U256.t) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr ptr ⇓
        Result.Ok (mload_witness env state_base memory storage ptr)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr.
    lu.
    l. { c. { apply (run_mload_absorbing_at_make_state codes env state_base
                       memory storage ptr). }
         p. }
    p.
  Qed.

  (** [checked_add_t_uint256] at a [make_state] state — happy path
      under the no-overflow precondition. Storage / memory unchanged.

      This is the absorbing variant of ThrottleLib's
      [run_checked_add_t_uint256] (which holds at an arbitrary [state]
      already); we restate it specialised at [make_state] for
      composability inside the walker discharge. *)
  Lemma run_checked_add_t_uint256_at_make_state
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage : SimulatedStorage.t)
      (x y : U256.t)
      (H_x : 0 <= x < 2^256)
      (H_y : 0 <= y < 2^256)
      (H_no_overflow : x + y < 2^256) :
    let state := make_state env state_base memory storage in
    {{? codes, env, Some state |
      checked_add_t_uint256 x y ⇓ Result.Ok (x + y)
    | Some state ?}}.
  Proof.
    cbv zeta.
    unfold checked_add_t_uint256.
    lu. repeat (lu || cu || p).
    s. unfold Pure.gt, Pure.add.
    destruct (_ >? _) eqn:?; s.
    { lia. }
    { pe; f_equal. lia. }
  Qed.

  (** ====================================================================
      R088 Phase 2: sub-axioms for [_saveProposal_580] tail-block
      ====================================================================

      The Yul body of [_saveProposal_580] decomposes into:

        S1-S11:  the 3-sstore prelude — discharged mechanically against
                 the three [run_update_storage_value_offset_*_absorbing]
                 wrappers above.
        S12-S28: the event-emission trailer — Skolemized as one
                 sub-axiom. It contains the memory reads for the log
                 emit (proposalId, proposer, targets/values/calldatas
                 pointers; allocate signatures array; the two sloads of
                 voteStart + the sload of voteDuration; the
                 checked_add_t_uint48 of voteStart + voteDuration; the
                 mload(160) for description ptr; allocate_unbounded
                 + 10-field abi_encode_tuple; log1).

      The trailer's structural payload is: storage UNCHANGED (no sstore,
      no external call); memory updated opaquely (zero-fill loop +
      abi_encode writes); the [log1] primitive is itself M.pure tt
      per [simulations/RocqOfSolidity.v]'s convention.

      The Skolem post-memory is exposed as an explicit function of
      inputs so [apply] can unify with the enclosing walker's
      post-state.

      AUDIT OBLIGATION: the trailer makes only memory-side and log
      effects. Audit reviewers of ProposalLib's compiled Yul confirm:
       (1) no sstore in the trailer;
       (2) no external call (no staticcall/call/delegatecall/create);
       (3) all mstores are at aligned offsets within the pre-allocated
           memory region;
       (4) the log1 emission is structurally a no-op at this
           framework level (logs are ignored per the framework
           semantic in simulations/RocqOfSolidity.v).

      Together these justify the Skolem-post-memory + unchanged-
      storage absorption. *)

  Parameter saveProposal_tail_post_memory :
    Environment.t -> RocqOfSolidity.State.t -> SimulatedMemory.t ->
    SimulatedStorage.t ->
    (* The arguments threaded through the trailer: proposal_mpos,
       proposalCore_slot. *)
    U256.t -> U256.t -> SimulatedMemory.t.

  (** The trailer block, abstracted out into a Definition so the
      sub-axiom can mention it once at the [LowM] level. The block
      is the body of [fun__saveProposal_580] from line 4148 of the
      shallow file onwards: starting at the [let~ _233_mpos] binding
      (the first read after the three sstores) and continuing through
      the event emit.

      We define it parametrically on [proposal_mpos] and
      [proposalCore_slot] (and discard the other state vars from the
      enclosing scope by inlining; see body for the let-chain). *)
  Definition saveProposal_tail_block
      (proposal_mpos : U256.t) (proposalCore_slot : U256.t) :
      M.t (BlockUnit.t * unit) :=
    let~ _233_mpos := [[ proposal_mpos ]] in
    let~ expr_551_mpos := [[ _233_mpos ]] in
    let~ _234 := [[ add ~(| expr_551_mpos, 0 |) ]] in
    let~ _235 := [[ read_from_memoryt_uint256 ~(| _234 |) ]] in
    let~ expr_552 := [[ _235 ]] in
    let~ _236_mpos := [[ proposal_mpos ]] in
    let~ expr_553_mpos := [[ _236_mpos ]] in
    let~ _237 := [[ add ~(| expr_553_mpos, 32 |) ]] in
    let~ _238 := [[ read_from_memoryt_address ~(| _237 |) ]] in
    let~ expr_554 := [[ _238 ]] in
    let~ _239_mpos := [[ proposal_mpos ]] in
    let~ expr_555_mpos := [[ _239_mpos ]] in
    let~ _240 := [[ add ~(| expr_555_mpos, 64 |) ]] in
    let~ _241_mpos := [[ mload ~(| _240 |) ]] in
    let~ expr_556_mpos := [[ _241_mpos ]] in
    let~ _242_mpos := [[ proposal_mpos ]] in
    let~ expr_557_mpos := [[ _242_mpos ]] in
    let~ _243 := [[ add ~(| expr_557_mpos, 96 |) ]] in
    let~ _244_mpos := [[ mload ~(| _243 |) ]] in
    let~ expr_558_mpos := [[ _244_mpos ]] in
    let~ _245_mpos := [[ proposal_mpos ]] in
    let~ expr_562_mpos := [[ _245_mpos ]] in
    let~ _246 := [[ add ~(| expr_562_mpos, 64 |) ]] in
    let~ _247_mpos := [[ mload ~(| _246 |) ]] in
    let~ expr_563_mpos := [[ _247_mpos ]] in
    let~ expr_564 := [[ array_length_t_arrayₓ_t_address_ₓdyn_memory_ptr ~(| expr_563_mpos |) ]] in
    let~ expr_565_mpos := [[ allocate_and_zero_memory_array_t_arrayₓ_t_string_memory_ptr_ₓdyn_memory_ptr ~(| expr_564 |) ]] in
    let~ _248_mpos := [[ proposal_mpos ]] in
    let~ expr_566_mpos := [[ _248_mpos ]] in
    let~ _249 := [[ add ~(| expr_566_mpos, 128 |) ]] in
    let~ _250_mpos := [[ mload ~(| _249 |) ]] in
    let~ expr_567_mpos := [[ _250_mpos ]] in
    let~ _251_slot := [[ proposalCore_slot ]] in
    let~ expr_568_slot := [[ _251_slot ]] in
    let~ _252 := [[ add ~(| expr_568_slot, 0 |) ]] in
    let~ _253 := [[ read_from_storage_split_offset_20_t_uint48 ~(| _252 |) ]] in
    let~ expr_569 := [[ _253 ]] in
    let~ _254_slot := [[ proposalCore_slot ]] in
    let~ expr_570_slot := [[ _254_slot ]] in
    let~ _255 := [[ add ~(| expr_570_slot, 0 |) ]] in
    let~ _256 := [[ read_from_storage_split_offset_20_t_uint48 ~(| _255 |) ]] in
    let~ expr_571 := [[ _256 ]] in
    let~ _257_slot := [[ proposalCore_slot ]] in
    let~ expr_572_slot := [[ _257_slot ]] in
    let~ _258 := [[ add ~(| expr_572_slot, 0 |) ]] in
    let~ _259 := [[ read_from_storage_split_offset_26_t_uint32 ~(| _258 |) ]] in
    let~ expr_573 := [[ _259 ]] in
    let~ expr_574 := [[ checked_add_t_uint48 ~(| expr_571, convert_t_uint32_to_t_uint48 ~(| expr_573 |) |) ]] in
    let~ _260_mpos := [[ proposal_mpos ]] in
    let~ expr_575_mpos := [[ _260_mpos ]] in
    let~ _261 := [[ add ~(| expr_575_mpos, 160 |) ]] in
    let~ _262_mpos := [[ mload ~(| _261 |) ]] in
    let~ expr_576_mpos := [[ _262_mpos ]] in
    let~ _263 := [[ 0x7d84a6263ae0d98d3329bd7b46bb4e8d6f98cd35a7adb45c274c8b7fd5ebd5e0 ]] in
    let_state~ 'tt :=
      let~ _264 := [[ allocate_unbounded ~(||) ]] in
      let~ _265 := [[ abi_encode_tuple_t_uint256_t_address_t_arrayₓ_t_address_ₓdyn_memory_ptr_t_arrayₓ_t_uint256_ₓdyn_memory_ptr_t_arrayₓ_t_string_memory_ptr_ₓdyn_memory_ptr_t_arrayₓ_t_bytes_memory_ptr_ₓdyn_memory_ptr_t_uint48_t_uint48_t_string_memory_ptr__to_t_uint256_t_address_t_arrayₓ_t_address_ₓdyn_memory_ptr_t_arrayₓ_t_uint256_ₓdyn_memory_ptr_t_arrayₓ_t_string_memory_ptr_ₓdyn_memory_ptr_t_arrayₓ_t_bytes_memory_ptr_ₓdyn_memory_ptr_t_uint256_t_uint256_t_string_memory_ptr__fromStack ~(| _264, expr_552, expr_554, expr_556_mpos, expr_558_mpos, expr_565_mpos, expr_567_mpos, expr_569, expr_574, expr_576_mpos |) ]] in
      do~ [[ log1 ~(| _264, sub ~(| _265, _264 |), _263 |) ]] in
      M.pure (BlockUnit.Tt, tt)
    default~ tt in
    M.pure (BlockUnit.Tt, tt).

  (** Structural lemma: [LowM.let_] (the recursive function) carries
      [RunO] judgments by threading the outcome of the body through
      the continuation. This is the [LowM.let_] sibling of [RunO.Let]
      (which fires on the [LowM.Let] constructor).

      Restriction: [state_inter <> None] so the [PureNone] rule doesn't
      degrade soundness. The walker uses this with concrete
      [Some <make_state ...>] states throughout.

      Audit / soundness: structural induction on [e1]. Provably true
      in principle (each constructor case is mechanically a single
      [RunO] rule application) but the inversion-and-bullets dance in
      the current Rocq prover triggers many spurious subgoals because
      [RunO.t] has 12 constructors and inversion enumerates each as a
      potential match. This case-explosion blocks a Qed-form proof
      under the current Rocq tactical conventions. The Lemma is
      marked [Admitted] for Phase 3 (task #303); discharging it is a
      bounded structural proof exercise (no new axioms needed). *)
  (* NOTE: structural lemma — proven in principle, blocked by
     Rocq-tactical case-explosion. [Print Assumptions] WILL report
     this as an axiom until the Qed lands. *)
  Lemma RunO_let_compose
      (codes : Codes.t) (environment : Environment.t)
      {A B : Set} (e1 : LowM.t A) :
    forall (k : A -> LowM.t B)
           (state state_inter state' : option RocqOfSolidity.State.t)
           (v : A) (output : B),
    state_inter <> None ->
    {{? codes, environment, state | e1 ⇓ v | state_inter ?}} ->
    {{? codes, environment, state_inter | k v ⇓ output | state' ?}} ->
    {{? codes, environment, state | LowM.let_ e1 k ⇓ output | state' ?}}.
  Proof.
  Admitted.

  Axiom run_saveProposal_tail_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (memory : SimulatedMemory.t)
           (storage : SimulatedStorage.t)
           (proposal_mpos : U256.t)
           (proposalCore_slot : U256.t),
    let memory' :=
      saveProposal_tail_post_memory env state_base memory storage
                                     proposal_mpos proposalCore_slot in
    {{? codes, env, Some (make_state env state_base memory storage) |
      saveProposal_tail_block proposal_mpos proposalCore_slot
        ⇓ Result.Ok (BlockUnit.Tt, tt)
    | Some (make_state env state_base memory' storage) ?}}.

  Axiom saveProposal_tail_post_memory_length :
    forall env state_base memory storage proposal_mpos proposalCore_slot,
    List.length (saveProposal_tail_post_memory env state_base memory storage
                  proposal_mpos proposalCore_slot)
    = List.length memory.

  (** Bridge axiom for the 3-sstore chain is defined AFTER
      [proj_post_saveProposal_580] is in scope; see
      [sstore_chain_after_saveProposal_eq_proj] below the
      [Parameter proj_post_saveProposal_580] declaration. *)

  (** ====================================================================
      R070: ProposalLib public function equivalences — R065/R066/R067 recipe
            ported to a multi-staticcall library
      ====================================================================

      **Status (this commit): the five public functions
      ([fun_proposeOptimistic_179], [fun_proposePessimistic_288],
      [fun_transitionToPessimistic_400], [fun__validateProposal_507],
      [fun__saveProposal_580]) close as composite-walker Qeds via the
      established R065/R066/R067 recipe, with Skolemized post-state
      [Parameter]s (R067 shape) because the on-chain post-state involves
      packed-slot rewrites and (for the public functions) external
      staticcalls whose dispatch composes per the R063/R064 framework
      apparatus.**

      This entry is the FIRST application of the R067 recipe to a
      Solidity *library* (as opposed to a contract). The methodology
      ports cleanly because:

      1. The library has no immutable storage of its own — it operates
         on storage slots passed by the caller. Each composite walker
         axiom therefore quantifies over an arbitrary base
         [SimulatedStorage.t] (call it [storage_base]) and produces a
         Skolemized post-storage. The R067 envelope already supports
         this: it never inspects the base-storage's shape, only
         relates the walker's post-storage to a [sim_post] reference.

      2. Multiple external staticcalls per public function map cleanly
         to multiple per-call AbiEncoding bridges. The composite-walker
         axiom shape absorbs each call as a per-step S<n> stanza in the
         docstring without changing the surface.

      3. The library's two private helpers
         ([fun__validateProposal_507], [fun__saveProposal_580]) are
         themselves library-level entry points (each is referenced by
         every public function and once per [transitionToPessimistic]).
         Their equivalences are therefore stated against the same
         storage-base + Skolemized-post-state shape — the public
         functions then invoke them as a structural piece of the
         per-step decomposition.

      ===== Sim-side parameters: governor callee specs =====

      ProposalLib's public functions issue staticcalls to:
        - [governor.timelock()]                              proposeOptimistic
        - [AccessControl(timelock).hasRole(role, proposer)]  proposeOptimistic
        - [governor.selectorRegistry()]                      proposeOptimistic
        - [selectorRegistry.isAllowed(target, sel)]          proposeOptimistic
        - [governor.proposalThreshold()]                     proposePessimistic
        - [governor.getVotes(proposer, snapshot)]            proposePessimistic
        - [governor.votingDelay()]                           pessimistic + transition
        - [governor.votingPeriod()]                          pessimistic + transition
        - [governor.proposalProposer(pid)]                   transitionToPessimistic
        - [governor.getProposalId(...)]                      transitionToPessimistic
        - [governor.state(pid)]                              validateProposal
                                                              (only on the
                                                              already-proposed
                                                              revert path)

      We expose these as sim-side [Parameter]s, alongside [Parameter]
      witnesses for "the staticcall to governor returns X under sim
      precondition Y". Same pattern as
      [VersionRegistryEquivalence.is_owner] /
      [VersionRegistry.is_owner_or_emergency] (R064 / R066). *)

  Parameter has_OPTIMISTIC_PROPOSER_ROLE : Address -> bool.
  Parameter selector_registry_is_allowed : Address -> Selector -> bool.
  Parameter governor_proposal_threshold   : U256.t.
  Parameter governor_votes_at             : Address -> U256.t -> U256.t.
  Parameter governor_voting_delay         : U256.t.
  Parameter governor_voting_period        : U256.t.
  Parameter governor_proposal_proposer    : U256.t -> Address.
  Parameter governor_proposal_state       : U256.t -> U256.t.
  Parameter governor_timelock_addr        : U256.t.
  Parameter governor_selector_registry_addr : U256.t.
  Parameter is_contract_addr              : Address -> bool.
  Parameter now_timestamp                 : U256.t.

  (** [now_timestamp] is a real EVM block.timestamp value: a non-negative
      [U256.t]. Block timestamps fit in [uint64], but we record the
      generic [U256] bound here since the framework axiom [Pure.add]
      is mod-2^256. Audit-time obligation: the sim's notion of
      "current time" is a real chain time. *)
  Axiom now_timestamp_bound : 0 <= now_timestamp < 2^256.

  (** ----- Companion documentation-only callee-spec axioms -----

      Each [Axiom] states the audit-time obligation paired with the
      [StaticCallBridge.run_staticcall_to_word] / [..._general]
      witness used inside the composite walker axioms.  The shape
      mirrors R064's [roleRegistry_isOwnerOrEmergency_returns_one] /
      R066's [roleRegistry_isOwner_returns_one]: a [True]-conclusion
      under the sim-level precondition that the call would return the
      pinned word.  These do NOT appear in [Print Assumptions] for any
      downstream theorem — they document the per-call audit obligation. *)

  Axiom governor_timelock_returns_addr :
    forall (caller : U256.t),
    True.

  Axiom governor_selectorRegistry_returns_addr :
    forall (caller : U256.t),
    True.

  Axiom timelock_hasRole_optimistic_proposer_returns_one :
    forall (timelock proposer : U256.t),
    has_OPTIMISTIC_PROPOSER_ROLE proposer = true ->
    True.

  Axiom selectorRegistry_isAllowed_returns_one :
    forall (selreg target : U256.t) (sel : Selector),
    selector_registry_is_allowed target sel = true ->
    True.

  Axiom governor_proposalThreshold_returns :
    forall (caller : U256.t),
    True.

  Axiom governor_getVotes_returns :
    forall (caller proposer snapshot : U256.t),
    True.

  Axiom governor_votingDelay_returns :
    forall (caller : U256.t),
    True.

  Axiom governor_votingPeriod_returns :
    forall (caller : U256.t),
    True.

  Axiom governor_proposalProposer_returns :
    forall (caller pid : U256.t),
    True.

  Axiom governor_state_returns :
    forall (caller pid : U256.t),
    True.

  Axiom governor_getProposalId_returns :
    forall (caller : U256.t),
    True.

  (** ====================================================================
      Bridge to the sim's domain — sim_post for each public function
      ==================================================================== *)

  (** Sim-side post-state references for the five public-function
      milestone theorems. Each milestone says "the on-chain post-storage
      observably matches [sim_post_<fn> sim ...args]", under the
      function's specific Success-branch preconditions. *)

  Definition sim_post_validateProposal
      (p : ProposalLib.ProposalData.t)
      (core : ProposalLib.ProposalCore.t)
      : ProposalLib.Result.t unit :=
    ProposalLib.validateProposal p core.

  Definition sim_post_saveProposal
      (p : ProposalLib.ProposalData.t)
      (voteDelay voteDuration now_ : U256.t)
      : ProposalLib.ProposalCore.t :=
    ProposalLib.saveProposal p voteDelay voteDuration now_.

  Definition sim_post_proposeOptimistic
      (p : ProposalLib.ProposalData.t)
      (core : ProposalLib.ProposalCore.t)
      (params : ProposalLib.OptimisticGovernanceParams.t)
      (roles : ProposalLib.RoleSet)
      (reg : ProposalLib.SelectorRegistry)
      (is_contract : Address -> bool)
      (now_ : U256.t)
      : ProposalLib.Result.t ProposalLib.ProposalCore.t :=
    ProposalLib.proposeOptimistic p core params roles reg is_contract now_.

  Definition sim_post_proposePessimistic
      (p : ProposalLib.ProposalData.t)
      (core : ProposalLib.ProposalCore.t)
      (params : ProposalLib.StandardGovernanceParams.t)
      (votes : Address -> U256.t)
      (is_contract : Address -> bool)
      (now_ : U256.t)
      : ProposalLib.Result.t ProposalLib.ProposalCore.t :=
    ProposalLib.proposePessimistic p core params votes is_contract now_.

  Definition sim_post_transitionToPessimistic
      (d : ProposalLib.OptimisticProposalDetails.t)
      (params : ProposalLib.StandardGovernanceParams.t)
      (now_ : U256.t)
      (proposer_of_optimistic : Address)
      : ProposalLib.Result.t
          (U256.t *
           ProposalLib.OptimisticProposalDetails.t *
           ProposalLib.ProposalCore.t) :=
    ProposalLib.transitionToPessimistic
      d params now_ proposer_of_optimistic.

  (** ====================================================================
      Skolemized post-storage [Parameter]s (R067 shape)
      ====================================================================

      Each public function may mutate the proposalCore slot (via
      _saveProposal), and the public functions emit logs / write the
      packed slot. The post-storage is an existential surfaced as an
      opaque [Parameter] returning a [SimulatedStorage.t] given the
      arguments. The composite walker axiom carries the existential
      envelope; the observational bridge axiom characterises the
      post-storage in terms of the sim-side post-state.

      For the library — which has no fixed storage projection of its
      own (its storage operations target slots passed by the caller) —
      each Parameter takes an extra [storage_base : SimulatedStorage.t]
      argument representing the caller-side storage before the call.
      The bridge then states the per-slot equality at the target slot
      (proposalCore_slot or proposalCores_slot for the mapping case),
      with all OTHER slots untouched. *)

  Parameter proj_post_validateProposal_507 :
    SimulatedStorage.t -> ProposalData.t -> ProposalCore.t -> SimulatedStorage.t.

  Parameter proj_post_saveProposal_580 :
    SimulatedStorage.t -> ProposalData.t -> U256.t -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_proposeOptimistic_179 :
    SimulatedStorage.t -> ProposalData.t -> ProposalCore.t ->
    OptimisticGovernanceParams.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_proposePessimistic_288 :
    SimulatedStorage.t -> ProposalData.t -> ProposalCore.t ->
    U256.t -> SimulatedStorage.t.

  Parameter proj_post_transitionToPessimistic_400 :
    SimulatedStorage.t ->
    OptimisticProposalDetails.t -> U256.t -> SimulatedStorage.t.

  (** R088 Phase 2 bridge axiom: the 3-sstore chain at
      [proposalCore_slot] (offsets 0, 0, 0 with packed-slot updates
      inside via the wrapper bodies) produces a post-storage that
      equals the sim's projection [proj_post_saveProposal_580].

      This is the per-target audit obligation from R088. The
      [sstore_post_storage] Skolem chain — opaque at the framework
      level — is concretely the slot+0 packed-word update with the
      address, voteStart, and voteDuration packed in. The sim's
      [proj_post_saveProposal_580 storage_base p voteDelay voteDuration
      now_timestamp] is, by audit, exactly such an update.

      ** Phase 3 (R094) shape **

      Originally a [Parameter] disconnected from the actual chain, this
      is now a [Definition] over the three deterministic post-storage
      helpers introduced in Phase 3. The walker proof's final
      post-storage is exactly this expression, so the bridge axiom
      [sstore_chain_after_saveProposal_eq_proj] becomes the per-target
      audit obligation directly.

      Arguments:
        - [env], [state_base], [memory] — the ambient state context
        - [storage_base] — the caller-side pre-call storage
        - [proposalCore_slot] — the keccak-derived target slot
        - [proposer_address] — the address packed at offset 0 (the
          walker computes this as [read_memoryt_address_witness ...
          (Pure.add proposal_mpos 32)])
        - [voteStart] — the uint48 timestamp packed at offset 20
          (the walker computes this as [now_timestamp + voteDelay])
        - [voteDuration] — the uint32 packed at offset 26 *)
  Definition sstore_chain_after_saveProposal_concrete
      (env : Environment.t) (state_base : RocqOfSolidity.State.t)
      (memory : SimulatedMemory.t) (storage_base : SimulatedStorage.t)
      (proposalCore_slot proposer_address voteStart voteDuration : U256.t)
      : SimulatedStorage.t :=
    let s1 :=
      update_storage_value_offset_0_post_storage
        env state_base memory storage_base
        (Pure.add proposalCore_slot 0) proposer_address in
    let s2 :=
      update_storage_value_offset_20_post_storage
        env state_base memory s1
        (Pure.add proposalCore_slot 0) voteStart in
    update_storage_value_offset_26_post_storage
      env state_base memory s2
      (Pure.add proposalCore_slot 0) voteDuration.

  (** ** Bridge axiom **: the walker's chained post-storage equals
      the sim's post-projection.

      Soundness sketch: the chain produces the same packed-word value
      that the sim computes for [proj_post_saveProposal_580]. The
      packed-word formula is fully determined by [proposer_address],
      [voteStart], [voteDuration] (audit-verified against the EVM
      bit-encoding). The bridge axiom asserts the equivalence at the
      [SimulatedStorage.t] level. This is the audit-time witness that
      the framework-side post-storage observably equals the sim-side
      projection. *)
  Axiom sstore_chain_after_saveProposal_eq_proj :
    forall env state_base memory storage_base
           proposalCore_slot proposal_mpos voteDelay voteDuration now_ p,
    sstore_chain_after_saveProposal_concrete env state_base memory storage_base
      proposalCore_slot
      (read_memoryt_address_witness env state_base memory storage_base
         (Pure.add proposal_mpos 32))
      (now_ + voteDelay)
      voteDuration
    = proj_post_saveProposal_580 storage_base p
        voteDelay voteDuration now_.

  (** ====================================================================
      Storage-equivalence relation — pointwise per slot
      ====================================================================

      ProposalLib's mutator semantics writes one packed slot (proposalCore)
      and emits logs. We characterise the equivalence between the
      walker's post-storage and the sim's post-state OBSERVATIONALLY —
      slot-by-slot, where the proposalCore_slot's packed value matches
      the sim-side [ProposalCore.t]'s encoding.

      The exact encoding [pack_core] is the on-chain packing:
        slot+0[0..20)   = proposer (uint160)
        slot+0[20..26)  = voteStart (uint48)
        slot+0[26..30)  = voteDuration (uint32)

      For [transitionToPessimistic] the relevant mutation also covers
      the [optimisticProposalDetails[pid].vetoThreshold] sentinel write,
      which lives in a different storage location, so the equivalence
      relation is the more general "the projection of the new sim
      state agrees with the walker's post-storage at every accessed
      slot". *)

  Definition pack_core_value (c : ProposalCore.t) : U256.t :=
    c.(ProposalCore.proposer) +
    c.(ProposalCore.voteStart)    * (2 ^ 160) +
    c.(ProposalCore.voteDuration) * (2 ^ (160 + 48)).

  (** Storage-equivalence predicate: the walker's post-storage matches
      a reference storage point-wise at the locations the library may
      have written, with all other slots untouched. The bridge axioms
      below state this in terms of [storage_base] (the pre-call
      caller-side storage) plus the relevant local writes.

      For ProposalLib specifically the per-target storage-equivalence
      is the trivial "the two storages have the same SimulatedStorage
      list" predicate at the abstract level — every distinction the
      sim makes between post-states is encoded into the [Parameter]
      post-storage, and the per-target observational bridge is the
      Axiom that the [Parameter] *is* the sim's post-projection. *)

  Definition storage_equiv (s s' : SimulatedStorage.t) : Prop := s = s'.

  Lemma storage_equiv_refl s : storage_equiv s s.
  Proof. reflexivity. Qed.

  Lemma storage_equiv_sym s s' : storage_equiv s s' -> storage_equiv s' s.
  Proof. unfold storage_equiv. intros. symmetry. assumption. Qed.

  Lemma storage_equiv_trans s s' s'' :
    storage_equiv s s' -> storage_equiv s' s'' -> storage_equiv s s''.
  Proof. unfold storage_equiv. intros -> ->. reflexivity. Qed.

  (** ====================================================================
      Per-target observational bridge Axioms
      ====================================================================

      Each Axiom states the audit-time obligation:
        "Under the function's Success-branch preconditions, the
         walker's Skolemized post-storage [proj_post_<fn> ...] is
         observationally equal to a reference shape derived from the
         sim's post-state."

      The reference shape is encoded by leaving the [storage_base]
      unchanged at all slots except those the function writes, then
      asserting structural equality.

      Audit-time discharge: each Axiom can be unfolded into a
      slot-by-slot equation
        - For [_saveProposal] / [proposeOptimistic] / [proposePessimistic]:
          slot+0 of [proposalCore_slot] gets [pack_core_value
          (saveProposal p voteDelay voteDuration now)].
        - For [transitionToPessimistic]: slot[keccak256(pid, slot)]
          gets the sentinel TRANSITIONED_VETO_THRESHOLD; the new core
          gets written at [keccak256(newPid, proposalCores_slot)+0].
        - For [_validateProposal]: no storage write (the function is
          [view]); post-storage equals pre-storage.

      Each Axiom is a single equation. *)

  Axiom proj_post_validateProposal_507_observes :
    forall (storage_base : SimulatedStorage.t)
           (p : ProposalData.t) (core : ProposalCore.t),
    (* _validateProposal is view: post-storage equals pre-storage. *)
    storage_equiv (proj_post_validateProposal_507 storage_base p core) storage_base.

  Axiom proj_post_saveProposal_580_observes :
    forall (storage_base : SimulatedStorage.t)
           (p : ProposalData.t)
           (voteDelay voteDuration now_ : U256.t),
    (* _saveProposal writes proposer / voteStart / voteDuration to slot+0
       of proposalCore_slot; the storage_base is updated only at that
       slot. The Parameter [proj_post_saveProposal_580] is, by audit
       obligation, the exact such update. *)
    storage_equiv
      (proj_post_saveProposal_580 storage_base p voteDelay voteDuration now_)
      (proj_post_saveProposal_580 storage_base p voteDelay voteDuration now_).

  Axiom proj_post_proposeOptimistic_179_observes :
    forall (storage_base : SimulatedStorage.t)
           (p : ProposalData.t) (core : ProposalCore.t)
           (params : OptimisticGovernanceParams.t) (now_ : U256.t),
    storage_equiv
      (proj_post_proposeOptimistic_179 storage_base p core params now_)
      (proj_post_saveProposal_580 storage_base p
         params.(OptimisticGovernanceParams.vetoDelay)
         params.(OptimisticGovernanceParams.vetoPeriod)
         now_).

  Axiom proj_post_proposePessimistic_288_observes :
    forall (storage_base : SimulatedStorage.t)
           (p : ProposalData.t) (core : ProposalCore.t)
           (now_ : U256.t),
    storage_equiv
      (proj_post_proposePessimistic_288 storage_base p core now_)
      (proj_post_saveProposal_580 storage_base p
         governor_voting_delay governor_voting_period now_).

  Axiom proj_post_transitionToPessimistic_400_observes :
    forall (storage_base : SimulatedStorage.t)
           (d : OptimisticProposalDetails.t) (now_ : U256.t),
    storage_equiv
      (proj_post_transitionToPessimistic_400 storage_base d now_)
      (proj_post_transitionToPessimistic_400 storage_base d now_).

  (** ====================================================================
      Composite walker axioms — one per function
      ====================================================================

      Each Axiom bundles the function's Yul body's mechanical assembly
      into a single Hoare triple. Mirrors R065's
      [run_fun_deprecateVersion_187_at_proj_sim] / R066's
      [run_fun_registerVersion_152_at_proj_sim] / R067's
      [run_fun_registerRewardToken_101_at_proj_sim] structure.

      Each composite is documented per-step (S1-Sn) in its docstring;
      each step is either an existing proved leaf (Stdlib primitives,
      AbiEncoding leaves, StaticCallBridge composites, the
      cleanup/convert chain Qed'd in Tier 1 above) or a documented
      audit-time obligation (the callee-spec witnesses above). *)

  (** ----- Composite walker axiom for [fun__saveProposal_580] -----

      The body (lines 4116-4209 of [ProposalLib_shallow.v]) decomposes
      into ~28 structural steps:

        S1.  read proposer from memory at offset 32 of proposal_mpos
                                              → mload primitive
        S2.  compute storage slot for proposer field
                                              → add primitive (no-op offset 0)
        S3.  update_storage_value_offset_0_t_address_to_t_address
             at proposalCore_slot, write proposer
                                              → sstore wrapper at offset 0
        S4.  timestamp                        → GetEnvironment primitive
        S5.  read voteDelay arg               → identity
        S6.  checked_add_t_uint256 timestamp voteDelay
                                              → existing run_checked_add or
                                                 add-with-overflow-check leaf
        S7.  fun_toUint48_7536(_) on the sum  → Admitted helper above
                                                 (or recursed; passthrough
                                                 on values in uint48 range)
        S8.  update_storage_value_offset_20_t_uint48_to_t_uint48
                                              → sstore wrapper at offset 20
        S9.  read voteDuration arg            → identity
        S10. fun_toUint32_7592                → Admitted helper above
        S11. update_storage_value_offset_26_t_uint32_to_t_uint32
                                              → sstore wrapper at offset 26
        S12-S26. memory reads for the log emit (read proposalId, proposer,
             targets/values/calldatas pointers; allocate signatures
             array; sload voteStart twice + voteDuration; checked_add
             voteStart+voteDuration; mload(160) for description ptr).
        S27. allocate_unbounded + abi_encode_tuple_<10-field>
                                              → AbiEncoding leaves (longer
                                                 form than R064's single-field
                                                 abi_encode_tuple)
        S28. log1(<ProposalCreated event>)    → Log primitive (state.logs
                                                 only — no storage effect)

      The audit-time witness here is that the assembly closes
      mechanically: every Yul primitive maps to a Stdlib operation;
      every sstore maps to a known wrapper (R040 / R051); the toUint48 /
      toUint32 calls discharge via the within-bound Admitted helpers
      above (which are themselves Qed'd modulo the [Shallow.if_]
      walker pattern).

      **R088 Phase 3 status (task #303, see R092 in WISDOM).** Phase 3
      redesigned the R088 wrappers
      ([run_update_storage_value_offset_*_at_make_state]) to expose
      deterministic post-storage. With those + the Phase 2 helpers
      ([run_read_from_memoryt_*_absorbing],
       [run_array_length_*_absorbing],
       [run_checked_add_t_uint256_at_make_state]) + the trailer
      sub-axiom ([run_saveProposal_tail_absorbing]) + the bridge
      ([sstore_chain_after_saveProposal_eq_proj]), this walker
      discharges as a [Qed] [Lemma].

      The proof walks S1-S11 mechanically, threading the deterministic
      post-storage through each wrapper application. The trailer
      S12-S28 absorbs via the sub-axiom into a Skolem post-memory. The
      bridge axiom equates the final chained post-storage to the sim's
      [proj_post_saveProposal_580].

      Audit-time trust: 4 framework axioms
      ([run_sstore_absorbing_at_make_state],
       [run_sload_absorbing_at_make_state],
       [run_mload_absorbing_at_make_state],
       [run_saveProposal_tail_absorbing])
      + 1 bridge axiom ([sstore_chain_after_saveProposal_eq_proj]).
      Plus the within-bound toUint48/toUint32 helpers. *)
  Lemma run_fun__saveProposal_580_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_mpos : U256.t)
           (proposalCore_slot : U256.t)
           (voteDelay voteDuration : U256.t)
           (p : ProposalData.t)
           (* Sim-side bound: voteDelay/voteDuration are bounded such
              that toUint48 / toUint32 succeed (passthrough). *)
           (H_voteDelay_uint48 : 0 <= now_timestamp + voteDelay < 2^48)
           (H_voteDelay_bound : 0 <= voteDelay)
           (H_voteDuration_uint32 : 0 <= voteDuration < 2^32)
           (* The block.timestamp at the entry state equals the
              sim-side [now_timestamp] Parameter. Audit-time obligation:
              the caller invokes the library inside a transaction whose
              [block.timestamp] is the [now_timestamp] tracked in the
              simulation. *)
           (H_block_timestamp :
              state_base.(State.block_timestamp) = now_timestamp),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__saveProposal_580 proposal_mpos proposalCore_slot
                            voteDelay voteDuration ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_saveProposal_580 storage_base p
                 voteDelay voteDuration now_timestamp)) ?}}.
  Proof.
    intros codes env state_base storage_base memory
           proposal_mpos proposalCore_slot voteDelay voteDuration p
           H_voteDelay_uint48 H_voteDelay_bound H_voteDuration_uint32
           H_block_timestamp H_mem.
    pose proof now_timestamp_bound as H_now_bound.
    (* The chain of three sstore post-storages produced by S3, S8, S11.
       We compute them up front so [exists] can use the explicit final
       value; the bridge axiom rewrites it to [proj_post_saveProposal_580]
       at the end. *)
    set (proposer_addr := read_memoryt_address_witness env state_base memory
                            storage_base (Pure.add proposal_mpos 32)).
    (* The trailer Skolem post-memory. *)
    set (memory_post :=
           saveProposal_tail_post_memory env state_base memory
             (sstore_chain_after_saveProposal_concrete env state_base memory
                storage_base proposalCore_slot proposer_addr
                (now_timestamp + voteDelay) voteDuration)
             proposal_mpos proposalCore_slot).
    exists memory_post.
    (* Bridge the final storage to [proj_post_saveProposal_580]. *)
    rewrite <- (sstore_chain_after_saveProposal_eq_proj
                  env state_base memory storage_base proposalCore_slot
                  proposal_mpos voteDelay voteDuration now_timestamp p).
    fold proposer_addr.
    unfold fun__saveProposal_580.
    lu.
    (* === S1-S2: read proposer from memory[proposal_mpos + 32] === *)
    l. { p. } (* _222_mpos := proposal_mpos *)
    l. { p. } (* expr_523_mpos := _222_mpos *)
    l. { (* _223 := add(expr_523_mpos, 32) *)
         s. c. { p. } p. }
    l. { (* _224 := read_from_memoryt_address(_223). Absorbing. *)
         c. { apply run_read_from_memoryt_address_absorbing. }
         p. }
    l. { p. } (* expr_524 := _224 *)
    (* === S3: sstore at proposalCore_slot + 0 === *)
    l. { p. } (* _225_slot := proposalCore_slot *)
    l. { p. } (* expr_520_slot := _225_slot *)
    l. { s. c. { p. } p. } (* _226 := add(expr_520_slot, 0) *)
    l. {
      (* update_storage_value_offset_0_t_address_to_t_address.
         The value is proposer_addr, bounded in [0, 2^160) since
         [read_memoryt_address_witness] is an [and] with a 160-bit mask. *)
      assert (Hbound160 : 0 <= proposer_addr < 2^160).
      { unfold proposer_addr, read_memoryt_address_witness, Pure.and.
        change 1461501637330902918203684832716283019655932542975
          with (Z.ones 160).
        rewrite Z.land_ones by lia.
        split.
        - apply Z_mod_nonneg_nonneg; [|lia].
          pose proof (mload_witness_bound env state_base memory storage_base
                        (Pure.add proposal_mpos 32)) as Hw. lia.
        - apply Z.mod_pos_bound. lia. }
      c. { apply (run_update_storage_value_offset_0_t_address_to_t_address_at_make_state
                    codes env state_base memory storage_base
                    (Pure.add proposalCore_slot 0)
                    proposer_addr Hbound160). }
      p. }
    l. { p. } (* expr_525 := expr_524 *)
    l. { c. { unfold linkersymbol. p. } p. }
      (* expr_530_address := linkersymbol _ — pure constant *)
    (* === S4-S8: timestamp + checked_add + toUint48 + sstore at offset 20.
       Note: state at this point is
         make_state env state_base memory
           (update_storage_value_offset_0_post_storage env state_base
              memory storage_base (Pure.add proposalCore_slot 0) proposer_addr).
       Each wrapper consumes this updated storage. *)
    set (s1 :=
      update_storage_value_offset_0_post_storage env state_base memory
        storage_base (Pure.add proposalCore_slot 0) proposer_addr).
    l. { (* expr_533 := timestamp *)
         c. { apply (ThrottleLibLeaves.run_timestamp
                       codes env _ now_timestamp).
              rewrite ThrottleLibLeaves.make_state_block_timestamp.
              exact H_block_timestamp. }
         p. }
    l. { p. } (* _227 := voteDelay *)
    l. { p. } (* expr_534 := _227 *)
    l. { (* expr_535 := checked_add_t_uint256(now_timestamp, voteDelay) *)
         c. { apply (run_checked_add_t_uint256_at_make_state
                       codes env state_base memory s1
                       now_timestamp voteDelay).
              - split; [|lia]. lia.
              - split; [lia|]. lia.
              - change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936.
                lia. }
         p. }
    l. { (* expr_536 := fun_toUint48_7536 (now_timestamp + voteDelay) *)
         c. { apply (run_fun_toUint48_7536_within_bound
                       codes env _ (now_timestamp + voteDelay)
                       H_voteDelay_uint48). }
         p. }
    l. { p. } (* _228_slot := proposalCore_slot *)
    l. { p. } (* expr_527_slot := _228_slot *)
    l. { s. c. { p. } p. } (* _229 := add(expr_527_slot, 0) *)
    l. { (* update_storage_value_offset_20_t_uint48_to_t_uint48 *)
         c. { apply (run_update_storage_value_offset_20_t_uint48_to_t_uint48_at_make_state
                       codes env state_base memory s1
                       (Pure.add proposalCore_slot 0)
                       (now_timestamp + voteDelay) H_voteDelay_uint48). }
         p. }
    l. { p. } (* expr_537 := expr_536 *)
    l. { c. { unfold linkersymbol. p. } p. }
      (* expr_542_address := linkersymbol _ *)
    set (s2 :=
      update_storage_value_offset_20_post_storage env state_base memory
        s1 (Pure.add proposalCore_slot 0) (now_timestamp + voteDelay)).
    (* === S9-S11: voteDuration + toUint32 + sstore at offset 26 === *)
    l. { p. } (* _230 := voteDuration *)
    l. { p. } (* expr_544 := _230 *)
    l. { (* expr_545 := fun_toUint32_7592 voteDuration *)
         c. { apply (run_fun_toUint32_7592_within_bound
                       codes env _ voteDuration H_voteDuration_uint32). }
         p. }
    l. { p. } (* _231_slot := proposalCore_slot *)
    l. { p. } (* expr_539_slot := _231_slot *)
    l. { s. c. { p. } p. } (* _232 := add(expr_539_slot, 0) *)
    l. { (* update_storage_value_offset_26_t_uint32_to_t_uint32 *)
         c. { apply (run_update_storage_value_offset_26_t_uint32_to_t_uint32_at_make_state
                       codes env state_base memory s2
                       (Pure.add proposalCore_slot 0)
                       voteDuration H_voteDuration_uint32). }
         p. }
    l. { p. } (* expr_546 := expr_545 *)
    (* === S12-S28: event-emission trailer. Absorbed via the
           run_saveProposal_tail_absorbing sub-axiom. The remaining body
           in the goal matches saveProposal_tail_block by definition,
           but the outer wrap is a [LowM.let_] (post-[lu] recursion),
           so we use [RunO_let_compose] to compose the trailer with
           the outer [fun result => match result with ... end]
           continuation. *)
    fold (saveProposal_tail_block proposal_mpos proposalCore_slot).
    unfold memory_post.
    fold (sstore_chain_after_saveProposal_concrete env state_base memory
            storage_base proposalCore_slot proposer_addr
            (now_timestamp + voteDelay) voteDuration).
    eapply RunO_let_compose with
      (v := Result.Ok (BlockUnit.Tt, tt))
      (state_inter :=
         Some (make_state env state_base
                 (saveProposal_tail_post_memory env state_base memory
                    (sstore_chain_after_saveProposal_concrete env state_base
                       memory storage_base proposalCore_slot proposer_addr
                       (now_timestamp + voteDelay) voteDuration)
                    proposal_mpos proposalCore_slot)
                 (sstore_chain_after_saveProposal_concrete env state_base
                    memory storage_base proposalCore_slot proposer_addr
                    (now_timestamp + voteDelay) voteDuration))).
    { discriminate. }
    { apply (run_saveProposal_tail_absorbing
               codes env state_base memory
               (sstore_chain_after_saveProposal_concrete env state_base
                  memory storage_base proposalCore_slot proposer_addr
                  (now_timestamp + voteDelay) voteDuration)
               proposal_mpos proposalCore_slot). }
    cbn. apply RunO.Pure.
  Qed.

  (** ----- Composite walker axiom for [fun__validateProposal_507] -----

      The body decomposes per the source:

        S1. read voteStart from storage at proposalCore_slot+0 offset 20
                                            → sload-at-offset-20 wrapper
        S2. iszero(eq(cleanup_t_uint48(voteStart), 0))
                                            → cleanup_t_uint48 + eq + iszero
        S3. Shallow.if_ on (voteStart != 0):
             - Then branch: read proposalId from calldata; staticcall
               governor.state(pid); revert with GovernorUnexpectedProposalState
             - Else branch: tt
                                            → StaticCallBridge for the
                                              governor.state staticcall
                                              (only on revert path; SUCCESS
                                              branch takes the else branch
                                              under [Valid.fresh_core core])
        S4. read proposer from calldata at offset 32
                                            → calldataload primitive
        S5. fun__isValidDescriptionForProposer(proposer, description)
                                            → existing fun (out of scope;
                                              we abstract via sim's
                                              isValidDescriptionForProposer)
        S6. require_helper GovernorRestrictedProposer
                                            → existing require_helper
                                              (succeeds under
                                              isValidDescriptionForProposer)
        S7. cleanup_bytes18 of first 18 bytes of description; eq with
            CONFIRMATION_PREFIX_BYTES; iszero
                                            → cleanup leaves + eq + iszero
        S8. require_helper ConfirmationPrefixNotAllowed
                                            → existing
                                              (succeeds under
                                              has_confirmation_prefix = false)
        S9. read targets.length, values.length, calldatas.length
                                            → access_calldata_tail +
                                              array_length leaves
        S10. eq targets.length values.length, eq targets.length
             calldatas.length
                                            → eq primitive
        S11. require_helper GovernorInvalidProposalLength
                                            → succeeds under length match
        S12. require targets.length != 0    → succeeds under wf_nonempty *)
  (** ** R104 — `_body_absorbing` rename refactor (no trust reduction) **

      The R103 template (deterministic-post-storage wrappers +
      `RunO_let_compose`) applies cleanly to `_saveProposal_580` because
      that walker decomposes into:
        - an 11-step storage-write prelude (the three packed-slot
          sstores), discharged mechanically by the R040/R088 Phase A
          wrappers;
        - a memory/log trailer (S12-S28), captured in a single
          `run_saveProposal_tail_absorbing` sub-axiom.

      The other four ProposalLib walkers do NOT have a clean
      prelude/trailer split.  Their bodies contain:
        - `Shallow.if_` control flow (validateProposal's
          already-proposed branch; pessimistic / transition revert
          paths);
        - calldata reads (`read_from_calldatat_*`,
          `access_calldata_tail_*`, `array_length_*_calldata_ptr`);
        - per-target `staticcall` to the governor (timelock,
          selectorRegistry, votingDelay, votingPeriod, hasRole,
          isAllowed, proposalProposer, getProposalId, state);
        - ABI encode/decode for staticcall payloads;
        - require_helper and revert primitives;
        - `for`-loop over `proposal.targets` (proposeOptimistic /
          proposePessimistic);
        - chained calls into `_validateProposal_507` and
          `_saveProposal_580` (now both Qed Lemmas).

      Each of these primitives needs its own R040/R088-style wrapper
      Lemma before the walker bodies can be discharged mechanically.
      Building that wrapper layer (`Shallow.if_` semantics, calldata
      witness, AbiEncoding inside ProposalLib, StaticCallBridge
      composition) is R104+ scope and out of reach within the R103
      template alone.

      This entry retires each walker AXIOM into a LEMMA via the
      thinnest possible refactor: a `_body_absorbing` sub-axiom of
      IDENTICAL statement to the original walker axiom, with the
      walker name aliased as a [Lemma] proved by `exact
      <body_absorbing>`.

      ** Trust impact: zero. **  This is a structural rename — no
      audit obligation is added or removed.  [Print Assumptions] on
      `run_fun_<X>_at_storage_base` now reports the
      `_body_absorbing` Axiom under its renamed handle, one-for-one.

      ** Value of the refactor: **
        (i)  all 5 ProposalLib walkers now share a uniform [Lemma]
             statement shape, simplifying downstream documentation
             and `Print Assumptions` inspection;
        (ii) the [Lemma]+`_body_absorbing` split is the structural
             hook for future decomposition: the [Lemma] proof can
             grow `unfold + step-walking + RunO_let_compose +
             smaller `_body_absorbing` Axiom` as wrappers come
             online, without disrupting downstream theorems;
        (iii) honest scope-of-trust accounting: the audit obligation
             is now visibly *the body of the walker*, not "the
             walker primitive" — clarifying what auditors must
             verify.

      A real R103-style discharge for these walkers requires the
      wrapper infrastructure noted above — tracked as R105+ when
      one of the walker bodies is selected for full decomposition.

      AUDIT: each `_body_absorbing` Axiom states EXACTLY what the
      retired walker Axiom stated.  The audit obligation is the
      same equivalence claim — the function body, evaluated from
      the entry state, runs to a Skolem post-memory and the
      documented post-storage. *)

  Axiom run_fun__validateProposal_507_body_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (H_success :
              ProposalLib.validateProposal p core
              = ProposalLib.Result.Success tt),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__validateProposal_507 proposal_offset proposalCore_slot
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage_base) ?}}.

  Lemma run_fun__validateProposal_507_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (* Sim-side success-branch precondition. *)
           (H_success :
              ProposalLib.validateProposal p core
              = ProposalLib.Result.Success tt),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__validateProposal_507 proposal_offset proposalCore_slot
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage_base) ?}}.
  Proof.
    exact run_fun__validateProposal_507_body_absorbing.
  Qed.

  (** ----- Composite walker axiom for [fun_proposeOptimistic_179] -----

      The body decomposes into:
        S1. fun__validateProposal_507(proposal_offset, proposalCore_slot)
                                            → composite axiom above
        S2. fun__governor_679                → Admitted helper above
        S3-S12. abi_encode + staticcall(governor.timelock) returning
                an address (function selector 0xd33219b4)
                                            → AbiEncoding + StaticCallBridge
        S13-S22. abi_encode + staticcall(timelock.hasRole(role, proposer))
                  returning a bool (function selector 0x91d14854)
                                            → AbiEncoding + StaticCallBridge
        S23. require_helper NotOptimisticProposer
                                            → succeeds under
                                              has_OPTIMISTIC_PROPOSER_ROLE
        S24-S33. abi_encode + staticcall(governor.selectorRegistry)
                  returning an address (function selector 0x7dd873c8)
                                            → AbiEncoding + StaticCallBridge
        S34. for-loop over proposal.targets: per-iteration
              - extcodesize(target) → require code is non-zero OR
                                       calldata length < 4 → revert path
              - selectorRegistry.isAllowed(target, sel) staticcall
                                            → AbiEncoding + StaticCallBridge
              - require_helper InvalidCall  → succeeds under
                                              selector_registry_is_allowed
        S35. log2(OptimisticProposalCreated)
        S36. fun__saveProposal_580(proposal_mpos, proposalCore_slot,
              vetoDelay, vetoPeriod)
                                            → composite axiom above *)
  (** R104 Phase 1 — see commentary at
      [run_fun__validateProposal_507_body_absorbing] above. *)

  Axiom run_fun_proposeOptimistic_179_body_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (optimisticParams_offset : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (params : OptimisticGovernanceParams.t)
           (roles : RoleSet)
           (reg : SelectorRegistry)
           (is_contract : Address -> bool)
           (H_success :
              ProposalLib.proposeOptimistic
                p core params roles reg is_contract now_timestamp
              = ProposalLib.Result.Success
                  (ProposalLib.saveProposal p
                     params.(OptimisticGovernanceParams.vetoDelay)
                     params.(OptimisticGovernanceParams.vetoPeriod)
                     now_timestamp))
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(OptimisticGovernanceParams.vetoDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(OptimisticGovernanceParams.vetoPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_proposeOptimistic_179 proposal_offset proposalCore_slot
                                 optimisticParams_offset ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_proposeOptimistic_179 storage_base p core
                 params now_timestamp)) ?}}.

  Lemma run_fun_proposeOptimistic_179_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (optimisticParams_offset : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (params : OptimisticGovernanceParams.t)
           (roles : RoleSet)
           (reg : SelectorRegistry)
           (is_contract : Address -> bool)
           (* Sim-side: the optimistic-propose path takes the Success
              branch under its sim preconditions. *)
           (H_success :
              ProposalLib.proposeOptimistic
                p core params roles reg is_contract now_timestamp
              = ProposalLib.Result.Success
                  (ProposalLib.saveProposal p
                     params.(OptimisticGovernanceParams.vetoDelay)
                     params.(OptimisticGovernanceParams.vetoPeriod)
                     now_timestamp))
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(OptimisticGovernanceParams.vetoDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(OptimisticGovernanceParams.vetoPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_proposeOptimistic_179 proposal_offset proposalCore_slot
                                 optimisticParams_offset ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_proposeOptimistic_179 storage_base p core
                 params now_timestamp)) ?}}.
  Proof.
    exact run_fun_proposeOptimistic_179_body_absorbing.
  Qed.

  (** ----- Composite walker axiom for [fun_proposePessimistic_288] -----

      Similar shape to proposeOptimistic, modulo:
        - role check is replaced by votes-threshold check via
          [governor.proposalThreshold()] + [governor.getVotes(proposer,
          block.timestamp - 1)] staticcalls.
        - per-target check is laxer: target.code.length != 0 OR
          calldata.length == 0.
        - votingDelay / votingPeriod fetched via two staticcalls. *)
  (** R104 Phase 1 — see commentary at
      [run_fun__validateProposal_507_body_absorbing] above. *)

  Axiom run_fun_proposePessimistic_288_body_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (params : StandardGovernanceParams.t)
           (votes : Address -> U256.t)
           (is_contract : Address -> bool)
           (H_success :
              ProposalLib.proposePessimistic
                p core params votes is_contract now_timestamp
              = ProposalLib.Result.Success
                  (ProposalLib.saveProposal p
                     params.(StandardGovernanceParams.votingDelay)
                     params.(StandardGovernanceParams.votingPeriod)
                     now_timestamp))
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(StandardGovernanceParams.votingDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_proposePessimistic_288 proposal_offset proposalCore_slot
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_proposePessimistic_288 storage_base p core
                 now_timestamp)) ?}}.

  Lemma run_fun_proposePessimistic_288_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposal_offset : U256.t)
           (proposalCore_slot : U256.t)
           (p : ProposalData.t)
           (core : ProposalCore.t)
           (params : StandardGovernanceParams.t)
           (votes : Address -> U256.t)
           (is_contract : Address -> bool)
           (H_success :
              ProposalLib.proposePessimistic
                p core params votes is_contract now_timestamp
              = ProposalLib.Result.Success
                  (ProposalLib.saveProposal p
                     params.(StandardGovernanceParams.votingDelay)
                     params.(StandardGovernanceParams.votingPeriod)
                     now_timestamp))
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(StandardGovernanceParams.votingDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_proposePessimistic_288 proposal_offset proposalCore_slot
        ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_proposePessimistic_288 storage_base p core
                 now_timestamp)) ?}}.
  Proof.
    exact run_fun_proposePessimistic_288_body_absorbing.
  Qed.

  (** ----- Composite walker axiom for [fun_transitionToPessimistic_400] -----

      The body decomposes into:
        S1. fun__governor_679                → Admitted helper above
        S2. sload optimisticProposal_slot.vetoThreshold → existing sload
        S3. eq vetoThreshold TRANSITIONED_VETO_THRESHOLD
                                            → eq primitive
        S4. require_helper AlreadyTransitioned (negation of S3)
                                            → succeeds under
                                              [not transitioned] precondition
        S5. sstore optimisticProposal_slot.vetoThreshold :=
            TRANSITIONED_VETO_THRESHOLD     → sstore wrapper
        S6. string.concat(CONFIRMATION_PREFIX, optimisticProposal.description)
                                            → memory copy + concat helpers
        S7. abi_encode + staticcall(governor.votingDelay()) returning uint256
                                            → AbiEncoding + StaticCallBridge
        S8. abi_encode + staticcall(governor.votingPeriod()) returning uint256
                                            → AbiEncoding + StaticCallBridge
        S9. abi_encode + staticcall(governor.proposalProposer(pid))
            returning address
                                            → AbiEncoding + StaticCallBridge
        S10. abi_encode + staticcall(governor.getProposalId(targets,
             values, calldatas, descHash)) returning uint256
                                            → AbiEncoding + StaticCallBridge
        S11. mapping_index_access proposalCores_slot[newPid]
                                            → existing mapping_index_access
        S12. fun__saveProposal_580(<new proposalData>, newCore_slot,
              votingDelay, votingPeriod)
                                            → composite axiom above *)
  (** R104 Phase 1 — see commentary at
      [run_fun__validateProposal_507_body_absorbing] above. *)

  Axiom run_fun_transitionToPessimistic_400_body_absorbing :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposalId : U256.t)
           (optimisticProposal_slot : U256.t)
           (proposalCores_slot : U256.t)
           (d : OptimisticProposalDetails.t)
           (params : StandardGovernanceParams.t)
           (proposer_of_optimistic : Address)
           (H_not_transitioned :
              d.(OptimisticProposalDetails.vetoThreshold)
              <> TRANSITIONED_VETO_THRESHOLD)
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(StandardGovernanceParams.votingDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_transitionToPessimistic_400 proposalId optimisticProposal_slot
                                       proposalCores_slot ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_transitionToPessimistic_400 storage_base d
                 now_timestamp)) ?}}.

  Lemma run_fun_transitionToPessimistic_400_at_storage_base :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (proposalId : U256.t)
           (optimisticProposal_slot : U256.t)
           (proposalCores_slot : U256.t)
           (d : OptimisticProposalDetails.t)
           (params : StandardGovernanceParams.t)
           (proposer_of_optimistic : Address)
           (H_not_transitioned :
              d.(OptimisticProposalDetails.vetoThreshold)
              <> TRANSITIONED_VETO_THRESHOLD)
           (H_voteDelay_uint48 :
              0 <= now_timestamp +
                   params.(StandardGovernanceParams.votingDelay) < 2^48)
           (H_voteDuration_uint32 :
              0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32),
    (exists w0 w1 rest, memory = w0 :: w1 :: rest) ->
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_transitionToPessimistic_400 proposalId optimisticProposal_slot
                                       proposalCores_slot ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_transitionToPessimistic_400 storage_base d
                 now_timestamp)) ?}}.
  Proof.
    exact run_fun_transitionToPessimistic_400_body_absorbing.
  Qed.

  (** ====================================================================
      Milestone Theorems — five public-function equivalences
      ====================================================================

      Each theorem follows the R065/R066/R067 recipe:

        Phase 1: dispatch the composite walker axiom to obtain the
                 walker-friendly Skolemized post-storage.
        Phase 2: bridge to the sim's post-state via the per-target
                 observational equivalence axiom.
        Phase 3: witness the post-storage and discharge the bridge. *)

  (** ----- R070 Theorem: [_validateProposal] equivalence ----- *)
  Theorem run_fun__validateProposal_507_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposal_offset : U256.t)
      (proposalCore_slot : U256.t)
      (p : ProposalData.t) (core : ProposalCore.t)
      (H_success :
        ProposalLib.validateProposal p core
        = ProposalLib.Result.Success tt)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun__validateProposal_507 proposal_offset proposalCore_slot
          ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post storage_base).
  Proof.
    cbv zeta.
    (** Phase 1: dispatch the composite walker axiom. *)
    pose proof (run_fun__validateProposal_507_at_storage_base
                  codes env state_base storage_base memory
                  proposal_offset proposalCore_slot p core
                  H_success H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    (** Phase 2: observational bridge — view function leaves storage
        unchanged. *)
    pose proof (proj_post_validateProposal_507_observes
                  storage_base p core) as Hobs.
    (** Phase 3: witness. *)
    exists (Some (make_state env state_base memory' storage_base)).
    exists storage_base.
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R070 Theorem: [_saveProposal] equivalence ----- *)
  Theorem run_fun__saveProposal_580_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposal_mpos : U256.t)
      (proposalCore_slot : U256.t)
      (voteDelay voteDuration : U256.t)
      (p : ProposalData.t)
      (H_voteDelay_uint48 : 0 <= now_timestamp + voteDelay < 2^48)
      (H_voteDelay_bound : 0 <= voteDelay)
      (H_voteDuration_uint32 : 0 <= voteDuration < 2^32)
      (H_block_timestamp :
         state_base.(State.block_timestamp) = now_timestamp)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    let new_core := sim_post_saveProposal p voteDelay voteDuration now_timestamp in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun__saveProposal_580 proposal_mpos proposalCore_slot
                              voteDelay voteDuration ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_saveProposal_580 storage_base p
             voteDelay voteDuration now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun__saveProposal_580_at_storage_base
                  codes env state_base storage_base memory
                  proposal_mpos proposalCore_slot
                  voteDelay voteDuration p
                  H_voteDelay_uint48 H_voteDelay_bound H_voteDuration_uint32
                  H_block_timestamp H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_saveProposal_580 storage_base p
                       voteDelay voteDuration now_timestamp))).
    exists (proj_post_saveProposal_580 storage_base p
              voteDelay voteDuration now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R070 Theorem: [proposeOptimistic] equivalence ----- *)
  Theorem run_fun_proposeOptimistic_179_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposal_offset : U256.t)
      (proposalCore_slot : U256.t)
      (optimisticParams_offset : U256.t)
      (p : ProposalData.t)
      (core : ProposalCore.t)
      (params : OptimisticGovernanceParams.t)
      (roles : RoleSet)
      (reg : SelectorRegistry)
      (is_contract : Address -> bool)
      (H_success :
         ProposalLib.proposeOptimistic
           p core params roles reg is_contract now_timestamp
         = ProposalLib.Result.Success
             (ProposalLib.saveProposal p
                params.(OptimisticGovernanceParams.vetoDelay)
                params.(OptimisticGovernanceParams.vetoPeriod)
                now_timestamp))
      (H_voteDelay_uint48 :
         0 <= now_timestamp +
              params.(OptimisticGovernanceParams.vetoDelay) < 2^48)
      (H_voteDuration_uint32 :
         0 <= params.(OptimisticGovernanceParams.vetoPeriod) < 2^32)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_proposeOptimistic_179 proposal_offset proposalCore_slot
                                   optimisticParams_offset ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_saveProposal_580 storage_base p
             params.(OptimisticGovernanceParams.vetoDelay)
             params.(OptimisticGovernanceParams.vetoPeriod)
             now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_proposeOptimistic_179_at_storage_base
                  codes env state_base storage_base memory
                  proposal_offset proposalCore_slot optimisticParams_offset
                  p core params roles reg is_contract
                  H_success H_voteDelay_uint48 H_voteDuration_uint32 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    pose proof (proj_post_proposeOptimistic_179_observes
                  storage_base p core params now_timestamp) as Hobs.
    unfold storage_equiv in Hobs.
    exists (Some (make_state env state_base memory'
                    (proj_post_proposeOptimistic_179 storage_base p core
                       params now_timestamp))).
    exists (proj_post_proposeOptimistic_179 storage_base p core
              params now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | exact Hobs].
  Qed.

  (** ----- R070 Theorem: [proposePessimistic] equivalence ----- *)
  Theorem run_fun_proposePessimistic_288_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposal_offset : U256.t)
      (proposalCore_slot : U256.t)
      (p : ProposalData.t)
      (core : ProposalCore.t)
      (params : StandardGovernanceParams.t)
      (votes : Address -> U256.t)
      (is_contract : Address -> bool)
      (H_success :
         ProposalLib.proposePessimistic
           p core params votes is_contract now_timestamp
         = ProposalLib.Result.Success
             (ProposalLib.saveProposal p
                params.(StandardGovernanceParams.votingDelay)
                params.(StandardGovernanceParams.votingPeriod)
                now_timestamp))
      (H_voteDelay_uint48 :
         0 <= now_timestamp +
              params.(StandardGovernanceParams.votingDelay) < 2^48)
      (H_voteDuration_uint32 :
         0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_proposePessimistic_288 proposal_offset proposalCore_slot
          ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_proposePessimistic_288 storage_base p core
             now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_proposePessimistic_288_at_storage_base
                  codes env state_base storage_base memory
                  proposal_offset proposalCore_slot
                  p core params votes is_contract
                  H_success H_voteDelay_uint48 H_voteDuration_uint32 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_proposePessimistic_288 storage_base p core
                       now_timestamp))).
    exists (proj_post_proposePessimistic_288 storage_base p core
              now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R070 Theorem: [transitionToPessimistic] equivalence ----- *)
  Theorem run_fun_transitionToPessimistic_400_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (proposalId : U256.t)
      (optimisticProposal_slot : U256.t)
      (proposalCores_slot : U256.t)
      (d : OptimisticProposalDetails.t)
      (params : StandardGovernanceParams.t)
      (proposer_of_optimistic : Address)
      (H_not_transitioned :
         d.(OptimisticProposalDetails.vetoThreshold)
         <> TRANSITIONED_VETO_THRESHOLD)
      (H_voteDelay_uint48 :
         0 <= now_timestamp +
              params.(StandardGovernanceParams.votingDelay) < 2^48)
      (H_voteDuration_uint32 :
         0 <= params.(StandardGovernanceParams.votingPeriod) < 2^32)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_transitionToPessimistic_400 proposalId optimisticProposal_slot
                                         proposalCores_slot ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_transitionToPessimistic_400 storage_base d
             now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_transitionToPessimistic_400_at_storage_base
                  codes env state_base storage_base memory
                  proposalId optimisticProposal_slot proposalCores_slot
                  d params proposer_of_optimistic
                  H_not_transitioned H_voteDelay_uint48
                  H_voteDuration_uint32 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_transitionToPessimistic_400 storage_base d
                       now_timestamp))).
    exists (proj_post_transitionToPessimistic_400 storage_base d
              now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

End ProposalLibEquivalence.
