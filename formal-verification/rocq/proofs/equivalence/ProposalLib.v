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
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.generated.ProposalLib_shallow.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module ProposalLibEquivalence.

  Import ProposalLib_680.ProposalLib_680_deployed.

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
      level. *)
  (** [_governor()] in Solidity is
        [ReserveOptimisticGovernor(payable(address(this)))]
      — a chain of identity casts on [address()], which returns the
      runtime's contract address. We model that as the same address,
      since every cast in the chain is value-identity at the U256
      level.

      RESIDUAL: the walker pattern for stepping through the let_ /
      strong_let_ tower mixed with the [Stdlib.address] primitive
      (which uses [let*] = M.let_, producing the LowM.let_ Fixpoint
      form mid-body) is non-trivial. The naive [repeat (lu || cu)]
      over-advances; explicit [l. { c. { leaf. } p. }] per-step
      requires careful matching of the LowM.Let / LowM.let_
      alternation that the M.monadic elaboration produces.

      The leaves above ([run_convert_t_contract_ProposalLib_to_t_address],
      etc.) are all closed Qed. The composition is the missing piece. *)
  Theorem run_fun__governor_679_equivalent codes env state
      (H_addr : 0 <= env.(Environment.address) < 2^160) :
    {{? codes, env, Some state |
      fun__governor_679 ⇓ Result.Ok env.(Environment.address)
    | Some state ?}}.
  Proof.
  Admitted.

  (** ========================================================
        Tier 0 — [SafeCast.toUint48] / [toUint32] within-bound
      ========================================================

      [fun_toUint48_7536] checks if [value > 2^48 - 1]; if yes, reverts
      with [SafeCastOverflowedUintDowncast(48, value)]; otherwise
      [convert_t_uint256_to_t_uint48] (identity on values in range).

      We prove the happy path: value already in uint48 range, the
      gt-check is false, the function returns the value unchanged. *)

  (** RESIDUAL — the function uses a [Shallow.if_] gating a revert
      sequence, then a [convert_t_uint256_to_t_uint48] for the happy
      path. Closing the equivalence requires:
        1. unfolding the M.monadic + Stdlib.if_ chain to expose the
           gt-check on the v argument
        2. case-splitting [v >? 2^48-1] (false branch)
        3. routing the false-branch through
           [run_convert_t_uint256_to_t_uint48].
      The walker pattern matches R047 in WISDOM but the residual
      [Shallow.let_state ... default~ ...] tower introduces extra
      goals that the simple [repeat (lu || cu)] doesn't drain.

      All upstream leaves ([run_convert_t_uint256_to_t_uint48], etc.)
      are Qed above. *)
  Lemma run_fun_toUint48_7536_within_bound codes env state (v : U256.t)
      (H_v : 0 <= v < 2^48) :
    {{? codes, env, Some state |
      fun_toUint48_7536 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
  Admitted.

  Lemma run_fun_toUint32_7592_within_bound codes env state (v : U256.t)
      (H_v : 0 <= v < 2^32) :
    {{? codes, env, Some state |
      fun_toUint32_7592 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
  Admitted.

End ProposalLibEquivalence.
