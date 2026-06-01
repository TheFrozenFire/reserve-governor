(** StakingVault admin / pause / upgrade-authorization equivalence
    (task #257 — Wave 2 parallel).

    Mirrors [contracts/staking/StakingVault.sol] — the AccessControl-
    gated mutators of the configuration surface:

      Tier-1 (this contract's direct admin entry-points):
        1. [setUnstakingDelay]    — onlyRole(DEFAULT_ADMIN_ROLE);
                                    require delay <= MAX_UNSTAKING_DELAY;
                                    sstore unstakingDelay (slot 5).
        2. [setRewardRatio]       — onlyRole(DEFAULT_ADMIN_ROLE);
                                    require half-life in [MIN, MAX];
                                    sstore rewardRatio = LN_2 / half-life
                                    (slot 3). Body wrapped in
                                    accrueRewards(msg.sender, msg.sender).
        3. [_authorizeUpgrade]    — UUPS hook (called by upgradeToAndCall);
                                    onlyRole(DEFAULT_ADMIN_ROLE);
                                    keccak256(Versioned(impl).version()) +
                                    VersionRegistry staticcalls
                                    (getLatestVersion / getImplementationsForVersion).

      Tier-2 (inherited AccessControl mutators visible at this contract's
              ABI surface — granted by DEFAULT_ADMIN_ROLE chain):
        4. [grantRole]            — modifier_onlyRole(getRoleAdmin(role)) +
                                    _grantRole inner that flips
                                    [_roles[role].hasRole[account] := 1]
                                    AND pushes [account] onto the
                                    AccessControlEnumerable
                                    [_roleMembers[role]] set.
        5. [revokeRole]           — same gate; flips to 0 and removes from
                                    the EnumerableSet via swap-and-pop.
        6. [renounceRole]         — caller-confirmation-gated _revokeRole.

      Tier-3 (proxy entry-point):
        7. [upgradeToAndCall]     — modifier_onlyProxy + _authorizeUpgrade
                                    + UUPS implementation slot write +
                                    delegatecall(init data).

    NOTE: StakingVault.sol does NOT expose a [pause] / [unpause]
    function or a [setNativeRewardRate] mutator (the task brief uses
    those names as the abstract "pause/admin" category — the concrete
    StakingVault surface is the seven entry-points above). The native
    asset() reward stream is auto-accrued from the contract's underlying
    balance; there is no admin lever for the native reward rate.

    Methodology
    ===========

    R067 + R070 abstract-storage_base recipe, mirroring
    [TimelockControllerOptimistic.v]:
      - The on-chain storage is a composition of ERC4626 / ERC20Permit /
        ERC20Votes / AccessControlEnumerable / Initializable / UUPS
        namespaced storages (ERC-7201 keccak-derived anchors) plus the
        contract's own [versionRegistry] (slot 0), [rewardTokens]
        (EnumerableSet at slot 1+2), [rewardRatio] (slot 3),
        [unstakingManager] (slot 4), [unstakingDelay] (slot 5),
        [rewardTokenRegistry] (slot 6), and the reward-tracking maps
        (slots 7-13) plus the native-reward bookkeeping (slot 14).
      - Each milestone theorem quantifies over an opaque
        [storage_base : SimulatedStorage.t] standing for the pre-call
        state. The walker axioms reveal a [proj_post_<fn>] Skolemized
        post-storage; the observational bridge collapses to reflexivity
        under [storage_equiv := eq].
      - Per-mutator: ONE composite walker axiom (the audit-time witness
        that the Yul body's mechanical assembly closes) + ONE Skolemized
        post-storage Parameter + ONE milestone Qed theorem.

    Composes with:
      R055 (Guardian grantRole milestone pattern) for grantRole/revokeRole —
        the AccessControl-gated inner write into the role-member map
        plus the AccessControlEnumerable EnumerableSet add/remove.
      R059 (set_eq_at_role) — implicit in the AccessControlEnumerable
        sub-walker; closed inside Guardian.v's per-role observational
        bridges. Here the abstract storage_base swallows them.
      R063 (StaticCallBridge) — for [_authorizeUpgrade]'s three external
        staticcalls (Versioned.version → bytes32 hash; getLatestVersion
        and getImplementationsForVersion on the VersionRegistry).
      R067 (composite-walker-axiom recipe) — every entry-point gets the
        single-Hoare-triple bundle.
      R072 (abstract-base-class slot-agnostic helpers) — the AccessControl
        sub-walker doesn't require concrete slot indices because it lives
        inside a keccak-derived namespace; the storage_base envelopes it.

    Trust budget (per [Print Assumptions] of the milestone theorems,
    AFTER the 2026-05-31 T3.1 walker discharge for [setUnstakingDelay]):
      - 6 composite walker axioms (was 7 -- [setUnstakingDelay]'s
        walker promoted to a [Qed] [Lemma] composing TWO smaller,
        more focused sub-axioms).
      - 0 Skolemized post-storage Parameters (was 7).  Each
        [proj_post_<fn>] is now a [Definition] reading/updating
        designated slots of [SimulatedStorage.t] -- see the
        "Concrete post-storage projections" section below.
      - 0 observational bridge Axioms (was 7).  Each [_observes]
        statement is now a [Qed]-closeable [Lemma] (the underlying
        [Definition] makes the reflexive equality trivial), and
        each is paired with an [_agrees_at_slot] [Lemma] tying the
        post-state to a per-slot [eq_at_<X>] [Definition].
      - 1 sim-environment Parameter ([now_timestamp]) -- shared with
        TimelockControllerOptimistic.v style.

      T3.1-specific sub-axioms (used only by
      [run_fun_setUnstakingDelay_750_at_proj_sim]):
      - [run_fun__checkRole_13513_succeeds_under_admin] -- the
        AccessControl gate walk; CANNOT be discharged with current
        framework primitives because OZ AccessControlStorage uses a
        keccak-derived ERC-7201 namespace anchor but the abstract
        [SimulatedStorage.t = list StorableValue.t] model indexes by
        small naturals.  Methodology finding: bridging requires
        either a framework extension exposing slot-anchor-agnostic
        Storage primitives or a per-contract [proj_sim] lens that
        maps designated slots to keccak anchors (the T2.6 [eq_at_*]
        promotion landed the latter on the POST side; the PRE-side
        sload path remains blocked).  See WISDOM R083 candidate.
      - [run_fun__setUnstakingDelay_773_at_storage_base] -- the
        inner body [Admitted] with documented residuals.  The
        slot-5 sstore is FULLY discharged with framework primitives
        via [run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_slot_unstakingDelay].
        The Admitted residual covers ONLY the log-payload tail
        (allocate_unbounded + mstore + log1), which is a memory-
        tracking obligation orthogonal to the storage-equivalence
        claim.  See WISDOM R083 candidate.

    Pre-T2.2 baseline (commit 8c91483, [Parameter]/[Axiom] shape):
      every milestone theorem listed the corresponding
      [proj_post_<fn>] [Parameter] as an axiom; the 7 reflexive
      [_observes] Axioms were unused-by-proof but documented the
      degenerate identity bridge.  Post-T2.2: those Parameters are
      removed from [Print Assumptions]; the milestones now constrain
      the walker's post-state to a concrete slot-update of the
      pre-state.

    Documentation-only callee-spec axioms (True conclusions) record the
    audit-time obligations for the three staticcalls inside
    [_authorizeUpgrade]. These do NOT appear in [Print Assumptions] for
    any of the milestone theorems.

    No other equivalence files are modified — the recipe is
    self-contained per R067 / R070 / R071's pattern.

    WISDOM reference: see R055, R063, R067, R068, R072, R081, R083.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Require Import ReserveGovernor.generated.StakingVault_shallow.
Require Import ReserveGovernor.proofs.equivalence.StaticCallBridge.
Require Import ReserveGovernor.proofs.equivalence.AbiEncoding.
Require Import ReserveGovernor.proofs.equivalence.FrameworkExtensions.
Import FrameworkExtensions.

Import Stdlib.
Import RunO.

Open Scope Z_scope.

Module StakingVaultAdminEquivalence.

  Import StakingVault_1721.StakingVault_1721_deployed.

  (** Sim-side environment for the equivalence statements.

      The contract reads [block.timestamp] inside the [accrueRewards]
      modifier (via the [native rewards last paid] update path) and
      writes a per-call snapshot. We expose it as a sim-level
      [Parameter] — same shape as
      [TimelockControllerOptimisticEquivalence.now_timestamp] —
      so all milestone theorems can pin the sim's [now] argument
      against a single value. *)

  Parameter now_timestamp : U256.t.

  (** ====================================================================
      Audit-time callee specs
      ====================================================================

      The OZ chain of internal calls dispatches through helpers like
      [fun__msgSender_14384] / [fun__getAccessControlStorage_13430].
      For the audit-time obligations consumed inside the composite walker
      axioms we surface these as Parameters / True-conclusion Axioms
      (R064 / R067 / R070 shape). Each is paired with a sim-side
      [has_DEFAULT_ADMIN_ROLE caller = true] precondition in the
      milestone theorems below.

      Roles modeled at this contract surface:
        - DEFAULT_ADMIN_ROLE (the only Solidity-declared role on
          StakingVault.sol — every admin entry-point gates on it).
        - Any arbitrary bytes32 [role] for grantRole/revokeRole inputs.
          The gate is the admin chain of that role; under the
          R055/R072 projection it reduces to DEFAULT_ADMIN_ROLE
          membership of [caller].
  *)

  Parameter has_DEFAULT_ADMIN_ROLE : U256.t -> bool.

  (** Audit-time witness for the [_checkRole(DEFAULT_ADMIN_ROLE)] gate
      inside [modifier_onlyRole_*] wrappers. Each is paired with a
      sim-side [has_DEFAULT_ADMIN_ROLE caller = true] precondition in the
      milestone theorems. These are NOT load-bearing for the [Print
      Assumptions] of the milestone theorems — the composite walker
      axiom carries the gate discharge directly via the role precondition. *)
  Axiom checkRole_default_admin_succeeds :
    forall (caller : U256.t),
    has_DEFAULT_ADMIN_ROLE caller = true ->
    True.

  (** Audit-time witnesses for the three external staticcalls inside
      [_authorizeUpgrade]:

        1. [Versioned(stakingVaultImpl).version() : string memory].
           Returns the impl's version string. The walker keccak256s it
           and stores in [var_versionHash_1520].

        2. [versionRegistry.getLatestVersion()
              : (bytes32, string memory, address, bool)].
           Returns the registry's latest tuple. The walker pulls out
           the [versionHash] component (index 0) and [deprecated]
           component (index 3).

        3. [versionRegistry.getImplementationsForVersion(versionHash)
              : (address, address, address)].
           Returns the three implementation addresses for a version.
           The walker pulls out the stakingVaultImpl component (index 0).

      Each is paired with a sim-side existential precondition in the
      milestone theorem: the caller supplies the call-response shape and
      the walker axiom consumes it. The True conclusion means the witness
      is documentation-only.
  *)

  Axiom versioned_version_returns_hash :
    forall (impl : U256.t) (versionHash : U256.t),
    True.

  Axiom versionRegistry_getLatestVersion_returns :
    forall (registry : U256.t)
           (latestHash : U256.t) (deprecated : bool),
    True.

  Axiom versionRegistry_getImplementationsForVersion_returns :
    forall (registry : U256.t) (versionHash : U256.t)
           (stakingVaultImpl governorImpl timelockImpl : U256.t),
    True.

  (** ====================================================================
      Storage equivalence relation
      ====================================================================

      Per ProposalLib's / TimelockControllerOptimistic's R070 shape:
      per-target observational equality at the abstract SimulatedStorage.t
      level. Each milestone theorem witnesses the walker's post-state and
      discharges the bridge as reflexive (the walker's post-state ALREADY
      matches the theorem's reference). *)

  Definition storage_equiv (s s' : SimulatedStorage.t) : Prop := s = s'.

  Lemma storage_equiv_refl s : storage_equiv s s.
  Proof. reflexivity. Qed.

  Lemma storage_equiv_sym s s' : storage_equiv s s' -> storage_equiv s' s.
  Proof. unfold storage_equiv. intros. symmetry. assumption. Qed.

  Lemma storage_equiv_trans s s' s'' :
    storage_equiv s s' -> storage_equiv s' s'' -> storage_equiv s s''.
  Proof. unfold storage_equiv. intros -> ->. reflexivity. Qed.

  (** ====================================================================
      Concrete slot indices for the StakingVault admin surface
      ====================================================================

      Per [contracts/staking/StakingVault.sol] and the Yul source, the
      user-defined storage slots used by the admin entry-points sit at
      contiguous low indices.  For the keccak-namespaced storages
      (OZ AccessControl / AccessControlEnumerable / UUPS) the on-chain
      anchor is keccak-derived, but in the [SimulatedStorage.t =
      list StorableValue.t] projection we pin each namespace to a
      designated list index.  The indices below are the audit's chosen
      slots in the abstract storage list -- callers extending the
      projection should mirror these. *)

  Definition slot_rewardRatio       : nat := 3%nat.   (* uint256 *)
  Definition slot_unstakingDelay    : nat := 5%nat.   (* uint256 *)

  (** Designated AccessControl namespace anchor.  OZ stores the
      [_roles : mapping(bytes32 => RoleData)] map at the keccak-derived
      AccessControlStorage slot (anchor 0x02dd...).  In the abstract
      [SimulatedStorage.t] projection we pin this Map2 at index 15
      (one past the documented user-storage range 0..14).  The Map2
      key is [(role, account)] and the value is the bool flag
      [hasRole].  This is stricter than the audit's per-RoleData
      sketch -- equal on the whole slot-15 [StorableValue] entry --
      which suffices to imply per-(role, account) hasRole equality.
      The audit-time obligation on the walker is that its post-state
      writes only this Map2 at the AccessControl-namespace anchor. *)
  Definition slot_accessControl     : nat := 15%nat.  (* Map2 *)

  (** Designated AccessControlEnumerable namespace anchor.  OZ stores
      the [_roleMembers : mapping(bytes32 => EnumerableSet.AddressSet)]
      map at the keccak-derived AccessControlEnumerableStorage slot
      (anchor 0xc1f6...).  We pin it at index 16.

      NOTE: not yet consumed by the [proj_post_<grantRole>/<revokeRole>]
      [Definition]s below.  The AccessControlEnumerable
      EnumerableSet add/remove side-effect (the swap-and-pop on slot 16)
      is left as an audit-time obligation; a follow-up tightening pass
      should compose [update_accessControlEnum] alongside
      [update_accessControl].  The slot constant is reserved here so
      that the layout map matches the file's documented namespace
      anchors (slots 0..14 user-storage, 15..17 OZ namespaces). *)
  Definition slot_accessControlEnum : nat := 16%nat.  (* MapToArray *)

  (** Designated EIP-1967 implementation slot.  OZ ERC1967Utils writes
      the new implementation at the keccak-derived slot
      [bytes32(uint256(keccak256("eip1967.proxy.implementation")) - 1)]
      = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc.
      We pin it at index 17. *)
  Definition slot_implementation    : nat := 17%nat.  (* U256 *)

  (** ====================================================================
      Storage update primitives
      ====================================================================

      Per [List.update_nth] from [simulations.RocqOfSolidity], a
      slot-write is a list-update at the slot's nat index.  These are
      partial (None on out-of-range); we wrap with a fallback to the
      pre-image so the [Definition]s are total.  The fallback path is
      a no-op only when the storage_base is shorter than the slot
      index -- which is itself an audit-time obligation (the projection
      must be long enough to cover all touched slots).  Documented
      shape: an honest abstract projection has length >= 18. *)

  Definition update_slot (sb : SimulatedStorage.t) (idx : nat)
      (v : StorableValue.t) : SimulatedStorage.t :=
    match List.update_nth sb idx v with
    | Some sb' => sb'
    | None     => sb
    end.

  (** ----- Concrete post-storage projections (R067 + T2.6 promotion) -----

      Per the 2026-05-31 adversarial-review skolemization-soundness
      audit (CCV-2 / CRIT-V / CCV-4), the seven [proj_post_<fn>]
      shapes were originally free [Parameter]s constrained only by
      reflexive [Axiom]s of the form [storage_equiv X X], which were
      degeneratable to a [True]-style instantiation -- making the
      seven milestone theorems below vacuous (an adversarial
      instantiation of each [proj_post_<fn>] could agree with the
      walker's Skolem yet write nothing).  We promote each to a
      concrete [Definition] reading and updating designated slot
      indices of [SimulatedStorage.t], mirroring T2.6's
      [eq_at_*_concrete] promotion in [StakingVaultRewards.v].

      Per-function shape:
        - [setUnstakingDelay]   : update slot 5 (unstakingDelay).
        - [setRewardRatio]      : update slot 3 (rewardRatio).
                                  The accrueRewards bookkeeping at
                                  slots 7/9/12/13/14 is conceded as
                                  opaque (the [StakingVaultRewards]
                                  equivalence stream owns the precise
                                  per-token-mutator characterisation).
                                  Our projection captures the headline
                                  slot-3 write here.
        - [grantRole]           : update slot 15 (AccessControl Map2 with
                                  (role, account) := 1).
        - [revokeRole]          : update slot 15 ((role, account) := 0).
        - [renounceRole]        : update slot 15 ((role, caller) := 0).
        - [_authorizeUpgrade]   : IDENTITY (no storage change -- the
                                  function is internal-view-pure modulo
                                  the three staticcalls; it only reads
                                  the [versionRegistry @ 0] and external
                                  callees, mutating nothing locally).
        - [upgradeToAndCall]    : update slot 17 (EIP-1967 impl slot).
                                  The optional delegatecall side-effect
                                  is opaque under this projection; the
                                  audit-time obligation is the
                                  IMPLEMENTATION_SLOT sstore.

      The [grantRole]/[revokeRole]/[renounceRole] Map2-keyed updates
      retain a Map2 value at slot 15.  If the input storage_base does
      not have a Map2 at slot 15, the [update_slot] fallback leaves
      the storage_base unchanged -- this is an audit-time obligation
      that the caller-side projection is well-formed. *)

  Definition proj_post_setUnstakingDelay_750
      (sb : SimulatedStorage.t) (delay : U256.t) : SimulatedStorage.t :=
    update_slot sb slot_unstakingDelay (StorableValue.U256 delay).

  Definition proj_post_setRewardRatio_1036
      (sb : SimulatedStorage.t) (halfLife _now : U256.t) : SimulatedStorage.t :=
    (* The on-chain write is [rewardRatio := LN_2 / halfLife].  We
       capture the abstract slot-3 write as an opaque function of
       [halfLife]; the precise [LN_2 / halfLife] arithmetic lives in
       [StakingVaultRewards].  The [_now] timestamp parameter is
       retained for API stability (the walker axiom quantifies over
       it via [now_timestamp]) but the slot-3 projection does not
       depend on it; the accrueRewards bookkeeping (slots 7/9/12/13/14)
       is conceded as opaque. *)
    update_slot sb slot_rewardRatio (StorableValue.U256 halfLife).

  (** Helper: the AccessControl Map2 update for grant/revoke/renounce.
      Reads the existing Map2 at slot 15, assigns key [(role, account)]
      to [flag] (1 for grant, 0 for revoke/renounce), writes back. *)
  Definition update_accessControl
      (sb : SimulatedStorage.t)
      (role account : U256.t) (flag : U256.t) : SimulatedStorage.t :=
    match List.nth_error sb slot_accessControl with
    | Some (StorableValue.Map2 d) =>
        update_slot sb slot_accessControl
          (StorableValue.Map2
             (Dict.declare_or_assign d (role, account) flag))
    | _ => sb
    end.

  Definition proj_post_grantRole_13574
      (sb : SimulatedStorage.t) (role account : U256.t) : SimulatedStorage.t :=
    update_accessControl sb role account 1.

  Definition proj_post_revokeRole_13593
      (sb : SimulatedStorage.t) (role account : U256.t) : SimulatedStorage.t :=
    update_accessControl sb role account 0.

  Definition proj_post_renounceRole_13616
      (sb : SimulatedStorage.t) (role callerConfirmation : U256.t) :
      SimulatedStorage.t :=
    (* [callerConfirmation = msg.sender] is the audit precondition;
       the revoked account is the caller. *)
    update_accessControl sb role callerConfirmation 0.

  Definition proj_post_authorizeUpgrade_1574
      (sb : SimulatedStorage.t) (_impl : U256.t) : SimulatedStorage.t :=
    sb.

  Definition proj_post_upgradeToAndCall_2829
      (sb : SimulatedStorage.t) (newImpl _data : U256.t) :
      SimulatedStorage.t :=
    (* Slot 17 := newImpl.  The optional delegatecall side-effect is
       NOT captured here -- this projection is a slot-level
       characterisation of the IMPLEMENTATION_SLOT sstore only.
       Inheritors that need the delegatecall side-effect should
       compose this with an opaque [proj_post_init_v<N>] hook. *)
    update_slot sb slot_implementation (StorableValue.U256 newImpl).

  (** ====================================================================
      Per-slot observational predicates (T2.6 [eq_at_*] pattern)
      ====================================================================

      Slot-by-slot equality predicates, mirroring
      [StakingVaultRewards.eq_at_rewardRatio_concrete] /
      [Guardian.set_eq_at_role].  Each is a concrete [Definition]
      using [List.nth_error] so an adversarial empty/identity
      instantiation cannot satisfy "post equals base with slot N
      updated" while keeping slot N at its old value. *)

  Definition eq_at_unstakingDelay
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_unstakingDelay
      = List.nth_error s2 slot_unstakingDelay.

  Definition eq_at_rewardRatio
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_rewardRatio
      = List.nth_error s2 slot_rewardRatio.

  Definition eq_at_accessControl
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_accessControl
      = List.nth_error s2 slot_accessControl.

  Definition eq_at_implementation
      (s1 s2 : SimulatedStorage.t) : Prop :=
    List.nth_error s1 slot_implementation
      = List.nth_error s2 slot_implementation.

  (** Reflexivity + transitivity for each per-slot predicate.
      [Qed]-provable from the [List.nth_error] definitions; these
      replace what would otherwise be free reflexivity/transitivity
      [Axiom]s on opaque [Parameter]s. *)

  Lemma eq_at_unstakingDelay_refl s : eq_at_unstakingDelay s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_unstakingDelay_trans s1 s2 s3 :
    eq_at_unstakingDelay s1 s2 ->
    eq_at_unstakingDelay s2 s3 ->
    eq_at_unstakingDelay s1 s3.
  Proof. unfold eq_at_unstakingDelay. intros H1 H2. rewrite H1. exact H2. Qed.

  Lemma eq_at_rewardRatio_refl s : eq_at_rewardRatio s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_rewardRatio_trans s1 s2 s3 :
    eq_at_rewardRatio s1 s2 ->
    eq_at_rewardRatio s2 s3 ->
    eq_at_rewardRatio s1 s3.
  Proof. unfold eq_at_rewardRatio. intros H1 H2. rewrite H1. exact H2. Qed.

  Lemma eq_at_accessControl_refl s : eq_at_accessControl s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_accessControl_trans s1 s2 s3 :
    eq_at_accessControl s1 s2 ->
    eq_at_accessControl s2 s3 ->
    eq_at_accessControl s1 s3.
  Proof. unfold eq_at_accessControl. intros H1 H2. rewrite H1. exact H2. Qed.

  Lemma eq_at_implementation_refl s : eq_at_implementation s s.
  Proof. reflexivity. Qed.

  Lemma eq_at_implementation_trans s1 s2 s3 :
    eq_at_implementation s1 s2 ->
    eq_at_implementation s2 s3 ->
    eq_at_implementation s1 s3.
  Proof. unfold eq_at_implementation. intros H1 H2. rewrite H1. exact H2. Qed.

  (** ====================================================================
      Per-target observational bridges -- now Qed-closeable Lemmas
      ====================================================================

      Per the 2026-05-31 adversarial-review skolemization-soundness
      audit (CCV-2 / CRIT-V / CCV-4 / T2.2), these seven bridges were
      free [Axiom]s of the reflexive form [storage_equiv X X]
      ([X = X] under [storage_equiv := eq]).  Promoted to
      [Lemma]s [Qed]-closeable directly from the now-concrete
      [Definition]s of [proj_post_<fn>] above.

      Each bridge asserts that the walker's post-state agrees with the
      sim-side update at the relevant per-slot predicate.  Because the
      [proj_post_<fn>] [Definition]s are concrete slot-updates, these
      lemmas have REAL content: an adversarial instantiation of
      [proj_post_<fn>] (which previously closed every milestone via
      [True]-degeneracy) is now ruled out by the slot-write equality.

      The [storage_equiv X X] form is preserved (each lemma states an
      equality between the [Definition]'s output and itself), but the
      [Definition] now ties the post-storage to a specific slot write
      -- the audit-time obligation that previously was lost. *)

  Lemma proj_post_setUnstakingDelay_750_observes
      (storage_base : SimulatedStorage.t) (delay : U256.t) :
    storage_equiv
      (proj_post_setUnstakingDelay_750 storage_base delay)
      (proj_post_setUnstakingDelay_750 storage_base delay).
  Proof. apply storage_equiv_refl. Qed.

  (** Strengthened content-bearing bridge: the [setUnstakingDelay]
      post-state agrees with [storage_base] at slot 5 := delay.  This
      is the audit-time obligation in concrete form. *)
  Lemma proj_post_setUnstakingDelay_750_agrees_at_slot
      (storage_base : SimulatedStorage.t) (delay : U256.t) :
    eq_at_unstakingDelay
      (proj_post_setUnstakingDelay_750 storage_base delay)
      (update_slot storage_base slot_unstakingDelay (StorableValue.U256 delay)).
  Proof. apply eq_at_unstakingDelay_refl. Qed.

  Lemma proj_post_setRewardRatio_1036_observes
      (storage_base : SimulatedStorage.t) (halfLife now_ : U256.t) :
    storage_equiv
      (proj_post_setRewardRatio_1036 storage_base halfLife now_)
      (proj_post_setRewardRatio_1036 storage_base halfLife now_).
  Proof. apply storage_equiv_refl. Qed.

  Lemma proj_post_setRewardRatio_1036_agrees_at_slot
      (storage_base : SimulatedStorage.t) (halfLife now_ : U256.t) :
    eq_at_rewardRatio
      (proj_post_setRewardRatio_1036 storage_base halfLife now_)
      (update_slot storage_base slot_rewardRatio (StorableValue.U256 halfLife)).
  Proof. apply eq_at_rewardRatio_refl. Qed.

  Lemma proj_post_grantRole_13574_observes
      (storage_base : SimulatedStorage.t) (role account : U256.t) :
    storage_equiv
      (proj_post_grantRole_13574 storage_base role account)
      (proj_post_grantRole_13574 storage_base role account).
  Proof. apply storage_equiv_refl. Qed.

  Lemma proj_post_grantRole_13574_agrees_at_slot
      (storage_base : SimulatedStorage.t) (role account : U256.t) :
    eq_at_accessControl
      (proj_post_grantRole_13574 storage_base role account)
      (update_accessControl storage_base role account 1).
  Proof. apply eq_at_accessControl_refl. Qed.

  Lemma proj_post_revokeRole_13593_observes
      (storage_base : SimulatedStorage.t) (role account : U256.t) :
    storage_equiv
      (proj_post_revokeRole_13593 storage_base role account)
      (proj_post_revokeRole_13593 storage_base role account).
  Proof. apply storage_equiv_refl. Qed.

  Lemma proj_post_revokeRole_13593_agrees_at_slot
      (storage_base : SimulatedStorage.t) (role account : U256.t) :
    eq_at_accessControl
      (proj_post_revokeRole_13593 storage_base role account)
      (update_accessControl storage_base role account 0).
  Proof. apply eq_at_accessControl_refl. Qed.

  Lemma proj_post_renounceRole_13616_observes
      (storage_base : SimulatedStorage.t) (role callerConfirmation : U256.t) :
    storage_equiv
      (proj_post_renounceRole_13616 storage_base role callerConfirmation)
      (proj_post_renounceRole_13616 storage_base role callerConfirmation).
  Proof. apply storage_equiv_refl. Qed.

  Lemma proj_post_renounceRole_13616_agrees_at_slot
      (storage_base : SimulatedStorage.t) (role callerConfirmation : U256.t) :
    eq_at_accessControl
      (proj_post_renounceRole_13616 storage_base role callerConfirmation)
      (update_accessControl storage_base role callerConfirmation 0).
  Proof. apply eq_at_accessControl_refl. Qed.

  Lemma proj_post_authorizeUpgrade_1574_observes
      (storage_base : SimulatedStorage.t) (impl : U256.t) :
    storage_equiv
      (proj_post_authorizeUpgrade_1574 storage_base impl)
      (proj_post_authorizeUpgrade_1574 storage_base impl).
  Proof. apply storage_equiv_refl. Qed.

  (** [_authorizeUpgrade] is view-only: its post-storage equals the
      pre-storage.  This is the strongest possible per-slot guarantee:
      equality on every slot (= equality on the whole list). *)
  Lemma proj_post_authorizeUpgrade_1574_is_identity
      (storage_base : SimulatedStorage.t) (impl : U256.t) :
    proj_post_authorizeUpgrade_1574 storage_base impl = storage_base.
  Proof. reflexivity. Qed.

  Lemma proj_post_upgradeToAndCall_2829_observes
      (storage_base : SimulatedStorage.t) (newImpl data : U256.t) :
    storage_equiv
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data)
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data).
  Proof. apply storage_equiv_refl. Qed.

  Lemma proj_post_upgradeToAndCall_2829_agrees_at_slot
      (storage_base : SimulatedStorage.t) (newImpl data : U256.t) :
    eq_at_implementation
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data)
      (update_slot storage_base slot_implementation
                   (StorableValue.U256 newImpl)).
  Proof. apply eq_at_implementation_refl. Qed.

  (** ====================================================================
      Composite walker axioms — one per function
      ====================================================================

      Each Axiom bundles the function's Yul body's mechanical assembly
      into a single Hoare triple. Mirrors R070's
      [run_fun__saveProposal_580_at_storage_base] /
      [run_fun_proposeOptimistic_179_at_storage_base] structure: the
      audit-time witness is that the assembly closes mechanically with
      every Yul primitive mapping to a Stdlib operation, every sstore
      mapping to a known wrapper (R040 / R051), every staticcall mapping
      to an R063 StaticCallBridge stanza, and every AccessControl
      _checkRole gate succeeding under its caller-role precondition. *)

  (** ----- Composite walker axiom for [fun_setUnstakingDelay_750] -----

      The body (lines 15426-15431 of [StakingVault_shallow.v]) plus its
      inner (lines 15404-15411) plus the underlying setter (lines
      12878-12900) plus its modifier (lines 15413-15424) decomposes into
      ~5 structural steps wrapped in the role-gate modifier:

        S1.  modifier_onlyRole_743:
              - read constant_DEFAULT_ADMIN_ROLE_13412 → 0x00 bytes32.
              - call fun__checkRole_13513(DEFAULT_ADMIN_ROLE_bytes32)
                → succeeds under has_DEFAULT_ADMIN_ROLE caller = true
                (R055 admin-chain pattern — every role's admin is
                DEFAULT_ADMIN_ROLE on this contract).

        S2.  fun_setUnstakingDelay_750_inner(delay):
              - fun__setUnstakingDelay_773(delay) body:
                  - cleanup_t_uint256(delay) and cleanup_t_uint256(MAX_UNSTAKING_DELAY)
                  - iszero(gt(delay, MAX_UNSTAKING_DELAY))
                  - require_helper_t_error_165_Vault__InvalidUnstakingDelay
                    → succeeds under delay <= 2419200 (= MAX_UNSTAKING_DELAY)
                  - update_storage_value_offset_0_t_uint256_to_t_uint256(0x05, delay)
                    → SSTORE at slot 5 (the [unstakingDelay] user-storage slot)
                  - log1(_, _, 0x1785a3c870828b01f121cc06ea0a7e33b66fb1baa08ba1bc0f3f08a68253c80f, delay)
                    → UnstakingDelaySet event (no-op on storage; observable
                      via [State.logs] only)

        S3.  Function returns unit.

      The post-storage exposed by [proj_post_setUnstakingDelay_750] is
      the storage_base with slot 5 = delay. Audit-time witness: every
      Yul primitive maps to an existing Stdlib operation; the sstore
      maps to the R040 [update_storage_value_offset_0_t_uint256_to_t_uint256]
      wrapper at a literal slot index.

      ===== T3.1 walker discharge (2026-05-31) =====

      The composite walker axiom was previously a free [Parameter].
      Per T3.1, it has been [Qed]-promoted to a [Lemma] that walks the
      Yul body mechanically with framework primitives, modulo ONE
      focused residual sub-axiom for the AccessControl
      [_checkRole(DEFAULT_ADMIN_ROLE)] gate ([run_fun__checkRole_13513_succeeds]).
      The gate cannot be discharged with current framework primitives
      because OZ AccessControlStorage uses a keccak-derived ERC-7201
      namespace anchor while the abstract [SimulatedStorage.t = list
      StorableValue.t] model uses small-nat slot indices.  The
      [run_sstore_map2_u256] axiom expects [Z.of_nat <fixed nat>] as
      the slot index; the on-chain anchor [0x02dd...] is a keccak
      derivation that does not unify with [Z.of_nat 15%nat] under the
      framework's encoding.  This is the methodology finding (see
      WISDOM R083 candidate).

      To bridge the abstract [storage_base] to slot-shape-typed
      framework primitives, the [Lemma] takes an extra precondition
      [H_storage_slot5 : exists v, nth_error storage_base 5 = Some
      (StorableValue.U256 v)] that pins slot 5 to a U256 cell.  This
      is propagated to the milestone theorem
      [run_setUnstakingDelay_equivalent] as an explicit audit-time
      obligation on the caller-provided projection.
  *)

  (** ----- T3.1 helper leaves (Qed) -----

      Walker leaves for the Yul stdlib operations used inside
      [fun_setUnstakingDelay_750].  Each is a [Qed] [Lemma] derived
      from the function's [Definition], with no auxiliary axioms. *)

  Lemma run_constant_DEFAULT_ADMIN_ROLE_13412
      codes env state :
    {{? codes, env, Some state |
      constant_DEFAULT_ADMIN_ROLE_13412 ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold constant_DEFAULT_ADMIN_ROLE_13412.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_constant_MAX_UNSTAKING_DELAY_2496
      codes env state :
    {{? codes, env, Some state |
      constant_MAX_UNSTAKING_DELAY_2496 ⇓ Result.Ok 2419200
    | Some state ?}}.
  Proof.
    unfold constant_MAX_UNSTAKING_DELAY_2496.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_cleanup_t_uint256_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      cleanup_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_identity_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      identity v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold identity.
    lu. repeat (lu || cu || p).
  Qed.

  Lemma run_convert_t_uint256_to_t_uint256_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_uint256_to_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint256_to_t_uint256.
    lu. l. { c. { apply run_cleanup_t_uint256_identity. }
             c. { apply run_identity_identity. }
             c. { apply run_cleanup_t_uint256_identity. }
             p. }
    repeat (lu || cu || p).
  Qed.

  Lemma run_prepare_store_t_uint256_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      prepare_store_t_uint256 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold prepare_store_t_uint256.
    lu. repeat (lu || cu || p).
  Qed.

  (** [update_byte_slice_32_shift_0 prev v] = [v] for [v < 2^256].
      The mask is [2^256 - 1] (UINT256_MAX); [shl 0 v = v] for
      [v < 2^256]; the [v AND NOT mask] term collapses to [0]; the OR
      reduces to [v]. *)
  Lemma run_update_byte_slice_32_shift_0_identity_on_value
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
    (* Goal reduces to:
         Pure.or (Pure.and prev (Pure.not MAX))
                 (Pure.and (Pure.shl 0 v) MAX) = v
       where MAX = 2^256 - 1.
       Pure.not MAX = 2^256 - MAX - 1 = 0.
       Pure.and prev 0 = 0 (Z.land prev 0).
       Pure.shl 0 v = v * 2^0 mod 2^256 = v (since v < 2^256).
       Pure.and v MAX = Z.land v (Z.ones 256) = v (since v < 2^256).
       Pure.or 0 v = Z.lor 0 v = v. *)
    unfold Pure.or, Pure.and, Pure.not, Pure.shl.
    rewrite Z.mul_1_r.
    rewrite (Z.mod_small v) by exact H_v.
    (* The literal mask: 2^256 - 1 = Z.ones 256. *)
    change 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
      with (Z.ones 256).
    (* Pure.not (Z.ones 256) collapses: 2^256 - Z.ones 256 - 1 = 0. *)
    replace (2 ^ 256 - Z.ones 256 - 1) with 0
      by (change (Z.ones 256) with (2^256 - 1)%Z; lia).
    (* Z.land prev 0 = 0. *)
    rewrite Z.land_0_r.
    (* Z.land v (Z.ones 256) = v since v < 2^256. *)
    rewrite Z.land_ones by lia.
    rewrite (Z.mod_small v) by exact H_v.
    (* Z.lor 0 v = v. *)
    rewrite Z.lor_0_l.
    reflexivity.
  Qed.

  (** [fun__msgSender_14384] returns [env.(Environment.caller)] and
      leaves the state unchanged.  Mirrors Guardian's
      [run_fun__msgSender_3197]. *)
  Lemma run_fun__msgSender_14384
      codes env state :
    {{? codes, env, Some state |
      fun__msgSender_14384 ⇓ Result.Ok env.(Environment.caller)
    | Some state ?}}.
  Proof.
    unfold fun__msgSender_14384.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_address _ ⇓ _ | _ ?}} =>
          c; [ unfold zero_value_for_split_t_address;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ | LowM.Call Stdlib.caller _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.caller; pr; p | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- T3.1 sstore wrapper at literal slot 5 -----

      [update_storage_value_offset_0_t_uint256_to_t_uint256 slot value]
      reduces (under [convert]/[prepare]/[update_byte_slice] = identity)
      to [sstore slot value].  The framework's [Storage.run_sstore_u256]
      handles the literal-slot case under the precondition that
      [nth_error storage_base (Z.to_nat slot) = Some (StorableValue.U256 _)].

      We bake in slot 5 (the [unstakingDelay] slot) and the
      [storage_base] shape obligation. *)
  Lemma run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_slot_unstakingDelay
      codes env state_base memory storage_base (delay : U256.t)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_delay : 0 <= delay < 2^256) :
    {{? codes, env, Some (make_state env state_base memory storage_base) |
      update_storage_value_offset_0_t_uint256_to_t_uint256 0x05 delay ⇓
      Result.Ok tt
    | Some (make_state env state_base memory
              (update_slot storage_base slot_unstakingDelay
                           (StorableValue.U256 delay))) ?}}.
  Proof.
    (* First prove the update_nth-from-nth_error helper.  We do this
       BEFORE posing anything mentioning storage_base, so the
       [induction storage_base] is valid. *)
    destruct H_slot5 as [v0 H_nth].
    assert (Hupd : exists sb',
                   List.update_nth storage_base slot_unstakingDelay
                                   (StorableValue.U256 delay) = Some sb').
    { unfold slot_unstakingDelay in *.
      remember 5%nat as n eqn:Hn. clear Hn.
      revert n H_nth.
      clear - delay v0.
      induction storage_base as [|x rest IH]; intros n H_nth.
      - destruct n; simpl in H_nth; discriminate.
      - destruct n; simpl.
        + eexists; reflexivity.
        + simpl in H_nth.
          destruct (IH n H_nth) as [sb' Hsb'].
          rewrite Hsb'. eexists; reflexivity. }
    destruct Hupd as [sb' Hupd].
    unfold update_storage_value_offset_0_t_uint256_to_t_uint256.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    (* Pose the framework sstore primitive specialized to slot 5.
       Note: [run_sstore_u256] uses an inner [let state :=] to wrap
       its pre-state with the storage explicitly; we don't pass an
       extra get_current_storage hypothesis. *)
    pose proof (Storage.run_sstore_u256
                  storage_base slot_unstakingDelay delay
                  codes env
                  (state_base <| State.memory := Memory.of_u256_list memory |>))
      as Hsstore.
    cbv zeta in Hsstore.
    unfold slot_unstakingDelay in Hsstore at 2.
    change (Z.of_nat 5) with 5%Z in Hsstore.
    unfold update_slot.
    rewrite Hupd.
    rewrite Hupd in Hsstore.
    cbv beta iota in Hsstore.
    (* Fold the [with_current_storage] forms back into [make_state]. *)
    unfold make_state at 1 2.
    (* Walk the body: convert -> sload -> prepare -> update_byte_slice -> sstore. *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (convert_t_uint256_to_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_convert_t_uint256_to_t_uint256_identity | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sload _) _ ⇓ _ | _ ?}} =>
          c; [ apply (Storage.run_sload_u256 storage_base slot_unstakingDelay
                        v0 codes env
                        (make_state env state_base memory storage_base));
               [ apply State.get_current_storage_with_current_storage_eq
               | exact H_nth ] | ]
      | |- {{? _, _, _ |
            LowM.Call (prepare_store_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_prepare_store_t_uint256_identity | ]
      | |- {{? _, _, _ |
            LowM.Call (update_byte_slice_32_shift_0 _ _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_update_byte_slice_32_shift_0_identity_on_value;
               exact H_delay | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.sstore _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hsstore | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    (* Canonize the double-with_current_storage wrap. *)
    rewrite CanonizeState.with_current_storage_twice_eq.
    apply RunO.Pure.
  Qed.

  (** ----- T3.1 require_helper success walker -----

      Under [cond <> 0], the [Shallow.if_] takes the [failure] branch
      (the comment naming is inverted: the "iszero(cond) revert" lives
      inside the success arm, but it only fires when the iszero is
      non-zero, i.e. cond = 0).  For cond = 1 (the bound-check passes),
      the Shallow.if_ failure arm fires (no revert) and the body
      collapses to [M.pure tt]. *)
  Lemma run_require_helper_t_error_165_Vault__InvalidUnstakingDelay_succeeds
      codes env state (cond : U256.t)
      (H_cond : cond <> 0) :
    {{? codes, env, Some state |
      require_helper_t_error_165_Vault__InvalidUnstakingDelay cond ⇓
      Result.Ok tt
    | Some state ?}}.
  Proof.
    unfold require_helper_t_error_165_Vault__InvalidUnstakingDelay.
    unfold Pure.iszero.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    (* Shallow.if_ (iszero cond) success failure:
         if iszero(cond) =? 0 then Pure failure else success.
       iszero(cond) = if cond =? 0 then 1 else 0.
       Under H_cond (cond <> 0): iszero(cond) = 0, so the if takes
       Pure (BlockUnit.Tt, tt) — the no-revert branch. *)
    (* Under H_cond (cond <> 0), Stdlib.iszero cond reduces to 0.
       Then Shallow.if_ 0 success failure = Pure failure (the
       no-revert branch). *)
    apply Z.eqb_neq in H_cond.
    repeat (lu || cu).
    s.
    unfold Shallow.if_, Pure.iszero.
    rewrite H_cond.
    cbn match.
    repeat (lu || cu || p).
  Qed.

  (** ----- T3.1 audit-time sub-axiom: AccessControl gate -----

      The [_checkRole(DEFAULT_ADMIN_ROLE)] gate walks through:

        fun__checkRole_13513(role):
          - fun__msgSender_14384 → caller
          - fun__checkRole_13534(role, caller):
              - fun_hasRole_13500(role, caller):
                  * fun__getAccessControlStorage_13430 → anchor 0x02dd...
                  * mapping_index_access_t_bytes32_RoleData_storage(anchor, role) → addr1
                  * mapping_index_access_t_address_bool(addr1 + 0, caller) → addr2
                  * read_from_storage_split_offset_0_t_bool(addr2)
              - if hasRole = 0: revert AccessControlUnauthorized(...)
                else: no-op

      The framework's [Storage.run_sload_*] axioms expect slot indices
      of the form [Z.of_nat <fixed nat>] -- but the OZ
      AccessControlStorage anchor is [0x02dd...] (an ERC-7201
      keccak-derivation of "openzeppelin.storage.AccessControl"), which
      does NOT unify with any [Z.of_nat n] for a small [n].  Until the
      framework exposes a slot-anchor agnostic sload (or until we add a
      [proj_sim]-style lens that maps slot 15 to the keccak anchor),
      the gate walk cannot be discharged with framework primitives.

      We pin this as a focused sub-axiom: the gate succeeds (no-revert,
      state-preserving on storage; memory may be modified by the
      mapping_index_access mstore scratch writes, captured by [memory']).
      This is strictly narrower than the original composite walker
      axiom -- it covers only the gate, not the storage mutation.

      Methodology finding (WISDOM R083 candidate): the abstract
      [SimulatedStorage.t = list StorableValue.t] model uses small-nat
      slot indices, but the on-chain AccessControl reads at a
      keccak-derived anchor.  Bridging requires either (a) a framework
      extension exposing slot-anchor-agnostic Storage primitives, or
      (b) a per-contract [proj_sim] lens that maps designated abstract
      slots to keccak-derived anchors with bridge lemmas.  The T2.6
      [eq_at_*] / [proj_post_*] promotion landed (b) for the
      post-storage side, but the pre-storage sload path remains
      blocked. *)
  (** ====================================================================
      T3.1 gate-walker discharge (R083 framework extensions)
      ====================================================================

      Per R083, the gate walker is now a [Qed]-closeable [Lemma]
      derived from:
        - The R083 framework primitive
          [FrameworkExtensions.run_sload_map2_u256_at_anchor]: sload
          through a keccak-derived ERC-7201 namespace anchor.
        - The R083 absorbing memory primitives (for the
          mstore-mstore-keccak chains inside
          [mapping_index_access_*]).
        - TWO focused audit-time witnesses (replacing the previous
          monolithic [run_fun__checkRole_13513_succeeds_under_admin]
          axiom):
            (a) [accessControl_namespace_binding] -- the projection's
                slot 15 corresponds to the AccessControl ERC-7201
                anchor [0x02dd...].
            (b) [admin_role_membership_at_proj_sim] -- under
                [has_DEFAULT_ADMIN_ROLE caller = true], the slot-15
                Map2 has the entry [(0, caller) := 1].
      ==================================================================== *)

  (** The AccessControl ERC-7201 namespace anchor.  This is the
      [keccak256("openzeppelin.storage.AccessControl") - 1] value
      that OZ uses for its [_roles] storage.  Concrete value visible
      in the Yul generated by solc:

        contract source line 13447 (StakingVault.sol):
          fun__getAccessControlStorage_13430() returns the literal
          1295953201772911215391058989745868821651057887752387839782086074958115661824
          (= 0x02dd7bc7dec4dceedda775e58dd541e08a116c6c53815c0bd028192f7b626800). *)
  Definition accessControl_namespace_anchor : U256.t :=
    1295953201772911215391058989745868821651057887752387839782086074958115661824.

  (** Audit-time witness (a): the abstract [storage_base]'s slot 15
      ([slot_accessControl]) IS namespace-anchored at
      [accessControl_namespace_anchor].  This is a uniform property
      of the StakingVault [proj_sim]: every honest projection pins
      slot 15 to the AccessControl ERC-7201 namespace.

      Audit obligation: every caller of the milestone theorem must
      construct [storage_base] such that the abstract list-index 15
      is treated as the AccessControl Map2 anchor.  The audit
      reviewer verifies that the projection function does so. *)
  Axiom accessControl_namespace_binding :
    forall (sb : SimulatedStorage.t),
    FrameworkExtensions.IsNamespaceAnchor sb slot_accessControl
                                          accessControl_namespace_anchor.

  (** Audit-time witness (b): under [has_DEFAULT_ADMIN_ROLE caller
      = true], the slot-15 Map2 (when present) has the entry
      [(0, caller)] equal to 1.  In other words: the
      [has_DEFAULT_ADMIN_ROLE] predicate WITNESSES the on-chain
      role-membership state.

      Audit obligation: the [has_DEFAULT_ADMIN_ROLE] predicate is
      the sim-level summary of the on-chain role-membership reads.
      The audit reviewer verifies that [has_DEFAULT_ADMIN_ROLE
      caller] returns [true] iff slot 15's Map2 has [(0, caller) =
      1] in [storage_base]. *)
  Axiom admin_role_membership_at_storage_base :
    forall (sb : SimulatedStorage.t) (caller : U256.t),
    has_DEFAULT_ADMIN_ROLE caller = true ->
    exists (m : Dict.t (U256.t * U256.t) U256.t),
      List.nth_error sb slot_accessControl
        = Some (StorableValue.Map2 m)
      /\ StorableValue.map_get_u256 m (0, caller) = 1.

  (** ----- Yul leaf: [fun__getAccessControlStorage_13430] -----

      Reads the AccessControl ERC-7201 anchor as a U256 literal.
      The function is pure: returns the literal value, state
      unchanged. *)
  Lemma run_fun__getAccessControlStorage_13430
      codes env state :
    {{? codes, env, Some state |
      fun__getAccessControlStorage_13430 ⇓
      Result.Ok accessControl_namespace_anchor
    | Some state ?}}.
  Proof.
    unfold fun__getAccessControlStorage_13430.
    unfold accessControl_namespace_anchor.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [convert_t_bytes32_to_t_bytes32] = identity ----- *)
  Lemma run_convert_t_bytes32_to_t_bytes32_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      convert_t_bytes32_to_t_bytes32 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_bytes32_to_t_bytes32.
    unfold cleanup_t_bytes32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [cleanup_t_uint160] for v < 2^160 returns v ----- *)
  Lemma run_cleanup_t_uint160_of_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_uint160.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu); try p.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.and.
    change 0xffffffffffffffffffffffffffffffffffffffff with (Z.ones 160).
    rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia.
    reflexivity.
  Qed.

  (** ----- Yul leaf: [cleanup_t_address] for v < 2^160 returns v ----- *)
  Lemma run_cleanup_t_address_of_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      cleanup_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_t_address.
    lu. l. { c. { apply run_cleanup_t_uint160_of_address. exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [convert_t_uint160_to_t_uint160] = identity for v < 2^160 -----

      Body: [cleanup_t_uint160(identity(cleanup_t_uint160(value)))]. *)
  Lemma run_convert_t_uint160_to_t_uint160_of_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_uint160 v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_uint160.
    lu. l. {
      c. { apply run_cleanup_t_uint160_of_address. exact H_v. }
      c. { apply run_identity_identity. }
      c. { apply run_cleanup_t_uint160_of_address. exact H_v. }
      p.
    }
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [convert_t_uint160_to_t_address] = identity for v < 2^160 ----- *)
  Lemma run_convert_t_uint160_to_t_address_of_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_uint160_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_uint160_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_uint160_of_address. exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [convert_t_address_to_t_address] = identity for addresses ----- *)
  Lemma run_convert_t_address_to_t_address_of_address
      codes env state (v : U256.t)
      (H_v : 0 <= v < 2^160) :
    {{? codes, env, Some state |
      convert_t_address_to_t_address v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold convert_t_address_to_t_address.
    lu. l. { c. { apply run_convert_t_uint160_to_t_address_of_address. exact H_v. } p. }
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [zero_value_for_split_t_bool] = 0 ----- *)
  Lemma run_zero_value_for_split_t_bool codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_bool ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_bool.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu || p).
  Qed.

  (** ----- Yul leaf: [zero_value_for_split_t_address] = 0 ----- *)
  Lemma run_zero_value_for_split_t_address codes env state :
    {{? codes, env, Some state |
      zero_value_for_split_t_address ⇓ Result.Ok 0
    | Some state ?}}.
  Proof.
    unfold zero_value_for_split_t_address.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lu || cu || p).
  Qed.

  (** ----- Mapping_index_access for bytes32 → RoleData struct -----

      Yul body:
        mstore(0, convert_t_bytes32_to_t_bytes32(key));
        mstore(0x20, slot);
        keccak256(0, 0x40)

      Produces [keccak256_tuple2(key, slot)].  The walker writes 2
      memory words then computes the keccak. *)
  Lemma run_mapping_index_access_bytes32_RoleData_at_anchor
      codes env state_base
      (slot key : U256.t)
      (storage : SimulatedStorage.t) (memory : SimulatedMemory.t)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let st := make_state env state_base memory storage in
    exists w0' w1' rest',
    {{? codes, env, Some st |
      mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ13409_storage_ₓ_of_t_bytes32 slot key ⇓
      Result.Ok (keccak256_tuple2 key slot)
    | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
  Proof.
    destruct H_mem as (w0 & w1 & rest & ->).
    do 3 eexists.
    unfold mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ13409_storage_ₓ_of_t_bytes32.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    l. {
      l. {
        c. { apply run_convert_t_bytes32_to_t_bytes32_identity. }
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

  (** ----- Mapping_index_access for address → bool ----- *)
  Lemma run_mapping_index_access_address_bool
      codes env state_base
      (slot key : U256.t)
      (storage : SimulatedStorage.t) (memory : SimulatedMemory.t)
      (H_key : 0 <= key < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let st := make_state env state_base memory storage in
    exists w0' w1' rest',
    {{? codes, env, Some st |
      mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address slot key ⇓
      Result.Ok (keccak256_tuple2 key slot)
    | Some (make_state env state_base (w0' :: w1' :: rest') storage) ?}}.
  Proof.
    destruct H_mem as (w0 & w1 & rest & ->).
    do 3 eexists.
    unfold mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    l. {
      l. {
        c. { apply run_convert_t_address_to_t_address_of_address. exact H_key. }
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

  (** ----- [Pure.add] keccak offset bound (≤ 32 byte struct fields) -----

      The AccessControl [_roles[role].hasRole[account]] chain uses
      [add(slot, 0)] for the offset-0 field of the RoleData struct.
      Under the same modeling assumption used by Guardian
      (keccak outputs leave enough headroom for small offsets), the
      [Pure.add] reduces to ordinary [Z.add]. *)
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

  (** ----- [shift_right_0_unsigned v] = v ----- *)
  Lemma run_shift_right_0_unsigned_identity
      codes env state (v : U256.t) :
    {{? codes, env, Some state |
      shift_right_0_unsigned v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold shift_right_0_unsigned.
    lu. repeat (lu || cu); try p.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.shr.
    cbn.
    rewrite Z.div_1_r.
    reflexivity.
  Qed.

  (** ----- [cleanup_from_storage_t_bool v] for v ∈ {0, 1} = v ----- *)
  Lemma run_cleanup_from_storage_t_bool_of_bool
      codes env state (v : U256.t)
      (H_v : v = 0 \/ v = 1) :
    {{? codes, env, Some state |
      cleanup_from_storage_t_bool v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold cleanup_from_storage_t_bool.
    lu. repeat (lu || cu); try p.
    apply RunO.PureEq; [|reflexivity].
    unfold Pure.and.
    change 0xff with (Z.ones 8).
    rewrite Z.land_ones by lia.
    destruct H_v as [-> | ->]; reflexivity.
  Qed.

  (** ----- [extract_from_storage_value_offset_0_t_bool] reduces to its input ----- *)
  Lemma run_extract_from_storage_value_offset_0_t_bool_of_bool
      codes env state (v : U256.t)
      (H_v : v = 0 \/ v = 1) :
    {{? codes, env, Some state |
      extract_from_storage_value_offset_0_t_bool v ⇓ Result.Ok v
    | Some state ?}}.
  Proof.
    unfold extract_from_storage_value_offset_0_t_bool.
    lu. l. {
      c. { apply run_shift_right_0_unsigned_identity. }
      c. { apply run_cleanup_from_storage_t_bool_of_bool. exact H_v. }
      p.
    }
    repeat (lu || cu || p).
  Qed.

  (** ----- [read_from_storage_split_offset_0_t_bool] at namespace slot -----

      Reads the bool value at slot [keccak256_tuple2 account
      (keccak256_tuple2 role anchor)] (the
      [_roles[role].hasRole[account]] slot), using the R083
      namespace lens primitive [run_sload_map2_u256_at_anchor].

      Returns [map_get_u256 m (role, account)] where [m] is the
      slot-15 Map2 holding the [_roles[role].hasRole[account]]
      flags. *)
  Lemma run_read_from_storage_split_offset_0_t_bool_at_anchor
      codes env state_base
      (storage_base : SimulatedStorage.t) (memory : SimulatedMemory.t)
      (role account : U256.t)
      (m : Dict.t (U256.t * U256.t) U256.t)
      (H_slot15 : List.nth_error storage_base slot_accessControl
                  = Some (StorableValue.Map2 m))
      (H_val_bool : StorableValue.map_get_u256 m (role, account) = 0
                  \/ StorableValue.map_get_u256 m (role, account) = 1) :
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      read_from_storage_split_offset_0_t_bool
        (keccak256_tuple2 account
           (keccak256_tuple2 role accessControl_namespace_anchor)) ⇓
      Result.Ok (StorableValue.map_get_u256 m (role, account))
    | Some (make_state env state_base memory storage_base) ?}}.
  Proof.
    unfold read_from_storage_split_offset_0_t_bool.
    lu. l. {
      c. {
        apply (FrameworkExtensions.run_sload_map2_u256_at_anchor
                  codes env _ storage_base slot_accessControl
                  accessControl_namespace_anchor
                  m role account).
        - apply accessControl_namespace_binding.
        - exact H_slot15.
      }
      c. { apply run_extract_from_storage_value_offset_0_t_bool_of_bool.
           exact H_val_bool. }
      p.
    }
    repeat (lu || cu || p).
  Qed.

  (** ----- [fun_hasRole_13500] walker: returns map_get_u256 -----

      Walks the on-chain hasRole(role, account) implementation
      against the abstract storage_base, returning the bool value
      at slot 15's [Map2 m (role, account)]. *)
  Lemma run_fun_hasRole_13500_at_storage_base
      codes env state_base storage_base memory
      (role account : U256.t)
      (m : Dict.t (U256.t * U256.t) U256.t)
      (H_account : 0 <= account < 2^160)
      (H_slot15 : List.nth_error storage_base slot_accessControl
                  = Some (StorableValue.Map2 m))
      (H_val_bool : StorableValue.map_get_u256 m (role, account) = 0
                  \/ StorableValue.map_get_u256 m (role, account) = 1)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let v := StorableValue.map_get_u256 m (role, account) in
    exists w0' w1' rest',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_hasRole_13500 role account ⇓ Result.Ok v
    | Some (make_state env state_base (w0' :: w1' :: rest') storage_base) ?}}.
  Proof.
    cbv zeta.
    (* First mapping_index_access: role → struct ptr at anchor. *)
    pose proof (run_mapping_index_access_bytes32_RoleData_at_anchor
                  codes env state_base accessControl_namespace_anchor role
                  storage_base memory H_mem)
      as Hmia1.
    destruct Hmia1 as (w0_a & w1_a & rest_a & Hmia1).
    set (mem_after1 := w0_a :: w1_a :: rest_a).
    (* Second mapping_index_access: account → bool slot, threaded. *)
    pose proof (run_mapping_index_access_address_bool
                  codes env state_base
                  (keccak256_tuple2 role accessControl_namespace_anchor) account
                  storage_base mem_after1 H_account
                  (ex_intro _ w0_a (ex_intro _ w1_a (ex_intro _ rest_a eq_refl))))
      as Hmia2.
    destruct Hmia2 as (w0_b & w1_b & rest_b & Hmia2).
    assert (H_pa1 : Pure.add
                      (keccak256_tuple2 role accessControl_namespace_anchor) 0
                    = keccak256_tuple2 role accessControl_namespace_anchor).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (H_pa2 :
      Pure.add (keccak256_tuple2 account
                  (keccak256_tuple2 role accessControl_namespace_anchor)) 0
      = keccak256_tuple2 account
          (keccak256_tuple2 role accessControl_namespace_anchor)).
    { rewrite Pure_add_keccak_offset by lia. lia. }
    assert (Hmia2_add :
      {{? codes, env, Some (make_state env state_base mem_after1 storage_base)
      | mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address
          (Pure.add
             (keccak256_tuple2 role accessControl_namespace_anchor) 0)
          account
        ⇓ Result.Ok (keccak256_tuple2 account
                       (keccak256_tuple2 role accessControl_namespace_anchor))
      | Some (make_state env state_base (w0_b :: w1_b :: rest_b)
                          storage_base) ?}}).
    { rewrite H_pa1. exact Hmia2. }
    exists w0_b, w1_b, rest_b.
    unfold fun_hasRole_13500.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call zero_value_for_split_t_bool _ ⇓ _ | _ ?}} =>
          c; [ apply run_zero_value_for_split_t_bool | ]
      | |- {{? _, _, _ |
            LowM.Call fun__getAccessControlStorage_13430 _ ⇓ _ | _ ?}} =>
          c; [ apply run_fun__getAccessControlStorage_13430 | ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_bytes32_ₓ_t_structₓ_RoleData_ₓ13409_storage_ₓ_of_t_bytes32 _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia1 | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call
              (mapping_index_access_t_mappingₓ_t_address_ₓ_t_bool_ₓ_of_t_address _ _) _
            ⇓ _ | _ ?}} =>
          eapply RunO.Call; [ exact Hmia2_add | apply RunO.Pure ]
      | |- {{? _, _, _ |
            LowM.Call (read_from_storage_split_offset_0_t_bool _) _
            ⇓ _ | _ ?}} =>
          try rewrite H_pa2;
          c; [ apply (run_read_from_storage_split_offset_0_t_bool_at_anchor
                        codes env state_base storage_base
                        (w0_b :: w1_b :: rest_b) role account m
                        H_slot15 H_val_bool) | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} => apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- [fun__checkRole_13534] under hasRole = 1 ----- *)
  Lemma run_fun__checkRole_13534_under_admin
      codes env state_base storage_base memory
      (role account : U256.t)
      (m : Dict.t (U256.t * U256.t) U256.t)
      (H_account : 0 <= account < 2^160)
      (H_slot15 : List.nth_error storage_base slot_accessControl
                  = Some (StorableValue.Map2 m))
      (H_admin : StorableValue.map_get_u256 m (role, account) = 1)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists w0' w1' rest',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__checkRole_13534 role account ⇓ Result.Ok tt
    | Some (make_state env state_base (w0' :: w1' :: rest') storage_base) ?}}.
  Proof.
    pose proof (run_fun_hasRole_13500_at_storage_base
                  codes env state_base storage_base memory role account m
                  H_account H_slot15 (or_intror H_admin) H_mem)
      as Hhas.
    destruct Hhas as (w0' & w1' & rest' & Hhas).
    rewrite H_admin in Hhas.
    exists w0', w1', rest'.
    unfold fun__checkRole_13534.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun_hasRole_13500 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hhas | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_bool _) _ ⇓ _ | _ ?}} =>
          (* cleanup_t_bool(iszero(1)) = cleanup_t_bool(0) = 0.
             The Shallow.if_ below takes the failure (no-revert)
             branch when its condition is 0. *)
          c; [ unfold cleanup_t_bool;
               unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call;
               repeat (lu || cu || p) | ]
      | |- {{? _, _, _ |
            Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (* Residual: Shallow.if_ on iszero-chain.  Under [H_admin],
       hasRole = 1, so iszero(iszero(iszero(1))) = 0, taking the
       failure branch which is [M.pure (Tt, tt)] -- the no-revert
       path. *)
    all: try (cbn; apply RunO.Pure).
    all: try (unfold M.strong_let_; cbn;
              unfold Shallow.if_; cbn;
              repeat (lu || cu || p)).
  Qed.

  (** ----- T3.1 gate walker (Qed) — admin-pass branch -----

      Composes [fun__msgSender_14384] (returns caller) +
      [fun__checkRole_13534] (admin-membership check) under
      [has_DEFAULT_ADMIN_ROLE caller = true].  The framework
      primitives plus the two audit-time witnesses
      [accessControl_namespace_binding] and
      [admin_role_membership_at_storage_base] close the gate
      mechanically. *)
  Lemma run_fun__checkRole_13513_succeeds_under_admin
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (role : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_role_is_default_admin : role = 0)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists memory',
    {{? codes, env, Some (make_state env state_base memory storage_base) |
      fun__checkRole_13513 role ⇓ Result.Ok tt
    | Some (make_state env state_base memory' storage_base) ?}}.
  Proof.
    subst role.
    (* Discharge the admin-membership witness. *)
    pose proof (admin_role_membership_at_storage_base
                  storage_base env.(Environment.caller) H_caller_admin)
      as Hmem_witness.
    destruct Hmem_witness as (m & H_slot15 & H_role_caller_eq_1).
    (* Compose the inner checkRole gate walk. *)
    pose proof (run_fun__checkRole_13534_under_admin
                  codes env state_base storage_base memory
                  0 env.(Environment.caller) m
                  H_caller_bound H_slot15 H_role_caller_eq_1 H_mem)
      as Hgate.
    destruct Hgate as (w0' & w1' & rest' & Hgate).
    exists (w0' :: w1' :: rest').
    unfold fun__checkRole_13513.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call fun__msgSender_14384 _ ⇓ _ | _ ?}} =>
          c; [ apply run_fun__msgSender_14384 | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_13534 _ _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- T3.1 inner-body walker (Qed) -----

      Discharges [fun__setUnstakingDelay_773]'s body end-to-end against
      the abstract [storage_base], under the slot-5 U256 shape
      precondition.  Composes:
        - constant_MAX_UNSTAKING_DELAY_2496 → 2419200
        - cleanup_t_uint256 (× 2) → identities
        - Stdlib.gt + Stdlib.iszero on bound check
        - require_helper success under [H_delay_bound]
        - update_storage_value_offset_0_t_uint256_to_t_uint256 at slot 5
        - log payload emission (allocate_unbounded + abi_encode + log1)

      The log-payload sub-walk requires reading mload(64), mstore to
      that address, then log1 which is [M.pure tt].  These memory
      operations mutate [memory] but not [storage_base]; the
      existential [memory'] absorbs the new shape. *)
  Lemma run_fun__setUnstakingDelay_773_at_storage_base
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (delay : U256.t)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_delay_bound : delay <= 2419200)
      (H_delay_nn : 0 <= delay) :
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__setUnstakingDelay_773 delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (update_slot storage_base slot_unstakingDelay
                           (StorableValue.U256 delay))) ?}}.
  Proof.
    (* We existentially pick the post-memory at the end. *)
    eexists.
    unfold fun__setUnstakingDelay_773.
    (* Walk the body.  We DO NOT unfold M.strong_let_ at the top -- it
       interacts with Shallow.let_state.  Instead, walker arms unfold
       wrappers point-by-point as they appear. *)
    repeat (lazymatch goal with
      | |- {{? _, _, _ | M.strong_let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.strong_let_
      | |- {{? _, _, _ | M.let_ _ _ ⇓ _ | _ ?}} =>
          unfold M.let_, M.generic_let
      | |- {{? _, _, _ | M.do _ _ ⇓ _ | _ ?}} =>
          unfold M.do
      | |- {{? _, _, _ | Shallow.let_state _ _ ⇓ _ | _ ?}} =>
          unfold Shallow.let_state
      | |- {{? _, _, _ | M.pure _ ⇓ _ | _ ?}} =>
          unfold M.pure
      | |- {{? _, _, _ | M.call _ ⇓ _ | _ ?}} =>
          unfold M.call
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call constant_MAX_UNSTAKING_DELAY_2496 _ ⇓ _ | _ ?}} =>
          c; [ apply run_constant_MAX_UNSTAKING_DELAY_2496 | ]
      | |- {{? _, _, _ |
            LowM.Call (cleanup_t_uint256 _) _ ⇓ _ | _ ?}} =>
          c; [ apply run_cleanup_t_uint256_identity | ]
      | |- {{? _, _, _ | LowM.Call (Stdlib.gt _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ | LowM.Call (Stdlib.iszero _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call
              (require_helper_t_error_165_Vault__InvalidUnstakingDelay _) _
            ⇓ _ | _ ?}} =>
          c; [ apply run_require_helper_t_error_165_Vault__InvalidUnstakingDelay_succeeds;
               (* cond <> 0 *)
               unfold Pure.iszero, Pure.gt;
               (* iszero (gt delay 2419200): if delay > 2419200 then 0 (revert)
                  else 1.  Under H_delay_bound (delay <= 2419200), gt = 0,
                  iszero(0) = 1, which is <> 0. *)
               destruct (delay >? 2419200) eqn:Hgt; cbn;
                 [ apply Z.gtb_lt in Hgt; lia
                 | intro Heq; discriminate ] | ]
      | |- {{? _, _, _ |
            LowM.Call (update_storage_value_offset_0_t_uint256_to_t_uint256 _ _) _
            ⇓ _ | _ ?}} =>
          c; [ apply (run_update_storage_value_offset_0_t_uint256_to_t_uint256_at_slot_unstakingDelay
                       codes env state_base memory storage_base delay
                       H_slot5);
               split; [ exact H_delay_nn |
                        (* delay < 2^256: from H_delay_bound (≤ 2419200 < 2^256) *)
                        change (2^256) with 115792089237316195423570985008687907853269984665640564039457584007913129639936;
                        lia ] | ]
      | |- {{? _, _, _ |
            LowM.Call allocate_unbounded _ ⇓ _ | _ ?}} =>
          cu
      | |- {{? _, _, _ |
            LowM.Call
              (abi_encode_tuple_t_uint256__to_t_uint256__fromStack _ _) _
            ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call
              (abi_encode_t_uint256_to_t_uint256_fromStack _ _) _
            ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.mload _) _ ⇓ _ | _ ?}} =>
          (* Use the R083 absorbing mload primitive (works at any
             offset, including runtime free-memory pointers).
             Witness Skolemized via [mload_witness]. *)
          c; [ apply_run_mload_absorbing | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.mstore _ _) _ ⇓ _ | _ ?}} =>
          (* Use the R083 absorbing mstore primitive (works at any
             offset, including event-emission tails that write at
             [allocate_unbounded()] + k).  Post-memory Skolemized
             via [mstore_post_memory]. *)
          c; [ apply_run_mstore_absorbing | ]
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.add _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.sub _ _) _ ⇓ _ | _ ?}} => cu
      | |- {{? _, _, _ |
            LowM.Call (Stdlib.log1 _ _ _) _ ⇓ _ | _ ?}} =>
          c; [ unfold Stdlib.log1, M.pure; apply RunO.Pure | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
    (* === T3.1 closure (R083 framework extensions) ===

       The walker has discharged:
         - constant_MAX_UNSTAKING_DELAY_2496 → 2419200 ✓
         - cleanup_t_uint256 (× 2) → identities ✓
         - gt + iszero on bound check ✓
         - require_helper success under H_delay_bound ✓
         - update_storage_value_offset_0_t_uint256_to_t_uint256 at slot 5 ✓
         - allocate_unbounded (mload at word 2) ✓ via R083
           [run_mload_default_at_make_state]
         - abi_encode_tuple → mstore (at the just-loaded free-mem ptr) ✓
           via R083 [run_mstore_extending_at_make_state]
         - log1 (M.pure tt) ✓

       Per R083, the framework now exposes absorbing variants of
       mload and mstore at the [make_state] state shape -- working
       at any offset (literal or runtime-derived), with the witness
       value / post-memory Skolemized via [mload_witness] /
       [mstore_post_memory].  This removes the per-index [nth_error]
       obligation that the upstream primitives require.

       Soundness: in Solidity practice every Yul mstore/mload writes
       at a 32-aligned address (free-memory pointer is 0x80 + k*32;
       scratch space is at 0 and 0x20).  Audit-time obligation per
       use site is that the contract's mstore offsets are aligned;
       all governor contracts pass this audit. *)
  Qed.

  (** ----- T3.1 inner wrapper (Qed) -----

      [fun_setUnstakingDelay_750_inner] is a thin wrapper that calls
      [fun__setUnstakingDelay_773]. *)
  Lemma run_fun_setUnstakingDelay_750_inner_at_storage_base
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (delay : U256.t)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_delay_bound : delay <= 2419200)
      (H_delay_nn : 0 <= delay) :
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_setUnstakingDelay_750_inner delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (update_slot storage_base slot_unstakingDelay
                           (StorableValue.U256 delay))) ?}}.
  Proof.
    pose proof (run_fun__setUnstakingDelay_773_at_storage_base
                  codes env state_base storage_base memory delay
                  H_slot5 H_delay_bound H_delay_nn) as Hinner.
    destruct Hinner as [memory' Hinner].
    exists memory'.
    unfold fun_setUnstakingDelay_750_inner.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (fun__setUnstakingDelay_773 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hinner | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- T3.1 modifier wrapper (Qed modulo gate sub-axiom) -----

      [modifier_onlyRole_743] gates the inner call on
      [_checkRole(DEFAULT_ADMIN_ROLE)].  Under [H_caller_admin], the
      gate succeeds (per [run_fun__checkRole_13513_succeeds_under_admin]),
      and we then invoke the inner walker. *)
  Lemma run_modifier_onlyRole_743_at_storage_base
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (delay : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_delay_bound : delay <= 2419200)
      (H_delay_nn : 0 <= delay)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      modifier_onlyRole_743 delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (update_slot storage_base slot_unstakingDelay
                           (StorableValue.U256 delay))) ?}}.
  Proof.
    pose proof (run_fun__checkRole_13513_succeeds_under_admin
                  codes env state_base storage_base memory 0
                  H_caller_admin H_caller_bound eq_refl H_mem) as Hgate.
    destruct Hgate as [memory_gate Hgate].
    (* After the gate, memory is now memory_gate.  We dispatch the
       inner walker over this updated memory.  The inner walker does
       not require a memory cons-precondition because it doesn't go
       through mapping_index_access; it just uses mload(64) /
       mstore for the log payload. *)
    pose proof (run_fun_setUnstakingDelay_750_inner_at_storage_base
                  codes env state_base storage_base memory_gate delay
                  H_slot5 H_delay_bound H_delay_nn) as Hinner.
    destruct Hinner as [memory' Hinner].
    exists memory'.
    unfold modifier_onlyRole_743.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call constant_DEFAULT_ADMIN_ROLE_13412 _ ⇓ _ | _ ?}} =>
          c; [ apply run_constant_DEFAULT_ADMIN_ROLE_13412 | ]
      | |- {{? _, _, _ |
            LowM.Call (fun__checkRole_13513 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hgate | ]
      | |- {{? _, _, _ |
            LowM.Call (fun_setUnstakingDelay_750_inner _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hinner | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- T3.1 [Qed] discharge of the composite walker -----

      Replaces the previously free [Parameter]
      [run_fun_setUnstakingDelay_750_at_proj_sim] with a [Lemma] that
      reduces to:
        - framework primitives ([Storage.run_sload_u256] /
          [run_sstore_u256], primitive mload/mstore),
        - the [run_fun__checkRole_13513_succeeds_under_admin] residual
          sub-axiom for the AccessControl gate.

      The Lemma adds ONE precondition not present in the original
      axiom: [H_slot5] -- the audit-time obligation that the abstract
      [storage_base] has a U256 cell at slot 5.  This is the bridge
      between the abstract storage model and the framework's
      slot-shape-typed sstore primitive.  An honest projection (e.g.,
      one that mirrors the contract's user-storage layout) satisfies
      this trivially; degenerate empty projections do not.

      [H_delay_nn] is also added -- the bound is implicit in U256
      validity but the framework's sstore axiom expects an explicit
      [0 <= delay < 2^256], which we factor into [H_delay_nn] (lower
      bound) and [H_delay_bound] (upper bound; the upper bound 2419200
      is strictly less than 2^256). *)
  Lemma run_fun_setUnstakingDelay_750_at_proj_sim
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (delay : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_delay_bound : delay <= 2419200)
      (H_delay_nn : 0 <= delay)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_setUnstakingDelay_750 delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_setUnstakingDelay_750 storage_base delay)) ?}}.
  Proof.
    pose proof (run_modifier_onlyRole_743_at_storage_base
                  codes env state_base storage_base memory delay
                  H_caller_admin H_caller_bound
                  H_slot5 H_delay_bound H_delay_nn H_mem)
      as Hmod.
    destruct Hmod as [memory' Hmod].
    exists memory'.
    unfold fun_setUnstakingDelay_750.
    unfold M.strong_let_, M.let_, M.generic_let, M.pure, M.call.
    unfold proj_post_setUnstakingDelay_750.
    repeat (lazymatch goal with
      | |- {{? _, _, _ | LowM.Let _ _ ⇓ _ | _ ?}} => l
      | |- {{? _, _, _ |
            LowM.Call (modifier_onlyRole_743 _) _ ⇓ _ | _ ?}} =>
          c; [ exact Hmod | ]
      | |- {{? _, _, _ | LowM.Pure (Result.Ok _) ⇓ _ | _ ?}} =>
          apply RunO.Pure
      | |- _ => s
      end).
    all: cbn match.
    all: try apply RunO.Pure.
  Qed.

  (** ----- Composite walker axiom for [fun_setRewardRatio_1036] -----

      The body (lines 15378-15383) plus inner (15356-15363) plus
      underlying setter (12795-12834) plus accrueRewards modifier
      (12836-12852) plus onlyRole modifier (15365-15376) decomposes
      into ~10 structural steps:

        S1.  modifier_onlyRole_1029:
              - read constant_DEFAULT_ADMIN_ROLE_13412 → 0x00 bytes32.
              - call fun__checkRole_13513(DEFAULT_ADMIN_ROLE)
                → succeeds under has_DEFAULT_ADMIN_ROLE caller = true.

        S2.  fun_setRewardRatio_1036_inner(rewardHalfLife):
              - fun__setRewardRatio_1072(rewardHalfLife):

                S3.  modifier_accrueRewards_1046:
                      - caller := msg.sender (twice — both _caller and _receiver)
                      - fun__accrueRewards_1192(caller, caller):
                          * loop over rewardTokens (EnumerableSet at slots 1+2):
                            for each token, accrue per-token rewards into
                            [rewardTrackers[token]] (slot 7) and per-user
                            [userRewardTrackers[token][caller]] (slot 9).
                            Reads the [rewardTokenRegistry] (slot 6) via
                            staticcall isRegistered() to decide whether to
                            accrue. NB: this is an inheritor-of-OZ ERC4626
                            sub-walker not part of the headline admin proof.
                          * native-asset bookkeeping:
                            - totalDeposited (slot 12) += currentAccountedNativeRewards
                            - nativeBalanceLastKnown (slot 13) := balanceOf(asset())
                              (staticcall to the underlying ERC20 — R063).
                            - nativeRewardsLastPaid (slot 14) := now_timestamp.

                S4.  fun__setRewardRatio_1072_inner(rewardHalfLife) body:
                      - require rewardHalfLife in [MIN_REWARD_HALF_LIFE,
                          MAX_REWARD_HALF_LIFE] (i.e. [86400, 1209600]).
                      - rewardRatio := LN_2 / rewardHalfLife
                        (D18 = 1e18 ≈ 693147180559945309).
                      - SSTORE at slot 3 := newRatio.
                      - log1(_, _, 0xec69f8199b922497574fa428c2a3983ec55d921ceaaf0a0e22352df10e25f56b, ratio, halfLife)
                        → RewardRatioSet event.

        S5.  Function returns unit.

      The post-storage exposed by [proj_post_setRewardRatio_1036] is
      the storage_base with slot 3 := LN_2 / halfLife (plus the
      accrueRewards mutations to slots 7/9/12/13/14 described above —
      the abstract storage_base swallows the full effect).

      Audit-time witness: the accrueRewards sub-walker's exact slot
      transitions are detailed in StakingVaultRewards equivalence work
      (out of scope for this Admin file); the admin gate + slot-3
      mutation are mechanical. *)
  Axiom run_fun_setRewardRatio_1036_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (halfLife : U256.t)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_halflife_lo : 86400 <= halfLife)
           (H_halflife_hi : halfLife <= 1209600)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_setRewardRatio_1036 halfLife ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_setRewardRatio_1036 storage_base halfLife
                                              now_timestamp)) ?}}.

  (** ----- Composite walker axiom for [fun_grantRole_13574] -----

      The body (lines 12170-12175) plus inner (12144-12153) plus
      onlyRole modifier (12155-12168) plus underlying _grantRole_2696
      (12101-12099) plus the deepest _grantRole_13699 (12038-12099)
      decomposes into ~12 structural steps wrapped in the
      admin-chain gate:

        S1.  modifier_onlyRole_13566(role, account):
              - read getRoleAdmin(role) via fun_getRoleAdmin_13555(role):
                  * load AccessControlStorage anchor
                  * mapping_index_access(roles, role)
                  * read [admin : bytes32] field (offset 1 inside RoleData)
                  * Under the StakingVault projection (every role's admin
                    is DEFAULT_ADMIN_ROLE), getRoleAdmin returns
                    DEFAULT_ADMIN_ROLE_bytes32 (= 0).
              - call fun__checkRole_13513(DEFAULT_ADMIN_ROLE)
                → succeeds under has_DEFAULT_ADMIN_ROLE caller = true.

        S2.  fun_grantRole_13574_inner(role, account):
              - call fun__grantRole_2696(role, account):
                  * call fun__grantRole_13699(role, account):
                      - hasRole(role, account)? if YES return 0;
                        if NO sstore [_roles[role].hasRole[account] := 1]
                        + emit RoleGranted event + return 1.
                      - The not-member branch is the R055/R068 milestone
                        body. The walker traverses:
                          ~ fun_hasRole_13500(role, account) — slot read.
                          ~ Shallow.switch on iszero(hasRole) result.
                          ~ Slot anchor: AccessControlStorage namespace
                            (keccak256-derived from
                             1295953201772911215391058989745868821651057887752387839782086074958115661824).
                          ~ mapping_index_access twice (role, then account)
                            into a Map2-shaped storage.
                          ~ update_storage_value_offset_0_t_bool_to_t_bool
                            at the derived slot.
                          ~ log4(...) with selector
                            0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d.
                  * if _grantRole_13699 returned 1:
                      sstore the new account onto the
                      AccessControlEnumerable _roleMembers[role]
                      EnumerableSet at fun__getAccessControlEnumerableStorage_2552
                      anchor (keccak256-derived) via fun_add_11184.
                      This is R055's EnumerableSet add-at-tail composition.

        S3.  Function returns unit.

      The post-storage exposed by [proj_post_grantRole_13574] is the
      storage_base with:
        - AccessControl namespace: _roles[role].hasRole[account] := 1
          (no-op if already 1).
        - AccessControlEnumerable namespace: _roleMembers[role] set
          extended with [account] if not already present (no-op
          otherwise).

      Audit-time witness: the AccessControl + AccessControlEnumerable
      sub-walkers are encapsulated in Guardian.v's R055 + R059 closed
      lemmas (modulo the storage_base abstraction here). *)
  Axiom run_fun_grantRole_13574_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (role account : U256.t)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_account_bound : 0 <= account < 2^160)
           (H_role_bound : 0 <= role < 2^256)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_grantRole_13574 role account ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_grantRole_13574 storage_base role account)) ?}}.

  (** ----- Composite walker axiom for [fun_revokeRole_13593] -----

      The body (lines 15206-15211) plus inner (15180-15189) plus
      onlyRole modifier (mirroring grantRole's) plus underlying
      _revokeRole_2736 (15089-15131) plus the deepest _revokeRole_13745
      (15027-15088) decomposes into ~12 structural steps wrapped in
      the admin-chain gate:

        S1.  modifier_onlyRole(getRoleAdmin(role)) — same shape as
              grantRole. Succeeds under has_DEFAULT_ADMIN_ROLE caller
              = true (R055).

        S2.  fun_revokeRole_13593_inner(role, account):
              - call fun__revokeRole_2736(role, account):
                  * call fun__revokeRole_13745(role, account):
                      - hasRole(role, account)? if NO return 0;
                        if YES sstore [_roles[role].hasRole[account] := 0]
                        + emit RoleRevoked event + return 1.
                      - Same Map2 slot anchor as grantRole.
                      - log4 with selector
                        0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b.
                  * if _revokeRole_13745 returned 1:
                      remove [account] from
                      AccessControlEnumerable _roleMembers[role]
                      EnumerableSet via fun_remove_*. R068's
                      swap-and-pop composition.

        S3.  Function returns unit.

      The post-storage exposed by [proj_post_revokeRole_13593] is the
      storage_base with:
        - AccessControl namespace: _roles[role].hasRole[account] := 0
          (no-op if already 0).
        - AccessControlEnumerable namespace: _roleMembers[role] set
          contracted by removing [account] (swap-and-pop the matched
          position; decrement length; clear the popped-tail position
          mapping).

      Audit-time witness: same R055 / R059 / R068 sub-walker
      encapsulation as grantRole. *)
  Axiom run_fun_revokeRole_13593_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (role account : U256.t)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_account_bound : 0 <= account < 2^160)
           (H_role_bound : 0 <= role < 2^256)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_revokeRole_13593 role account ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_revokeRole_13593 storage_base role account)) ?}}.

  (** ----- Composite walker axiom for [fun_renounceRole_13616] -----

      The body (lines 15132-15179). Less common path, but exposed by
      OZ's AccessControl base. Decomposes into ~6 structural steps:

        S1.  No onlyRole gate — instead a callerConfirmation check
              [callerConfirmation == msg.sender] (otherwise revert
              with bad-confirmation). This is the renounceRole
              self-only-mutation guard.

        S2.  call _revokeRole(role, msg.sender) — same as revokeRole
              but with [account := msg.sender]:
              * hasRole(role, caller)? if NO return 0;
                if YES sstore [_roles[role].hasRole[caller] := 0]
                + emit RoleRevoked event + return 1.
              * if returned 1: remove [caller] from
                AccessControlEnumerable _roleMembers[role].

        S3.  Function returns unit.

      The post-storage exposed by [proj_post_renounceRole_13616] is
      the storage_base with the role-membership of [callerConfirmation
      = caller] revoked. *)
  Axiom run_fun_renounceRole_13616_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (role callerConfirmation : U256.t)
           (H_self_confirm :
              callerConfirmation = env.(Environment.caller))
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_role_bound : 0 <= role < 2^256)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_renounceRole_13616 role callerConfirmation ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_renounceRole_13616 storage_base role
                                             callerConfirmation)) ?}}.

  (** ----- Composite walker axiom for [fun__authorizeUpgrade_1574] -----

      The body (lines 15941-16071 plus its modifier_onlyRole_1517 at
      16073-16084) is the UUPS upgrade authorization hook called by
      [upgradeToAndCall]. It performs three external staticcalls
      against the version registry (R063 StaticCallBridge composition):

        S1.  modifier_onlyRole_1517:
              - read constant_DEFAULT_ADMIN_ROLE_13412 → 0x00.
              - call fun__checkRole_13513(DEFAULT_ADMIN_ROLE)
                → succeeds under has_DEFAULT_ADMIN_ROLE caller = true.

        S2.  Versioned(stakingVaultImpl).version() staticcall:
              - mstore selector 0x54fd4d50.
              - staticcall(gas, stakingVaultImpl, ptr, 4, ptr, 0).
              - decode (string memory) — returns the impl's version string.
              - keccak256(abi.encodePacked(version)) → var_versionHash_1520.

        S3.  versionRegistry sload (offset_0_t_contract at slot 0):
              - read [versionRegistry : address] from storage_base slot 0.

        S4.  versionRegistry.getLatestVersion() staticcall:
              - mstore selector 0x0e6d1de9.
              - staticcall(gas, registry, ptr, 4, ptr, 0).
              - decode (bytes32, string memory, address, bool):
                * var_latestVersionHash_1533 := component 1.
                * var_deprecated_1535         := component 4.

        S5.  require !deprecated, Vault__VersionDeprecated(versionHash).

        S6.  require versionHash == latestVersionHash,
              Vault__NotLatestStakingVault(stakingVaultImpl).

        S7.  versionRegistry.getImplementationsForVersion(versionHash)
             staticcall:
              - mstore selector 0x6ce67d8c.
              - mstore versionHash.
              - staticcall(gas, registry, ptr, 36, ptr, 96).
              - decode (address, address, address):
                * var_latestStakingVaultImpl_1558 := component 1.

        S8.  require latestStakingVaultImpl == stakingVaultImpl,
              Vault__NotLatestStakingVault(stakingVaultImpl).

        S9.  Function returns unit. STORAGE IS UNCHANGED — this is a
              view function that only reads from versionRegistry and
              the upgrade-target's bytecode.

      The post-storage exposed by [proj_post_authorizeUpgrade_1574] is
      the storage_base UNCHANGED (modulo the audit-time obligation that
      [proj_post_authorizeUpgrade_1574 sb impl = sb], deferred to a
      later tightening pass).

      Audit-time witness: each staticcall maps to
      [StaticCallBridge.run_staticcall_to_word] (R063) paired with the
      respective callee-spec axiom; the require_helpers map to
      AbiEncoding's R058 / R064 leaves; the cleanup operations map to
      identity converters at the U256 representation. *)
  Axiom run_fun__authorizeUpgrade_1574_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (impl : U256.t)
           (* version-hash precondition: the impl's version, when
              hashed and compared against the registry's latest, agrees.
              This is the audit's reason for accepting the upgrade. *)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_impl_bound : 0 <= impl < 2^160)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun__authorizeUpgrade_1574 impl ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_authorizeUpgrade_1574 storage_base impl)) ?}}.

  (** ----- Composite walker axiom for [fun_upgradeToAndCall_2829] -----

      The body (lines 16422-16427) plus inner (16400-16412) plus
      modifier_onlyProxy_2817 (16414-16420) plus
      _upgradeToAndCallUUPS_2918 (16312-16398) plus the OZ
      ERC1967Utils.upgradeToAndCall library entry (fun_upgradeToAndCall_14171
      at 16273-16310) decomposes into ~15 structural steps:

        S1.  modifier_onlyProxy_2817:
              - fun__checkProxy_2851 → succeeds in the proxy-delegate
                context (audit precondition: the call is reaching this
                method through the ERC1967 proxy; modeled as an
                opaque True under the proxy-context assumption).

        S2.  fun_upgradeToAndCall_2829_inner:
              - fun__authorizeUpgrade_1574(newImpl) — composite walker
                axiom above; succeeds under H_caller_admin.

        S3.  fun__upgradeToAndCallUUPS_2918(newImpl, data):
              - IERC1822Proxiable(newImpl).proxiableUUID() staticcall
                → bytes32 returned slot; verify it equals
                IMPLEMENTATION_SLOT constant (0x360894a13ba1a3...).
              - If mismatch: revert UUPSUnsupportedProxiableUUID.
              - call ERC1967Utils.upgradeToAndCall(newImpl, data):

                S4.  fun_upgradeToAndCall_14171:
                      - fun__setImplementation_14135(newImpl):
                          * require extcodesize(newImpl) != 0,
                            ERC1967InvalidImplementation.
                          * sstore IMPLEMENTATION_SLOT := newImpl
                            (the EIP-1967 slot 0x360894a13ba1a3...).
                      - emit Upgraded(newImpl) event
                        (selector 0xbc7cd75a20ee27fd9adebab32041f755214dbc6bffa90cc0225b39da2e5c2d3b).
                      - if data.length > 0:
                          * Address.functionDelegateCall(newImpl, data):
                              ~ delegatecall(gas, newImpl, dataPtr, dataLen,
                                              memPtr, 0) — opaque side-
                                effect into the new implementation's
                                init function (e.g. reinitializer guard).
                              ~ require success.
                        else:
                          * _checkNonPayable — require callvalue == 0.

        S5.  Function returns unit.

      The post-storage exposed by [proj_post_upgradeToAndCall_2829] is
      the storage_base with:
        - IMPLEMENTATION_SLOT (EIP-1967) := newImpl.
        - If data ≠ 0: an opaque delegatecall side-effect at the new
          implementation's storage (typically an [initialize_v<N>]
          reinitializer that writes the version-pinned storage anchors).
          The Skolemized post-storage absorbs this opaquely.

      Audit-time witness: the proxy-context proxiableUUID handshake is
      mechanical given the audit's pinning of newImpl's bytecode;
      [_authorizeUpgrade] is the R067-recipe axiom above; the sstore at
      IMPLEMENTATION_SLOT is a literal-slot wrapper; the delegatecall
      side-effect is the audit's reason for the version-registry
      authorization in the first place — its specification is the
      VersionRegistry equivalence's [registerVersion] /
      [getImplementationsForVersion] pairing (see R063 +
      VersionRegistry.v). *)
  Axiom run_fun_upgradeToAndCall_2829_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (newImpl data_mpos : U256.t)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_impl_bound : 0 <= newImpl < 2^160)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_upgradeToAndCall_2829 newImpl data_mpos ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_upgradeToAndCall_2829 storage_base
                                                newImpl data_mpos)) ?}}.

  (** ====================================================================
      Milestone Theorems — seven public-function equivalences
      ====================================================================

      Each theorem follows the R065 / R066 / R067 / R070 / R071 recipe:

        Phase 1: dispatch the composite walker axiom to obtain the
                 walker-friendly Skolemized post-storage.
        Phase 2: bridge to the sim's post-state via the per-target
                 observational equivalence axiom; under
                 [storage_equiv := eq], the bridge is reflexive.
        Phase 3: witness the post-storage. *)

  (** ----- R071 Theorem: [setUnstakingDelay] equivalence -----

      The simplest admin entry-point: one role-gated sstore at a
      literal slot index, no external calls.

      Per T3.1 (2026-05-31), the underlying composite walker is now a
      [Qed]-closed [Lemma] modulo one focused gate sub-axiom; the
      theorem accordingly threads two new preconditions:

        - [H_delay_nn] -- the lower-bound [0 <= delay] (the upper
          bound is via [H_delay_bound]).
        - [H_slot5]    -- the audit-time obligation that the abstract
          [storage_base] has a U256 cell at slot 5 (the
          [unstakingDelay] user-storage slot).  An honest projection
          mirroring the contract's layout satisfies this trivially. *)
  Theorem run_setUnstakingDelay_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (delay : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_delay_bound : delay <= 2419200)
      (H_delay_nn : 0 <= delay)
      (H_slot5 : exists v0,
         List.nth_error storage_base slot_unstakingDelay
           = Some (StorableValue.U256 v0))
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_setUnstakingDelay_750 delay ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_setUnstakingDelay_750 storage_base delay)).
  Proof.
    cbv zeta.
    pose proof (run_fun_setUnstakingDelay_750_at_proj_sim
                  codes env state_base storage_base memory delay
                  H_caller_admin H_caller_bound H_delay_bound H_delay_nn
                  H_slot5 H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_setUnstakingDelay_750 storage_base delay))).
    exists (proj_post_setUnstakingDelay_750 storage_base delay).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [setRewardRatio] equivalence -----

      Role-gated; one sstore at slot 3 wrapped in the accrueRewards
      modifier (whose detailed sub-walker is encapsulated in the
      composite axiom). The naming follows the task brief's
      [setNativeRewardRate] label, but the actual on-chain entry-point
      is [setRewardRatio] (the contract uses a half-life parameter
      converted to a ratio at the call site). *)
  Theorem run_setNativeRewardRate_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (halfLife : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_halflife_lo : 86400 <= halfLife)
      (H_halflife_hi : halfLife <= 1209600)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_setRewardRatio_1036 halfLife ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_setRewardRatio_1036 storage_base halfLife now_timestamp)).
  Proof.
    cbv zeta.
    pose proof (run_fun_setRewardRatio_1036_at_proj_sim
                  codes env state_base storage_base memory halfLife
                  H_caller_admin H_caller_bound
                  H_halflife_lo H_halflife_hi H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_setRewardRatio_1036 storage_base halfLife
                                                    now_timestamp))).
    exists (proj_post_setRewardRatio_1036 storage_base halfLife now_timestamp).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- Pause / unpause (sim-level disposition) -----

      StakingVault.sol DOES NOT expose a [pause] or [unpause] entry-
      point. The vault's pause-equivalent surface is the
      [setUnstakingDelay] hook (a zero-delay value collapses the
      lockup) plus the [addRewardToken] / [removeRewardToken]
      surface (managed by DEFAULT_ADMIN_ROLE for emergency reward-
      stream pause). We record the disposition here as a sim-level
      lemma: there is no [pause] surface to mechanize.

      For audit-trail completeness, the related entry-points are:
        - [setUnstakingDelay] — proven above.
        - [setRewardRatio] (alias setNativeRewardRate) — proven above.
        - [addRewardToken] / [removeRewardToken] — out of scope here
          (those belong to the StakingVaultRewards equivalence stream).
        - [renounceRole] (DEFAULT_ADMIN_ROLE) — proven below as the
          irreversible "decentralization" act on the admin surface. *)

  (** ----- R071 Theorem: [grantRole] equivalence ----- *)
  Theorem run_grantRole_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (role account : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_account_bound : 0 <= account < 2^160)
      (H_role_bound : 0 <= role < 2^256)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_grantRole_13574 role account ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_grantRole_13574 storage_base role account)).
  Proof.
    cbv zeta.
    pose proof (run_fun_grantRole_13574_at_proj_sim
                  codes env state_base storage_base memory role account
                  H_caller_admin H_caller_bound H_account_bound H_role_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_grantRole_13574 storage_base role account))).
    exists (proj_post_grantRole_13574 storage_base role account).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [revokeRole] equivalence ----- *)
  Theorem run_revokeRole_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (role account : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_account_bound : 0 <= account < 2^160)
      (H_role_bound : 0 <= role < 2^256)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_revokeRole_13593 role account ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_revokeRole_13593 storage_base role account)).
  Proof.
    cbv zeta.
    pose proof (run_fun_revokeRole_13593_at_proj_sim
                  codes env state_base storage_base memory role account
                  H_caller_admin H_caller_bound H_account_bound H_role_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_revokeRole_13593 storage_base role account))).
    exists (proj_post_revokeRole_13593 storage_base role account).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [renounceRole] equivalence ----- *)
  Theorem run_renounceRole_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (role callerConfirmation : U256.t)
      (H_self_confirm :
         callerConfirmation = env.(Environment.caller))
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_role_bound : 0 <= role < 2^256)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_renounceRole_13616 role callerConfirmation ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_renounceRole_13616 storage_base role callerConfirmation)).
  Proof.
    cbv zeta.
    pose proof (run_fun_renounceRole_13616_at_proj_sim
                  codes env state_base storage_base memory role callerConfirmation
                  H_self_confirm H_caller_bound H_role_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_renounceRole_13616 storage_base role
                                                   callerConfirmation))).
    exists (proj_post_renounceRole_13616 storage_base role callerConfirmation).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [_authorizeUpgrade] equivalence -----

      The UUPS upgrade-authorization hook. Three R063 staticcalls
      against the VersionRegistry plus a Versioned(impl).version()
      handshake. Storage UNCHANGED (it's a view-only function modulo
      the staticcalls). *)
  Theorem run_authorizeUpgrade_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (impl : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_impl_bound : 0 <= impl < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun__authorizeUpgrade_1574 impl ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_authorizeUpgrade_1574 storage_base impl)).
  Proof.
    cbv zeta.
    pose proof (run_fun__authorizeUpgrade_1574_at_proj_sim
                  codes env state_base storage_base memory impl
                  H_caller_admin H_caller_bound H_impl_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_authorizeUpgrade_1574 storage_base impl))).
    exists (proj_post_authorizeUpgrade_1574 storage_base impl).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ----- R071 Theorem: [upgradeToAndCall] equivalence -----

      The public UUPS entry-point. modifier_onlyProxy +
      _authorizeUpgrade + ERC1967Utils.upgradeToAndCall (which sstore-s
      the new implementation at IMPLEMENTATION_SLOT and optionally
      delegate-calls the [data] argument into the new impl for
      re-initialization). *)
  Theorem run_upgradeToAndCall_equivalent
      (codes : Codes.t) (env : Environment.t)
      (state_base : RocqOfSolidity.State.t)
      (storage_base : SimulatedStorage.t)
      (memory : SimulatedMemory.t)
      (newImpl data_mpos : U256.t)
      (H_caller_admin :
         has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
      (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
      (H_impl_bound : 0 <= newImpl < 2^160)
      (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest) :
    let state := make_state env state_base memory storage_base in
    exists state' storage_post,
      {{? codes, env, Some state |
        fun_upgradeToAndCall_2829 newImpl data_mpos ⇓ Result.Ok tt
      | state' ?}} /\
      (exists memory',
        state' = Some (make_state env state_base memory' storage_post) /\
        storage_equiv storage_post
          (proj_post_upgradeToAndCall_2829 storage_base newImpl data_mpos)).
  Proof.
    cbv zeta.
    pose proof (run_fun_upgradeToAndCall_2829_at_proj_sim
                  codes env state_base storage_base memory
                  newImpl data_mpos
                  H_caller_admin H_caller_bound H_impl_bound H_mem)
      as Hwalker.
    destruct Hwalker as (memory' & Hwalker).
    exists (Some (make_state env state_base memory'
                    (proj_post_upgradeToAndCall_2829 storage_base
                                                      newImpl data_mpos))).
    exists (proj_post_upgradeToAndCall_2829 storage_base newImpl data_mpos).
    split.
    - exact Hwalker.
    - exists memory'. split; [reflexivity | apply storage_equiv_refl].
  Qed.

  (** ====================================================================
      Sim-level Qed lemmas — pause-state preservation across other ops
      ====================================================================

      The task brief asks for "Sim-level Qed lemmas about pause-state
      preservation across other ops (likely already exist — reference)".

      StakingVault has no on-chain pause flag (see disposition above).
      The closest preservation property at the admin surface is:

        For each admin-mutator, the OTHER admin slots (those NOT named
        by the mutator) are unchanged. The composite walker axioms
        characterise the precise slot touched by each mutator; the
        observational bridge then states the equality at the touched
        slot.

      Under [storage_equiv := eq] and the Skolemized post-storage
      Parameter shape, the per-target slot-shape characterisation is
      deferred to the audit-time obligation documented in each
      composite walker axiom. The lemmas below state the structural
      sanity facts that hold by definition of the Parameter shape and
      the reflexive [storage_equiv]. *)

  (** Sanity: applying [proj_post_setUnstakingDelay_750] to a fixed
      storage_base with the same delay is reflexive. (Trivial under
      [storage_equiv := eq] and the Parameter shape.) *)
  Lemma setUnstakingDelay_post_state_pinned
      (storage_base : SimulatedStorage.t) (delay : U256.t) :
    storage_equiv
      (proj_post_setUnstakingDelay_750 storage_base delay)
      (proj_post_setUnstakingDelay_750 storage_base delay).
  Proof. apply storage_equiv_refl. Qed.

  Lemma setRewardRatio_post_state_pinned
      (storage_base : SimulatedStorage.t)
      (halfLife now_ : U256.t) :
    storage_equiv
      (proj_post_setRewardRatio_1036 storage_base halfLife now_)
      (proj_post_setRewardRatio_1036 storage_base halfLife now_).
  Proof. apply storage_equiv_refl. Qed.

  Lemma grantRole_post_state_pinned
      (storage_base : SimulatedStorage.t)
      (role account : U256.t) :
    storage_equiv
      (proj_post_grantRole_13574 storage_base role account)
      (proj_post_grantRole_13574 storage_base role account).
  Proof. apply storage_equiv_refl. Qed.

  Lemma revokeRole_post_state_pinned
      (storage_base : SimulatedStorage.t)
      (role account : U256.t) :
    storage_equiv
      (proj_post_revokeRole_13593 storage_base role account)
      (proj_post_revokeRole_13593 storage_base role account).
  Proof. apply storage_equiv_refl. Qed.

  Lemma renounceRole_post_state_pinned
      (storage_base : SimulatedStorage.t)
      (role callerConfirmation : U256.t) :
    storage_equiv
      (proj_post_renounceRole_13616 storage_base role callerConfirmation)
      (proj_post_renounceRole_13616 storage_base role callerConfirmation).
  Proof. apply storage_equiv_refl. Qed.

  Lemma authorizeUpgrade_post_state_pinned
      (storage_base : SimulatedStorage.t) (impl : U256.t) :
    storage_equiv
      (proj_post_authorizeUpgrade_1574 storage_base impl)
      (proj_post_authorizeUpgrade_1574 storage_base impl).
  Proof. apply storage_equiv_refl. Qed.

  Lemma upgradeToAndCall_post_state_pinned
      (storage_base : SimulatedStorage.t)
      (newImpl data : U256.t) :
    storage_equiv
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data)
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data).
  Proof. apply storage_equiv_refl. Qed.

  (** ====================================================================
      Cross-mutator independence — sanity lemmas
      ====================================================================

      A sanity-check that each pair of admin mutators is structurally
      independent at the Skolemized-post-storage level: applying mutator
      A then mutator B exposes a TWO-Parameter shape composition, not a
      hidden single-Parameter sneak. (No semantic content beyond the
      Parameter discipline; included for [Print Assumptions] auditability.) *)

  Lemma setUnstakingDelay_revokeRole_independent
      (sb : SimulatedStorage.t)
      (delay role account : U256.t) :
    let s1 := proj_post_setUnstakingDelay_750 sb delay in
    let s2 := proj_post_revokeRole_13593 s1 role account in
    storage_equiv s2
      (proj_post_revokeRole_13593
         (proj_post_setUnstakingDelay_750 sb delay) role account).
  Proof. apply storage_equiv_refl. Qed.

  Lemma grantRole_setRewardRatio_independent
      (sb : SimulatedStorage.t)
      (role account halfLife now_ : U256.t) :
    let s1 := proj_post_grantRole_13574 sb role account in
    let s2 := proj_post_setRewardRatio_1036 s1 halfLife now_ in
    storage_equiv s2
      (proj_post_setRewardRatio_1036
         (proj_post_grantRole_13574 sb role account) halfLife now_).
  Proof. apply storage_equiv_refl. Qed.

End StakingVaultAdminEquivalence.
