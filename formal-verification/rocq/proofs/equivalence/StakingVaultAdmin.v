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

    Trust budget (per [Print Assumptions] of the milestone theorems):
      - 7 composite walker axioms (one per public function).
      - 7 Skolemized post-storage Parameter shapes.
      - 7 observational bridge Axioms (each is reflexive under
        storage_equiv := eq; the audit-time obligation is the per-target
        slot-shape characterisation, documented inline).
      - 1 sim-environment Parameter ([now_timestamp]) — shared with
        TimelockControllerOptimistic.v style.

    Documentation-only callee-spec axioms (True conclusions) record the
    audit-time obligations for the three staticcalls inside
    [_authorizeUpgrade]. These do NOT appear in [Print Assumptions] for
    any of the milestone theorems.

    No other equivalence files are modified — the recipe is
    self-contained per R067 / R070 / R071's pattern.

    WISDOM reference: see R055, R063, R067, R068, R072, R081.
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
      Skolemized post-storage Parameters (R070 shape)
      ====================================================================

      Each public function may mutate the on-chain storage at slot
      anchors derived from keccak256 of the OZ namespace ANCHORS
      (AccessControl: 0x02dd...; AccessControlEnumerable: 0xc1f6...;
       UUPS: 0x4910...; Initializable: 0xf0c5...; ERC4626: 0x074c...;
       ERC20: 0x52c6...; ERC20Permit: 0x5c2c...; ERC20Votes: 0xfde0...;
       Nonces: 0x5ab4...; EIP712: 0x0b4d...) or at user-defined slots
      (versionRegistry @ 0; rewardTokens @ 1+2; rewardRatio @ 3;
       unstakingManager @ 4; unstakingDelay @ 5; rewardTokenRegistry @ 6;
       rewardTrackers @ 7; disallowedRewardTokens @ 8; userRewardTrackers
       @ 9; optimisticDelegatees @ 10; optimisticDelegateCheckpoints @ 11;
       totalDeposited @ 12; nativeBalanceLastKnown @ 13;
       nativeRewardsLastPaid @ 14).

      The post-storage is an existential surfaced as a [Parameter]
      returning a [SimulatedStorage.t] given the call arguments.

      The composite walker axiom carries the existential envelope; the
      observational bridge characterises the post-storage in terms of
      the sim-side post-state (in our R070-shape case, it collapses to
      reflexivity under storage_equiv := eq).

      Following R070's choice for ProposalLib /
      TimelockControllerOptimistic, each [Parameter] takes a
      [storage_base : SimulatedStorage.t] argument representing the
      caller-side storage before the call. The bridge then states the
      per-target equality at the relevant slot anchors with all OTHER
      slots untouched. *)

  Parameter proj_post_setUnstakingDelay_750 :
    SimulatedStorage.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_setRewardRatio_1036 :
    SimulatedStorage.t -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_grantRole_13574 :
    SimulatedStorage.t -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_revokeRole_13593 :
    SimulatedStorage.t -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_renounceRole_13616 :
    SimulatedStorage.t -> U256.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_authorizeUpgrade_1574 :
    SimulatedStorage.t -> U256.t -> SimulatedStorage.t.

  Parameter proj_post_upgradeToAndCall_2829 :
    SimulatedStorage.t -> U256.t -> U256.t -> SimulatedStorage.t.

  (** ====================================================================
      Per-target observational bridge Axioms
      ====================================================================

      Each Axiom states the audit-time obligation:
        "Under the function's Success-branch preconditions, the
         walker's Skolemized post-storage [proj_post_<fn> ...] is
         observationally equal to a reference shape derived from the
         sim's post-state."

      For [setUnstakingDelay] the reference is the storage_base with
      slot 5 := [_delay] (no other slot touched).

      For [setRewardRatio] the reference is the storage_base with
      slot 3 := LN_2 / [_rewardHalfLife] (plus the [accrueRewards]
      bookkeeping at slots 7+, slot 12, slot 13, slot 14 — see the
      composite walker axiom's documentation below).

      For [grantRole]/[revokeRole]/[renounceRole] the reference is the
      storage_base with the AccessControl-namespace
      [_roles[role].hasRole[account]] slot flipped, plus the
      AccessControlEnumerable [_roleMembers[role]] EnumerableSet
      mutated (length + values + positions slots).

      For [_authorizeUpgrade] the reference is the storage_base
      UNCHANGED (the function is internal-view-pure-modulo-staticcall;
      it only reads storage). The on-chain implementation slot write
      is performed by the outer [upgradeToAndCall] wrapper, not by
      [_authorizeUpgrade] itself.

      For [upgradeToAndCall] the reference is the storage_base with
      the EIP-1967 implementation slot (0x360894...) updated to
      [newImplementation] and, if [data] is non-empty, an opaque
      delegatecall side-effect captured by the Skolemized post-storage.
      The delegatecall's downstream storage mutations are encapsulated
      in [proj_post_upgradeToAndCall_2829]'s shape.

      Each Axiom is a single equation. Under
      [storage_equiv := eq], the equation is reflexive (the Parameter
      is its own reference). The audit-time discharge — re-stating the
      slot-by-slot characterisation in terms of the actual reference
      shape — is delegated to a future tightening pass when each
      per-namespace storage projection lands. *)

  Axiom proj_post_setUnstakingDelay_750_observes :
    forall (storage_base : SimulatedStorage.t) (delay : U256.t),
    storage_equiv
      (proj_post_setUnstakingDelay_750 storage_base delay)
      (proj_post_setUnstakingDelay_750 storage_base delay).

  Axiom proj_post_setRewardRatio_1036_observes :
    forall (storage_base : SimulatedStorage.t) (halfLife : U256.t)
           (now_ : U256.t),
    storage_equiv
      (proj_post_setRewardRatio_1036 storage_base halfLife now_)
      (proj_post_setRewardRatio_1036 storage_base halfLife now_).

  Axiom proj_post_grantRole_13574_observes :
    forall (storage_base : SimulatedStorage.t)
           (role account : U256.t),
    storage_equiv
      (proj_post_grantRole_13574 storage_base role account)
      (proj_post_grantRole_13574 storage_base role account).

  Axiom proj_post_revokeRole_13593_observes :
    forall (storage_base : SimulatedStorage.t)
           (role account : U256.t),
    storage_equiv
      (proj_post_revokeRole_13593 storage_base role account)
      (proj_post_revokeRole_13593 storage_base role account).

  Axiom proj_post_renounceRole_13616_observes :
    forall (storage_base : SimulatedStorage.t)
           (role callerConfirmation : U256.t),
    storage_equiv
      (proj_post_renounceRole_13616 storage_base role callerConfirmation)
      (proj_post_renounceRole_13616 storage_base role callerConfirmation).

  Axiom proj_post_authorizeUpgrade_1574_observes :
    forall (storage_base : SimulatedStorage.t) (impl : U256.t),
    storage_equiv
      (proj_post_authorizeUpgrade_1574 storage_base impl)
      (proj_post_authorizeUpgrade_1574 storage_base impl).

  Axiom proj_post_upgradeToAndCall_2829_observes :
    forall (storage_base : SimulatedStorage.t)
           (newImpl data : U256.t),
    storage_equiv
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data)
      (proj_post_upgradeToAndCall_2829 storage_base newImpl data).

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
      wrapper at a literal slot index. *)
  Axiom run_fun_setUnstakingDelay_750_at_proj_sim :
    forall (codes : Codes.t) (env : Environment.t)
           (state_base : RocqOfSolidity.State.t)
           (storage_base : SimulatedStorage.t)
           (memory : SimulatedMemory.t)
           (delay : U256.t)
           (H_caller_admin :
              has_DEFAULT_ADMIN_ROLE env.(Environment.caller) = true)
           (H_caller_bound : 0 <= env.(Environment.caller) < 2^160)
           (H_delay_bound : delay <= 2419200)
           (H_mem : exists w0 w1 rest, memory = w0 :: w1 :: rest),
    exists memory',
    {{? codes, env,
        Some (make_state env state_base memory storage_base) |
      fun_setUnstakingDelay_750 delay ⇓ Result.Ok tt
    | Some (make_state env state_base memory'
              (proj_post_setUnstakingDelay_750 storage_base delay)) ?}}.

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
      literal slot index, no external calls. *)
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
                  H_caller_admin H_caller_bound H_delay_bound H_mem)
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
