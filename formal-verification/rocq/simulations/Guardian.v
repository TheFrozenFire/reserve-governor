(** Guardian simulation.

    Mirrors contracts/Guardian.sol — a singleton
    AccessControlEnumerable contract that acts as CANCELLER_ROLE for
    all optimistic governors and routes role management to those
    governors' timelocks.

    Three roles partition the privileges:

      DEFAULT_ADMIN_ROLE
        - admin of every other role
        - can cancel ANY proposal via [cancel] (no optimistic/defeated
          check)
        - can call [revokeOptimisticProposer] on a managed governor's
          timelock

      OPTIMISTIC_GUARDIAN_ROLE
        - can call [cancel] ONLY when:
            * governor.isOptimistic(pid) = true
            * governor.state(pid) != IGovernor.ProposalState.Defeated
        - has no role-management powers

      OPTIMISTIC_GUARDIAN_MANAGER_ROLE
        - can grant OPTIMISTIC_GUARDIAN_ROLE via
          [grantOptimisticGuardian] to a non-zero account
        - cannot cancel, cannot revoke

    Modeling abstractions:

    * Each role is modeled as a [list Address] of role-holders. The
      OZ AccessControlEnumerable mapping {role -> EnumerableSet<address>}
      is collapsed to one list per role; uniqueness is captured by the
      [Valid.state] invariant.

    * External calls into the Governor and Timelock are treated as
      oracles:
        - [is_optimistic_oracle : ProposalId -> bool]
        - [proposal_state_oracle : ProposalId -> ProposalState]
        - [governor_timelock_oracle : Address -> Address]
        - [getProposalId_oracle : ProposalKey -> ProposalId]
        - [has_code : Address -> bool]
      These appear as explicit arguments rather than [Parameter]s so
      the simulation is total and composes cleanly with [vm_compute]
      cross-checks. Injectivity of [getProposalId_oracle] (keccak
      collision resistance) is captured in the proof file when needed.

    * The actual [managedGovernor.cancel(...)] call returns the
      proposalId. The simulation records this as a [Cancelled] event
      so the proof layer can talk about "the cancel was performed"
      without modeling the downstream governor mutation.

    * Reverts use the two-constructor Result pattern shared with the
      other simulations in this tree; Yul revert offsets are
      placeholders pinned during the (still-pending) Yul-equivalence
      proof.

    Revert coverage modeled:
      - [revert_unauthorized]     caller has neither admin nor
                                  guardian role on [cancel].
      - [revert_zero_address]     [_requireNonZero] caught a zero
                                  address on [grantOptimisticGuardian].
      - [revert_not_optimistic]   guardian-only caller on a proposal
                                  that is not optimistic.
      - [revert_defeated]         guardian-only caller on a Defeated
                                  optimistic proposal.
      - [revert_invalid_governor] zero address or no-code governor
                                  observed by [_governor].
      - [revert_invalid_timelock] zero address or no-code timelock
                                  observed by [_timelock].
      - [revert_missing_manager]  caller lacks
                                  OPTIMISTIC_GUARDIAN_MANAGER_ROLE on
                                  [grantOptimisticGuardian].
      - [revert_missing_admin]    caller lacks DEFAULT_ADMIN_ROLE on
                                  [revokeOptimisticProposer].

    Not modeled (deliberately):
      - The full DEFAULT_ADMIN_ROLE -> per-role admin-of-admin chain.
        OZ AccessControl's [_setRoleAdmin] is not invoked by Guardian;
        the contract uses the default linkage where DEFAULT_ADMIN_ROLE
        admins every role.
      - The enumerable index. AccessControlEnumerable exposes
        [getRoleMember(role, index)] which the contract itself does
        not call; we only need set membership semantics.
      - The keccak hash inside [getProposalId]. We pass the oracle a
        product type [ProposalKey] standing in for (targets, values,
        calldatas, descriptionHash) and never inspect its internals.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module Guardian.

Definition Address    : Set := U256.t.
Definition ProposalId : Set := U256.t.

(** OpenZeppelin IGovernor.ProposalState — the variants Guardian
    actually distinguishes are [Defeated] (rejection by guardian) and
    everything else. We carry an explicit constructor for each named
    state so the [observe]-style proofs can match precisely. *)
Inductive ProposalState : Set :=
| PSPending
| PSActive
| PSCanceled
| PSDefeated
| PSSucceeded
| PSQueued
| PSExpired
| PSExecuted.

(** ProposalKey is a placeholder product. Each component is a
    [list U256.t] standing in for the abi-encoded payload bytes;
    the simulation never inspects the contents. *)
Module ProposalKey.
  Record t : Set := {
    targets       : list Address;
    values        : list U256.t;
    calldatas     : list (list U256.t);
    descHash      : U256.t;
  }.
End ProposalKey.

(** ===== Guardian state =====

    Three sets of role-holders. Each set is a list of addresses; the
    [Valid.state] invariant enforces no-duplicates and the absence of
    the zero address. *)
Module State.
  Record t : Set := {
    admins                       : list Address;
    optimisticGuardians          : list Address;
    optimisticGuardianManagers   : list Address;
  }.
End State.

(** ===== Result ===== *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert  {_}.
End Result.

Definition revert_unauthorized     {A : Set} : Result.t A := Result.Revert 0   32.
Definition revert_zero_address     {A : Set} : Result.t A := Result.Revert 32  32.
Definition revert_not_optimistic   {A : Set} : Result.t A := Result.Revert 64  32.
Definition revert_defeated         {A : Set} : Result.t A := Result.Revert 96  32.
Definition revert_invalid_governor {A : Set} : Result.t A := Result.Revert 128 32.
Definition revert_invalid_timelock {A : Set} : Result.t A := Result.Revert 160 32.
Definition revert_missing_manager  {A : Set} : Result.t A := Result.Revert 192 32.
Definition revert_missing_admin    {A : Set} : Result.t A := Result.Revert 224 32.

(** ===== Membership helpers ===== *)
Fixpoint addr_in (lst : list Address) (a : Address) : bool :=
  match lst with
  | []     => false
  | h :: t => if h =? a then true else addr_in t a
  end.

Definition has_admin (s : State.t) (a : Address) : bool :=
  addr_in s.(State.admins) a.

Definition has_guardian (s : State.t) (a : Address) : bool :=
  addr_in s.(State.optimisticGuardians) a.

Definition has_manager (s : State.t) (a : Address) : bool :=
  addr_in s.(State.optimisticGuardianManagers) a.

(** Add [a] to the role set [lst] if not already present, mirroring
    OZ's _grantRole semantics (idempotent on existing members). *)
Definition add_role (lst : list Address) (a : Address) : list Address :=
  if addr_in lst a then lst else a :: lst.

(** ===== _requireNonZero ===== *)
Definition require_non_zero (a : Address) : Result.t Address :=
  if a =? 0 then revert_zero_address else Result.Success a.

(** ===== grantOptimisticGuardian =====

    Source: contracts/Guardian.sol#L61-L63.

    Gate: caller must hold OPTIMISTIC_GUARDIAN_MANAGER_ROLE.
    Then _requireNonZero(account) and _grantRole(GUARDIAN, account). *)
Definition grantOptimisticGuardian
    (s : State.t) (caller : Address) (account : Address)
    : Result.t State.t :=
  if negb (has_manager s caller) then revert_missing_manager
  else if account =? 0 then revert_zero_address
  else
    Result.Success {|
      State.admins                     := s.(State.admins);
      State.optimisticGuardians        := add_role s.(State.optimisticGuardians) account;
      State.optimisticGuardianManagers := s.(State.optimisticGuardianManagers);
    |}.

(** ===== revokeOptimisticProposer =====

    Source: contracts/Guardian.sol#L66-L68.

    Gate: caller must hold DEFAULT_ADMIN_ROLE.
    Side effect: routes through [_timelock(governor)] which checks
    [governor != 0 && governor.code.length != 0] and
    [timelock != 0 && timelock.code.length != 0], then invokes
    [ITimelockControllerOptimistic.revokeOptimisticProposer(account)].

    The simulation records the call as an event (timelock_addr,
    account) so the proof layer can talk about "the revoke was
    dispatched to [timelock_addr]" without modeling the timelock's
    internal state. *)
Module RevokeEvent.
  Record t : Set := {
    timelock : Address;
    account  : Address;
  }.
End RevokeEvent.

Definition revokeOptimisticProposer
    (s : State.t)
    (governor_timelock_oracle : Address -> Address)
    (has_code : Address -> bool)
    (caller : Address) (governor : Address) (account : Address)
    : Result.t RevokeEvent.t :=
  if negb (has_admin s caller) then revert_missing_admin
  else if governor =? 0 then revert_invalid_governor
  else if negb (has_code governor) then revert_invalid_governor
  else
    let tl := governor_timelock_oracle governor in
    if tl =? 0 then revert_invalid_timelock
    else if negb (has_code tl) then revert_invalid_timelock
    else Result.Success {|
      RevokeEvent.timelock := tl;
      RevokeEvent.account  := account;
    |}.

(** ===== cancel =====

    Source: contracts/Guardian.sol#L72-L97.

    Two-tier authorization:
      isAdmin = hasRole(DEFAULT_ADMIN_ROLE, caller)
      if !isAdmin && !hasRole(GUARDIAN, caller): revert unauthorized
      managedGovernor = _governor(governor)
      pid = governor.getProposalId(targets, values, calldatas, descHash)
      if !isAdmin:
        require(managedGovernor.isOptimistic(pid))    : not_optimistic
        require(state(pid) != Defeated)               : defeated
      return managedGovernor.cancel(...)

    The simulation produces a [CancelEvent.t] when the gate passes —
    capturing the proposalId derived from the inputs and the governor
    address — so the proof layer can talk about "cancel was
    dispatched on [pid]" without modeling the governor's downstream
    state mutation. *)
Module CancelEvent.
  Record t : Set := {
    governor   : Address;
    proposalId : ProposalId;
  }.
End CancelEvent.

Definition cancel
    (s : State.t)
    (is_optimistic_oracle  : ProposalId -> bool)
    (proposal_state_oracle : ProposalId -> ProposalState)
    (getProposalId_oracle  : ProposalKey.t -> ProposalId)
    (has_code              : Address -> bool)
    (caller : Address) (governor : Address) (key : ProposalKey.t)
    : Result.t CancelEvent.t :=
  let isAdmin    := has_admin s caller in
  let isGuardian := has_guardian s caller in
  if negb (isAdmin || isGuardian) then revert_unauthorized
  else if governor =? 0 then revert_invalid_governor
  else if negb (has_code governor) then revert_invalid_governor
  else
    let pid := getProposalId_oracle key in
    if isAdmin then
      Result.Success {|
        CancelEvent.governor   := governor;
        CancelEvent.proposalId := pid;
      |}
    else
      (* guardian-only gate *)
      if negb (is_optimistic_oracle pid) then revert_not_optimistic
      else
        match proposal_state_oracle pid with
        | PSDefeated => revert_defeated
        | _ =>
            Result.Success {|
              CancelEvent.governor   := governor;
              CancelEvent.proposalId := pid;
            |}
        end.

(** ===== Validity =====

    Storage invariants:
      - every role set is duplicate-free
      - no role set contains the zero address
        (the only ingress is _grantRole, always preceded by
         _requireNonZero for OPTIMISTIC_GUARDIAN, and the constructor
         enforces it for the seed admin / manager / guardians; the
         simulation models a state with role sets that already satisfy
         this invariant)
      - every address in every role set is a valid U256.t. *)
Module Valid.
  Definition no_dup_admins (s : State.t) : Prop :=
    NoDup s.(State.admins).
  Definition no_dup_guardians (s : State.t) : Prop :=
    NoDup s.(State.optimisticGuardians).
  Definition no_dup_managers (s : State.t) : Prop :=
    NoDup s.(State.optimisticGuardianManagers).

  Definition no_zero_admins (s : State.t) : Prop :=
    Forall (fun a => a <> 0) s.(State.admins).
  Definition no_zero_guardians (s : State.t) : Prop :=
    Forall (fun a => a <> 0) s.(State.optimisticGuardians).
  Definition no_zero_managers (s : State.t) : Prop :=
    Forall (fun a => a <> 0) s.(State.optimisticGuardianManagers).

  Record state (s : State.t) : Prop := {
    admins_nd      : no_dup_admins s;
    guardians_nd   : no_dup_guardians s;
    managers_nd    : no_dup_managers s;
    admins_nz      : no_zero_admins s;
    guardians_nz   : no_zero_guardians s;
    managers_nz    : no_zero_managers s;
  }.
End Valid.

End Guardian.
