(** ReserveOptimisticGovernanceVersionRegistry simulation.

    Mirrors contracts/VersionRegistry.sol — an append-only registry of
    ReserveOptimisticGovernorDeployer instances, keyed by
    [keccak256(abi.encodePacked(version_string))]. Each deployer carries
    a fixed triple of implementation addresses

      (stakingVaultImpl, governorImpl, timelockImpl)

    plus a sticky [isDeprecated] flag set by a separate role
    (owner-or-emergency-council). The registry is consulted by
    [StakingVault._authorizeUpgrade] to gate upgrades: only the latest
    non-deprecated version's stakingVaultImpl may be installed.

    Modeled production surface:
      registerVersion(deployer)               — onlyOwner; appends.
      deprecateVersion(versionHash)           — onlyOwnerOrEmergency.
      getLatestVersion() view                 — returns (hash, version,
                                                deployer, deprecated).
      getImplementationsForVersion(hash) view — returns the impl triple.

    Modeling abstractions:
      - The contract stores [string version] indirectly (via
        [Versioned(deployer).version()]) and computes its keccak hash
        at registration time. We model this by an opaque
        [Version : Set] type and an abstract injective
        [version_hash : Version -> U256.t]. The bytes of the keccak
        output are irrelevant to the registry's behavior — the only
        load-bearing property is hash injectivity over the corpus of
        version strings that have actually been registered. We capture
        this with a [Parameter] + [Axiom] (mirroring the abstract
        treatment of forbidden-target equality in SelectorRegistry).

      - Implementation addresses are opaque [U256.t] values stored at
        registration time. The registry only ever compares them by
        equality and returns them in a triple; their internal structure
        is irrelevant.

      - Role authorization is modeled as two abstract boolean
        predicates on caller addresses:
          [is_owner(caller)]
          [is_owner_or_emergency(caller)]
        with the natural inclusion
          is_owner caller = true -> is_owner_or_emergency caller = true.
        These are [Parameter]s — the concrete role registry lives in
        RoleRegistry.sol and is out of scope. What matters here is
        that mutations are gated on these predicates.

    Revert coverage:
      revert_invalid_caller       — caller fails role check.
      revert_zero_address         — deployer address is zero.
      revert_invalid_registration — versionHash already registered.
      revert_already_deprecated   — versionHash already deprecated.
      revert_not_configured       — getLatestVersion before any register.

    Not modeled here (production-side, out of scope):
      - The Versioned(deployer).version() string read itself; we
        operate at the (already-hashed) versionHash + Version pair.
      - The on-chain emitted events (VersionRegistered, VersionDeprecated).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module VersionRegistry.

(** Opaque address — equality is the only operation the registry uses. *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** Opaque version-string type. The keccak256 output of the actual
    string is what the registry stores; the bytes of the hash are not
    modeled. We assume injectivity over the registered corpus, which
    matches the real-world cryptographic property of keccak256 with
    overwhelming probability and is the only property that matters
    for the contract's behavior. *)
Parameter Version : Set.
Parameter version_hash : Version -> U256.t.

(** Hash injectivity. We don't model keccak — we *assume* the property
    that's load-bearing for the registry: distinct version strings
    yield distinct hashes. *)
Axiom version_hash_injective :
  forall v1 v2, version_hash v1 = version_hash v2 -> v1 = v2.

(** Role-authorization predicates. Owner is a strict subset of
    owner-or-emergency-council. *)
Parameter is_owner               : Address -> bool.
Parameter is_owner_or_emergency  : Address -> bool.

Axiom owner_implies_owner_or_emergency :
  forall caller,
    is_owner caller = true ->
    is_owner_or_emergency caller = true.

(** A single registered version entry. The deployer address is opaque;
    we record the impl triple at registration time so subsequent
    [getImplementationsForVersion] calls return the exact triple the
    contract recorded. *)
Module VersionEntry.
  Record t : Set := {
    versionHash      : U256.t;
    version          : Version;     (** for getLatestVersion's view *)
    deployer         : Address;     (** non-zero on register *)
    stakingVaultImpl : Address;
    governorImpl     : Address;
    timelockImpl     : Address;
    deprecated       : bool;        (** sticky once set *)
  }.
End VersionEntry.

(** Registry state. [history] is the append-only list of entries in
    registration order; [latest_index] is [Some i] when there's at
    least one registered version (always [length history - 1], by
    construction), and [None] before the first register. *)
Module State.
  Record t : Set := {
    history      : list VersionEntry.t;
    latest_index : option nat;   (** None iff history = [] *)
  }.
End State.

Definition empty_state : State.t := {|
  State.history      := [];
  State.latest_index := None;
|}.

(** Two-constructor result mirroring the rest of the FV tree. The
    [(p s)] fields are placeholders; Yul revert offsets get pinned
    during equivalence. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert  {_}.
End Result.

Definition revert_invalid_caller        {A : Set} : Result.t A := Result.Revert  0 32.
Definition revert_zero_address          {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_invalid_registration  {A : Set} : Result.t A := Result.Revert 64 32.
Definition revert_already_deprecated    {A : Set} : Result.t A := Result.Revert 96 32.
Definition revert_not_configured        {A : Set} : Result.t A := Result.Revert 128 32.

(** ----- Helpers ----- *)

(** Find the entry with the given hash. Returns the list index plus
    the entry, or [None]. We carry the index so [deprecateVersion] can
    update in place. *)
Fixpoint find_entry_idx
    (hist : list VersionEntry.t) (h : U256.t) (i : nat) : option (nat * VersionEntry.t) :=
  match hist with
  | [] => None
  | e :: rest =>
      if e.(VersionEntry.versionHash) =? h
      then Some (i, e)
      else find_entry_idx rest h (S i)
  end.

Definition find_entry (s : State.t) (h : U256.t) : option (nat * VersionEntry.t) :=
  find_entry_idx s.(State.history) h 0.

(** Lookup without index — used by view functions. *)
Definition entry_for_hash (s : State.t) (h : U256.t) : option VersionEntry.t :=
  match find_entry s h with
  | Some (_, e) => Some e
  | None => None
  end.

(** In-place set at index — used by deprecateVersion. Out-of-bounds
    leaves the list unchanged (won't happen in valid flows). *)
Fixpoint set_nth {A : Type} (n : nat) (a : A) (xs : list A) : list A :=
  match xs, n with
  | [], _ => []
  | _ :: rest, O => a :: rest
  | x :: rest, S k => x :: set_nth k a rest
  end.

(** Mark the entry at [i] as deprecated. *)
Definition deprecate_at (s : State.t) (i : nat) : State.t :=
  match nth_error s.(State.history) i with
  | None => s   (** unreachable in valid flows; kept total *)
  | Some e =>
      let e' := {|
        VersionEntry.versionHash      := e.(VersionEntry.versionHash);
        VersionEntry.version          := e.(VersionEntry.version);
        VersionEntry.deployer         := e.(VersionEntry.deployer);
        VersionEntry.stakingVaultImpl := e.(VersionEntry.stakingVaultImpl);
        VersionEntry.governorImpl     := e.(VersionEntry.governorImpl);
        VersionEntry.timelockImpl     := e.(VersionEntry.timelockImpl);
        VersionEntry.deprecated       := true;
      |} in
      {| State.history      := set_nth i e' s.(State.history);
         State.latest_index := s.(State.latest_index); |}
  end.

(** ----- Operations ----- *)

(** [registerVersion(deployer)] — owner-only. Production reads the
    version string off the deployer (Versioned(deployer).version()),
    hashes it, and inserts. We take [v : Version] explicitly so the
    simulation is pure — the production read is a deterministic
    side-effect-free getter. *)
Definition registerVersion
    (s : State.t) (caller : Address) (v : Version) (deployer : Address)
    (stakingVaultImpl governorImpl timelockImpl : Address)
    : Result.t State.t :=
  if negb (is_owner caller) then
    revert_invalid_caller
  else if deployer =? zero_address then
    revert_zero_address
  else
    let h := version_hash v in
    match find_entry s h with
    | Some _ => revert_invalid_registration
    | None =>
        let e := {|
          VersionEntry.versionHash      := h;
          VersionEntry.version          := v;
          VersionEntry.deployer         := deployer;
          VersionEntry.stakingVaultImpl := stakingVaultImpl;
          VersionEntry.governorImpl     := governorImpl;
          VersionEntry.timelockImpl     := timelockImpl;
          VersionEntry.deprecated       := false;
        |} in
        Result.Success {|
          State.history      := s.(State.history) ++ [e];
          State.latest_index := Some (length s.(State.history));
        |}
    end.

(** [deprecateVersion(versionHash)] — owner-or-emergency. *)
Definition deprecateVersion
    (s : State.t) (caller : Address) (h : U256.t)
    : Result.t State.t :=
  if negb (is_owner_or_emergency caller) then
    revert_invalid_caller
  else
    match find_entry s h with
    | None =>
        (** Production reads from a mapping, so missing entries return
            [isDeprecated = false] and the require passes — i.e. an
            unregistered hash CAN be marked deprecated on-chain. We
            model the same: deprecate writes [isDeprecated[h] = true]
            in a mapping, which we approximate as success without
            a backing entry. To preserve our "history is the source
            of truth" invariant, we surface this case explicitly: the
            registry-flag and the entry-flag drift only for unregistered
            hashes, which can never satisfy [_authorizeUpgrade]
            anyway. For simulation purposes we leave state unchanged
            on missing hash (a divergence that's safe for upgrade
            authorization — see Integration_upgrade_authorization). *)
        Result.Success s
    | Some (i, e) =>
        if e.(VersionEntry.deprecated) then
          revert_already_deprecated
        else
          Result.Success (deprecate_at s i)
    end.

(** [getLatestVersion()] view. Reverts if no version has been
    registered yet. Returns the (hash, version, deployer, deprecated)
    quadruple. *)
Module LatestView.
  Record t : Set := {
    versionHash : U256.t;
    version     : Version;
    deployer    : Address;
    deprecated  : bool;
  }.
End LatestView.

Definition getLatestVersion (s : State.t) : Result.t LatestView.t :=
  match s.(State.latest_index) with
  | None => revert_not_configured
  | Some i =>
      match nth_error s.(State.history) i with
      | None => revert_not_configured   (** unreachable under Valid.state *)
      | Some e =>
          Result.Success {|
            LatestView.versionHash := e.(VersionEntry.versionHash);
            LatestView.version     := e.(VersionEntry.version);
            LatestView.deployer    := e.(VersionEntry.deployer);
            LatestView.deprecated  := e.(VersionEntry.deprecated);
          |}
      end
  end.

(** [getImplementationsForVersion(versionHash)] view. Returns the
    triple recorded at registration time. On the contract this calls
    [deployments[versionHash].stakingVaultImpl()] et al; if the hash
    is unregistered, the call reverts with [CALL to address(0)]. We
    surface that as [None] (caller decides how to translate). *)
Module ImplTriple.
  Record t : Set := {
    stakingVaultImpl : Address;
    governorImpl     : Address;
    timelockImpl     : Address;
  }.
End ImplTriple.

Definition getImplementationsForVersion
    (s : State.t) (h : U256.t) : option ImplTriple.t :=
  match entry_for_hash s h with
  | None => None
  | Some e =>
      Some {|
        ImplTriple.stakingVaultImpl := e.(VersionEntry.stakingVaultImpl);
        ImplTriple.governorImpl     := e.(VersionEntry.governorImpl);
        ImplTriple.timelockImpl     := e.(VersionEntry.timelockImpl);
      |}
  end.

(** Storage invariants.

    [latest_consistent]: [latest_index] is [None] iff the history is
    empty; otherwise it indexes the final element.

    [hashes_unique]: every registered hash appears exactly once in
    the history. This is enforced by [registerVersion]'s
    [InvalidRegistration] check.

    [deployers_nonzero]: every registered deployer is non-zero — the
    contract requires this at registration. (Implementation addresses
    are not constrained, intentionally: production accepts whatever
    [Versioned(deployer).stakingVaultImpl()] returns.) *)
Module Valid.
  Definition latest_consistent (s : State.t) : Prop :=
    match s.(State.latest_index), s.(State.history) with
    | None,   []      => True
    | Some i, _ :: _  => i = (length s.(State.history) - 1)%nat
    | _, _            => False
    end.

  Definition hashes_unique (s : State.t) : Prop :=
    NoDup (map VersionEntry.versionHash s.(State.history)).

  Definition deployers_nonzero (s : State.t) : Prop :=
    Forall (fun e => e.(VersionEntry.deployer) <> zero_address) s.(State.history).

  Record state (s : State.t) : Prop := {
    latest_ok     : latest_consistent s;
    hashes_nd     : hashes_unique s;
    deployers_nz  : deployers_nonzero s;
  }.

  Lemma empty_state_valid : state empty_state.
  Proof.
    constructor; unfold latest_consistent, hashes_unique, deployers_nonzero;
      simpl; auto using NoDup_nil.
  Qed.
End Valid.

(** The upgrade-gate predicate as exposed by
    [StakingVault._authorizeUpgrade]: a [(versionHash, impl)] pair is
    accepted iff
      (1) versionHash equals the registry's latest registered hash,
      (2) the latest entry is not deprecated,
      (3) the entry's stakingVaultImpl matches the proposed impl.

    Formally, this folds in [getLatestVersion] + check on
    [getImplementationsForVersion] in a single decidable predicate. *)
Definition upgrade_authorized
    (s : State.t) (versionHash : U256.t) (stakingVaultImpl : Address) : bool :=
  match getLatestVersion s with
  | Result.Revert _ _ => false
  | Result.Success lv =>
      andb (negb lv.(LatestView.deprecated))
           (andb (lv.(LatestView.versionHash) =? versionHash)
                 (match getImplementationsForVersion s versionHash with
                  | None => false
                  | Some t =>
                      t.(ImplTriple.stakingVaultImpl) =? stakingVaultImpl
                  end))
  end.

End VersionRegistry.
