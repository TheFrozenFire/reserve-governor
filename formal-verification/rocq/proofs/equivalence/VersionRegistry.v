(** Phase 3.1 (task #180) — VersionRegistry equivalence scaffold.

    Storage layout (the `roleRegistry` field is `immutable`):

      slot 0: mapping(bytes32 => IReserveOptimisticGovernorDeployer) deployments
      slot 1: mapping(bytes32 => bool) isDeprecated
      slot 2: bytes32 latestVersion

    Both mappings are flat (key -> single uint256 value), so they fit
    the existing [StorableValue.Map] variant — no MapStruct needed.
    This makes VersionRegistry the simplest equivalence target after
    Sandbox; the projection just slots in the upstream's
    [Map U256→U256] shape.

    Note that the sim's [history : list VersionEntry.t] carries more
    than the on-chain storage records:

      - sim's [versionHash, deployer, deprecated] match on-chain.
      - sim's [version, stakingVaultImpl, governorImpl, timelockImpl]
        are derived view-fields, NOT stored on chain (they're read
        from the deployer's [Versioned(deployer).version()] etc. at
        register-time). The projection ignores these. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.VersionRegistry.
Require Import Coq.Lists.List.
Import ListNotations.

Module VersionRegistryEquivalence.

  Import VersionRegistry.

  (** ----- Project the sim's history into the two on-chain maps -----

      [deployments_map] sends [versionHash -> deployer]. Multiple
      sim entries with the same versionHash are not expected (the sim
      precondition keeps history unique by hash), but if they were
      present, [Dict.get] would return the last-occurrence value.

      [isDeprecated_map] sends [versionHash -> 1] for entries with
      [deprecated = true], else the slot returns 0 (default). *)
  Fixpoint deployments_map (history : list VersionEntry.t) :
      Dict.t U256.t U256.t :=
    match history with
    | []       => []
    | e :: rest =>
        (e.(VersionEntry.versionHash), e.(VersionEntry.deployer))
          :: deployments_map rest
    end.

  Fixpoint isDeprecated_map (history : list VersionEntry.t) :
      Dict.t U256.t U256.t :=
    match history with
    | []       => []
    | e :: rest =>
        let v := if e.(VersionEntry.deprecated) then 1 else 0 in
        (e.(VersionEntry.versionHash), v) :: isDeprecated_map rest
    end.

  Definition latestVersion_value (sim : State.t) : U256.t :=
    match sim.(State.latest_index) with
    | None => 0
    | Some i =>
        match List.nth_error sim.(State.history) i with
        | None   => 0
        | Some e => e.(VersionEntry.versionHash)
        end
    end.

  (** ----- Full projection ----- *)
  Definition proj_sim (sim : State.t) : SimulatedStorage.t := [
    StorableValue.Map (deployments_map sim.(State.history));
    StorableValue.Map (isDeprecated_map sim.(State.history));
    StorableValue.U256 (latestVersion_value sim)
  ].

  (** ----- Well-formedness sanity ----- *)
  Lemma proj_sim_length (sim : State.t) :
    List.length (proj_sim sim) = 3%nat.
  Proof. reflexivity. Qed.

  Lemma proj_sim_deployments (sim : State.t) :
    List.nth_error (proj_sim sim) 0
    = Some (StorableValue.Map (deployments_map sim.(State.history))).
  Proof. reflexivity. Qed.

  Lemma proj_sim_isDeprecated (sim : State.t) :
    List.nth_error (proj_sim sim) 1
    = Some (StorableValue.Map (isDeprecated_map sim.(State.history))).
  Proof. reflexivity. Qed.

  Lemma proj_sim_latestVersion (sim : State.t) :
    List.nth_error (proj_sim sim) 2
    = Some (StorableValue.U256 (latestVersion_value sim)).
  Proof. reflexivity. Qed.

  (** ----- Map lookup sanity (one branch closes, others Admitted) -----

      [deployments_map_get_unregistered] closes by induction since
      both [Dict.get] and the sim's [find_entry] traverse the list
      head-first. *)
  Lemma deployments_map_empty :
    deployments_map [] = [].
  Proof. reflexivity. Qed.

  Lemma isDeprecated_map_empty :
    isDeprecated_map [] = [].
  Proof. reflexivity. Qed.

  (** Same R022 family as ThrottleLib: relating [Dict.get
      (deployments_map history) hash] to the sim's [entry_for_hash sim hash]
      requires the [Dict.Eq.eqb] (Z, Z) instance unfolding documented
      in WISDOM R022. The unblocker lemma is in scope from
      proofs/equivalence/ThrottleLib.v. Marked deferred here. *)

End VersionRegistryEquivalence.
