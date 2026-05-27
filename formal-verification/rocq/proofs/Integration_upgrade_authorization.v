(** Integration: VersionRegistry x StakingVault._authorizeUpgrade.

    Bridges the [VersionRegistry.upgrade_authorized] predicate
    (defined on top of [getLatestVersion] +
    [getImplementationsForVersion]) to the on-chain
    [StakingVault._authorizeUpgrade] checking sequence:

      bytes32 versionHash = keccak256(stakingVaultImpl.version());

      (latestVersionHash, _, _, deprecated) = registry.getLatestVersion();
      require(!deprecated);
      require(versionHash == latestVersionHash);

      (latestImpl, _, _) = registry.getImplementationsForVersion(versionHash);
      require(latestImpl == stakingVaultImpl);

    The integration headline:
      (a) After [registerVersion(_, _, v, _, svi, gi, ti)],
          [upgrade_authorized] accepts (version_hash v, svi).
      (b) After registering v1 and then v2,
          [upgrade_authorized] rejects (version_hash v1, _) -- only the
          latest version is acceptable.
      (c) After [deprecateVersion(version_hash v_latest)],
          [upgrade_authorized] rejects (version_hash v_latest, _).

    Together (a)-(c) capture the "only latest && !deprecated" gate.
    The contract's role check on the upgrade caller itself
    ([onlyRole(DEFAULT_ADMIN_ROLE)]) is orthogonal -- it gates who can
    *initiate* an upgrade, not which impl is acceptable. The registry
    side is what we prove here.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.VersionRegistry.
Require Import ReserveGovernor.proofs.VersionRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationUpgradeAuthorization.

Import ReserveGovernor.simulations.VersionRegistry.
Import VersionRegistry.
Import VersionRegistryProofs.

(** ----- (a) Register v -> upgrade_authorized accepts (hash v, svi). ----- *)
Theorem register_then_authorize_self :
  forall s caller v deployer svi gi ti s',
    registerVersion s caller v deployer svi gi ti = Result.Success s' ->
    upgrade_authorized s' (version_hash v) svi = true.
Proof.
  intros s caller v deployer svi gi ti s' Hok.
  pose proof (registerVersion_getLatestVersion _ _ _ _ _ _ _ _ Hok)
       as (lv & Hgetlat & Hh & _ & _ & Hdep).
  pose proof (registerVersion_impl_triple _ _ _ _ _ _ _ _ Hok) as Htriple.
  unfold upgrade_authorized.
  rewrite Hgetlat.
  rewrite Hdep. simpl.
  rewrite Hh.
  rewrite Z.eqb_refl. simpl.
  rewrite Htriple. simpl.
  apply Z.eqb_refl.
Qed.

(** ----- (b) Register v1, then v2 -> upgrade_authorized rejects v1 (any impl). -----
    Specifically: any (versionHash, impl) pair where versionHash !=
    [version_hash v2] gets rejected because the latest-hash check
    fails. *)
Theorem register_two_then_authorize_rejects_old :
  forall s caller v1 v2 d1 d2 svi1 gi1 ti1 svi2 gi2 ti2 s1 s2 any_impl,
    registerVersion s  caller v1 d1 svi1 gi1 ti1 = Result.Success s1 ->
    registerVersion s1 caller v2 d2 svi2 gi2 ti2 = Result.Success s2 ->
    v1 <> v2 ->
    upgrade_authorized s2 (version_hash v1) any_impl = false.
Proof.
  intros s caller v1 v2 d1 d2 svi1 gi1 ti1 svi2 gi2 ti2 s1 s2 any_impl
         Hok1 Hok2 Hne.
  pose proof (registerVersion_getLatestVersion _ _ _ _ _ _ _ _ Hok2)
       as (lv & Hgetlat & Hh2 & _ & _ & Hdep).
  unfold upgrade_authorized.
  rewrite Hgetlat.
  rewrite Hdep. simpl.
  rewrite Hh2.
  (* version_hash v2 =? version_hash v1: false because v1 <> v2 and
     version_hash is injective. *)
  assert (Hne_hash : version_hash v2 <> version_hash v1).
  { intros Heq.
    apply version_hash_injective in Heq. apply Hne. symmetry. exact Heq. }
  assert (Hb : (version_hash v2 =? version_hash v1) = false).
  { apply Z.eqb_neq. exact Hne_hash. }
  rewrite Hb. simpl. reflexivity.
Qed.

(** ----- (c) Register v, deprecate v, upgrade_authorized rejects. -----
    The deprecated flag on the latest entry trips the
    [upgrade_authorized] check, regardless of impl. Proof strategy:
    leverage the [getLatestVersion]-after-deprecate computation, then
    short-circuit on the [deprecated] field. *)
Theorem register_deprecate_then_authorize_rejects :
  forall s caller_reg caller_dep v deployer svi gi ti s1 s2 impl,
    registerVersion s caller_reg v deployer svi gi ti = Result.Success s1 ->
    deprecateVersion s1 caller_dep (version_hash v) = Result.Success s2 ->
    upgrade_authorized s2 (version_hash v) impl = false.
Proof.
  intros s creg cdep v deployer svi gi ti s1 s2 impl Hreg Hdep.
  (* The post-deprecate state s2 = deprecate_at s1 i where i is the
     index of the registered entry. We need: [getLatestVersion s2]
     returns a [LatestView] with [deprecated = true]. This requires
     the latest_index of s1 to point at the very entry being
     deprecated (which it does, because register made it the most
     recent). We prove this directly using [getLatestVersion] on s2. *)
  assert (Hlatest2_deprecated :
    exists lv, getLatestVersion s2 = Result.Success lv /\
               lv.(LatestView.deprecated) = true).
  { (* Unfold register and deprecate to expose s2's shape. *)
    unfold registerVersion in Hreg.
    destruct (is_owner creg) eqn:Hown_reg; [|simpl in Hreg; discriminate].
    destruct (deployer =? zero_address) eqn:Hd; [discriminate|].
    destruct (find_entry s (version_hash v)) eqn:Hpre_reg; [discriminate|].
    injection Hreg as <-.
    unfold deprecateVersion in Hdep.
    destruct (is_owner_or_emergency cdep) eqn:Hrole;
      [|simpl in Hdep; discriminate].
    (* find_entry on s1 must succeed at the just-appended entry. *)
    set (new_e := {|
      VersionEntry.versionHash      := version_hash v;
      VersionEntry.version          := v;
      VersionEntry.deployer         := deployer;
      VersionEntry.stakingVaultImpl := svi;
      VersionEntry.governorImpl     := gi;
      VersionEntry.timelockImpl     := ti;
      VersionEntry.deprecated       := false; |}) in *.
    assert (Hne_hash : new_e.(VersionEntry.versionHash) = version_hash v)
      by reflexivity.
    unfold find_entry in Hdep.
    simpl in Hdep.
    unfold find_entry in Hpre_reg.
    rewrite (find_entry_idx_app_none _ new_e _ _ Hpre_reg Hne_hash) in Hdep.
    simpl in Hdep.
    (* new_e.(deprecated) = false, so we hit the "set and return Success" branch. *)
    injection Hdep as <-.
    unfold getLatestVersion.
    unfold deprecate_at.
    simpl.
    (* The deprecated branch is taken when the looked-up entry's
       deprecated flag was false. find_entry_idx_app_none gave us
       Some (0+length history, new_e). new_e.deprecated = false ok. *)
    (* Hdep now has shape: Result.Success s2 = Result.Success (deprecate_at ...). *)
    assert (Hnth_app :
      nth_error (s.(State.history) ++ [new_e])
                (length s.(State.history))
      = Some new_e).
    { clear. induction s.(State.history) as [|x rest IH]; simpl; auto. }
    (* deprecate_at uses nth_error at index (0 + length history) = length history *)
    replace (0%nat + length s.(State.history))%nat
       with (length s.(State.history)) in * by lia.
    rewrite Hnth_app. simpl.
    (* Now set_nth at index (length history) on (history ++ [new_e])
       replaces the last element with the deprecated copy. *)
    assert (Hsnth :
      forall hist,
      nth_error
        (set_nth (length hist)
                 {| VersionEntry.versionHash      := new_e.(VersionEntry.versionHash);
                    VersionEntry.version          := new_e.(VersionEntry.version);
                    VersionEntry.deployer         := new_e.(VersionEntry.deployer);
                    VersionEntry.stakingVaultImpl := new_e.(VersionEntry.stakingVaultImpl);
                    VersionEntry.governorImpl     := new_e.(VersionEntry.governorImpl);
                    VersionEntry.timelockImpl     := new_e.(VersionEntry.timelockImpl);
                    VersionEntry.deprecated       := true |}
                 (hist ++ [new_e]))
        (length hist)
      = Some {| VersionEntry.versionHash      := new_e.(VersionEntry.versionHash);
                VersionEntry.version          := new_e.(VersionEntry.version);
                VersionEntry.deployer         := new_e.(VersionEntry.deployer);
                VersionEntry.stakingVaultImpl := new_e.(VersionEntry.stakingVaultImpl);
                VersionEntry.governorImpl     := new_e.(VersionEntry.governorImpl);
                VersionEntry.timelockImpl     := new_e.(VersionEntry.timelockImpl);
                VersionEntry.deprecated       := true |}).
    { intros hist. induction hist as [|x rest IH]; simpl; auto. }
    rewrite Hsnth.
    eexists. split; [reflexivity|]. simpl. reflexivity. }
  destruct Hlatest2_deprecated as (lv & Hgl & Hdep_true).
  unfold upgrade_authorized.
  rewrite Hgl. rewrite Hdep_true. simpl. reflexivity.
Qed.

End IntegrationUpgradeAuthorization.
