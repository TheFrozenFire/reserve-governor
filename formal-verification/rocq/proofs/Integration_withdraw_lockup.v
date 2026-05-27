(** Cross-domain integration: StakingVault withdraw + UnstakingManager lock.

    The Solidity flow at [contracts/staking/StakingVault.sol#L266-L293]
    handles withdraws with [unstakingDelay > 0] by

      totalDeposited -= _assets;
      unstakingManager.createLock(_receiver, _assets,
                                  block.timestamp + unstakingDelay);

    i.e. the assets *move* out of the vault's [totalDeposited] book and
    into a fresh [Lock] sitting in the [UnstakingManager]. No value is
    burned in transit: what the vault releases must show up as an
    active lock on the manager side, dollar-for-dollar.

    This file stitches the two per-domain simulations together,
    defining the composite operation [withdraw_with_lockup] and
    proving the conservation invariant:

      pre_exchange.totalDeposited
        = post_exchange.totalDeposited
          + (total_active post_manager.locks
             - total_active pre_manager.locks)

    plus a complementary cancel theorem showing that [cancelLock]
    erases the lock from [total_active], so a subsequent
    re-deposit-to-vault step (modeled by [StakingVaultExchange.deposit])
    restores the original sum.

    Modeling notes:
      - We model only the [unstakingDelay > 0] branch — the [== 0]
        branch in production calls [super._withdraw] (direct ERC20
        transfer to the receiver) and never touches the manager. The
        conservation invariant in that branch is trivial in the manager
        dimension (no lock created) and reduces to the per-domain
        [withdraw] storage delta already proved in
        [StakingVaultExchange.v].
      - We pass [unlockTime] as an explicit parameter rather than
        modeling [block.timestamp + unstakingDelay] internally. The
        production constraint [unlockTime > 0] is captured as a
        precondition.
      - The vault address [vault] is passed both as the caller and the
        expected-vault parameter to [createLock], mirroring the
        Solidity reality where the vault contract is the sole caller.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module IntegrationWithdrawLockup.

(** Disambiguate the two [Result.t] constructors — both modules define
    one. We use the fully-qualified names everywhere below. *)

(** ===== Composite operation ===== *)

(** [withdraw_with_lockup] models the [unstakingDelay > 0] branch of
    [StakingVault._withdraw]. It performs

      1. [StakingVaultExchange.withdraw s_ex assets]  — decreases
         [totalDeposited] by [assets] (and burns the equivalent
         shares); reverts if [assets > totalAssets].
      2. [UnstakingManager.createLock s_mg vault vault receiver
            assets unlockTime] — appends a fresh active lock; reverts
         if [caller != vault] (here trivially [vault =? vault]).

    The composite returns a pair of post-states wrapped in a [Result.t]
    so a revert from either leg short-circuits the whole flow.

    Mirrors Solidity [StakingVault._withdraw] when [unstakingDelay > 0]:

      totalDeposited -= _assets;
      unstakingManager.createLock(_receiver, _assets,
                                  block.timestamp + unstakingDelay);
*)
Definition withdraw_with_lockup
    (s_ex : StakingVaultExchange.State.t)
    (s_mg : UnstakingManager.State.t)
    (vault receiver : UnstakingManager.Address)
    (assets unlockTime : U256.t)
    : UnstakingManager.Result.t
        (StakingVaultExchange.State.t * UnstakingManager.State.t) :=
  match StakingVaultExchange.withdraw s_ex assets with
  | StakingVaultExchange.Result.Revert p q =>
      UnstakingManager.Result.Revert p q
  | StakingVaultExchange.Result.Success (s_ex', _shares) =>
      match UnstakingManager.createLock s_mg vault vault receiver
              assets unlockTime with
      | UnstakingManager.Result.Revert p q =>
          UnstakingManager.Result.Revert p q
      | UnstakingManager.Result.Success s_mg' =>
          UnstakingManager.Result.Success (s_ex', s_mg')
      end
  end.

(** ===== Helper: total_active over an append ===== *)

(** A single-step folding lemma: appending one lock to the locks list
    adds exactly that lock's [active_amount] to the running
    [total_active] sum. The proof is by induction on the prefix. *)
Lemma total_active_app_singleton (locks : list UnstakingManager.Lock.t)
    (new_lock : UnstakingManager.Lock.t) :
  UnstakingManager.total_active (locks ++ [new_lock])
    = UnstakingManager.total_active locks
      + UnstakingManager.active_amount new_lock.
Proof.
  induction locks as [|l rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** Generalization: total_active distributes over list append.
    Stated for completeness; not needed by the conservation theorem
    directly but useful for downstream proofs. *)
Lemma total_active_app (l1 l2 : list UnstakingManager.Lock.t) :
  UnstakingManager.total_active (l1 ++ l2)
    = UnstakingManager.total_active l1 + UnstakingManager.total_active l2.
Proof.
  induction l1 as [|x xs IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** The [active_amount] of a freshly-created lock equals [amount]
    exactly when [unlockTime > 0] — the production constraint that
    distinguishes a default-zero slot from a real lock. *)
Lemma active_amount_fresh (user : UnstakingManager.Address)
    (amount unlockTime : U256.t) :
  0 < unlockTime ->
  UnstakingManager.active_amount {|
    UnstakingManager.Lock.user       := user;
    UnstakingManager.Lock.amount     := amount;
    UnstakingManager.Lock.unlockTime := unlockTime;
    UnstakingManager.Lock.claimedAt  := 0;
  |} = amount.
Proof.
  intros Hut.
  unfold UnstakingManager.active_amount; simpl.
  assert (Hne : (unlockTime =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite Hne. simpl. reflexivity.
Qed.

(** ===== Conservation theorem ===== *)

(** [withdraw_with_lockup_conserves_value]: under the [unstakingDelay > 0]
    branch, the assets that leave the vault's [totalDeposited] are
    exactly accounted for by the increase in active locks on the
    manager side.

    Precondition [0 < unlockTime] excludes the default-zero slot
    shape; without it [active_amount] would return 0 and the
    conservation would not hold (the assets would vanish on paper).
    In production [unlockTime = block.timestamp + unstakingDelay] with
    [unstakingDelay > 0], so [unlockTime > 0] is the natural witness. *)
Theorem withdraw_with_lockup_conserves_value
    (s_ex s_ex' : StakingVaultExchange.State.t)
    (s_mg s_mg' : UnstakingManager.State.t)
    (vault receiver : UnstakingManager.Address)
    (assets unlockTime : U256.t) :
  0 < unlockTime ->
  withdraw_with_lockup s_ex s_mg vault receiver assets unlockTime
    = UnstakingManager.Result.Success (s_ex', s_mg') ->
  s_ex.(StakingVaultExchange.State.totalDeposited)
    = s_ex'.(StakingVaultExchange.State.totalDeposited)
      + UnstakingManager.total_active
          s_mg'.(UnstakingManager.State.locks)
      - UnstakingManager.total_active
          s_mg.(UnstakingManager.State.locks).
Proof.
  intros Hut Hok.
  unfold withdraw_with_lockup in Hok.
  (* Case-split on the inner withdraw call. *)
  destruct (StakingVaultExchange.withdraw s_ex assets)
    as [inner_pair | p q] eqn:Hwd;
    [|discriminate].
  destruct inner_pair as (s_ex_inner & shares).
  (* Case-split on the inner createLock call. *)
  destruct (UnstakingManager.createLock s_mg vault vault receiver
              assets unlockTime) as [s_mg_inner | p q] eqn:Hcl;
    [|discriminate].
  injection Hok as Hex_eq Hmg_eq.
  subst s_ex'. subst s_mg'.
  (* Unpack withdraw to learn the totalDeposited delta. *)
  unfold StakingVaultExchange.withdraw in Hwd.
  destruct (assets >? StakingVaultExchange.totalAssets s_ex) eqn:Hgt;
    [discriminate|].
  injection Hwd as Hex_inner_eq Hshares_eq.
  subst s_ex_inner.
  (* Unpack createLock to learn the new locks list. *)
  unfold UnstakingManager.createLock in Hcl.
  destruct (negb (vault =? vault)) eqn:Hauth.
  { (* vault =? vault must be true; contradiction *)
    rewrite Z.eqb_refl in Hauth. discriminate. }
  injection Hcl as Hmg_inner_eq.
  subst s_mg_inner.
  (* Both states are now known; compute. *)
  simpl.
  rewrite total_active_app_singleton.
  rewrite active_amount_fresh by exact Hut.
  lia.
Qed.

(** ===== Cancel-restores conservation ===== *)

(** Once the lock has been cancelled, the cancelled lock no longer
    contributes to [total_active]: the slot is now [default_lock]
    whose [active_amount] is 0. So the manager's running sum drops
    by exactly the cancelled amount.

    Combined with the conservation theorem above, this captures the
    full round-trip story: a withdraw moves [assets] from the vault
    into a lock, and a cancel moves [assets] back out of the lock-side
    [total_active]. A subsequent [deposit] on the vault (modeled
    separately in [StakingVaultExchange.deposit]) restores the
    original [totalDeposited]. *)

(** Helper: changing one entry of a list by [set_nth] changes
    [total_active] by exactly the difference in [active_amount]. *)
Lemma total_active_set_nth (locks : list UnstakingManager.Lock.t)
    (n : nat) (l_new : UnstakingManager.Lock.t) :
  (n < length locks)%nat ->
  UnstakingManager.total_active
    (UnstakingManager.set_nth n l_new locks)
  = UnstakingManager.total_active locks
    - UnstakingManager.active_amount
        (nth n locks UnstakingManager.default_lock)
    + UnstakingManager.active_amount l_new.
Proof.
  revert n.
  induction locks as [|x rest IH]; intros n Hlen; simpl in Hlen.
  - lia.
  - destruct n; simpl.
    + lia.
    + rewrite IH by lia. lia.
Qed.

(** [active_amount default_lock = 0] — trivial but worth stating. *)
Lemma active_amount_default :
  UnstakingManager.active_amount UnstakingManager.default_lock = 0.
Proof. reflexivity. Qed.

(** [cancel_drops_total_active]: a successful [cancelLock] decreases
    [total_active] by the cancelled lock's [active_amount]. Stated in
    the inequality direction so the caller doesn't need to know the
    exact pre-cancel [active_amount]. *)
Theorem cancel_drops_total_active
    (s_mg s_mg' : UnstakingManager.State.t)
    (lockId : U256.t)
    (caller : UnstakingManager.Address) :
  (Z.to_nat lockId < length s_mg.(UnstakingManager.State.locks))%nat ->
  UnstakingManager.cancelLock s_mg lockId caller
    = UnstakingManager.Result.Success s_mg' ->
  UnstakingManager.total_active
    s_mg'.(UnstakingManager.State.locks)
  = UnstakingManager.total_active
      s_mg.(UnstakingManager.State.locks)
    - UnstakingManager.active_amount
        (UnstakingManager.lock_at s_mg lockId).
Proof.
  intros Hbound Hok.
  unfold UnstakingManager.cancelLock in Hok.
  destruct (negb (_ =? _)) eqn:Hauth in Hok; [discriminate|].
  destruct (negb (_ =? _)) eqn:Hclaim in Hok; [discriminate|].
  injection Hok as Hs'.
  subst s_mg'.
  unfold UnstakingManager.set_lock. simpl.
  rewrite total_active_set_nth by exact Hbound.
  unfold UnstakingManager.lock_at.
  rewrite active_amount_default.
  lia.
Qed.

(** ===== Cross-check (vm_compute) =====

    Calibration scenario: start with [totalDeposited = 1e21] in the
    vault and an empty manager, then [withdraw_with_lockup 3e20] with
    a positive [unlockTime]. After the composite operation:

      - The vault's [totalDeposited] is [1e21 - 3e20 = 7e20].
      - The manager's [total_active] is [3e20].
      - The sum matches the pre-vault [totalDeposited = 1e21].

    Then [cancelLock] on the freshly-created lock: [total_active]
    drops to zero, and the conservation closes via a re-deposit. *)

(** A starting vault state with 1e21 deposited and 1e21 shares (1:1 from
    the initial-deposit edge of [convertToShares] — see
    [StakingVaultExchange.empty_state] semantics for supply = 0). *)
Definition cal_vault : StakingVaultExchange.State.t := {|
  StakingVaultExchange.State.totalSupply              := 10^21;
  StakingVaultExchange.State.totalDeposited           := 10^21;
  StakingVaultExchange.State.accumulatedNativeRewards := 0;
|}.

Definition cal_manager : UnstakingManager.State.t :=
  UnstakingManager.empty_state.

(** Calibration: vault address 100, receiver address 201. *)
Definition cal_vault_addr : UnstakingManager.Address := 100.
Definition cal_receiver   : UnstakingManager.Address := 201.

(** Withdraw 3e20 with a positive unlockTime (e.g. 50 + delay). *)
Definition cal_assets   : U256.t := 3 * 10^20.
Definition cal_unlockTime : U256.t := 1000.

(** The composite operation succeeds. *)
Lemma xcheck_withdraw_with_lockup_succeeds :
  exists s_ex' s_mg',
    withdraw_with_lockup cal_vault cal_manager
      cal_vault_addr cal_receiver cal_assets cal_unlockTime
    = UnstakingManager.Result.Success (s_ex', s_mg').
Proof. vm_compute. eexists. eexists. reflexivity. Qed.

(** The vault's totalDeposited drops by exactly [cal_assets]. *)
Lemma xcheck_vault_totalDeposited_post :
  match withdraw_with_lockup cal_vault cal_manager
          cal_vault_addr cal_receiver cal_assets cal_unlockTime with
  | UnstakingManager.Result.Success (s_ex', _) =>
      s_ex'.(StakingVaultExchange.State.totalDeposited) = 7 * 10^20
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The manager's [total_active] is exactly [cal_assets]. *)
Lemma xcheck_manager_total_active_post :
  match withdraw_with_lockup cal_vault cal_manager
          cal_vault_addr cal_receiver cal_assets cal_unlockTime with
  | UnstakingManager.Result.Success (_, s_mg') =>
      UnstakingManager.total_active
        s_mg'.(UnstakingManager.State.locks) = 3 * 10^20
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** End-to-end conservation: pre.totalDeposited = post.totalDeposited +
    delta total_active.  Numerically: 1e21 = 7e20 + (3e20 - 0). *)
Lemma xcheck_conservation_holds :
  match withdraw_with_lockup cal_vault cal_manager
          cal_vault_addr cal_receiver cal_assets cal_unlockTime with
  | UnstakingManager.Result.Success (s_ex', s_mg') =>
      cal_vault.(StakingVaultExchange.State.totalDeposited)
        = s_ex'.(StakingVaultExchange.State.totalDeposited)
          + UnstakingManager.total_active
              s_mg'.(UnstakingManager.State.locks)
          - UnstakingManager.total_active
              cal_manager.(UnstakingManager.State.locks)
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** After the withdraw, [cancelLock 0] by the receiver drops the lock
    back to default, restoring [total_active = 0] on the manager. *)
Definition cal_after_withdraw : StakingVaultExchange.State.t * UnstakingManager.State.t :=
  match withdraw_with_lockup cal_vault cal_manager
          cal_vault_addr cal_receiver cal_assets cal_unlockTime with
  | UnstakingManager.Result.Success p => p
  | _ => (cal_vault, cal_manager)  (* unreachable per above *)
  end.

Definition cal_after_cancel : UnstakingManager.State.t :=
  match UnstakingManager.cancelLock (snd cal_after_withdraw) 0 cal_receiver with
  | UnstakingManager.Result.Success s => s
  | _ => snd cal_after_withdraw  (* unreachable on the live scenario *)
  end.

Lemma xcheck_cancel_restores_zero_active :
  UnstakingManager.total_active
    cal_after_cancel.(UnstakingManager.State.locks) = 0.
Proof. vm_compute. reflexivity. Qed.

(** Full round-trip: pre.totalDeposited matches
    (post-withdraw vault.totalDeposited) + (post-cancel manager
    total_active) + (cancelled lock's pre-cancel active_amount). The
    last term is the amount the receiver can now re-deposit into the
    vault to fully close the loop. *)
Lemma xcheck_round_trip_book_keeps :
  cal_vault.(StakingVaultExchange.State.totalDeposited)
    = (fst cal_after_withdraw).(StakingVaultExchange.State.totalDeposited)
      + UnstakingManager.total_active
          cal_after_cancel.(UnstakingManager.State.locks)
      + cal_assets.
Proof. vm_compute. reflexivity. Qed.

End IntegrationWithdrawLockup.
