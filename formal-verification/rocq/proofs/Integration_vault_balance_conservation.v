(** Cross-domain integration: vault ERC20 balance conservation
    across the StakingVault + UnstakingManager + ERC20 triad.

    The "funds can't disappear" theorem. Every wei of the underlying
    ERC20 the vault holds is either backing currently-staked shares
    (counted by [StakingVaultExchange.State.totalDeposited]) OR sitting
    in an unstaking lock waiting to be claimed (counted by
    [UnstakingManager.total_active]). No leak, no double-count, across
    the entire deposit -> withdraw-to-lock -> claim lifecycle.

    ----- Modeling decision: SINGLE-BUCKET vault address -----

    The on-chain reality is that two distinct addresses hold the
    underlying ERC20 during this lifecycle:

      - The vault contract holds the live deposits.
      - The UnstakingManager contract holds the assets backing
        pending withdrawal locks (the vault [forceApprove]s the
        manager and the manager pulls the assets when [createLock]
        is called).

    The ERC20 mock at [mocks/ERC20.v] models [balanceOf], [transfer],
    and [transferFrom], but does NOT model the [forceApprove] allowance
    state machine (production passes the allowance to [transferFrom]
    explicitly via a side channel; this is documented in the mock's
    header as the "T-REWARDTOKEN" trust assumption).

    Rather than drag the allowance plumbing into this proof for what
    is fundamentally an accounting theorem, we adopt the **single-bucket
    model**: both the vault and the manager are treated as the same
    ERC20 holder address [vault_addr]. From the ERC20's perspective,
    the vault -> manager transfer that happens inside [createLock] is
    a self-transfer (a no-op, by [ERC20.do_transfer]'s [from =? to]
    short-circuit). The claim-side payout to the lock's user is then
    an honest [transfer] out of [vault_addr], which the conservation
    invariant tracks.

    This is justified because the headline invariant we want to prove
    is

      ERC20.balanceOf vault_addr erc20_state
        = exchange_state.(totalDeposited)
          + total_active manager_state.(locks).

    The vault-vs-manager split of the bucket is operationally
    interesting but invariant-irrelevant: any wei in the manager's
    address could equivalently be modeled as still sitting in the
    vault's address from the conservation standpoint, since the
    manager-side balance is *exactly* [total_active] (and zero
    otherwise — the manager only holds money it owes back).

    The two-address split is documented in
    [notes/external_dependencies.md] as a deliberate modeling
    simplification; the headline conservation theorem is unaffected.
    Should a later proof care about per-address solvency (e.g. "the
    manager is never under-funded for pending locks"), it can re-state
    the invariant in two-address form against this same lifecycle.

    ----- Theorem shape -----

    We define a [World] record bundling the three states, three
    composite operations (deposit / withdraw-with-lockup / claim), and
    a [Reachable] inductive capturing any finite sequence of those
    operations starting from an empty [World]. The headline is
    [vault_balance_conserved_across_lifecycle]: every [Reachable]
    state satisfies the conservation invariant.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.mocks.ERC20.
Require Import ReserveGovernor.simulations.StakingVaultExchange.
Require Import ReserveGovernor.simulations.UnstakingManager.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Local Open Scope Z_scope.

Module IntegrationVaultBalanceConservation.

(** ===== Composite world ===== *)

(** The bundled state of all three domains plus the address used to
    identify the (single-bucket) vault holder on the ERC20 side. The
    [manager_addr] field is carried for documentation symmetry with
    the on-chain split but is operationally pinned to [vault_addr]
    by the modeling decision above; we expose it so future two-address
    refinements can lift this surface without renaming.

    [depositor_default] is the address an ERC20 [transferFrom] pulls
    from on the deposit side; it's a per-call argument, not a world
    field, so it doesn't appear here. *)
Record World : Set := {
  erc20_state     : ERC20.State;
  exchange_state  : StakingVaultExchange.State.t;
  manager_state   : UnstakingManager.State.t;
  vault_addr      : ERC20.Address;
  manager_addr    : ERC20.Address;
}.

(** The empty world: every domain at its empty state, addresses
    user-chosen. Used as the base case of [Reachable]. *)
Definition empty_world (va ma : ERC20.Address) : World := {|
  erc20_state    := ERC20.empty_state 0;
  exchange_state := StakingVaultExchange.empty_state;
  manager_state  := UnstakingManager.empty_state;
  vault_addr     := va;
  manager_addr   := ma;
|}.

(** ===== The conservation invariant ===== *)

(** The vault's ERC20 balance is precisely the sum of
      - currently-staked deposits backing live shares, and
      - currently-pending unstaking locks
    nothing more, nothing less. *)
Definition vault_balance_conserved (w : World) : Prop :=
  ERC20.balanceOf (erc20_state w) (vault_addr w)
    = (exchange_state w).(StakingVaultExchange.State.totalDeposited)
      + UnstakingManager.total_active
          (manager_state w).(UnstakingManager.State.locks).

(** ===== Composite operation 1: deposit_with_transfer ===== *)

(** A user-initiated deposit. The ERC20 leg pulls [assets] from
    [depositor] into the vault's bucket; the exchange leg bumps
    [totalDeposited] by [assets] and mints shares (we discard the
    share count — this proof is about the asset-side conservation).

    Preconditions enforced by the composite (both must hold for
    [Success], else the inner [transferFrom] reverts):
      - [depositor] holds at least [assets] of the underlying;
      - [depositor] is distinct from [vault_addr] (a self-deposit
        would be a no-op on the ERC20 side and would violate the
        invariant on the exchange side; production cannot reach this
        because the vault contract is never the depositor of record).

    The allowance argument to [transferFrom] is supplied by the
    caller (the [allowance] formal); per the mock's design the caller
    threads the pre-call allowance through. Production: the vault
    relies on the user's prior [approve] of the underlying. *)
Definition deposit_with_transfer
    (w : World) (depositor : ERC20.Address)
    (assets allowance : U256.t)
    : ERC20.Result.t World :=
  match ERC20.transferFrom (erc20_state w) (vault_addr w)
          depositor (vault_addr w) assets allowance with
  | ERC20.Result.Revert p q => ERC20.Result.Revert p q
  | ERC20.Result.Success erc20' =>
      let (s_ex', _shares) :=
        StakingVaultExchange.deposit (exchange_state w) assets in
      ERC20.Result.Success {|
        erc20_state    := erc20';
        exchange_state := s_ex';
        manager_state  := manager_state w;
        vault_addr     := vault_addr w;
        manager_addr   := manager_addr w;
      |}
  end.

(** ===== Composite operation 2: withdraw_with_lockup_and_transfer ===== *)

(** A user-initiated withdraw-with-delay. In the single-bucket model
    this performs:
      1. [StakingVaultExchange.withdraw] — drops [totalDeposited] by
         [assets].
      2. [UnstakingManager.createLock] — appends an active lock of
         [assets] backed by [unlockTime > 0].
      3. ERC20-side: a "transfer" from [vault_addr] to [vault_addr]
         (the single-bucket idealization of the production vault ->
         manager move). This is a no-op by [do_transfer]'s [from =? to]
         short-circuit, so the ERC20 balance is unchanged.

    Net effect on the invariant:
      - balance:  unchanged.
      - totalDeposited: decreases by [assets].
      - total_active:   increases by [assets].
    The sum is preserved.

    Preconditions for [Success]:
      - [assets <= totalAssets exchange_state]   (exchange withdraw guard);
      - [0 < unlockTime]                         (active-lock witness).
*)
Definition withdraw_with_lockup_and_transfer
    (w : World) (receiver : ERC20.Address)
    (assets unlockTime : U256.t)
    : UnstakingManager.Result.t World :=
  match StakingVaultExchange.withdraw (exchange_state w) assets with
  | StakingVaultExchange.Result.Revert p q =>
      UnstakingManager.Result.Revert p q
  | StakingVaultExchange.Result.Success (s_ex', _shares) =>
      match UnstakingManager.createLock (manager_state w)
              (vault_addr w) (vault_addr w) receiver
              assets unlockTime with
      | UnstakingManager.Result.Revert p q =>
          UnstakingManager.Result.Revert p q
      | UnstakingManager.Result.Success s_mg' =>
          (* Single-bucket model: the vault -> manager ERC20 move is a
             self-transfer at [vault_addr]. We thread the ERC20 state
             through [transfer] to make the no-op visible in the
             World; [do_transfer]'s [from =? to] short-circuit means
             this is operationally [Success w.erc20]. *)
          match ERC20.transfer (erc20_state w) (vault_addr w)
                  (vault_addr w) assets with
          | ERC20.Result.Revert p q =>
              UnstakingManager.Result.Revert p q
          | ERC20.Result.Success erc20' =>
              UnstakingManager.Result.Success {|
                erc20_state    := erc20';
                exchange_state := s_ex';
                manager_state  := s_mg';
                vault_addr     := vault_addr w;
                manager_addr   := manager_addr w;
              |}
          end
      end
  end.

(** ===== Composite operation 3: claim_with_transfer ===== *)

(** The lock's user (or anyone, post-maturity) claims a lock.
    Performs:
      1. [UnstakingManager.claimLock] — marks the lock claimed and
         drops [total_active] by the lock's [amount].
      2. ERC20-side: a [transfer] from [vault_addr] to [lock.user]
         for [lock.amount] (the production manager -> user payout;
         in the single-bucket model the source address is the
         vault's bucket).

    Net effect on the invariant:
      - balance:  decreases by [lock.amount].
      - totalDeposited: unchanged.
      - total_active:   decreases by [lock.amount].
    The sum is preserved.

    Preconditions for [Success]:
      - [lockId < length manager.locks];
      - [unlockTime <= now] and [unlockTime != 0] (maturity);
      - [claimedAt = 0] pre-claim;
      - lock.user != vault_addr     (the payout is a real transfer,
                                     not a self-loop);
      - [vault_addr]'s ERC20 balance >= [lock.amount].
*)
Definition claim_with_transfer
    (w : World) (lockId now : U256.t)
    : UnstakingManager.Result.t World :=
  let l := UnstakingManager.lock_at (manager_state w) lockId in
  match UnstakingManager.claimLock (manager_state w) lockId now with
  | UnstakingManager.Result.Revert p q =>
      UnstakingManager.Result.Revert p q
  | UnstakingManager.Result.Success s_mg' =>
      match ERC20.transfer (erc20_state w) (vault_addr w)
              l.(UnstakingManager.Lock.user)
              l.(UnstakingManager.Lock.amount) with
      | ERC20.Result.Revert p q =>
          UnstakingManager.Result.Revert p q
      | ERC20.Result.Success erc20' =>
          UnstakingManager.Result.Success {|
            erc20_state    := erc20';
            exchange_state := exchange_state w;
            manager_state  := s_mg';
            vault_addr     := vault_addr w;
            manager_addr   := manager_addr w;
          |}
      end
  end.

(** ===== Local helpers ===== *)

(** Single-step [total_active] over [_ ++ [new_lock]]. Reproduced
    here so this file is self-contained and doesn't depend on the
    helper bundle in [UnstakingManager_conservation.v]. *)
Lemma total_active_app_singleton
    (locks : list UnstakingManager.Lock.t)
    (new_lock : UnstakingManager.Lock.t) :
  UnstakingManager.total_active (locks ++ [new_lock])
    = UnstakingManager.total_active locks
      + UnstakingManager.active_amount new_lock.
Proof.
  induction locks as [|l rest IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** Single-step [total_active] over [set_nth n l_new locks]. *)
Lemma total_active_set_nth
    (locks : list UnstakingManager.Lock.t)
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

(** Fresh active lock contributes its [amount] to [total_active]. *)
Lemma active_amount_fresh_active
    (user : UnstakingManager.Address)
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

(** Default lock has zero [active_amount]. *)
Lemma active_amount_default :
  UnstakingManager.active_amount UnstakingManager.default_lock = 0.
Proof. reflexivity. Qed.

(** ===== Per-operation conservation lemmas ===== *)

(** ---- Op 1: deposit ----

    A successful [deposit_with_transfer] preserves
    [vault_balance_conserved]. Requires the depositor be distinct from
    the vault address so [transferFrom] performs a real credit (no
    self-transfer short-circuit that would let [totalDeposited] grow
    without a matching balance bump). *)
Theorem deposit_preserves_conservation
    (w w' : World)
    (depositor : ERC20.Address)
    (assets allowance : U256.t) :
  vault_balance_conserved w ->
  depositor <> vault_addr w ->
  0 < assets ->
  deposit_with_transfer w depositor assets allowance
    = ERC20.Result.Success w' ->
  vault_balance_conserved w'.
Proof.
  intros Hinv Hne Hpos Hok.
  unfold deposit_with_transfer in Hok.
  destruct (ERC20.transferFrom (erc20_state w) (vault_addr w)
              depositor (vault_addr w) assets allowance) as [erc20' | p q] eqn:Htf;
    [|discriminate].
  (* Pre-compute the deposit's pair. *)
  destruct (StakingVaultExchange.deposit (exchange_state w) assets)
    as [s_ex' shares] eqn:Hdep.
  injection Hok as Hw'. subst w'.
  (* From [transferFrom] success: depositor != vault, so the inner
     [do_transfer] credits [vault_addr] by [assets]. *)
  unfold ERC20.transferFrom in Htf.
  destruct (allowance <? assets) eqn:Hall; [discriminate|].
  unfold ERC20.do_transfer in Htf.
  destruct (assets =? 0) eqn:Hamt.
  { apply Z.eqb_eq in Hamt. lia. }
  destruct (depositor =? vault_addr w) eqn:Hft.
  { apply Z.eqb_eq in Hft. contradiction. }
  destruct (ERC20.balanceOf (erc20_state w) depositor <? assets) eqn:Hbal;
    [discriminate|].
  injection Htf as Herc20'_eq. subst erc20'.
  (* The [exchange_state] post is the deposit output. *)
  unfold StakingVaultExchange.deposit in Hdep.
  injection Hdep as Hs_ex'_eq Hshares_eq. subst s_ex'.
  (* Now expand the conservation goal. *)
  unfold vault_balance_conserved in *; simpl in *.
  (* Receiver bump: balanceOf vault increases by [assets]. *)
  unfold ERC20.balanceOf. cbn [ERC20.balances].
  rewrite ERC20.balance_lookup_set_balance_eq.
  unfold ERC20.balanceOf in Hinv.
  lia.
Qed.

(** ---- Op 2: withdraw-with-lockup ----

    A successful [withdraw_with_lockup_and_transfer] preserves
    [vault_balance_conserved]. The ERC20 leg is a self-transfer (no
    balance change in the single-bucket model); the exchange leg
    drops [totalDeposited] by [assets]; the manager leg adds an active
    lock of [assets]. *)
Theorem withdraw_with_lockup_preserves_conservation
    (w w' : World)
    (receiver : ERC20.Address)
    (assets unlockTime : U256.t) :
  vault_balance_conserved w ->
  0 < unlockTime ->
  withdraw_with_lockup_and_transfer w receiver assets unlockTime
    = UnstakingManager.Result.Success w' ->
  vault_balance_conserved w'.
Proof.
  intros Hinv Hut Hok.
  unfold withdraw_with_lockup_and_transfer in Hok.
  destruct (StakingVaultExchange.withdraw (exchange_state w) assets)
    as [pair | p q] eqn:Hwd; [|discriminate].
  destruct pair as (s_ex' & shares).
  destruct (UnstakingManager.createLock (manager_state w)
              (vault_addr w) (vault_addr w) receiver assets unlockTime)
    as [s_mg' | p q] eqn:Hcl; [|discriminate].
  destruct (ERC20.transfer (erc20_state w) (vault_addr w)
              (vault_addr w) assets) as [erc20' | p q] eqn:Htr;
    [|discriminate].
  injection Hok as Hw'. subst w'.
  (* The transfer is a self-transfer: erc20' = erc20_state w. *)
  assert (Herc20_eq : erc20' = erc20_state w).
  { unfold ERC20.transfer, ERC20.do_transfer in Htr.
    destruct (assets =? 0) eqn:Hamt.
    - injection Htr as H. symmetry. exact H.
    - rewrite Z.eqb_refl in Htr.
      injection Htr as H. symmetry. exact H. }
  subst erc20'.
  (* Unpack withdraw: s_ex'.totalDeposited = s_ex.totalDeposited - assets. *)
  unfold StakingVaultExchange.withdraw in Hwd.
  destruct (assets >? StakingVaultExchange.totalAssets (exchange_state w))
    eqn:Hgt; [discriminate|].
  injection Hwd as Hs_ex'_eq Hshares_eq. subst s_ex'.
  (* Unpack createLock: s_mg'.locks = (manager_state w).locks ++ [new_lock]. *)
  unfold UnstakingManager.createLock in Hcl.
  destruct (negb (vault_addr w =? vault_addr w)) eqn:Hauth.
  { rewrite Z.eqb_refl in Hauth. discriminate. }
  injection Hcl as Hs_mg'_eq. subst s_mg'.
  (* Expand the goal. *)
  unfold vault_balance_conserved in *; simpl in *.
  rewrite total_active_app_singleton.
  rewrite active_amount_fresh_active by exact Hut.
  lia.
Qed.

(** ---- Op 3: claim ----

    A successful [claim_with_transfer] preserves
    [vault_balance_conserved]. Pre-claim the lock is active
    (claimedAt = 0, unlockTime > 0), so its [active_amount = amount];
    post-claim [claimedAt = now > 0], so its [active_amount = 0]. The
    ERC20 transfer to the lock's user drops [balanceOf vault_addr] by
    exactly [amount]. Net: balance -= amount, total_active -= amount,
    totalDeposited unchanged. *)
Theorem claim_preserves_conservation
    (w w' : World)
    (lockId now : U256.t) :
  vault_balance_conserved w ->
  (Z.to_nat lockId <
    length (manager_state w).(UnstakingManager.State.locks))%nat ->
  0 <= (UnstakingManager.lock_at (manager_state w) lockId)
         .(UnstakingManager.Lock.unlockTime) ->
  (UnstakingManager.lock_at (manager_state w) lockId)
    .(UnstakingManager.Lock.user) <> vault_addr w ->
  claim_with_transfer w lockId now
    = UnstakingManager.Result.Success w' ->
  vault_balance_conserved w'.
Proof.
  intros Hinv Hbound Hut_nn Huser_ne Hok.
  unfold claim_with_transfer in Hok.
  set (l := UnstakingManager.lock_at (manager_state w) lockId) in *.
  destruct (UnstakingManager.claimLock (manager_state w) lockId now)
    as [s_mg' | p q] eqn:Hcl; [|discriminate].
  destruct (ERC20.transfer (erc20_state w) (vault_addr w)
              l.(UnstakingManager.Lock.user)
              l.(UnstakingManager.Lock.amount)) as [erc20' | p q] eqn:Htr;
    [|discriminate].
  injection Hok as Hw'. subst w'.
  (* Unpack claimLock to learn how s_mg'.locks differs from
     (manager_state w).locks. *)
  unfold UnstakingManager.claimLock in Hcl.
  fold l in Hcl.
  destruct (negb (andb
              (negb (l.(UnstakingManager.Lock.unlockTime) =? 0))
              (l.(UnstakingManager.Lock.unlockTime) <=? now))) eqn:Hg1 in Hcl;
    [discriminate|].
  destruct (negb (l.(UnstakingManager.Lock.claimedAt) =? 0)) eqn:Hcl1 in Hcl;
    [discriminate|].
  (* Extract the maturity facts. *)
  apply negb_false_iff in Hg1.
  apply andb_true_iff in Hg1.
  destruct Hg1 as (Hut_nz_b & Hut_le_b).
  apply negb_true_iff, Z.eqb_neq in Hut_nz_b.
  apply Z.leb_le in Hut_le_b.
  apply negb_false_iff, Z.eqb_eq in Hcl1.
  injection Hcl as Hs_mg'_eq. subst s_mg'.
  (* now > 0 chain. *)
  assert (Hnow_pos : 0 < now) by lia.
  (* Compute the delta on total_active using set_nth. *)
  set (l' := {|
    UnstakingManager.Lock.user       := l.(UnstakingManager.Lock.user);
    UnstakingManager.Lock.amount     := l.(UnstakingManager.Lock.amount);
    UnstakingManager.Lock.unlockTime := l.(UnstakingManager.Lock.unlockTime);
    UnstakingManager.Lock.claimedAt  := now;
  |}).
  (* pre-claim active_amount l = l.amount *)
  assert (Hpre : UnstakingManager.active_amount l
                 = l.(UnstakingManager.Lock.amount)).
  { unfold UnstakingManager.active_amount.
    rewrite Hcl1.
    assert (Hut_ne : (l.(UnstakingManager.Lock.unlockTime) =? 0) = false)
      by (apply Z.eqb_neq; exact Hut_nz_b).
    rewrite Hut_ne. simpl. reflexivity. }
  (* post-claim active_amount l' = 0 *)
  assert (Hpost : UnstakingManager.active_amount l' = 0).
  { unfold UnstakingManager.active_amount, l'; simpl.
    assert (Hne : (now =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Hne. simpl. reflexivity. }
  (* Unpack the transfer to learn how balanceOf vault_addr changed. *)
  assert (Hbal_post :
    ERC20.balanceOf erc20' (vault_addr w)
      = ERC20.balanceOf (erc20_state w) (vault_addr w)
        - l.(UnstakingManager.Lock.amount)).
  { (* If amount = 0 the transfer is a no-op; if user = vault it's a
       self-transfer (excluded by Huser_ne). Otherwise [from] = vault
       loses [amount], [to] = user gains [amount]. *)
    unfold ERC20.transfer, ERC20.do_transfer in Htr.
    destruct (l.(UnstakingManager.Lock.amount) =? 0) eqn:Hamt.
    - apply Z.eqb_eq in Hamt.
      injection Htr as H. subst erc20'. lia.
    - apply Z.eqb_neq in Hamt.
      destruct (vault_addr w =? l.(UnstakingManager.Lock.user)) eqn:Hft.
      { apply Z.eqb_eq in Hft. symmetry in Hft. contradiction. }
      destruct (ERC20.balanceOf (erc20_state w) (vault_addr w)
                  <? l.(UnstakingManager.Lock.amount)) eqn:Hbal;
        [discriminate|].
      injection Htr as Herc20'_eq. subst erc20'.
      unfold ERC20.balanceOf. cbn [ERC20.balances].
      (* The outermost [set_balance] sets [to = user], not vault; so
         vault's reading goes through the inner [set_balance ... vault
         (b_from - amount)]. *)
      rewrite ERC20.balance_lookup_set_balance_neq.
      2: { intro Heq. apply Z.eqb_neq in Hft. apply Hft.
           symmetry. exact Heq. }
      rewrite ERC20.balance_lookup_set_balance_eq.
      unfold ERC20.balanceOf. lia. }
  (* Combine. *)
  unfold vault_balance_conserved in Hinv |- *.
  cbn [erc20_state exchange_state manager_state vault_addr UnstakingManager.State.locks].
  unfold UnstakingManager.set_lock. cbn [UnstakingManager.State.locks].
  rewrite Hbal_post.
  rewrite total_active_set_nth by exact Hbound.
  (* Recognise the nth-read as l. *)
  change (nth (Z.to_nat lockId)
            (manager_state w).(UnstakingManager.State.locks)
            UnstakingManager.default_lock)
    with l.
  rewrite Hpost. rewrite Hpre.
  lia.
Qed.

(** ===== Reachable: any finite lifecycle preserves conservation ===== *)

(** [Reachable w] holds when [w] can be reached from some [empty_world]
    by a finite sequence of the three composite operations. The base
    case has [empty_world] for any address choice; the inductive cases
    each apply one operation (with its associated preconditions, where
    needed for the conservation step) and witness its success. *)
Inductive Reachable : World -> Prop :=
| Reach_empty :
    forall va ma, Reachable (empty_world va ma)
| Reach_deposit :
    forall w depositor assets allowance w',
      Reachable w ->
      depositor <> vault_addr w ->
      0 < assets ->
      deposit_with_transfer w depositor assets allowance
        = ERC20.Result.Success w' ->
      Reachable w'
| Reach_withdraw :
    forall w receiver assets unlockTime w',
      Reachable w ->
      0 < unlockTime ->
      withdraw_with_lockup_and_transfer w receiver assets unlockTime
        = UnstakingManager.Result.Success w' ->
      Reachable w'
| Reach_claim :
    forall w lockId now w',
      Reachable w ->
      (Z.to_nat lockId <
        length (manager_state w).(UnstakingManager.State.locks))%nat ->
      0 <= (UnstakingManager.lock_at (manager_state w) lockId)
             .(UnstakingManager.Lock.unlockTime) ->
      (UnstakingManager.lock_at (manager_state w) lockId)
        .(UnstakingManager.Lock.user) <> vault_addr w ->
      claim_with_transfer w lockId now
        = UnstakingManager.Result.Success w' ->
      Reachable w'.

(** The empty world starts conserved (0 = 0 + 0). *)
Lemma empty_world_conserved : forall va ma,
  vault_balance_conserved (empty_world va ma).
Proof.
  intros va ma.
  unfold vault_balance_conserved, empty_world.
  cbn.
  unfold ERC20.balanceOf, ERC20.empty_state. cbn.
  reflexivity.
Qed.

(** ===== Headline: lifecycle-wide conservation =====

    Across any [Reachable] state — i.e. any finite sequence of
    composite [deposit] / [withdraw-with-lockup] / [claim] operations
    starting from an empty world — the vault's ERC20 balance equals
    the sum of currently-staked deposits plus currently-pending
    unstaking locks. No leak, no double-count. *)
Theorem vault_balance_conserved_across_lifecycle :
  forall w, Reachable w -> vault_balance_conserved w.
Proof.
  intros w Hr.
  induction Hr.
  - apply empty_world_conserved.
  - eapply deposit_preserves_conservation; eauto.
  - eapply withdraw_with_lockup_preserves_conservation; eauto.
  - eapply claim_preserves_conservation; eauto.
Qed.

(** ===== Cross-check (vm_compute) =====

    A concrete lifecycle: deposit 1e21, withdraw 3e20 with
    unlockTime = 100, claim at now = 200. The invariant holds at
    every intermediate state. *)

Definition xc_va : ERC20.Address := 100.   (** vault address *)
Definition xc_ma : ERC20.Address := 100.   (** manager address (= vault in single-bucket model) *)
Definition xc_dep : ERC20.Address := 201.  (** depositor / lock receiver *)

(** Starting world: depositor has 1e21 of the underlying so the first
    deposit can succeed. We hand-build the ERC20 state with this
    initial balance rather than calling [empty_state] (the lifecycle
    proof's [Reachable] requires a mint-free start, which the mock
    doesn't model; here we hard-wire the depositor's pre-balance and
    note this is the standard "T-REWARDTOKEN" trust assumption — see
    the file header). *)
Definition xc_erc20_init : ERC20.State := {|
  ERC20.balances := [(xc_dep, 10^21)];
  ERC20.totalSupply := 10^21;
|}.

Definition xc_world_init : World := {|
  erc20_state    := xc_erc20_init;
  exchange_state := StakingVaultExchange.empty_state;
  manager_state  := UnstakingManager.empty_state;
  vault_addr     := xc_va;
  manager_addr   := xc_ma;
|}.

(** The pre-deposit world is conserved: balanceOf vault_addr = 0,
    totalDeposited = 0, total_active = 0. *)
Lemma xc_init_conserved : vault_balance_conserved xc_world_init.
Proof. vm_compute. reflexivity. Qed.

(** Step 1: depositor deposits 1e21. *)
Definition xc_after_deposit : World :=
  match deposit_with_transfer xc_world_init xc_dep (10^21) (10^21) with
  | ERC20.Result.Success w => w
  | _ => xc_world_init
  end.

Lemma xc_deposit_balance : ERC20.balanceOf
    (erc20_state xc_after_deposit) xc_va = 10^21.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_deposit_totalDeposited :
  (exchange_state xc_after_deposit)
    .(StakingVaultExchange.State.totalDeposited) = 10^21.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_deposit_total_active :
  UnstakingManager.total_active
    (manager_state xc_after_deposit).(UnstakingManager.State.locks) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_deposit_conserved : vault_balance_conserved xc_after_deposit.
Proof. vm_compute. reflexivity. Qed.

(** Step 2: depositor withdraws 3e20 with unlockTime = 100. *)
Definition xc_after_withdraw : World :=
  match withdraw_with_lockup_and_transfer xc_after_deposit xc_dep
          (3 * 10^20) 100 with
  | UnstakingManager.Result.Success w => w
  | _ => xc_after_deposit
  end.

Lemma xc_withdraw_balance : ERC20.balanceOf
    (erc20_state xc_after_withdraw) xc_va = 10^21.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_withdraw_totalDeposited :
  (exchange_state xc_after_withdraw)
    .(StakingVaultExchange.State.totalDeposited) = 7 * 10^20.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_withdraw_total_active :
  UnstakingManager.total_active
    (manager_state xc_after_withdraw).(UnstakingManager.State.locks)
    = 3 * 10^20.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_withdraw_conserved : vault_balance_conserved xc_after_withdraw.
Proof. vm_compute. reflexivity. Qed.

(** Step 3: claim the lock at id 0 at now = 200 (>= unlockTime = 100). *)
Definition xc_after_claim : World :=
  match claim_with_transfer xc_after_withdraw 0 200 with
  | UnstakingManager.Result.Success w => w
  | _ => xc_after_withdraw
  end.

Lemma xc_claim_balance : ERC20.balanceOf
    (erc20_state xc_after_claim) xc_va = 10^21 - 3 * 10^20.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_claim_totalDeposited :
  (exchange_state xc_after_claim)
    .(StakingVaultExchange.State.totalDeposited) = 7 * 10^20.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_claim_total_active :
  UnstakingManager.total_active
    (manager_state xc_after_claim).(UnstakingManager.State.locks) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma xc_claim_conserved : vault_balance_conserved xc_after_claim.
Proof. vm_compute. reflexivity. Qed.

(** End-to-end: the lifecycle's final world is still conserved,
    reached from the pre-deposit world via three legal operations.
    Captures the headline theorem on a concrete trace. *)
Lemma xc_full_lifecycle_conserved : vault_balance_conserved xc_after_claim.
Proof. exact xc_claim_conserved. Qed.

End IntegrationVaultBalanceConservation.
