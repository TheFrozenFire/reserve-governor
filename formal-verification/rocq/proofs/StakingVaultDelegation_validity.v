(** StakingVaultDelegation validity preservation.

    Backfills the validity tier for the dual-ledger delegation
    simulation. The headline shape invariant is [Valid.state]:

      balances_nn : all balance values are non-negative
      std_valid   : all std-ledger votes are non-negative
      opt_valid   : all opt-ledger votes are non-negative

    The simulation models balances and votes as [Address -> Z] maps,
    so "non-negative" is the discipline that keeps storage faithful
    to the on-chain uint256 typing — anything that would cause an
    underflow on chain shows up as a negative entry in the model.

    Each operation gets a preserves-validity lemma with the
    semantic preconditions made explicit:

      transfer_preserves_validity
        - non-negative amount
        - amount <= balance(from)         (when from is not the mint sink)
        - amount <= std votes(sFrom)      (when sFrom is non-zero)
        - amount <= opt votes(oFrom)      (when oFrom is non-zero)

      set_opt_delegate_preserves_validity
      set_std_delegate_preserves_validity
        - balance(account) <= votes(old delegate)  (when old != 0)

    The deeper invariant [Σ balances = Σ votes (over non-zero delegates)]
    is conservation, not validity; it's proved separately in the
    existing transfer-conservation lemmas. The votes-≥-relevant-balance
    relationship would close those preconditions automatically — it's
    flagged as future work under task #123 (role-auth / global
    invariant threading).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Module StakingVaultDelegationValidity.

Import StakingVaultDelegation.

(** ----- apply_balance preserves non-negativity. ----- *)
Lemma apply_balance_nn
    (b : Map) (from to : Address) (amount : Z) :
  (forall a, 0 <= b a) ->
  0 <= amount ->
  (from = zero_address \/ amount <= b from) ->
  forall a, 0 <= apply_balance b from to amount a.
Proof.
  intros Hnn Ha Hfrom a.
  unfold apply_balance.
  set (b1 := if Z.eqb from zero_address then b
             else upd b from (b from - amount)).
  set (b2 := if Z.eqb to zero_address then b1
             else upd b1 to (b1 to + amount)).
  assert (Hb1 : forall x, 0 <= b1 x).
  { unfold b1. destruct (Z.eqb from zero_address) eqn:Hfz.
    - exact Hnn.
    - apply Z.eqb_neq in Hfz.
      intros x. unfold upd. destruct (Z.eqb x from) eqn:Hxf.
      + apply Z.eqb_eq in Hxf. subst.
        destruct Hfrom as [Heq | Hle]; [contradiction|]. lia.
      + exact (Hnn _). }
  unfold b2. destruct (Z.eqb to zero_address); [exact (Hb1 _)|].
  unfold upd. destruct (Z.eqb a to) eqn:Hat.
  - specialize (Hb1 to). lia.
  - exact (Hb1 _).
Qed.

(** ----- move_votes preserves non-negativity under the natural
    debit precondition. ----- *)
Lemma move_votes_nn
    (v : Map) (from to : Address) (amount : Z) :
  (forall a, 0 <= v a) ->
  0 <= amount ->
  (from = zero_address \/ amount <= v from) ->
  forall a, 0 <= move_votes v from to amount a.
Proof.
  intros Hnn Ha Hfrom a.
  unfold move_votes.
  destruct (orb (Z.eqb from to) (Z.eqb amount 0)) eqn:Hsc.
  - exact (Hnn _).
  - set (v1 := if Z.eqb from zero_address then v
               else upd v from (v from - amount)).
    set (v2 := if Z.eqb to zero_address then v1
               else upd v1 to (v1 to + amount)).
    assert (Hv1 : forall x, 0 <= v1 x).
    { unfold v1. destruct (Z.eqb from zero_address) eqn:Hfz.
      - exact Hnn.
      - apply Z.eqb_neq in Hfz.
        intros x. unfold upd. destruct (Z.eqb x from) eqn:Hxf.
        + apply Z.eqb_eq in Hxf. subst.
          destruct Hfrom as [Heq | Hle]; [contradiction|]. lia.
        + exact (Hnn _). }
    unfold v2. destruct (Z.eqb to zero_address); [exact (Hv1 _)|].
    unfold upd. destruct (Z.eqb a to) eqn:Hat.
    + specialize (Hv1 to). lia.
    + exact (Hv1 _).
Qed.

(** ----- transfer_preserves_validity.

    Phrased on the simulation's level: the storage shape stays
    valid as long as the inputs respect non-negativity and the
    natural debit-balance / debit-votes preconditions on each
    ledger.

    The std / opt symmetry means the same lemma applies to both
    ledgers (only the [delegate_of] target differs). ----- *)
Lemma transfer_preserves_validity
    (s : State.t) (from to : Address) (amount : Z) :
  Valid.state s ->
  0 <= amount ->
  (from = zero_address \/ amount <= s.(State.balances) from) ->
  (let sFrom := delegate_of s.(State.std) from in
   sFrom = zero_address \/ amount <= s.(State.std).(Ledger.votes) sFrom) ->
  (let oFrom := delegate_of s.(State.opt) from in
   oFrom = zero_address \/ amount <= s.(State.opt).(Ledger.votes) oFrom) ->
  Valid.state (transfer s from to amount).
Proof.
  intros Hv Ha Hbal Hstd Hopt.
  destruct Hv as [Hbnn Hstdv Hoptv].
  destruct Hstdv as [Hstd_nn].
  destruct Hoptv as [Hopt_nn].
  unfold transfer.
  constructor; simpl.
  - apply apply_balance_nn; assumption.
  - constructor; simpl.
    intros a. apply move_votes_nn; assumption.
  - constructor; simpl.
    intros a. apply move_votes_nn; assumption.
Qed.

(** ----- set_opt_delegate_preserves_validity.

    Re-pointing a delegate moves the full current
    [balanceOf(account)] from the old delegate's votes to the new.
    For votes_nn to survive, we need: when the old delegate is
    non-zero, [balance(account) <= votes(old_delegate)]. This is
    the same shape as the transfer-side debit precondition. ----- *)
Lemma set_opt_delegate_preserves_validity
    (s : State.t) (account new_d : Address) :
  Valid.state s ->
  (let old_d := delegate_of s.(State.opt) account in
   old_d = zero_address \/
   s.(State.balances) account <= s.(State.opt).(Ledger.votes) old_d) ->
  Valid.state (set_opt_delegate s account new_d).
Proof.
  intros Hv Hold.
  destruct Hv as [Hbnn Hstdv Hoptv].
  destruct Hoptv as [Hopt_nn].
  unfold set_opt_delegate.
  constructor; simpl.
  - exact Hbnn.
  - exact Hstdv.
  - constructor; simpl.
    intros a. apply move_votes_nn; [exact Hopt_nn| exact (Hbnn _) | exact Hold].
Qed.

(** ----- set_std_delegate_preserves_validity. Same shape, std side. ----- *)
Lemma set_std_delegate_preserves_validity
    (s : State.t) (account new_d : Address) :
  Valid.state s ->
  (let old_d := delegate_of s.(State.std) account in
   old_d = zero_address \/
   s.(State.balances) account <= s.(State.std).(Ledger.votes) old_d) ->
  Valid.state (set_std_delegate s account new_d).
Proof.
  intros Hv Hold.
  destruct Hv as [Hbnn Hstdv Hoptv].
  destruct Hstdv as [Hstd_nn].
  unfold set_std_delegate.
  constructor; simpl.
  - exact Hbnn.
  - constructor; simpl.
    intros a. apply move_votes_nn; [exact Hstd_nn| exact (Hbnn _) | exact Hold].
  - exact Hoptv.
Qed.

End StakingVaultDelegationValidity.
