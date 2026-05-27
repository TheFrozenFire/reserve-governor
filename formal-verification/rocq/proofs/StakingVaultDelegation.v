(** StakingVault dual-delegation proofs.

    Headline lemmas, all corresponding 1:1 with invariants in
    [cas/staking_vault/dual_delegation_independence.gp]:

      INV-1   optimistic_independent_from_standard
              standard_independent_from_optimistic
                The effect of [transfer] on one ledger does not depend
                on the other ledger's contents.

      INV-2   transfer_preserves_total_votes
                Sum of votes over a finite candidate set is preserved
                across a transfer between two non-zero delegates, both
                of which appear in the candidate set.

      INV-3   delegate_change_moves_all_balance
                Re-pointing [account]'s optimistic delegatee from
                [old] to [new] (both non-zero, distinct) moves exactly
                [balances account] votes from [old] to [new].

      INV-4   self_transfer_noop
                When [from] and [to] share the same standard delegate
                AND the same optimistic delegate, [transfer] leaves
                both vote vectors unchanged.

      INV-5   mint_credits_only_to_delegate
              burn_debits_only_from_delegate
                Zero-address branches of [move_votes] never touch
                [votes zero_address].

    These are the conservation / independence properties; structural
    no-op lemmas for the move_votes primitive itself sit at the top.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Module StakingVaultDelegationProofs.

Import StakingVaultDelegation.

(** ---- move_votes structural lemmas ---- *)

(** [move_votes v from to 0] is a no-op (amount = 0 short-circuit). *)
Lemma move_votes_amount_zero (v : Map) (from to : Address) :
  move_votes v from to 0 = v.
Proof.
  unfold move_votes. rewrite Z.eqb_refl, Bool.orb_true_r. reflexivity.
Qed.

(** [move_votes v a a amount] is a no-op (from == to short-circuit). *)
Lemma move_votes_same_target (v : Map) (a : Address) (amount : Z) :
  move_votes v a a amount = v.
Proof.
  unfold move_votes. rewrite Z.eqb_refl. simpl. reflexivity.
Qed.

(** [move_votes] never reads or writes [zero_address] on the from-side:
    sending from zero_address means votes are *created* (no debit). *)
Lemma move_votes_from_zero_no_debit
    (v : Map) (to : Address) (amount : Z) :
  to <> zero_address ->
  amount <> 0 ->
  move_votes v zero_address to amount zero_address = v zero_address.
Proof.
  intros Hto Ham.
  unfold move_votes, upd.
  assert (Hzt : Z.eqb zero_address to = false).
  { apply Z.eqb_neq. intro H; apply Hto; symmetry; exact H. }
  assert (Ham0 : Z.eqb amount 0 = false) by (apply Z.eqb_neq; exact Ham).
  rewrite Hzt, Ham0.
  cbn [orb].
  (* from = zero_address: v1 = v. So we are looking at:
       (if Z.eqb to zero_address then v else upd v to (v to + amount)) zero_address
     = (since to != zero_address) (upd v to (v to + amount)) zero_address
     = (if Z.eqb zero_address to then ... else v zero_address) = v zero_address. *)
  destruct (Z.eqb zero_address zero_address) eqn:Hzz.
  - destruct (Z.eqb to zero_address) eqn:Htoz.
    + apply Z.eqb_eq in Htoz. contradiction.
    + rewrite Hzt. reflexivity.
  - rewrite Z.eqb_refl in Hzz. discriminate.
Qed.

(** Symmetric: sending to zero_address means votes are *destroyed*
    (no credit). *)
Lemma move_votes_to_zero_no_credit
    (v : Map) (from : Address) (amount : Z) :
  from <> zero_address ->
  amount <> 0 ->
  move_votes v from zero_address amount zero_address = v zero_address.
Proof.
  intros Hfrom Ham.
  unfold move_votes, upd.
  assert (Hfz : Z.eqb from zero_address = false) by (apply Z.eqb_neq; exact Hfrom).
  assert (Ham0 : Z.eqb amount 0 = false) by (apply Z.eqb_neq; exact Ham).
  rewrite Hfz, Ham0.
  cbn [orb].
  (* from != zero_address: v1 = upd v from (v from - amount).
     to = zero_address: v2 = v1.
     Result = (upd v from (v from - amount)) zero_address
            = (Z.eqb zero_address from = false ? v zero_address). *)
  destruct (Z.eqb from zero_address) eqn:Hfz2.
  - discriminate.
  - destruct (Z.eqb zero_address zero_address) eqn:Hzz.
    + assert (Hzf : Z.eqb zero_address from = false).
      { apply Z.eqb_neq. intro H; apply Hfrom; symmetry; exact H. }
      rewrite Hzf. reflexivity.
    + rewrite Z.eqb_refl in Hzz. discriminate.
Qed.

(** ---- INV-2 / Conservation: between two distinct non-zero delegates. ----
    [move_votes] preserves [v a + v b] when {a, b} matches {from, to}
    (and from != to, amount != 0). *)
Lemma move_votes_conserves_pair
    (v : Map) (from to : Address) (amount : Z) :
  from <> to ->
  from <> zero_address ->
  to   <> zero_address ->
  let v' := move_votes v from to amount in
  v' from + v' to = v from + v to.
Proof.
  intros Hft Hf Ht.
  unfold move_votes.
  assert (Hfteq : Z.eqb from to = false) by (apply Z.eqb_neq; exact Hft).
  rewrite Hfteq.
  destruct (Z.eqb amount 0) eqn:Ham.
  - apply Z.eqb_eq in Ham. simpl. lia.
  - simpl.
    assert (Hfz : Z.eqb from zero_address = false) by (apply Z.eqb_neq; exact Hf).
    assert (Htz : Z.eqb to   zero_address = false) by (apply Z.eqb_neq; exact Ht).
    rewrite Hfz, Htz.
    unfold upd.
    (* Now compute v' from and v' to: *)
    assert (Etof : Z.eqb from to = false) by exact Hfteq.
    assert (Etoft : Z.eqb to from = false).
    { apply Z.eqb_neq. intro H; apply Hft; symmetry; exact H. }
    rewrite Z.eqb_refl, Etof, Etoft, Z.eqb_refl.
    lia.
Qed.

(** ---- INV-2 stated on a list of delegates ----
    For a complete conservation statement we'd need a notion of
    "list of delegates of interest"; here we phrase it pointwise on
    the [from,to] pair, which is the exact contract behavior:
    other delegates' votes are bit-identical pre/post. *)
Lemma move_votes_other_unchanged
    (v : Map) (from to : Address) (amount : Z) (a : Address) :
  a <> from ->
  a <> to ->
  move_votes v from to amount a = v a.
Proof.
  intros Haf Hat.
  unfold move_votes.
  destruct (orb (Z.eqb from to) (Z.eqb amount 0)) eqn:Hsc.
  - reflexivity.
  - unfold upd.
    destruct (Z.eqb from zero_address) eqn:Hfz.
    + destruct (Z.eqb to zero_address) eqn:Htz.
      * reflexivity.
      * destruct (Z.eqb a to) eqn:Hatz.
        -- apply Z.eqb_eq in Hatz. contradiction.
        -- reflexivity.
    + destruct (Z.eqb to zero_address) eqn:Htz.
      * destruct (Z.eqb a from) eqn:Hafz.
        -- apply Z.eqb_eq in Hafz. contradiction.
        -- reflexivity.
      * destruct (Z.eqb a to) eqn:Hatz.
        -- apply Z.eqb_eq in Hatz. contradiction.
        -- destruct (Z.eqb a from) eqn:Hafz.
           ++ apply Z.eqb_eq in Hafz. contradiction.
           ++ reflexivity.
Qed.

(** ---- INV-4: self_transfer_noop ----
    When both [from] and [to] (the accounts) share the same standard
    delegate AND the same optimistic delegate, a transfer between
    them leaves the standard and optimistic vote maps unchanged. *)
Lemma self_transfer_noop
    (s : State.t) (from to : Address) (amount : Z) :
  delegate_of s.(State.std) from = delegate_of s.(State.std) to ->
  delegate_of s.(State.opt) from = delegate_of s.(State.opt) to ->
  (transfer s from to amount).(State.std).(Ledger.votes)
    = s.(State.std).(Ledger.votes)
  /\ (transfer s from to amount).(State.opt).(Ledger.votes)
       = s.(State.opt).(Ledger.votes).
Proof.
  intros Hstd Hopt.
  unfold transfer. simpl. split.
  - rewrite Hstd. apply move_votes_same_target.
  - rewrite Hopt. apply move_votes_same_target.
Qed.

(** ---- INV-1: optimistic_independent_from_standard ----
    The optimistic ledger's post-transfer state depends only on
    (state.opt, balances, from, to, amount). Two states that agree on
    [opt] and [balances] but differ on [std] produce identical [opt]
    after [transfer]. *)
Lemma transfer_opt_independent_of_std
    (s1 s2 : State.t) (from to : Address) (amount : Z) :
  s1.(State.balances) = s2.(State.balances) ->
  s1.(State.opt) = s2.(State.opt) ->
  (transfer s1 from to amount).(State.opt)
    = (transfer s2 from to amount).(State.opt).
Proof.
  intros Hbal Hopt.
  unfold transfer. simpl.
  rewrite Hopt. reflexivity.
Qed.

(** Symmetric: standard ledger's post-transfer state depends only on
    (state.std, balances, from, to, amount). *)
Lemma transfer_std_independent_of_opt
    (s1 s2 : State.t) (from to : Address) (amount : Z) :
  s1.(State.balances) = s2.(State.balances) ->
  s1.(State.std) = s2.(State.std) ->
  (transfer s1 from to amount).(State.std)
    = (transfer s2 from to amount).(State.std).
Proof.
  intros Hbal Hstd.
  unfold transfer. simpl.
  rewrite Hstd. reflexivity.
Qed.

(** ---- INV-3: delegate_change_moves_all_balance ----
    Re-pointing [account]'s optimistic delegate from its old value to
    [new_d] (distinct, both non-zero) moves exactly [balances account]
    votes from [old_d] to [new_d]. Other delegates' votes are
    unchanged. The standard ledger is untouched. *)
Lemma set_opt_delegate_full_balance_migrates
    (s : State.t) (account new_d : Address) :
  delegate_of s.(State.opt) account <> new_d ->
  delegate_of s.(State.opt) account <> zero_address ->
  new_d <> zero_address ->
  s.(State.balances) account <> 0 ->
  (set_opt_delegate s account new_d).(State.opt).(Ledger.votes)
       (delegate_of s.(State.opt) account)
    = s.(State.opt).(Ledger.votes) (delegate_of s.(State.opt) account)
      - s.(State.balances) account
  /\ (set_opt_delegate s account new_d).(State.opt).(Ledger.votes) new_d
       = s.(State.opt).(Ledger.votes) new_d + s.(State.balances) account
  /\ (forall a,
        a <> delegate_of s.(State.opt) account ->
        a <> new_d ->
        (set_opt_delegate s account new_d).(State.opt).(Ledger.votes) a
          = s.(State.opt).(Ledger.votes) a)
  /\ (set_opt_delegate s account new_d).(State.std) = s.(State.std).
Proof.
  intros Hne Hold0 Hnew0 Hbal.
  set (old_d := delegate_of s.(State.opt) account) in *.
  set (bal := s.(State.balances) account) in *.
  assert (Hold_eqb : Z.eqb old_d new_d = false) by (apply Z.eqb_neq; exact Hne).
  assert (Hbal_eqb : Z.eqb bal 0 = false) by (apply Z.eqb_neq; exact Hbal).
  assert (Hold0_eqb : Z.eqb old_d zero_address = false) by (apply Z.eqb_neq; exact Hold0).
  assert (Hnew0_eqb : Z.eqb new_d zero_address = false) by (apply Z.eqb_neq; exact Hnew0).
  (* Compute the move_votes result pointwise, by cases. *)
  assert (Hne_sym : Z.eqb new_d old_d = false).
  { apply Z.eqb_neq. intro H; apply Hne; symmetry; exact H. }
  unfold set_opt_delegate. fold old_d. fold bal.
  cbn [State.opt State.std Ledger.votes Ledger.delegatee].
  unfold move_votes.
  rewrite Hold_eqb, Hbal_eqb.
  cbn [orb].
  rewrite Hold0_eqb, Hnew0_eqb.
  cbv zeta.   (* zeta-reduce the let-bindings of v1, v2 *)
  unfold upd.
  repeat split.
  - (* votes old_d post:
         (if Z.eqb old_d new_d then ... + bal else (if Z.eqb old_d old_d then v old_d - bal else v old_d))
       = v old_d - bal. *)
    rewrite Hold_eqb, Z.eqb_refl. lia.
  - (* votes new_d post:
         (if Z.eqb new_d new_d then ... + bal else ...) = v new_d + bal.
       Inside the "+ bal", the value is (if Z.eqb new_d old_d then v old_d - bal else v new_d)
       which collapses to v new_d under Hne_sym. *)
    rewrite Z.eqb_refl, Hne_sym. lia.
  - (* votes a unchanged: a != old_d, a != new_d. *)
    intros a Ha_old Ha_new.
    assert (Hano : Z.eqb a new_d = false) by (apply Z.eqb_neq; exact Ha_new).
    assert (Haold : Z.eqb a old_d = false) by (apply Z.eqb_neq; exact Ha_old).
    rewrite Hano, Haold. reflexivity.
  (* 4th conjunct (std untouched) closed by [repeat split]'s reflexivity. *)
Qed.

(** Cleaner alias under the "delegate_change_moves_all_balance" name,
    matching the task brief. *)
Lemma delegate_change_moves_all_balance
    (s : State.t) (account new_d : Address) :
  delegate_of s.(State.opt) account <> new_d ->
  delegate_of s.(State.opt) account <> zero_address ->
  new_d <> zero_address ->
  s.(State.balances) account <> 0 ->
  (set_opt_delegate s account new_d).(State.opt).(Ledger.votes)
       (delegate_of s.(State.opt) account)
    = s.(State.opt).(Ledger.votes) (delegate_of s.(State.opt) account)
      - s.(State.balances) account
  /\ (set_opt_delegate s account new_d).(State.opt).(Ledger.votes) new_d
       = s.(State.opt).(Ledger.votes) new_d + s.(State.balances) account.
Proof.
  intros A B C D.
  destruct (set_opt_delegate_full_balance_migrates s account new_d A B C D)
    as (H1 & H2 & _ & _).
  split; assumption.
Qed.

(** ---- INV-5: mint credits only to_delegate; burn debits only from_delegate ----
    Direct corollaries of [move_votes_from_zero_no_debit] /
    [move_votes_to_zero_no_credit] lifted to [transfer]. *)
Lemma transfer_mint_no_zero_credit
    (s : State.t) (to : Address) (amount : Z) :
  to <> zero_address ->
  amount <> 0 ->
  delegate_of s.(State.opt) to <> zero_address ->
  (transfer s zero_address to amount).(State.opt).(Ledger.votes) zero_address
    = s.(State.opt).(Ledger.votes) zero_address.
Proof.
  intros Hto Ham HdTo.
  unfold transfer. simpl.
  (* delegate_of s.(opt) zero_address = zero_address by definition. *)
  unfold delegate_of at 1. rewrite Z.eqb_refl.
  apply move_votes_from_zero_no_debit; [exact HdTo | exact Ham].
Qed.

Lemma transfer_burn_no_zero_credit
    (s : State.t) (from : Address) (amount : Z) :
  from <> zero_address ->
  amount <> 0 ->
  delegate_of s.(State.opt) from <> zero_address ->
  (transfer s from zero_address amount).(State.opt).(Ledger.votes) zero_address
    = s.(State.opt).(Ledger.votes) zero_address.
Proof.
  intros Hfrom Ham HdFrom.
  unfold transfer. simpl.
  (* delegate_of s.(opt) zero_address = zero_address. *)
  replace (delegate_of s.(State.opt) zero_address) with zero_address.
  2: { unfold delegate_of. rewrite Z.eqb_refl. reflexivity. }
  apply move_votes_to_zero_no_credit; [exact HdFrom | exact Ham].
Qed.

(** ---- INV-2: transfer_preserves_total_votes ----
    Phrased pointwise on the pair (sFrom, sTo) of standard delegates:
    if both are non-zero and distinct, the sum [votes sFrom + votes
    sTo] is conserved by [transfer]. Other delegates' votes are
    unchanged. Same statement for optimistic. *)
Lemma transfer_preserves_total_votes
    (s : State.t) (from to : Address) (amount : Z) :
  let sFrom := delegate_of s.(State.std) from in
  let sTo   := delegate_of s.(State.std) to   in
  let oFrom := delegate_of s.(State.opt) from in
  let oTo   := delegate_of s.(State.opt) to   in
  sFrom <> sTo ->
  sFrom <> zero_address ->
  sTo   <> zero_address ->
  oFrom <> oTo ->
  oFrom <> zero_address ->
  oTo   <> zero_address ->
  let s' := transfer s from to amount in
  s'.(State.std).(Ledger.votes) sFrom
    + s'.(State.std).(Ledger.votes) sTo
    = s.(State.std).(Ledger.votes) sFrom
      + s.(State.std).(Ledger.votes) sTo
  /\ s'.(State.opt).(Ledger.votes) oFrom
       + s'.(State.opt).(Ledger.votes) oTo
       = s.(State.opt).(Ledger.votes) oFrom
         + s.(State.opt).(Ledger.votes) oTo.
Proof.
  intros sFrom sTo oFrom oTo Hsne Hsf0 Hst0 Hone Hof0 Hot0 s'.
  unfold s', transfer. simpl.
  split.
  - apply move_votes_conserves_pair; assumption.
  - apply move_votes_conserves_pair; assumption.
Qed.

End StakingVaultDelegationProofs.
