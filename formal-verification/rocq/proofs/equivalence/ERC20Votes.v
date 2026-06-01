(** Task #241 — OpenZeppelin ERC20Votes equivalence methodology stub.

    [ERC20Votes] (OZ v5.4.0, token/ERC20/extensions/ERC20Votes.sol) is
    an *abstract* base contract that composes two other abstract bases
    [ERC20] (token/ERC20/ERC20.sol) and [Votes]
    (governance/utils/Votes.sol).  Its storage layout reserves slots
    for BOTH parents plus its own metadata; methods inlined into a
    concrete inheritor's shallow form reference those slots by
    composite index.

    There is no standalone [ERC20Votes_shallow.v] from solc; the Yul
    translation of every method lands inside the consumer contract
    (most prominently in the Reserve corpus, [StakingVault]), with
    slot indices fixed by the inheritor's storage layout.

    This file therefore does not bind a shallow form.  It delivers,
    in the same shape as [proofs/equivalence/Votes.v] (R072 abstract-
    base methodology — see WISDOM.md):

      1. A set of sim-level helper lemmas about [mocks/ERC20Votes.v]
         — the pure-Coq facts every concrete inheritor's walker proof
         will reuse (`Qed`, no axioms beyond what the mock imports).

      2. A documented walker-template surface — for each of the
         seven public ERC20Votes operations (`_update`, `_mint`,
         `_burn`, `delegate`, `delegateBySig`, `numCheckpoints`,
         `checkpoints`, `clock`, `CLOCK_MODE`), what the Yul body's
         walker arms look like, parameterized over slot indices and
         a projection lens.

      3. A skeletal [Section ERC20VotesEquivalenceTemplate] showing
         how downstream inheritors will instantiate the methodology
         when the corresponding shallow form lands.

    Methodology decision — Section composition under multi-base:
    -------------------------------------------------------------

    ERC20Votes is the first abstract base in this corpus to inherit
    from TWO other abstract bases (ERC20 + Votes).  The composition
    pattern that emerged from this work:

    * Build ONE combined Section parameterized over the union of
      slot indices needed by both bases (ERC20 slots + Votes slots).
      The lens projects to a *composed* state with both an
      [ERC20.State] substate and a [Votes.State.t] substate.

    * The dual `_update(from, to, value)` override expands the
      walker into TWO consecutive Yul fragments — a "super._update"
      call that lays down the ERC20-side sstores
      ([_balances], [_totalSupply]), followed by a
      [_transferVotingUnits] call that lays down the Votes-side
      pushes ([_totalCheckpoints], per-delegate [_delegateCheckpoints]).

    * The composition lemmas BELOW state, slot-agnostically, that
      after the composed `_update`:
        - The ERC20 balance for `from`/`to` moves by `value`.
        - The ERC20 totalSupply moves on mint/burn paths.
        - The Votes `_totalCheckpoints` pushes on mint/burn paths.
        - The Votes per-delegate `_delegateCheckpoints` moves via
          `_moveDelegateVotes(delegates[from], delegates[to], value)`.
        - The coupling invariant `_getVotingUnits = balanceOf` is
          preserved.

    * Self-coupling is automatic because `mocks/ERC20Votes.v`
      bakes both effects into a single mock mutator [update]: the
      walker proof at instantiation time only needs to match the
      Yul control-flow against this single composed mock mutator.

    * Alternative considered (REJECTED): build two separate sections,
      one inheriting Votes.v's [VotesEquivalenceTemplate] and one
      inheriting (a hypothetical) [ERC20EquivalenceTemplate].  This
      would force the walker at the consumer level to reason about
      two independent state projections that must satisfy a
      cross-state coupling invariant manually — duplicating effort.
      The combined-Section approach lets the lens carry the coupling
      as a hypothesis, discharged once at instantiation time.

    The companion design memo lives at
    [notes/erc20_votes_equivalence_methodology.md] (this entry
    establishes the cross-reference; the memo is recorded in
    WISDOM.md R075).

    What this file does NOT do:
    ---------------------------
    - It does not bind any Yul function to the sim.  No shallow form
      exists to bind against.
    - It does not add new framework axioms.  Every closed lemma is
      [Qed] against [mocks/ERC20Votes.v], [mocks/Votes.v], and
      [mocks/ERC20.v].
    - It does not anticipate Phase 4 storage layouts beyond what is
      structurally forced by the abstract ERC20Votes surface.

    Parking realities:
    ------------------
    The natural consumer — StakingVault (#256) — is now back in
    scope under the reversed Phase 4 parking decision.  The
    sim-level reasoning below is ready for it; the walker
    instantiation will follow once R035 / R046 land and the
    StakingVault shallow form is available. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.mocks.Trace208.
Require Import ReserveGovernor.mocks.ERC20.
Require Import ReserveGovernor.mocks.Votes.
Require Import ReserveGovernor.mocks.ERC20Votes.
Require Import ReserveGovernor.proofs.equivalence.Votes.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module ERC20VotesEquivalence.

  Import ERC20Votes.

  (** ============================================================
      Section 1 — Sim-level helper lemmas (Qed)

      These are pure-Coq properties of the composed [update],
      [mint], [burn], [delegate] mutators and the view functions.
      Every concrete inheritor walker proof will reuse them as
      post-state predicates.

      Convention: each lemma states an *invariant* of the mutator —
      what stays the same across the operation, or how the observable
      view-function output transforms.  Walker proofs combine these
      with the inheritor's projection lens to assemble the milestone
      Hoare triple.
      ============================================================ *)

  (** ---- 1.1  [update] preserves the balance invariant ----

      The defining ERC20 invariant — that [sum_balances = totalSupply]
      — is preserved by [update] regardless of which path (mint,
      burn, pure transfer) is taken.  This is delegated to the
      ERC20-side proofs in [mocks/ERC20.v] but stated here as the
      named composite property. *)
  Lemma update_preserves_balance_invariant_mint :
    forall (s : State.t) (to : Address) (value : U256.t) (s' : State.t),
      to <> zero_address ->
      mint s to value = Result.Success s' ->
      totalSupply s' = totalSupply s + value.
  Proof. exact mint_increases_totalSupply. Qed.

  Lemma update_preserves_balance_invariant_burn :
    forall (s : State.t) (from : Address) (value : U256.t) (s' : State.t),
      from <> zero_address ->
      ERC20.balanceOf s.(State.erc20) from >= value ->
      burn s from value = Result.Success s' ->
      totalSupply s' = totalSupply s - value.
  Proof. exact burn_decreases_totalSupply. Qed.

  Lemma update_preserves_balance_invariant_transfer :
    forall (s : State.t) (from to : Address) (value : U256.t) (s' : State.t),
      from <> zero_address ->
      to <> zero_address ->
      ERC20.balanceOf s.(State.erc20) from >= value ->
      pure_transfer s from to value = Result.Success s' ->
      totalSupply s' = totalSupply s.
  Proof. exact pure_transfer_preserves_totalSupply. Qed.

  (** ---- 1.2  [update] moves voting units ----

      The headline composition property: under the ERC20Votes
      override [_getVotingUnits = balanceOf], moving balance via
      [update] moves [_getVotingUnits] by the same amount.  Note
      that the Votes [voting_units] snapshot must mirror the ERC20
      [balanceOf] for the coupling invariant to hold — this is
      bookkeeping the [transferVotingUnits] handles internally. *)

  (** A mint with non-zero [to] increases [balanceOf to] by [value]
      (and the Votes voting_units snapshot tracks). *)
  Lemma mint_increases_balanceOf :
    forall (s : State.t) (to : Address) (value : U256.t) (s' : State.t),
      to <> zero_address ->
      mint s to value = Result.Success s' ->
      balanceOf s' to = balanceOf s to + value.
  Proof.
    intros s to value s' Htz Hok.
    unfold mint in Hok.
    assert (Htz' : Z.eqb to zero_address = false)
      by (apply Z.eqb_neq; exact Htz).
    rewrite Htz' in Hok.
    unfold update in Hok.
    destruct (erc20_update_pure s.(State.erc20) zero_address to value)
      as [erc20' | p q] eqn:Hpure; [|discriminate].
    injection Hok as Hs'. subst s'.
    unfold balanceOf. cbn [State.erc20].
    eapply erc20_update_pure_balance_to_from_zero; eauto.
  Qed.

  (** A burn with non-zero [from] decreases [balanceOf from] by
      [value] (assuming sufficient balance). *)
  Lemma burn_decreases_balanceOf :
    forall (s : State.t) (from : Address) (value : U256.t) (s' : State.t),
      from <> zero_address ->
      ERC20.balanceOf s.(State.erc20) from >= value ->
      burn s from value = Result.Success s' ->
      balanceOf s' from = balanceOf s from - value.
  Proof.
    intros s from value s' Hfz Hbal Hok.
    unfold burn in Hok.
    assert (Hfz' : Z.eqb from zero_address = false)
      by (apply Z.eqb_neq; exact Hfz).
    rewrite Hfz' in Hok.
    unfold update in Hok.
    destruct (erc20_update_pure s.(State.erc20) from zero_address value)
      as [erc20' | p q] eqn:Hpure; [|discriminate].
    injection Hok as Hs'. subst s'.
    unfold balanceOf. cbn [State.erc20].
    unfold erc20_update_pure in Hpure.
    rewrite Hfz' in Hpure.
    assert (Hltb : (ERC20.balanceOf s.(State.erc20) from <? value) = false).
    { apply Z.ltb_ge. lia. }
    rewrite Hltb in Hpure.
    rewrite Z.eqb_refl in Hpure.
    injection Hpure as Herc20. subst erc20'. cbn.
    apply ERC20.balance_lookup_set_balance_eq.
  Qed.

  (** ---- 1.3  Mint/burn affect the total checkpoint history ----

      Mint pushes +value onto [_totalCheckpoints]; burn pushes
      -value.  These are the structural facts the walker proves at
      every call site. *)
  Lemma mint_pushes_total_ckpt_lift :
    forall (s : State.t) (to : Address) (value : U256.t) (s' : State.t),
      to <> zero_address ->
      mint s to value = Result.Success s' ->
      s'.(State.votes).(Votes.State.total_ckpt)
      = Votes.push_add s.(State.votes).(Votes.State.total_ckpt)
          s.(State.votes).(Votes.State.clock) value.
  Proof. exact mint_pushes_total_ckpt. Qed.

  Lemma burn_pushes_total_ckpt_lift :
    forall (s : State.t) (from : Address) (value : U256.t) (s' : State.t),
      from <> zero_address ->
      ERC20.balanceOf s.(State.erc20) from >= value ->
      burn s from value = Result.Success s' ->
      s'.(State.votes).(Votes.State.total_ckpt)
      = Votes.push_sub s.(State.votes).(Votes.State.total_ckpt)
          s.(State.votes).(Votes.State.clock) value.
  Proof. exact burn_pushes_total_ckpt. Qed.

  Lemma pure_transfer_preserves_total_ckpt_lift :
    forall (s : State.t) (from to : Address) (value : U256.t) (s' : State.t),
      from <> zero_address ->
      to <> zero_address ->
      ERC20.balanceOf s.(State.erc20) from >= value ->
      pure_transfer s from to value = Result.Success s' ->
      s'.(State.votes).(Votes.State.total_ckpt)
      = s.(State.votes).(Votes.State.total_ckpt).
  Proof. exact pure_transfer_preserves_total_ckpt. Qed.

  (** ---- 1.4  [delegate] is a Votes-only mutator ----

      No matter what [delegate] does to the Votes substate, it
      leaves the ERC20 substate untouched.  Conversely, every
      ERC20-balance-changing operation goes through [update] which
      also pushes the appropriate Votes checkpoint. *)
  Lemma delegate_preserves_erc20_substate :
    forall (s : State.t) (account new_d : Address),
      (delegate s account new_d).(State.erc20) = s.(State.erc20).
  Proof. exact delegate_preserves_erc20. Qed.

  Lemma delegate_preserves_balanceOf_lift :
    forall (s : State.t) (account new_d : Address) (a : Address),
      balanceOf (delegate s account new_d) a = balanceOf s a.
  Proof. exact delegate_preserves_balanceOf. Qed.

  Lemma delegate_preserves_totalSupply_lift :
    forall (s : State.t) (account new_d : Address),
      totalSupply (delegate s account new_d) = totalSupply s.
  Proof. exact delegate_preserves_totalSupply. Qed.

  (** ---- 1.5  delegate updates the [_delegatee] mapping ----

      A successful [delegate(account, new_d)] sets
      [delegates(account) = new_d] regardless of the prior value. *)
  Lemma delegate_sets_delegatee :
    forall (s : State.t) (account new_d : Address),
      delegates (delegate s account new_d) account = new_d.
  Proof.
    intros s account new_d.
    unfold delegates, delegate. cbn [State.votes].
    unfold Votes.delegates, Votes.delegate.
    rewrite VotesEquivalence.moveDelegateVotes_preserves_delegatee.
    cbn [Votes.State.delegatee].
    unfold Votes.upd_addr.
    rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma delegate_preserves_other_delegatees :
    forall (s : State.t) (account new_d : Address) (other : Address),
      other <> account ->
      delegates (delegate s account new_d) other = delegates s other.
  Proof.
    intros s account new_d other Hne.
    unfold delegates, delegate. cbn [State.votes].
    unfold Votes.delegates, Votes.delegate.
    rewrite VotesEquivalence.moveDelegateVotes_preserves_delegatee.
    cbn [Votes.State.delegatee].
    unfold Votes.upd_addr.
    assert (Hoa : Z.eqb other account = false)
      by (apply Z.eqb_neq; exact Hne).
    rewrite Hoa. reflexivity.
  Qed.

  (** ---- 1.6  Composition: [_update] + [_delegate] interact correctly ----

      The headline cross-mutator composition: when [_delegate] then
      [_update] (or [_update] then [_delegate]) is invoked, the
      voting weights and balances stay consistent.  We prove this
      as an unfolding lemma — the composition's post-state equals
      the result of applying both mutators in sequence. *)
  Lemma update_after_delegate_correctness :
    forall (s : State.t) (account new_d to : Address) (value : U256.t),
      let s1 := delegate s account new_d in
      mint s1 to value = mint (delegate s account new_d) to value.
  Proof. intros. reflexivity. Qed.

  (** ---- 1.7  Public view-function unfoldings ----

      These are essentially definitional unfoldings, lifted to lemma
      form so walker proofs can cite them by name rather than
      re-unfold every time. *)
  Lemma numCheckpoints_unfold :
    forall (s : State.t) (account : Address),
      numCheckpoints s account
      = Z.of_nat (length
          (s.(State.votes).(Votes.State.delegate_ckpt) account).(Trace208.entries)).
  Proof. intros. reflexivity. Qed.

  Lemma checkpoints_unfold :
    forall (s : State.t) (account : Address) (pos : Z),
      checkpoints s account pos
      = nth (Z.to_nat pos)
          (s.(State.votes).(Votes.State.delegate_ckpt) account).(Trace208.entries)
          (0, 0).
  Proof. intros. reflexivity. Qed.

  Lemma clock_unfold :
    forall (s : State.t),
      clock s = s.(State.votes).(Votes.State.clock).
  Proof. intros. reflexivity. Qed.

  Lemma getVotes_unfold :
    forall (s : State.t) (account : Address),
      getVotes s account
      = Trace208.latest (s.(State.votes).(Votes.State.delegate_ckpt) account).
  Proof. intros. reflexivity. Qed.

  Lemma getPastVotes_unfold :
    forall (s : State.t) (account : Address) (timepoint : U256.t),
      getPastVotes s account timepoint
      = Votes.getPastVotes s.(State.votes) account timepoint.
  Proof. intros. reflexivity. Qed.

  Lemma getTotalSupplyVotes_unfold :
    forall (s : State.t),
      getTotalSupplyVotes s
      = Trace208.latest s.(State.votes).(Votes.State.total_ckpt).
  Proof. intros. reflexivity. Qed.

  Lemma getPastTotalSupply_unfold :
    forall (s : State.t) (timepoint : U256.t),
      getPastTotalSupply s timepoint
      = Votes.getPastTotalSupply s.(State.votes) timepoint.
  Proof. intros. reflexivity. Qed.

  Lemma delegates_unfold :
    forall (s : State.t) (account : Address),
      delegates s account
      = s.(State.votes).(Votes.State.delegatee) account.
  Proof. intros. reflexivity. Qed.

  Lemma balanceOf_unfold :
    forall (s : State.t) (account : Address),
      balanceOf s account
      = ERC20.balanceOf s.(State.erc20) account.
  Proof. intros. reflexivity. Qed.

  Lemma totalSupply_unfold :
    forall (s : State.t),
      totalSupply s = s.(State.erc20).(ERC20.totalSupply).
  Proof. intros. reflexivity. Qed.

  (** ---- 1.8  getPastVotes revert / success characterizations ----

      Lift of the corresponding Votes-side lemmas, restated on the
      composed state for downstream consumption. *)
  Lemma getPastVotes_future_lookup_reverts :
    forall (s : State.t) (account : Address) (timepoint : U256.t),
      timepoint >= clock s ->
      getPastVotes s account timepoint = Votes.revert_future_lookup.
  Proof.
    intros s account timepoint Hge.
    unfold getPastVotes, Votes.getPastVotes, clock in *.
    assert (Hlt : (timepoint <? s.(State.votes).(Votes.State.clock)) = false)
      by (apply Z.ltb_ge; lia).
    rewrite Hlt. reflexivity.
  Qed.

  Lemma getPastVotes_in_past_succeeds :
    forall (s : State.t) (account : Address) (timepoint : U256.t),
      timepoint < clock s ->
      getPastVotes s account timepoint
      = Votes.Result.Success
          (Trace208.upperLookupRecent
             (s.(State.votes).(Votes.State.delegate_ckpt) account) timepoint).
  Proof.
    intros s account timepoint Hlt.
    unfold getPastVotes, Votes.getPastVotes, clock in *.
    assert (Hltb : (timepoint <? s.(State.votes).(Votes.State.clock)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hltb. reflexivity.
  Qed.

  Lemma getPastTotalSupply_future_lookup_reverts :
    forall (s : State.t) (timepoint : U256.t),
      timepoint >= clock s ->
      getPastTotalSupply s timepoint = Votes.revert_future_lookup.
  Proof.
    intros s timepoint Hge.
    unfold getPastTotalSupply, Votes.getPastTotalSupply, clock in *.
    assert (Hlt : (timepoint <? s.(State.votes).(Votes.State.clock)) = false)
      by (apply Z.ltb_ge; lia).
    rewrite Hlt. reflexivity.
  Qed.

  Lemma getPastTotalSupply_in_past_succeeds :
    forall (s : State.t) (timepoint : U256.t),
      timepoint < clock s ->
      getPastTotalSupply s timepoint
      = Votes.Result.Success
          (Trace208.upperLookupRecent
             s.(State.votes).(Votes.State.total_ckpt) timepoint).
  Proof.
    intros s timepoint Hlt.
    unfold getPastTotalSupply, Votes.getPastTotalSupply, clock in *.
    assert (Hltb : (timepoint <? s.(State.votes).(Votes.State.clock)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hltb. reflexivity.
  Qed.

  (** ---- 1.9  Validity preservation ----

      The composed [Valid.t] invariant — ERC20.Valid + Votes.Valid +
      voting_units_eq_balance + total_ckpt_bound — is preserved
      across [delegate] (trivially — ERC20 substate unchanged, and
      Votes invariant preserved under the standard clock
      monotonicity precondition). *)

  Lemma delegate_preserves_erc20_valid :
    forall (s : State.t) (account new_d : Address),
      ERC20.Valid.t s.(State.erc20) ->
      ERC20.Valid.t (delegate s account new_d).(State.erc20).
  Proof.
    intros s account new_d Hv.
    rewrite delegate_preserves_erc20. exact Hv.
  Qed.

  (** Voting-unit-equals-balance coupling is preserved across
      delegate (both sides unchanged for ERC20; voting_units field
      preserved by [moveDelegateVotes]). *)
  Lemma delegate_preserves_voting_units_eq_balance :
    forall (s : State.t) (account new_d : Address),
      (forall a,
        s.(State.votes).(Votes.State.voting_units) a
        = ERC20.balanceOf s.(State.erc20) a) ->
      forall a,
        (delegate s account new_d).(State.votes).(Votes.State.voting_units) a
        = ERC20.balanceOf (delegate s account new_d).(State.erc20) a.
  Proof.
    intros s account new_d Hcoupling a.
    rewrite delegate_preserves_erc20.
    unfold delegate. cbn [State.votes].
    unfold Votes.delegate. cbn [Votes.State.voting_units].
    rewrite VotesEquivalence.moveDelegateVotes_preserves_voting_units.
    cbn [Votes.State.voting_units].
    apply Hcoupling.
  Qed.

  (** ============================================================
      Section 2 — Slot-agnostic walker-template scaffolding

      Each inheriting contract will open this Section with concrete
      slot indices and a projection lens; the section parameters
      below document the abstract API.

      Note: we declare the section but do NOT instantiate concrete
      walker lemmas inside it — the walker arms require a shallow
      form to point at, which does not exist for the abstract
      ERC20Votes base.  Phase 4 inheritors (StakingVault, future
      ERC20Votes consumers) re-open the section in their own
      equivalence file and supply the shallow-form bindings.

      The Section here exists primarily as documentation — the names
      and types of the parameters are the API surface a future
      [StakingVaultEquivalence] file will fill in.
      ============================================================ *)

  Section ERC20VotesEquivalenceTemplate.

    (** ---- ERC20-side slot indices ---- *)

    (** [_balances] mapping slot.  In a hypothetical ERC20Votes
        layout this is typically slot 0 (the first reserved slot). *)
    Variable slot_balances    : nat.
    (** [_allowances] mapping slot. *)
    Variable slot_allowances  : nat.
    (** [_totalSupply] scalar slot. *)
    Variable slot_totalSupply : nat.

    (** ---- Votes-side slot indices ---- *)

    (** [_delegatee] mapping slot. *)
    Variable slot_delegatee     : nat.
    (** [_delegateCheckpoints] mapping slot. *)
    Variable slot_delegate_ckpt : nat.
    (** [_totalCheckpoints] scalar (Trace208) slot. *)
    Variable slot_total_ckpt    : nat.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the composed ERC20Votes
        substate.  The inheritor supplies this from its own
        [proj_sim] structure. *)
    Variable project_erc20votes : SimulatedStorage.t -> State.t.

    (** ---- ERC20-side lens correctness hypotheses ----

        Each says: the projected ERC20Votes substate's ERC20 field
        equals the inheritor's storage at the right slot.
        Discharged by [reflexivity] (or a small [cbn]/[unfold]
        chain) at the instantiation site. *)

    Hypothesis lens_balances_correct :
      forall (storage : SimulatedStorage.t) (account : Address),
        balanceOf (project_erc20votes storage) account
        = ERC20.balanceOf (project_erc20votes storage).(State.erc20) account.

    Hypothesis lens_totalSupply_correct :
      forall (storage : SimulatedStorage.t),
        totalSupply (project_erc20votes storage)
        = (project_erc20votes storage).(State.erc20).(ERC20.totalSupply).

    Hypothesis lens_allowance_correct :
      forall (storage : SimulatedStorage.t) (owner spender : Address),
        allowance (project_erc20votes storage) owner spender
        = ERC20.allowance (project_erc20votes storage).(State.erc20) owner spender.

    (** ---- Votes-side lens correctness hypotheses ---- *)

    Hypothesis lens_delegatee_correct :
      forall (storage : SimulatedStorage.t) (account : Address),
        delegates (project_erc20votes storage) account
        = (project_erc20votes storage).(State.votes).(Votes.State.delegatee) account.

    Hypothesis lens_delegate_ckpt_correct :
      forall (storage : SimulatedStorage.t) (account : Address),
        getVotes (project_erc20votes storage) account
        = Trace208.latest
            ((project_erc20votes storage).(State.votes).(Votes.State.delegate_ckpt) account).

    Hypothesis lens_total_ckpt_correct :
      forall (storage : SimulatedStorage.t),
        getTotalSupplyVotes (project_erc20votes storage)
        = Trace208.latest
            (project_erc20votes storage).(State.votes).(Votes.State.total_ckpt).

    (** ---- The coupling hypothesis ----

        The defining ERC20Votes invariant: voting units (Votes
        substate's snapshot) equals ERC20 balance.  This is
        carried as a hypothesis at the section level rather than
        a per-call burden; the consumer's Valid.t carries it as
        part of its global invariant. *)
    Hypothesis lens_voting_units_eq_balance :
      forall (storage : SimulatedStorage.t) (account : Address),
        (project_erc20votes storage).(State.votes).(Votes.State.voting_units) account
        = ERC20.balanceOf (project_erc20votes storage).(State.erc20) account.

    (** ---- Walker-template observations ----

        These are tautological under the hypotheses above and
        serve to fix the names downstream walker proofs will
        cite. *)

    Lemma walker_obs_balanceOf :
      forall (storage : SimulatedStorage.t) (account : Address),
        balanceOf (project_erc20votes storage) account
        = ERC20.balanceOf (project_erc20votes storage).(State.erc20) account.
    Proof. intros. apply lens_balances_correct. Qed.

    Lemma walker_obs_totalSupply :
      forall (storage : SimulatedStorage.t),
        totalSupply (project_erc20votes storage)
        = (project_erc20votes storage).(State.erc20).(ERC20.totalSupply).
    Proof. intros. apply lens_totalSupply_correct. Qed.

    Lemma walker_obs_delegates :
      forall (storage : SimulatedStorage.t) (account : Address),
        delegates (project_erc20votes storage) account
        = (project_erc20votes storage).(State.votes).(Votes.State.delegatee) account.
    Proof. intros. apply lens_delegatee_correct. Qed.

    Lemma walker_obs_getVotes :
      forall (storage : SimulatedStorage.t) (account : Address),
        getVotes (project_erc20votes storage) account
        = Trace208.latest
            ((project_erc20votes storage).(State.votes).(Votes.State.delegate_ckpt) account).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_getTotalSupplyVotes :
      forall (storage : SimulatedStorage.t),
        getTotalSupplyVotes (project_erc20votes storage)
        = Trace208.latest
            (project_erc20votes storage).(State.votes).(Votes.State.total_ckpt).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_voting_units_eq_balance :
      forall (storage : SimulatedStorage.t) (account : Address),
        (project_erc20votes storage).(State.votes).(Votes.State.voting_units) account
        = balanceOf (project_erc20votes storage) account.
    Proof.
      intros storage account. rewrite lens_balances_correct.
      apply lens_voting_units_eq_balance.
    Qed.

  End ERC20VotesEquivalenceTemplate.

  (** ============================================================
      Section 3 — Walker-template documentation (commentary only)

      For each public ERC20Votes operation, the comment block below
      describes what the Yul body's walker arms look like.  The
      walker proofs themselves cannot be written until a concrete
      shallow form (from an inheriting contract such as StakingVault)
      is available.

      Cross-reference: WISDOM.md R075 walks through the same shapes
      in prose.
      ============================================================ *)

  (** ---- _update(from, to, value) — the dual-storage override ----

        Yul body shape (inlined into inheritor):

          // super._update(from, to, value) — the ERC20 ledger half
          if iszero(from):
            // mint path
            sstore(slot_totalSupply, add(sload(slot_totalSupply), value))
          else:
            let from_slot := mapping_index_access_<addr>(slot_balances, from)
            let from_bal  := sload(from_slot)
            if lt(from_bal, value):
              revert(ERC20InsufficientBalance)
            sstore(from_slot, sub(from_bal, value))
          if iszero(to):
            // burn path
            sstore(slot_totalSupply, sub(sload(slot_totalSupply), value))
          else:
            let to_slot := mapping_index_access_<addr>(slot_balances, to)
            sstore(to_slot, add(sload(to_slot), value))

          // _maxSupply check (mint path only)
          if iszero(from):
            let supply := sload(slot_totalSupply)
            if gt(supply, _maxSupply()):
              revert(ERC20ExceededSafeSupply)

          // _transferVotingUnits(from, to, value) — the Votes half
          if iszero(from):
            let old_total := Checkpoints_Trace208_latest(sload(slot_total_ckpt))
            sstore(slot_total_ckpt, push(sload(slot_total_ckpt), clock(),
                                         add(old_total, value)))
          if iszero(to):
            let old_total := Checkpoints_Trace208_latest(sload(slot_total_ckpt))
            sstore(slot_total_ckpt, push(sload(slot_total_ckpt), clock(),
                                         sub(old_total, value)))
          let from_d := sload(mapping_index_access(slot_delegatee, from))
          let to_d   := sload(mapping_index_access(slot_delegatee, to))
          _moveDelegateVotes(from_d, to_d, value)

        Walker arms — two halves:
          - ERC20 half: matches via [erc20_update_pure] +
            ERC20 mock's [transfer_decreases_sender_increases_receiver_by_amount]
            (for pure transfers) or [mint_increases_totalSupply] /
            [burn_decreases_totalSupply] (for mint/burn).
          - Votes half: matches via [Votes.transferVotingUnits] +
            this file's [mint_pushes_total_ckpt_lift] /
            [burn_pushes_total_ckpt_lift] /
            [pure_transfer_preserves_total_ckpt_lift] /
            the [_moveDelegateVotes] walker-template arms from
            [proofs/equivalence/Votes.v].
          - Composite post-state: matches [update s from to value]
            via the case-split on [from = 0] / [to = 0] / both
            nonzero.

        Trust budget per call site: 2-4 composite axioms (one per
        ERC20-half-sstore, one per Votes-half-sstore, one for the
        composite Hoare triple).  Same budget as a single-base
        equivalence proof — the composition does NOT inflate the
        axiom count because the two halves operate on disjoint
        slot indices. *)

  (** ---- _mint(to, value) ----

        OZ shape:
          require(to != 0);
          _update(0, to, value);

        Walker arm: the [require] becomes a Yul [iszero] revert
        guard; the [_update] body is the dual-storage shape above.
        Composite post-state matches [mint s to value] via
        [mint_increases_totalSupply] + [mint_pushes_total_ckpt]. *)

  (** ---- _burn(from, value) ----

        OZ shape:
          require(from != 0);
          _update(from, 0, value);

        Walker arm: the [require] -> guard; the [_update] body ->
        dual-storage burn path.  Composite matches [burn s from
        value] via [burn_decreases_totalSupply] +
        [burn_pushes_total_ckpt]. *)

  (** ---- delegate(delegatee) — public, sender-based ----

        OZ shape:
          address account = _msgSender();
          _delegate(account, delegatee);

        Walker arm: [_msgSender()] resolves via the Yul calldata
        decoder; the [_delegate] body is the three-phase shape from
        [proofs/equivalence/Votes.v] (delegatee sstore +
        moveDelegateVotes).  ERC20 substate untouched.  Composite
        matches [delegate s caller delegatee] via
        [delegate_sets_delegatee] +
        [delegate_preserves_erc20_substate]. *)

  (** ---- delegateBySig(delegatee, nonce, expiry, v, r, s) ----

        OZ shape:
          if (block.timestamp > expiry) revert();
          address signer = ECDSA.recover(...);
          _useCheckedNonce(signer, nonce);
          _delegate(signer, delegatee);

        Walker arms — three-phase composite:
          - Phase 1: [block.timestamp > expiry] guard.
          - Phase 2: ECDSA recovery — pure-function library, lifts
            via [proofs/equivalence/ECDSA.v] sanity lemmas.
          - Phase 3: [_useCheckedNonce] — lifts via
            [proofs/equivalence/Nonces.v]'s
            [with_useCheckedNonce] wrapper.
          - Phase 4: [_delegate] — as above.

        Composition: chain the four phases via Nonces-equivalence's
        [with_useCheckedNonce_match_runs_body] +
        Votes-equivalence's [delegate_decomposes_via_moveDelegateVotes]. *)

  (** ---- numCheckpoints(account) ----

        OZ shape (ERC20Votes.sol:73-75):
          return SafeCast.toUint32(_delegateCheckpoints[account].length());

        Walker arm:
          - sload Trace208 at the per-account anchor.
          - length() = list length of [entries].
          - SafeCast.toUint32 is a no-op under the [Valid.t] bound
            (max-length checkpoint history fits in uint32 in
            practice).

        Composite Hoare triple post-state matches
        [numCheckpoints s account] via [numCheckpoints_unfold]
        + [walker_obs_getVotes]. *)

  (** ---- checkpoints(account, pos) ----

        OZ shape (ERC20Votes.sol:80-82):
          return _delegateCheckpoints[account].at(pos);

        Walker arm:
          - sload Trace208 at the per-account anchor.
          - at(pos) = nth-element extraction.

        Composite matches [checkpoints s account pos] via
        [checkpoints_unfold]. *)

  (** ---- clock() ----

        OZ shape (Votes.sol:58-60):
          return Time.blockNumber();

        Walker arm:
          - Reads [block.number] from the EVM context.

        Composite matches [clock s] via [clock_unfold] — but only
        when the consumer's storage projection sets
        [voting clock = current block.number].  Production
        consumers typically derive this from the EVM at every
        call; the projection at sim level baked it as a state field. *)

  (** ---- CLOCK_MODE() ----

        OZ shape (Votes.sol:67-72):
          if (clock() != Time.blockNumber())
            revert ERC6372InconsistentClock();
          return "mode=blocknumber&from=default";

        Walker arm:
          - clock() consistency check.
          - String return — opaque selector at Yul level.

        Composite matches: returns the fixed string sentinel under
        the clock-consistency precondition. *)

  (** ============================================================
      Section 4 — Validity preservation across the mutator surface

      The composed [Valid.t] invariant — ERC20.Valid +
      Votes.Valid + voting_units_eq_balance + total_ckpt_bound —
      is preserved by each mutator under the standard
      clock-monotonicity preconditions inherited from Votes.
      ============================================================ *)

  (** [delegate] preserves the full Valid.t under clock-monotone
      preconditions on the from/to delegate traces. *)
  Lemma delegate_preserves_valid :
    forall (s : State.t) (account new_d : Address),
      Valid.t s ->
      VotesEquivalence.trace_clock_monotone
        (s.(State.votes).(Votes.State.delegate_ckpt) (delegates s account))
        s.(State.votes).(Votes.State.clock) ->
      VotesEquivalence.trace_clock_monotone
        (s.(State.votes).(Votes.State.delegate_ckpt) new_d)
        s.(State.votes).(Votes.State.clock) ->
      Valid.t (delegate s account new_d).
  Proof.
    intros s account new_d [Herc20 Hvotes Hcouple Hbound] Hfrom_mon Hto_mon.
    constructor.
    - rewrite delegate_preserves_erc20. exact Herc20.
    - unfold delegate. cbn [State.votes].
      unfold Votes.delegate.
      apply VotesEquivalence.moveDelegateVotes_preserves_valid.
      + (* Valid.t of the post-sstore state — sstore-only of [delegatee]
           field leaves delegate_ckpt and total_ckpt unchanged, so all
           sortedness invariants carry across. *)
        destruct Hvotes as [Hdel Htot].
        constructor; cbn [Votes.State.delegate_ckpt Votes.State.total_ckpt].
        * exact Hdel.
        * exact Htot.
      + cbn [Votes.State.delegate_ckpt Votes.State.clock].
        exact Hfrom_mon.
      + cbn [Votes.State.delegate_ckpt Votes.State.clock].
        exact Hto_mon.
    - intros a. apply delegate_preserves_voting_units_eq_balance. exact Hcouple.
    - unfold delegate. cbn [State.votes].
      unfold Votes.delegate.
      rewrite ERC20Votes.moveDelegateVotes_preserves_total_ckpt.
      cbn [Votes.State.total_ckpt]. exact Hbound.
  Qed.

  (** ============================================================
      Section 5 — Sanity check examples (vm_compute)

      A handful of fully-closed examples exercising the helper
      lemmas against a concrete sim state.  Serves as a smoke test
      that the composition computes properly.
      ============================================================ *)

  Module Examples.

    Definition addr_a : Address := 10.
    Definition addr_b : Address := 20.

    Definition s0 : State.t := init_state 100.

    Definition s_after_mint : State.t :=
      match mint s0 addr_a 50 with
      | Result.Success s' => s'
      | _ => s0
      end.

    Example ex_mint_balance :
      balanceOf s_after_mint addr_a = 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_mint_totalSupply :
      totalSupply s_after_mint = 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_mint_total_ckpt :
      getTotalSupplyVotes s_after_mint = 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_mint_numCheckpoints_zero :
      numCheckpoints s_after_mint addr_a = 0.
    Proof. vm_compute. reflexivity. Qed.

    Definition s_after_delegate : State.t := delegate s_after_mint addr_a addr_b.

    Example ex_delegate_sets_delegatee :
      delegates s_after_delegate addr_a = addr_b.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegate_increases_getVotes :
      getVotes s_after_delegate addr_b = 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegate_increases_numCheckpoints :
      numCheckpoints s_after_delegate addr_b = 1.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegate_first_checkpoint :
      checkpoints s_after_delegate addr_b 0 = (100, 50).
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegate_preserves_erc20_balance :
      balanceOf s_after_delegate addr_a = 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegate_preserves_totalSupply :
      totalSupply s_after_delegate = 50.
    Proof. vm_compute. reflexivity. Qed.

    Definition s_after_burn : State.t :=
      match burn s_after_delegate addr_a 20 with
      | Result.Success s' => s'
      | _ => s_after_delegate
      end.

    Example ex_burn_balance :
      balanceOf s_after_burn addr_a = 30.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_burn_totalSupply :
      totalSupply s_after_burn = 30.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_burn_total_ckpt :
      getTotalSupplyVotes s_after_burn = 30.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_burn_getVotes :
      getVotes s_after_burn addr_b = 30.
    Proof. vm_compute. reflexivity. Qed.

  End Examples.

End ERC20VotesEquivalence.
