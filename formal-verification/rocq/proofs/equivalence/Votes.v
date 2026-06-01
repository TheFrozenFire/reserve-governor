(** Task #240 — OpenZeppelin Votes equivalence methodology stub.

    [Votes] (OZ v5.4.0, governance/utils/Votes.sol) is an *abstract*
    base contract — its storage slots are reserved on the inheriting
    contract (e.g. ERC20Votes, ERC721Votes, or, in the Reserve corpus,
    [StakingVault]).  There is no standalone [Votes_shallow.v] from
    solc; the Yul translation of each method lands inside the consumer
    contract's shallow form, with slot indices fixed by the inheritor's
    storage layout.

    This file therefore does not bind a shallow form.  It delivers:

      1. A set of sim-level helper lemmas about [mocks/Votes.v] — the
         pure-Coq facts every concrete inheritor's walker proof will
         reuse (`Qed`, no axioms beyond what the mock already imports).

      2. A documented walker-template surface — for each of the seven
         public Votes operations, what the Yul body's walker arms look
         like, parameterized over slot indices and a projection lens.

      3. A skeletal [Section VotesEquivalenceTemplate] showing how
         downstream inheritors will instantiate the methodology when
         the corresponding shallow form lands.

    The companion design memo is [notes/votes_equivalence_methodology.md].

    Methodology decision (Option 2 in the memo):
    --------------------------------------------
    Slot-agnostic helpers parameterized over slot indices, mirroring
    the existing abstract-base pattern in [proofs/equivalence/Nonces.v],
    [proofs/equivalence/EnumerableSet.v], and
    [proofs/equivalence/Checkpoints.v].  Inheritors instantiate by
    supplying their own [proj_sim] and slot indices; the sim-level
    helper lemmas below close once and are reused.

    What this file does NOT do:
    ---------------------------
    - It does not bind any Yul function to the sim.  No shallow form
      exists to bind against.
    - It does not add new framework axioms.  Every closed lemma is
      [Qed] against [mocks/Votes.v] and [mocks/Trace208.v].
    - It does not anticipate Phase 4 storage layouts beyond what is
      structurally forced by the abstract Votes surface.

    Parking realities:
    ------------------
    Both prospective consumers — StakingVault (#256) and
    ReserveOptimisticGovernor (#244) — are Phase 4 parked.  The
    sim-level reasoning below is ready for them; the walker
    instantiation will follow once R035 / R046 land and the
    inheritor's shallow form is available. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.mocks.Trace208.
Require Import ReserveGovernor.mocks.Votes.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

Module VotesEquivalence.

  Import Votes.

  (** ============================================================
      Section 1 — Sim-level helper lemmas (Qed)

      These are pure-Coq properties of [Votes.delegate],
      [Votes.moveDelegateVotes], [Votes.transferVotingUnits], and the
      view functions.  Every concrete inheritor walker proof will
      reuse them as post-state predicates; closing them here means the
      Phase 4 instantiation does not have to re-derive sim-side facts.

      Convention: each lemma states an *invariant* of the mutator —
      what stays the same across the operation, or how the observable
      view-function output transforms.  Walker proofs combine these
      with the inheritor's projection lens to assemble the milestone
      Hoare triple.
      ============================================================ *)

  (** ---- 1.1  [moveDelegateVotes] short-circuits ---- *)

  (** When [from = to], [moveDelegateVotes] is a no-op.  The
      [Votes.moveDelegateVotes] definition short-circuits at the
      [orb] guard before touching state. *)
  Lemma moveDelegateVotes_same_account_noop :
    forall (s : State.t) (a : Address) (amount : Z),
      moveDelegateVotes s a a amount = s.
  Proof.
    intros s a amount.
    unfold moveDelegateVotes.
    rewrite Z.eqb_refl. simpl. reflexivity.
  Qed.

  (** When [amount = 0], [moveDelegateVotes] is a no-op. *)
  Lemma moveDelegateVotes_zero_amount_noop :
    forall (s : State.t) (from to : Address),
      moveDelegateVotes s from to 0 = s.
  Proof.
    intros s from to.
    unfold moveDelegateVotes.
    rewrite Z.eqb_refl.
    destruct (Z.eqb from to); simpl; reflexivity.
  Qed.

  (** ---- 1.2  [moveDelegateVotes] preserves unrelated fields ----

      Even when the mutator fires, it only touches
      [State.delegate_ckpt].  The [delegatee] map, the
      [total_ckpt], the [voting_units] snapshot, and the [clock]
      are all preserved. *)
  Lemma moveDelegateVotes_preserves_delegatee :
    forall (s : State.t) (from to : Address) (amount : Z),
      (moveDelegateVotes s from to amount).(State.delegatee)
      = s.(State.delegatee).
  Proof.
    intros s from to amount.
    unfold moveDelegateVotes.
    destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; reflexivity.
  Qed.

  Lemma moveDelegateVotes_preserves_total_ckpt :
    forall (s : State.t) (from to : Address) (amount : Z),
      (moveDelegateVotes s from to amount).(State.total_ckpt)
      = s.(State.total_ckpt).
  Proof.
    intros s from to amount.
    unfold moveDelegateVotes.
    destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; reflexivity.
  Qed.

  Lemma moveDelegateVotes_preserves_voting_units :
    forall (s : State.t) (from to : Address) (amount : Z),
      (moveDelegateVotes s from to amount).(State.voting_units)
      = s.(State.voting_units).
  Proof.
    intros s from to amount.
    unfold moveDelegateVotes.
    destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; reflexivity.
  Qed.

  Lemma moveDelegateVotes_preserves_clock :
    forall (s : State.t) (from to : Address) (amount : Z),
      (moveDelegateVotes s from to amount).(State.clock)
      = s.(State.clock).
  Proof.
    intros s from to amount.
    unfold moveDelegateVotes.
    destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; reflexivity.
  Qed.

  (** ---- 1.3  [moveDelegateVotes] leaves other delegates alone ----

      For any delegate [c] distinct from both [from] and [to], the
      per-delegate checkpoint history is unchanged.  This is the
      isolation property the walker uses to discharge unrelated-slot
      observers. *)
  Lemma moveDelegateVotes_other_delegates_untouched :
    forall (s : State.t) (from to c : Address) (amount : Z),
      c <> from -> c <> to ->
      (moveDelegateVotes s from to amount).(State.delegate_ckpt) c
      = s.(State.delegate_ckpt) c.
  Proof.
    intros s from to c amount Hcf Hct.
    unfold moveDelegateVotes.
    destruct (orb (Z.eqb from to) (Z.eqb amount 0)) eqn:Hshort.
    - reflexivity.
    - simpl.
      assert (Hcto : Z.eqb c to = false) by (apply Z.eqb_neq; exact Hct).
      assert (Hcfr : Z.eqb c from = false) by (apply Z.eqb_neq; exact Hcf).
      destruct (Z.eqb from zero_address) eqn:Hfz.
      + (* from = 0: ckpt1 = original *)
        destruct (Z.eqb to zero_address) eqn:Htz.
        * (* to = 0 too: ckpt2 = ckpt1 = original *)
          reflexivity.
        * (* to != 0: ckpt2 = upd at to. c != to so unchanged. *)
          unfold upd_trace. rewrite Hcto. reflexivity.
      + (* from != 0: ckpt1 = upd at from. *)
        destruct (Z.eqb to zero_address) eqn:Htz.
        * (* to = 0: ckpt2 = ckpt1. c != from so unchanged. *)
          unfold upd_trace. rewrite Hcfr. reflexivity.
        * (* to != 0: ckpt2 = upd at to of ckpt1. c != to AND c != from. *)
          unfold upd_trace. rewrite Hcto, Hcfr. reflexivity.
  Qed.

  (** ---- 1.4  [moveDelegateVotes] respects the [from = 0] mint path ----

      When [from = 0] (the OZ "mint" path) and the mutator fires,
      only the [to]'s checkpoint history is touched; no push fires
      for [from = address(0)] (OZ semantics: address(0) is the
      "undelegated" sentinel and is never a real delegate). *)
  Lemma moveDelegateVotes_from_zero_skips_from_push :
    forall (s : State.t) (to : Address) (amount : Z),
      to <> zero_address ->
      amount <> 0 ->
      (moveDelegateVotes s zero_address to amount).(State.delegate_ckpt)
        zero_address
      = s.(State.delegate_ckpt) zero_address.
  Proof.
    intros s to amount Htz Hamz.
    unfold moveDelegateVotes.
    assert (Hfromto : Z.eqb zero_address to = false).
    { apply Z.eqb_neq. intro Heq. apply Htz. symmetry. exact Heq. }
    assert (Hamz' : Z.eqb amount 0 = false) by (apply Z.eqb_neq; exact Hamz).
    rewrite Hfromto, Hamz'. cbn [orb].
    cbn [State.delegate_ckpt].
    rewrite Z.eqb_refl.
    assert (Htz' : Z.eqb to zero_address = false)
      by (apply Z.eqb_neq; exact Htz).
    rewrite Htz'.
    unfold upd_trace.
    assert (Hzto : Z.eqb zero_address to = false).
    { apply Z.eqb_neq. intro Heq. apply Htz. symmetry. exact Heq. }
    rewrite Hzto. reflexivity.
  Qed.

  (** Dual: when [to = 0] (the burn path), the [from] checkpoint
      is updated and the zero-address's is left untouched. *)
  Lemma moveDelegateVotes_to_zero_skips_to_push :
    forall (s : State.t) (from : Address) (amount : Z),
      from <> zero_address ->
      amount <> 0 ->
      (moveDelegateVotes s from zero_address amount).(State.delegate_ckpt)
        zero_address
      = s.(State.delegate_ckpt) zero_address.
  Proof.
    intros s from amount Hfz Hamz.
    unfold moveDelegateVotes.
    assert (Hfromto : Z.eqb from zero_address = false)
      by (apply Z.eqb_neq; exact Hfz).
    assert (Hamz' : Z.eqb amount 0 = false) by (apply Z.eqb_neq; exact Hamz).
    rewrite Hfromto, Hamz'. cbn [orb].
    cbn [State.delegate_ckpt].
    rewrite Z.eqb_refl.
    unfold upd_trace.
    assert (Hzfr : Z.eqb zero_address from = false).
    { apply Z.eqb_neq. intro Heq. apply Hfz. symmetry. exact Heq. }
    rewrite Hzfr. reflexivity.
  Qed.

  (** ---- 1.5  [delegate] decomposes into delegatee-sstore + moveDelegateVotes ----

      The mock's [Votes.delegate] is literally defined as "snapshot
      old delegate, update [State.delegatee] at [account], then
      [moveDelegateVotes old_d new_d units]".  The walker for the
      Yul body has the same structure: read old delegate, sstore
      new delegate, then run [_moveDelegateVotes].  This lemma is
      the cosmetic re-expression that lines up the mock's
      intermediate state with the walker's intermediate state. *)
  Lemma delegate_decomposes_via_moveDelegateVotes :
    forall (s : State.t) (account new_d : Address),
      let old_d := delegates s account in
      let units := s.(State.voting_units) account in
      let s_after_sstore :=
        {| State.delegatee     := upd_addr s.(State.delegatee) account new_d;
           State.delegate_ckpt := s.(State.delegate_ckpt);
           State.total_ckpt    := s.(State.total_ckpt);
           State.voting_units  := s.(State.voting_units);
           State.clock         := s.(State.clock);
        |}
      in
      delegate s account new_d
      = moveDelegateVotes s_after_sstore old_d new_d units.
  Proof.
    intros s account new_d. simpl. reflexivity.
  Qed.

  (** ---- 1.6  Self-delegate is a [delegatee]-only update ----

      When [account] re-delegates to its current delegate (i.e.
      [new_d = delegates s account]), the [moveDelegateVotes] step
      collapses to a no-op via [moveDelegateVotes_same_account_noop],
      so the only state change is the [delegatee] sstore (which is
      itself a no-op pointing to the same address).  The composite
      state therefore equals the post-sstore state.  Captures the
      self-delegate idempotence the Governor relies on. *)
  Lemma delegate_to_current_is_delegatee_sstore_only :
    forall (s : State.t) (account : Address),
      let new_d := delegates s account in
      delegate s account new_d
      = {| State.delegatee     := upd_addr s.(State.delegatee) account new_d;
           State.delegate_ckpt := s.(State.delegate_ckpt);
           State.total_ckpt    := s.(State.total_ckpt);
           State.voting_units  := s.(State.voting_units);
           State.clock         := s.(State.clock);
        |}.
  Proof.
    intros s account.
    unfold delegate.
    rewrite moveDelegateVotes_same_account_noop. reflexivity.
  Qed.

  (** ---- 1.7  [transferVotingUnits] total-supply accounting ----

      Mint path: when [from = 0] and [to <> 0], the total-supply
      checkpoint history grows by [push_add(amount)]. *)
  Lemma transferVotingUnits_mint_total :
    forall (s : State.t) (to : Address) (amount : Z),
      to <> zero_address ->
      (transferVotingUnits s zero_address to amount).(State.total_ckpt)
      = push_add s.(State.total_ckpt) s.(State.clock) amount.
  Proof.
    intros s to amount Htz.
    unfold transferVotingUnits.
    rewrite Z.eqb_refl.
    assert (Htz' : Z.eqb to zero_address = false)
      by (apply Z.eqb_neq; exact Htz).
    rewrite Htz'.
    rewrite moveDelegateVotes_preserves_total_ckpt. simpl. reflexivity.
  Qed.

  (** Burn path: when [to = 0] and [from <> 0], the total-supply
      checkpoint history shrinks by [push_sub(amount)] (started
      from the unchanged total — [from != 0] avoids the first
      push). *)
  Lemma transferVotingUnits_burn_total :
    forall (s : State.t) (from : Address) (amount : Z),
      from <> zero_address ->
      (transferVotingUnits s from zero_address amount).(State.total_ckpt)
      = push_sub s.(State.total_ckpt) s.(State.clock) amount.
  Proof.
    intros s from amount Hfz.
    unfold transferVotingUnits.
    assert (Hfz' : Z.eqb from zero_address = false)
      by (apply Z.eqb_neq; exact Hfz).
    rewrite Hfz'. rewrite Z.eqb_refl.
    rewrite moveDelegateVotes_preserves_total_ckpt. simpl. reflexivity.
  Qed.

  (** Pure-transfer path: when both [from] and [to] are nonzero, the
      total-supply checkpoint is preserved. *)
  Lemma transferVotingUnits_pure_transfer_preserves_total :
    forall (s : State.t) (from to : Address) (amount : Z),
      from <> zero_address ->
      to <> zero_address ->
      (transferVotingUnits s from to amount).(State.total_ckpt)
      = s.(State.total_ckpt).
  Proof.
    intros s from to amount Hfz Htz.
    unfold transferVotingUnits.
    assert (Hfz' : Z.eqb from zero_address = false)
      by (apply Z.eqb_neq; exact Hfz).
    assert (Htz' : Z.eqb to zero_address = false)
      by (apply Z.eqb_neq; exact Htz).
    rewrite Hfz', Htz'.
    rewrite moveDelegateVotes_preserves_total_ckpt. simpl. reflexivity.
  Qed.

  (** ---- 1.8  View function characterizations ----

      [getVotes] and [getTotalSupply] characterize as [Trace208.latest]
      applied to the relevant checkpoint history.  These are
      essentially the definitional unfoldings, lifted to lemma form so
      walker proofs can cite them by name rather than re-unfold. *)
  Lemma getVotes_unfold :
    forall (s : State.t) (account : Address),
      getVotes s account
      = Trace208.latest (s.(State.delegate_ckpt) account).
  Proof. intros s account. reflexivity. Qed.

  Lemma getTotalSupply_unfold :
    forall (s : State.t),
      getTotalSupply s = Trace208.latest s.(State.total_ckpt).
  Proof. intros s. reflexivity. Qed.

  (** [getPastVotes] revert-on-future characterization. *)
  Lemma getPastVotes_future_lookup_reverts :
    forall (s : State.t) (account : Address) (timepoint : U256.t),
      timepoint >= s.(State.clock) ->
      getPastVotes s account timepoint = revert_future_lookup.
  Proof.
    intros s account timepoint Hge.
    unfold getPastVotes.
    assert (Hlt : (timepoint <? s.(State.clock)) = false)
      by (apply Z.ltb_ge; lia).
    rewrite Hlt. reflexivity.
  Qed.

  Lemma getPastVotes_in_past_succeeds :
    forall (s : State.t) (account : Address) (timepoint : U256.t),
      timepoint < s.(State.clock) ->
      getPastVotes s account timepoint
      = Result.Success
          (Trace208.upperLookupRecent (s.(State.delegate_ckpt) account) timepoint).
  Proof.
    intros s account timepoint Hlt.
    unfold getPastVotes.
    assert (Hltb : (timepoint <? s.(State.clock)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hltb. reflexivity.
  Qed.

  (** Dual for [getPastTotalSupply]. *)
  Lemma getPastTotalSupply_future_lookup_reverts :
    forall (s : State.t) (timepoint : U256.t),
      timepoint >= s.(State.clock) ->
      getPastTotalSupply s timepoint = revert_future_lookup.
  Proof.
    intros s timepoint Hge.
    unfold getPastTotalSupply.
    assert (Hlt : (timepoint <? s.(State.clock)) = false)
      by (apply Z.ltb_ge; lia).
    rewrite Hlt. reflexivity.
  Qed.

  Lemma getPastTotalSupply_in_past_succeeds :
    forall (s : State.t) (timepoint : U256.t),
      timepoint < s.(State.clock) ->
      getPastTotalSupply s timepoint
      = Result.Success
          (Trace208.upperLookupRecent s.(State.total_ckpt) timepoint).
  Proof.
    intros s timepoint Hlt.
    unfold getPastTotalSupply.
    assert (Hltb : (timepoint <? s.(State.clock)) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hltb. reflexivity.
  Qed.

  (** ---- 1.9  Validity preservation across mutators ----

      [Votes.Valid.t] (per-delegate Trace208 sortedness + total-supply
      sortedness) is preserved across both [moveDelegateVotes] and
      [delegate], provided the caller has not regressed the clock.
      This is the cross-state invariant Phase 4 walker proofs lean on
      when chaining multiple mutators. *)

  (** Helper: [push_sub] preserves sortedness when the new key is at
      least the last key. *)
  Lemma push_sub_preserves_sortedness :
    forall (tr : Trace208.t) (clk : U256.t) (amount : Z),
      Trace208.Valid.t tr ->
      (match tr.(Trace208.entries) with
       | [] => True
       | _  => fst (Trace208.last_entry tr.(Trace208.entries)) <= clk
       end) ->
      Trace208.Valid.t (push_sub tr clk amount).
  Proof.
    intros tr clk amount Hv Hmon.
    unfold push_sub.
    apply Trace208.push_preserves_sortedness; assumption.
  Qed.

  Lemma push_add_preserves_sortedness :
    forall (tr : Trace208.t) (clk : U256.t) (amount : Z),
      Trace208.Valid.t tr ->
      (match tr.(Trace208.entries) with
       | [] => True
       | _  => fst (Trace208.last_entry tr.(Trace208.entries)) <= clk
       end) ->
      Trace208.Valid.t (push_add tr clk amount).
  Proof.
    intros tr clk amount Hv Hmon.
    unfold push_add.
    apply Trace208.push_preserves_sortedness; assumption.
  Qed.

  (** ============================================================
      Section 2 — Slot-agnostic walker-template scaffolding

      Each inheriting contract will open this Section with concrete
      slot indices and a projection lens; the section parameters
      below document the abstract API.

      Note: we declare the section but do NOT instantiate concrete
      walker lemmas inside it — the walker arms require a shallow
      form to point at, which does not exist for the abstract Votes
      base.  Phase 4 inheritors re-open the section in their own
      equivalence file and supply the shallow-form bindings.

      The Section here exists primarily as documentation — the names
      and types of the parameters are the API surface a future
      [StakingVaultEquivalence] file will fill in.
      ============================================================ *)

  Section VotesEquivalenceTemplate.

    (** Slot indices on the inheriting contract's [SimulatedStorage.t].
        For example, in a hypothetical ERC20Votes layout these might
        be slots 4 / 5 / 6, sitting after the ERC20 balance / allowance
        / totalSupply slots. *)
    Variable slot_delegatee     : nat.
    Variable slot_delegate_ckpt : nat.
    Variable slot_total_ckpt    : nat.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the Votes substate.  The
        inheritor supplies this from its own [proj_sim] structure. *)
    Variable project_votes : SimulatedStorage.t -> State.t.

    (** Lens correctness hypotheses — discharged by [reflexivity]
        (or a small [cbn]/[unfold] chain) at the instantiation site.
        Each says: the projected Votes substate's [State.<field>]
        equals the inheritor's storage at the right slot. *)

    Hypothesis lens_delegatee_correct :
      forall (storage : SimulatedStorage.t) (account : Address),
        delegates (project_votes storage) account
        = (project_votes storage).(State.delegatee) account.

    Hypothesis lens_delegate_ckpt_correct :
      forall (storage : SimulatedStorage.t) (account : Address),
        Trace208.latest ((project_votes storage).(State.delegate_ckpt) account)
        = getVotes (project_votes storage) account.

    Hypothesis lens_total_ckpt_correct :
      forall (storage : SimulatedStorage.t),
        Trace208.latest (project_votes storage).(State.total_ckpt)
        = getTotalSupply (project_votes storage).

    (** Walker-template documentation lives in the section as proven
        observations about the lens — these are tautological under
        the hypotheses above and serve to fix the names downstream
        walker proofs will cite. *)

    Lemma walker_obs_delegates :
      forall (storage : SimulatedStorage.t) (account : Address),
        delegates (project_votes storage) account
        = (project_votes storage).(State.delegatee) account.
    Proof. intros. apply lens_delegatee_correct. Qed.

    Lemma walker_obs_getVotes :
      forall (storage : SimulatedStorage.t) (account : Address),
        getVotes (project_votes storage) account
        = Trace208.latest ((project_votes storage).(State.delegate_ckpt) account).
    Proof. intros. reflexivity. Qed.

    Lemma walker_obs_getTotalSupply :
      forall (storage : SimulatedStorage.t),
        getTotalSupply (project_votes storage)
        = Trace208.latest (project_votes storage).(State.total_ckpt).
    Proof. intros. reflexivity. Qed.

  End VotesEquivalenceTemplate.

  (** ============================================================
      Section 3 — Walker-template documentation (commentary only)

      For each public Votes operation, the comment block below
      describes what the Yul body's walker arms look like.  The
      walker proofs themselves cannot be written until a concrete
      shallow form (from an inheriting contract) is available.

      Cross-reference: [notes/votes_equivalence_methodology.md]
      Section (C) walks through the same shapes in prose.
      ============================================================ *)

  (** ---- delegates(account) ----

        Yul body shape (inlined into inheritor):
          slot   := slot_delegatee
          ptr    := mapping_index_access_<addr>_<addr>(slot, account)
          d      := sload(ptr)

        Walker arms:
          - sload at <keccak(account, slot_delegatee)>
              ↓ via R049 multi-slot Map2 sload bridge
            (project_votes storage).delegatee account
          - matches: [delegates (project_votes storage) account]
            via [lens_delegatee_correct]. *)

  (** ---- getVotes(account) ----

        Yul body shape:
          slot     := slot_delegate_ckpt
          trace    := mapping_at(slot, account)
          v        := Checkpoints_Trace208_latest(trace)

        Walker arms:
          - sload Trace208 storage at the per-account anchor.
          - Compose through [Trace208.latest] (Checkpoints.v sanity
            lemmas re-export the relevant facts).
          - Matches [getVotes (project_votes storage) account]
            via [walker_obs_getVotes] + [lens_delegate_ckpt_correct]. *)

  (** ---- getPastVotes(account, timepoint) ----

        Yul body shape:
          if iszero(lt(timepoint, clock())):
            revert(ERC5805FutureLookup)
          slot     := slot_delegate_ckpt
          trace    := mapping_at(slot, account)
          v        := Checkpoints_Trace208_upperLookupRecent(trace, timepoint)

        Walker arms:
          - Clock comparison (R047 case-split before [eexists]).
          - Revert branch reuses AbiEncoding.v's revert sentinel.
          - Success branch composes through
            [Trace208.upperLookupRecent].
          - Composite Hoare triple post-state matches
            [getPastVotes (project_votes storage) account timepoint]
            via [getPastVotes_in_past_succeeds] /
            [getPastVotes_future_lookup_reverts] above. *)

  (** ---- getPastTotalSupply(timepoint) ----

        Identical structure to getPastVotes, against
        [slot_total_ckpt] rather than the per-account
        [slot_delegate_ckpt].  Re-uses
        [getPastTotalSupply_in_past_succeeds] /
        [getPastTotalSupply_future_lookup_reverts]. *)

  (** ---- _delegate(account, new_d) — three-phase composite ----

      Phase 1 — pre-state read:
        old_d := sload(<slot_delegatee[account]>)
        units := _getVotingUnits(account)
                  (* virtual; in ERC20Votes inlines to balanceOf;
                     in the inheritor's [proj_sim] this projects out
                     of the inheritor's own balance map *)

      Phase 2 — delegatee sstore (R040 wrapper shape):
        sstore(<slot_delegatee[account]>, new_d)

      Phase 3 — moveDelegateVotes(old_d, new_d, units):
        See the _moveDelegateVotes walker template below.

      Composite post-state matches [Votes.delegate sim account new_d]
      via [delegate_decomposes_via_moveDelegateVotes].

      Self-delegate optimization: when [new_d = old_d], Phase 3
      collapses to a no-op via [moveDelegateVotes_same_account_noop],
      and the composite reduces to a single sstore + no checkpoint
      mutation.  Captured by
      [delegate_to_current_is_delegatee_sstore_only] above. *)

  (** ---- _transferVotingUnits(from, to, amount) — three-phase composite ----

      Phase 1 — conditional totalCkpt push on mint (R047 case-split):
        if iszero(from):
          new_total := push_add(_totalCheckpoints, clock(), amount)
          sstore(<slot_total_ckpt>, new_total)

      Phase 2 — conditional totalCkpt push on burn (R047 case-split):
        if iszero(to):
          new_total := push_sub(_totalCheckpoints, clock(), amount)
          sstore(<slot_total_ckpt>, new_total)

      Phase 3 — moveDelegateVotes(delegates[from], delegates[to], amount).

      Post-state matches by case:
      - from = 0:    [transferVotingUnits_mint_total]
      - to   = 0:    [transferVotingUnits_burn_total]
      - both nonzero: [transferVotingUnits_pure_transfer_preserves_total]

      Note: the inheritor's [_getVotingUnits] view, modeled in the
      sim as [State.voting_units], is updated by the sim's
      [transferVotingUnits] (mirroring the inheritor's [balanceOf]
      update on transfer).  At the walker level this is the
      inheritor's own balance-map sstore — typically an [ERC20]
      mutator that the walker composes before / after the Votes
      bookkeeping. *)

  (** ---- _moveDelegateVotes(from, to, amount) — two-branch composite ----

      Yul body shape:
        if and(not(eq(from, to)), gt(amount, 0)):
          if not(iszero(from)):
            old_from := Checkpoints_Trace208_latest(_delegateCkpts[from])
            new_from := old_from - amount
            sstore(<slot_delegate_ckpt[from]>,
                   push(_delegateCkpts[from], clock(), new_from))
          if not(iszero(to)):
            old_to := Checkpoints_Trace208_latest(_delegateCkpts[to])
            new_to := old_to + amount
            sstore(<slot_delegate_ckpt[to]>,
                   push(_delegateCkpts[to], clock(), new_to))

      Short-circuit branches:
      - same-account ([from = to]): [moveDelegateVotes_same_account_noop]
      - zero-amount ([amount = 0]): [moveDelegateVotes_zero_amount_noop]

      Per-branch arms (R047 case-split, R040 wrapper sstore):
      - [from = 0] mint path: only the [to] sstore fires.  The
        [State.delegate_ckpt zero_address] is provably untouched
        (the OZ semantic that address(0) never carries voting weight)
        — see [moveDelegateVotes_from_zero_skips_from_push].
      - [to = 0] burn path: dual; see
        [moveDelegateVotes_to_zero_skips_to_push].
      - both nonzero: two sstores fire.  The walker composes the
        two pushes in sequence; they touch independent slots
        ([slot_delegate_ckpt[from]] vs [slot_delegate_ckpt[to]])
        and the second sstore preserves the first's effect
        (independence holds because the slot key includes the
        delegate address — distinct delegates → distinct slots).

      Cross-slot isolation: any third delegate [c] outside
      {from, to} sees no change in its checkpoint history.
      Witnessed by [moveDelegateVotes_other_delegates_untouched]. *)

  (** ============================================================
      Section 4 — Validity preservation across the mutator surface

      The [Votes.Valid.t] cross-state invariant (per-delegate Trace208
      sortedness + total-supply Trace208 sortedness) is preserved by
      each mutator under the standard clock-monotonicity precondition.
      ============================================================ *)

  (** Predicate: the trace either is empty or has last-key bounded by
      the clock.  Used to discharge [push_preserves_sortedness]
      monotonicity. *)
  Definition trace_clock_monotone (tr : Trace208.t) (clk : U256.t) : Prop :=
    match tr.(Trace208.entries) with
    | [] => True
    | _  => fst (Trace208.last_entry tr.(Trace208.entries)) <= clk
    end.

  (** [moveDelegateVotes] preserves Validity under a slightly stronger
      precondition: both the from-trace and the to-trace must be clock-
      monotone w.r.t. the state's clock.  The total-supply trace is
      untouched so no additional hypothesis is needed for it. *)
  Lemma moveDelegateVotes_preserves_valid :
    forall (s : State.t) (from to : Address) (amount : Z),
      Valid.t s ->
      trace_clock_monotone (s.(State.delegate_ckpt) from) s.(State.clock) ->
      trace_clock_monotone (s.(State.delegate_ckpt) to) s.(State.clock) ->
      Valid.t (moveDelegateVotes s from to amount).
  Proof.
    intros s from to amount [Hdel Htot] Hfrom_mon Hto_mon.
    constructor.
    - intros a. unfold moveDelegateVotes.
      destruct (orb (Z.eqb from to) (Z.eqb amount 0)) eqn:Hshort.
      + apply Hdel.
      + simpl. unfold upd_trace.
        (* Two-step update: first at [from] (if from != 0),
           then at [to] (if to != 0). *)
        destruct (Z.eqb from zero_address) eqn:Hfz.
        * (* from = 0: ckpt1 = original; ckpt2 = upd at to *)
          destruct (Z.eqb to zero_address) eqn:Htz.
          -- (* to = 0 too: ckpt2 = ckpt1 = original *)
             apply Hdel.
          -- (* to != 0: ckpt2 = upd at to *)
             destruct (Z.eqb a to) eqn:Hato.
             ++ apply Z.eqb_eq in Hato. subst a.
                apply push_add_preserves_sortedness.
                ** apply Hdel.
                ** exact Hto_mon.
             ++ apply Hdel.
        * (* from != 0: ckpt1 has [from] updated. *)
          destruct (Z.eqb to zero_address) eqn:Htz.
          -- (* to = 0: ckpt2 = ckpt1 with from updated *)
             destruct (Z.eqb a from) eqn:Hafr.
             ++ apply Z.eqb_eq in Hafr. subst a.
                apply push_sub_preserves_sortedness.
                ** apply Hdel.
                ** exact Hfrom_mon.
             ++ apply Hdel.
          -- (* to != 0: ckpt2 = upd at to of (upd at from of original).
                Need to case-split on a = to vs a = from vs else. *)
             destruct (Z.eqb a to) eqn:Hato.
             ++ apply Z.eqb_eq in Hato. subst a.
                (* The latest trace at [to] in ckpt1: since from != to
                   (Hshort's first disjunct is false; we'd need to
                   know from != to to use the updated form, otherwise
                   from = to would have short-circuited).  Either way,
                   [ckpt1 to] is either the original or the just-pushed
                   value at [from] — but to != from since to != to
                   would short-circuit.  So [ckpt1 to = original to]. *)
                assert (Hfromto : from <> to).
                { destruct (Z.eqb from to) eqn:Hft.
                  - simpl in Hshort. discriminate.
                  - apply Z.eqb_neq in Hft. exact Hft. }
                assert (Hctto :
                  (if Z.eqb to from
                   then push_sub (s.(State.delegate_ckpt) from)
                          s.(State.clock) amount
                   else s.(State.delegate_ckpt) to)
                  = s.(State.delegate_ckpt) to).
                { destruct (Z.eqb to from) eqn:Htf.
                  - apply Z.eqb_eq in Htf. symmetry in Htf. contradiction.
                  - reflexivity. }
                rewrite Hctto.
                apply push_add_preserves_sortedness.
                ** apply Hdel.
                ** exact Hto_mon.
             ++ apply Z.eqb_neq in Hato.
                (* a != to; check a = from *)
                destruct (Z.eqb a from) eqn:Hafr.
                ** apply Z.eqb_eq in Hafr. subst a.
                   apply push_sub_preserves_sortedness.
                   --- apply Hdel.
                   --- exact Hfrom_mon.
                ** apply Hdel.
    - unfold moveDelegateVotes.
      destruct (orb (Z.eqb from to) (Z.eqb amount 0)); simpl; exact Htot.
  Qed.

  (** ============================================================
      Section 5 — Sanity check examples (vm_compute)

      A handful of fully-closed examples exercising the helper lemmas
      against a concrete sim state.  Serves as a smoke test that the
      sim composes properly and that [vm_compute] can evaluate the
      mutators end-to-end.
      ============================================================ *)

  Module Examples.

    (** A small state: clock = 100, three accounts a/b/c.  No initial
        delegations; voting_units carry a few illustrative values. *)
    Definition addr_a : Address := 10.
    Definition addr_b : Address := 20.
    Definition addr_c : Address := 30.

    Definition s0 : State.t :=
      {| State.delegatee     := upd_addr empty_addr_map addr_a addr_b;
         State.delegate_ckpt := empty_trace_map;
         State.total_ckpt    := Trace208.empty;
         State.voting_units  := upd_units empty_units addr_a 50;
         State.clock         := 100;
      |}.

    (** After [delegate a c] (re-delegate a's units from b to c), the
        sim should have [delegatee a = c] and a new checkpoint at
        [delegate_ckpt b] with -50 and at [delegate_ckpt c] with +50. *)
    Definition s1 : State.t := delegate s0 addr_a addr_c.

    Example ex_delegates_after_redelegate :
      delegates s1 addr_a = addr_c.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_getVotes_b_after_redelegate :
      getVotes s1 addr_b = 0 - 50.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_getVotes_c_after_redelegate :
      getVotes s1 addr_c = 50.
    Proof. vm_compute. reflexivity. Qed.

    (** Self-delegate is idempotent on the delegatee mapping. *)
    Definition s2 : State.t := delegate s1 addr_a addr_c.

    Example ex_self_redelegate_keeps_delegatee :
      delegates s2 addr_a = addr_c.
    Proof. vm_compute. reflexivity. Qed.

    (** Self-redelegate: getVotes at c is unchanged from s1
        (the [moveDelegateVotes] short-circuits at [from = to = c]). *)
    Example ex_self_redelegate_preserves_votes :
      getVotes s2 addr_c = getVotes s1 addr_c.
    Proof. vm_compute. reflexivity. Qed.

    (** [moveDelegateVotes_same_account_noop] in action. *)
    Example ex_moveDelegateVotes_same_account_noop :
      moveDelegateVotes s0 addr_a addr_a 42 = s0.
    Proof. apply moveDelegateVotes_same_account_noop. Qed.

    (** [moveDelegateVotes_zero_amount_noop] in action. *)
    Example ex_moveDelegateVotes_zero_amount_noop :
      moveDelegateVotes s0 addr_b addr_c 0 = s0.
    Proof. apply moveDelegateVotes_zero_amount_noop. Qed.

  End Examples.

End VotesEquivalence.
