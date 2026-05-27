(** Tier-1 composition: Governor.propose_optimistic composes
    ProposerThrottle + SelectorRegistry.

    The Governor simulation in [simulations/Governor.v] models the
    external surface of [proposeOptimistic] with two oracle
    abstractions:

      - [throttleCharges : U256.t] — an integer feed for the
        proposer-throttle gate (a [<? 1] revert at the boundary),
        modeled in detail by [simulations/ProposerThrottle.v] as
        [proposalsAvailable] of a [Throttle.t].

      - [allow : list (Address * Selector)] — a flat tuple list
        consulted by [allowed_tuple] / [all_calls_allowed], modeled in
        detail by [simulations/SelectorRegistry.v] as
        [State.allowedSelectors] (a per-target map) plus
        [SelectorRegistry.isAllowed].

    Each oracle has its own well-developed proof corpus, but the
    Governor's proofs do not directly link to them. This integration
    file builds the bridge:

      - [proposer_throttle_charges_bridge] turns a [Throttle.t] +
        capacity + now into the [U256.t] the Governor expects. Carries
        the headline equivalence: the Governor's
        [revert_throttle_exceeded] guard fires exactly when
        [ProposerThrottle.consume] would revert.

      - [selector_registry_allowlist_bridge] flattens a
        [SelectorRegistry.State.t] into a [list (Address * Selector)],
        carrying [allowed_tuple flatten = isAllowed] pointwise.

      - Composition theorem
        [propose_optimistic_implies_throttle_consumed_and_selectors_whitelisted]:
        if propose_optimistic succeeds under the bridged oracles, then
        (a) [ProposerThrottle.consume throttle cap now] succeeds and
        (b) [SelectorRegistry.isAllowed registry t s = true] for every
        (t, s) in the call payload.

      - vm_compute cross-check
        [xcheck_concrete_calibration]: a concrete state where throttle
        has charge, selectors are whitelisted, and a specific
        propose_optimistic succeeds; we verify by vm_compute that all
        three component-level predicates hold.

    Modeling decision: we make the bridge tight where the oracle types
    require it (the [throttleCharges] feed is computed as
    [proposalsAvailable], so success/revert agree exactly via INV-5),
    and loose where the Governor erases information the components
    distinguish (the Governor's oracle is a pure [U256.t]
    countdown; the throttle's per-slot leak and the wall-clock refill
    are observable only inside the component). The composition theorem
    states the conjunction of component-level predicates, not the
    full component-level traces — that's the right granularity for a
    Tier-1 integration lemma.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require Import ReserveGovernor.simulations.ProposerThrottle.
Require Import ReserveGovernor.simulations.SelectorRegistry.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Module IntegrationOptimisticPropose.

(** ======================================================================
    1. ProposerThrottle bridge
    ====================================================================== *)

(** [throttle_charges_for_governor] reads the available proposal
    slots for the calling account at [now] under [capacity]. This is
    the [U256.t] the Governor's [propose_optimistic] expects as its
    [throttleCharges] argument. *)
Definition throttle_charges_for_governor
    (throttle : ProposerThrottle.Throttle.t)
    (capacity now : U256.t) : U256.t :=
  ProposerThrottle.proposalsAvailable throttle capacity now.

(** [throttle_oracle_via_proposer_throttle] mirrors the shape of
    [Governor.consume_throttle_oracle] but is driven by the concrete
    [ProposerThrottle.consume]. On success it returns the post-consume
    throttle (so storage can be written back) alongside the new
    available count. On revert the original throttle is preserved by
    convention — the caller would never read it because the operation
    aborted. *)
Definition throttle_oracle_via_proposer_throttle
    (throttle : ProposerThrottle.Throttle.t)
    (capacity now : U256.t)
    : Governor.Result.t (ProposerThrottle.Throttle.t * U256.t) :=
  match ProposerThrottle.consume throttle capacity now with
  | ProposerThrottle.Result.Success throttle' =>
      Governor.Result.Success
        (throttle',
         ProposerThrottle.proposalsAvailable throttle' capacity now)
  | ProposerThrottle.Result.Revert _ _ =>
      Governor.revert_throttle_exceeded
  end.

(** Bridge equivalence: the Governor's pure [U256.t] guard
    [throttleCharges <? 1] fires exactly when [ProposerThrottle.consume]
    would revert. This is the load-bearing fact that ties the two
    simulations together at the propose boundary. *)
Lemma throttle_governor_guard_matches_consume_revert
    (throttle : ProposerThrottle.Throttle.t)
    (capacity now : U256.t) :
  (throttle_charges_for_governor throttle capacity now <? 1) = true
  <-> (exists p s, ProposerThrottle.consume throttle capacity now
                  = ProposerThrottle.Result.Revert p s).
Proof.
  unfold throttle_charges_for_governor, ProposerThrottle.proposalsAvailable,
         ProposerThrottle.consume.
  split.
  - intros Hb.
    rewrite Hb. eexists. eexists. reflexivity.
  - intros (p & s & Hrev).
    destruct ((capacity * ProposerThrottle.readCharge throttle now)
              / ProposerThrottle.FIX_ONE <? 1) eqn:Hb.
    + reflexivity.
    + discriminate.
Qed.

(** Bridge equivalence (positive side): the Governor's
    [throttleCharges >= 1] guard passes exactly when
    [ProposerThrottle.consume] succeeds. *)
Lemma throttle_governor_guard_matches_consume_success
    (throttle : ProposerThrottle.Throttle.t)
    (capacity now : U256.t) :
  1 <= throttle_charges_for_governor throttle capacity now
  <-> (exists throttle', ProposerThrottle.consume throttle capacity now
                       = ProposerThrottle.Result.Success throttle').
Proof.
  unfold throttle_charges_for_governor, ProposerThrottle.proposalsAvailable,
         ProposerThrottle.consume.
  split.
  - intros Hge.
    assert (Hb : (capacity * ProposerThrottle.readCharge throttle now)
                 / ProposerThrottle.FIX_ONE <? 1 = false)
      by (apply Z.ltb_ge; exact Hge).
    rewrite Hb. eexists. reflexivity.
  - intros [t' Hok].
    destruct ((capacity * ProposerThrottle.readCharge throttle now)
              / ProposerThrottle.FIX_ONE <? 1) eqn:Hb.
    + discriminate.
    + apply Z.ltb_ge in Hb. exact Hb.
Qed.

(** ======================================================================
    2. SelectorRegistry bridge
    ====================================================================== *)

(** [flatten_per_target_selectors] turns a per-target selector list
    [(t, [s1; s2; ...])] into the flat tuple list
    [[(t, s1); (t, s2); ...]] consumed by [Governor.allowed_tuple]. *)
Fixpoint flatten_per_target_selectors
    (target : Governor.Address) (sels : list Governor.Selector)
    : list (Governor.Address * Governor.Selector) :=
  match sels with
  | [] => []
  | s :: rest => (target, s) :: flatten_per_target_selectors target rest
  end.

(** [selector_registry_allowlist_bridge] flattens a
    [SelectorRegistry.State.t] into the flat [list (Address * Selector)]
    expected by the Governor.

    We drive the flattening from [State.targets] (which the registry
    guarantees is [NoDup] under [Valid.state]) and look up the selector
    list via [allowed_for] — the same lookup [SelectorRegistry.isAllowed]
    uses. This makes the bridge agree with [isAllowed] pointwise by
    construction, no extra hypotheses needed about the shape of the
    underlying [allowedSelectors] association list. *)
Fixpoint selector_registry_allowlist_bridge_walk
    (targets : list SelectorRegistry.Address)
    (mp : list (SelectorRegistry.Address * list SelectorRegistry.Selector))
    : list (Governor.Address * Governor.Selector) :=
  match targets with
  | [] => []
  | t :: rest =>
      flatten_per_target_selectors t (SelectorRegistry.allowed_for mp t)
        ++ selector_registry_allowlist_bridge_walk rest mp
  end.

Definition selector_registry_allowlist_bridge
    (reg : SelectorRegistry.State.t)
    : list (Governor.Address * Governor.Selector) :=
  selector_registry_allowlist_bridge_walk
    reg.(SelectorRegistry.State.targets)
    reg.(SelectorRegistry.State.allowedSelectors).

(** Helper: [allowed_tuple] of a flattened per-target list agrees with
    [list_contains] of the inner selector list. *)
Lemma allowed_tuple_flatten_per_target
    (target_in : Governor.Address) (sels : list Governor.Selector)
    (target : Governor.Address) (sel : Governor.Selector) :
  Governor.allowed_tuple (flatten_per_target_selectors target_in sels) target sel
  = if target_in =? target
    then SelectorRegistry.list_contains sels sel
    else false.
Proof.
  destruct (target_in =? target) eqn:Ht.
  - (* target_in = target *)
    induction sels as [|s rest IH].
    + reflexivity.
    + cbn [flatten_per_target_selectors Governor.allowed_tuple
           SelectorRegistry.list_contains].
      rewrite Ht. cbn [andb].
      destruct (s =? sel) eqn:Hs.
      * reflexivity.
      * exact IH.
  - (* target_in <> target *)
    induction sels as [|s rest IH].
    + reflexivity.
    + cbn [flatten_per_target_selectors Governor.allowed_tuple
           SelectorRegistry.list_contains].
      rewrite Ht. cbn [andb]. exact IH.
Qed.

(** [allowed_tuple] distributes over the [++] used to concatenate
    per-target flattenings: a tuple is in [a ++ b] iff it is in [a] or
    in [b]. *)
Lemma allowed_tuple_app
    (a b : list (Governor.Address * Governor.Selector))
    (target : Governor.Address) (sel : Governor.Selector) :
  Governor.allowed_tuple (a ++ b) target sel
  = orb (Governor.allowed_tuple a target sel)
        (Governor.allowed_tuple b target sel).
Proof.
  induction a as [|[t' s'] rest IH]; simpl.
  - reflexivity.
  - destruct (andb (t' =? target) (s' =? sel)) eqn:Hand; simpl.
    + reflexivity.
    + exact IH.
Qed.

(** Bridge equivalence: the Governor's [allowed_tuple] applied to a
    [selector_registry_allowlist_bridge_walk] returns [true] iff the
    target is in the walked [targets] list AND the selector is in
    [allowed_for mp target].

    This is the structural lemma; the headline [isAllowed] equivalence
    uses it under the cross-invariant. *)
Lemma allowed_tuple_walk_iff
    (targets : list SelectorRegistry.Address)
    (mp : list (SelectorRegistry.Address * list SelectorRegistry.Selector))
    (target : Governor.Address) (sel : Governor.Selector) :
  Governor.allowed_tuple
    (selector_registry_allowlist_bridge_walk targets mp) target sel
  = andb (SelectorRegistry.list_contains targets target)
         (SelectorRegistry.list_contains
            (SelectorRegistry.allowed_for mp target) sel).
Proof.
  induction targets as [|t' rest IH]; simpl.
  - reflexivity.
  - rewrite allowed_tuple_app.
    rewrite allowed_tuple_flatten_per_target.
    destruct (t' =? target) eqn:Ht.
    + (* t' = target: collapse to allowed_for mp target. *)
      apply Z.eqb_eq in Ht. subst t'.
      rewrite IH.
      destruct (SelectorRegistry.list_contains
                  (SelectorRegistry.allowed_for mp target) sel);
        destruct (SelectorRegistry.list_contains rest target); reflexivity.
    + exact IH.
Qed.

(** Headline bridge equivalence: under the registry's cross-invariant
    (target in [targets] iff [allowed_for] is non-empty for that
    target), the Governor's [allowed_tuple] over the bridged list
    agrees with [SelectorRegistry.isAllowed] pointwise.

    The cross-invariant is part of [SelectorRegistry.Valid.state] —
    every well-formed registry built through the public API satisfies
    it. *)
Lemma allowed_tuple_bridge_eq_isAllowed
    (reg : SelectorRegistry.State.t)
    (target : Governor.Address) (sel : Governor.Selector) :
  SelectorRegistry.cross_invariant reg ->
  Governor.allowed_tuple (selector_registry_allowlist_bridge reg) target sel
  = SelectorRegistry.isAllowed reg target sel.
Proof.
  intros Hcross.
  unfold selector_registry_allowlist_bridge, SelectorRegistry.isAllowed.
  rewrite allowed_tuple_walk_iff.
  (* Goal: list_contains targets target && list_contains (allowed_for ...) sel
           = list_contains (allowed_for ...) sel *)
  destruct (SelectorRegistry.list_contains
              (SelectorRegistry.allowed_for
                 reg.(SelectorRegistry.State.allowedSelectors) target) sel)
           eqn:Hsel.
  - rewrite Bool.andb_true_r.
    (* sel is in allowed_for, so allowed_for is non-empty, so by
       cross_inv, target is in targets. *)
    apply Hcross.
    destruct (SelectorRegistry.allowed_for
                reg.(SelectorRegistry.State.allowedSelectors) target).
    + simpl in Hsel. discriminate.
    + simpl. lia.
  - rewrite Bool.andb_false_r. reflexivity.
Qed.

(** ======================================================================
    3. Composition theorem
    ====================================================================== *)

(** The propose-side "every call in the payload is allowed by the
    selector registry" predicate, walking the parallel target/selector
    lists. *)
Fixpoint all_isAllowed
    (reg : SelectorRegistry.State.t)
    (targets : list Governor.Address) (selectors : list Governor.Selector)
    : bool :=
  match targets, selectors with
  | [], [] => true
  | t :: ts, s :: ss =>
      if SelectorRegistry.isAllowed reg t s
      then all_isAllowed reg ts ss
      else false
  | _, _ => false
  end.

(** Bridge: walking the bridged tuple list with the Governor's
    [all_calls_allowed] is the same as walking the registry with
    [all_isAllowed], under the registry's cross-invariant. *)
Lemma all_calls_allowed_bridge_eq_all_isAllowed
    (reg : SelectorRegistry.State.t)
    (targets : list Governor.Address) (selectors : list Governor.Selector) :
  SelectorRegistry.cross_invariant reg ->
  Governor.all_calls_allowed (selector_registry_allowlist_bridge reg)
                              targets selectors
  = all_isAllowed reg targets selectors.
Proof.
  intros Hcross.
  revert selectors.
  induction targets as [|t ts IH]; intros [|s ss]; simpl; try reflexivity.
  rewrite (allowed_tuple_bridge_eq_isAllowed reg t s Hcross).
  destruct (SelectorRegistry.isAllowed reg t s); simpl.
  - apply IH.
  - reflexivity.
Qed.

(** Composition theorem.

    Premises:
      - [propose_optimistic] succeeds at the Governor surface, with
        the [throttleCharges] feed bridged from a concrete
        [ProposerThrottle.Throttle.t] via [proposalsAvailable], and
        the [allow] tuple list bridged from a concrete
        [SelectorRegistry.State.t] via the flattener.

    Conclusion:
      (a) The same call to [ProposerThrottle.consume throttle cap now]
          would have succeeded (the throttle counter was actually
          consumable at that moment), AND
      (b) Every (target, selector) pair in the call payload satisfies
          [SelectorRegistry.isAllowed registry target selector = true].

    This stitches the Governor's two oracle abstractions to the
    component-level operations they morally represent. The Governor
    proofs already establish that successful propose decrements the
    abstract throttle counter (INV-5) and that the abstract allowlist
    is honored (INV-6); this theorem promotes both to the concrete
    component layer. *)
Lemma propose_optimistic_implies_throttle_consumed_and_selectors_whitelisted
    (pid : U256.t) (proposer : Governor.Address)
    (vetoDelay vetoPeriod vetoThresholdD18 pastSupply now : U256.t)
    (throttle : ProposerThrottle.Throttle.t)
    (capacity : U256.t)
    (targets : list Governor.Address)
    (selectors : list Governor.Selector)
    (reg : SelectorRegistry.State.t)
    (p' : Governor.Proposal.t) :
  SelectorRegistry.cross_invariant reg ->
  Governor.propose_optimistic
    pid proposer vetoDelay vetoPeriod vetoThresholdD18 pastSupply
    (throttle_charges_for_governor throttle capacity now)
    targets selectors
    (selector_registry_allowlist_bridge reg)
    now
  = Governor.Result.Success p' ->
  (exists throttle',
     ProposerThrottle.consume throttle capacity now
     = ProposerThrottle.Result.Success throttle')
  /\ all_isAllowed reg targets selectors = true.
Proof.
  intros Hcross Hok.
  unfold Governor.propose_optimistic in Hok.
  destruct (throttle_charges_for_governor throttle capacity now <? 1) eqn:Hc;
    [discriminate|].
  apply Z.ltb_ge in Hc.
  destruct (Nat.eqb (length targets) 0) eqn:Hlen0; [discriminate|].
  destruct (negb (Governor.lengths_match targets selectors)) eqn:Hlm;
    [discriminate|].
  destruct (negb (Governor.all_calls_allowed
                    (selector_registry_allowlist_bridge reg) targets selectors))
           eqn:Hno; [discriminate|].
  apply negb_false_iff in Hno.
  split.
  - apply throttle_governor_guard_matches_consume_success. exact Hc.
  - rewrite (all_calls_allowed_bridge_eq_all_isAllowed reg targets selectors
              Hcross) in Hno.
    exact Hno.
Qed.

(** ======================================================================
    4. vm_compute cross-check at a concrete calibration
    ====================================================================== *)

(** Concrete calibration:

      - Capacity = 2 proposal slots / 12 hours.
      - Throttle: currentCharge = FIX_ONE (full), lastUpdated = 0.
        → proposalsAvailable = 2.
      - Selector registry: target 20 has selector 1000 whitelisted.
      - Call payload: targets=[20], selectors=[1000].
      - now = 1, well before any deadline.

    We then verify by [vm_compute]:
      (a) The throttle has charge available (proposalsAvailable >= 1).
      (b) Every (target, selector) is whitelisted by isAllowed.
      (c) propose_optimistic under the bridged oracles succeeds. *)

Definition demo_throttle : ProposerThrottle.Throttle.t :=
  {| ProposerThrottle.Throttle.currentCharge := ProposerThrottle.FIX_ONE;
     ProposerThrottle.Throttle.lastUpdated   := 0 |}.

Definition demo_capacity : U256.t := 2.

Definition demo_now : U256.t := 1.

(** A registry built by adding (20, 1000) on top of [empty_state].
    We compute it once and pin the result so [vm_compute] in the
    headline lemma below has minimal work. The forbidden list is
    irrelevant here (target 20 isn't forbidden). *)
Definition demo_registry : SelectorRegistry.State.t :=
  match SelectorRegistry.addSelector
          SelectorRegistry.empty_state [] 20 1000 with
  | SelectorRegistry.Result.Success s => s
  | _ => SelectorRegistry.empty_state
  end.

Definition demo_targets   : list Governor.Address  := [20].
Definition demo_selectors : list Governor.Selector := [1000].

(** Cross-check (a): throttle has at least one proposal slot. *)
Lemma xcheck_concrete_throttle_has_charge :
  1 <= throttle_charges_for_governor demo_throttle demo_capacity demo_now.
Proof. vm_compute. discriminate. Qed.

(** Cross-check (a'): the bridged throttle oracle succeeds. *)
Lemma xcheck_concrete_throttle_consume_succeeds :
  exists throttle',
    ProposerThrottle.consume demo_throttle demo_capacity demo_now
    = ProposerThrottle.Result.Success throttle'.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Cross-check (b): the selector is whitelisted in the registry. *)
Lemma xcheck_concrete_selector_whitelisted :
  SelectorRegistry.isAllowed demo_registry 20 1000 = true.
Proof. vm_compute. reflexivity. Qed.

(** Cross-check (b'): the bridge agrees — the flattened registry
    contains (20, 1000). *)
Lemma xcheck_concrete_bridge_contains_call :
  Governor.allowed_tuple
    (selector_registry_allowlist_bridge demo_registry) 20 1000 = true.
Proof. vm_compute. reflexivity. Qed.

(** Cross-check (c): propose_optimistic under the bridged oracles
    succeeds at this calibration. *)
Lemma xcheck_concrete_propose_optimistic_succeeds :
  exists p',
    Governor.propose_optimistic
      777 1001 100 1000 (Governor.FIX_ONE / 10) 100
      (throttle_charges_for_governor demo_throttle demo_capacity demo_now)
      demo_targets demo_selectors
      (selector_registry_allowlist_bridge demo_registry)
      demo_now
    = Governor.Result.Success p'.
Proof. vm_compute. eexists. reflexivity. Qed.

(** Headline cross-check tying (a) + (b) + (c) together. *)
Lemma xcheck_concrete_calibration :
  (1 <= throttle_charges_for_governor demo_throttle demo_capacity demo_now)
  /\ all_isAllowed demo_registry demo_targets demo_selectors = true
  /\ (exists p',
        Governor.propose_optimistic
          777 1001 100 1000 (Governor.FIX_ONE / 10) 100
          (throttle_charges_for_governor demo_throttle demo_capacity demo_now)
          demo_targets demo_selectors
          (selector_registry_allowlist_bridge demo_registry)
          demo_now
        = Governor.Result.Success p').
Proof.
  split; [|split].
  - exact xcheck_concrete_throttle_has_charge.
  - vm_compute. reflexivity.
  - exact xcheck_concrete_propose_optimistic_succeeds.
Qed.

End IntegrationOptimisticPropose.
