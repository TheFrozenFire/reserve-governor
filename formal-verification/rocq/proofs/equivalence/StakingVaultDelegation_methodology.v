(** Task #256 + Task #280 — StakingVault dual delegation + BySig
    equivalence methodology.

    ==================================================================
    STATUS (post Task #280 / 2026-05-31 audit response):
        ABSTRACT METHODOLOGY — NOT A CONCRETE INHERITOR
    ==================================================================

    This file is the R051+R072 composite-walker methodology template
    for StakingVault's four delegation entrypoints. The milestone
    theorems in Section 7 (renamed [run_<fn>_equivalent_methodology])
    close inside [Section StakingVaultDelegationSection], whose
    [Variable]s abstract over the entire Hoare-triple carrier
    ([Codes / Env / Walker / State / hoare / make_state]), the
    projection lens ([project_sim]), the per-fn post-state Skolems
    ([proj_post_<fn>]), the concrete walker symbols ([walker_<fn>]),
    and the storage slot indices.

    Because the Section is NEVER instantiated at a concrete
    StakingVault inheritor in this corpus, every milestone is
    FORALL-quantified over those Section variables at Section
    closure. [Print Assumptions run_delegate_equivalent_methodology]
    reveals only [ECDSA.Domain.deployment_id : Set] (plus the mock
    primitives pulled in by the BySig variants); the Hoare-triple
    obligations themselves are universally quantified away. As a
    result, the milestones constrain nothing about the deployed
    StakingVault bytecode on their own — they say "FOR ANY walker /
    lens / post-state Skolem satisfying the Section hypotheses, the
    composition closes." The Section hypotheses are the real trust
    budget; the milestone Qeds are content-free until instantiated.

    The 2026-05-31 adversarial review (skolemization-soundness
    auditor, CCV-2 in [notes/adversarial_review_2026_05_31/
    SYNTHESIS.md]; trust-axiom auditor CRIT-6) identified this
    Section-bound vapor as a CRITICAL audit-honesty concern: a
    reader of [Print Assumptions] would otherwise incorrectly
    conclude the file is closed against the actual contract.

    What this file IS (genuine value):
    ----------------------------------
    A reusable methodology template that:

      - Defines the joined SimState carrier (Section 0).
      - Provides ~22 sim-level Qed lemmas characterizing the four
        delegation mutators field-by-field (Sections 1-3). These
        lemmas are NOT Section-bound — they appear as regular
        top-level Qeds outside the Section, and are genuine
        sim-level results consumed elsewhere (e.g. the validity
        proofs in [proofs/]).
      - Documents the dual-axis Trace208 push composition (R080,
        Section 3.3).
      - Specifies the R051+R072 walker-axiom shape that a future
        concrete inheritor would discharge once the StakingVault
        shallow form is added to the default build tier.

    What this file is NOT:
    ----------------------
      - It is NOT a concrete equivalence claim against the deployed
        StakingVault Yul. The Section hypotheses parameterize the
        walker; no inheritor binds them.
      - It is NOT a milestone in the audit-corpus sense — the
        milestone theorems are abstract templates whose conclusions
        are universally quantified at Section closure.
      - Audit citations of "delegate / delegateBySig equivalence" for
        StakingVault should reference the sim-level Qed lemmas in
        [proofs/StakingVaultDelegation*.v] (which ARE concrete, are
        consumed by [Audit.v], and bind directly to the simulation),
        not this file's Section-bound methodology templates.

    Concrete-inheritor work blocker:
    --------------------------------
    Instantiating the Section requires:
      1. Adding [generated/StakingVault_shallow.v] to the default
         [_RocqProject] tier (currently gated by a build-time flag
         due to ~3-minute compile cost).
      2. Providing the concrete [project_sim : SimulatedStorage.t ->
         SimState.t] lens against StakingVault's storage layout.
      3. Binding the four [walker_<fn>] symbols to the actual Yul
         function identifiers ([fun_delegate_15192] etc.) and
         discharging the four [run_fun_<fn>_at_proj_sim] Hypotheses
         with concrete walker tactics.
    See [WISDOM.md] R080 "Handoff notes for inheritor / Wave 2
    follow-up" for the full instantiation recipe.

    Filename suffix [_methodology] makes the abstract status
    explicit at the filesystem level (renamed in Task #280 from
    [StakingVaultDelegation.v]). The four headline theorems carry
    the [_methodology] suffix on their identifiers so any
    cross-reference from elsewhere in the corpus surfaces the
    abstract nature.

    Cross-reference:
      - [notes/adversarial_review_2026_05_31/SYNTHESIS.md] CCV-2
      - [notes/adversarial_review_2026_05_31/trust_axiom_auditor.md]
        CRIT-6
      - [Audit.v] Caveat-5 (entry: StakingVault delegation
        methodology, not concrete equivalence)
      - [WISDOM.md] R080 (dual-axis Trace208; handoff notes)

    ==================================================================

    Source contract entrypoints documented by the methodology:

      - [delegate(delegatee)]                       — L10063 fun_delegate_15192
      - [delegateOptimistic(delegatee)]             — L10034 fun_delegateOptimistic_422
      - [delegateBySig(delegatee, nonce, expiry,
                        v, r, s)]                   — L9692  fun_delegateBySig_15249
      - [delegateOptimisticBySig(delegatee, nonce, expiry,
                                  v, r, s)]         — L9956  fun_delegateOptimisticBySig_480

    The first pair mutates the standard / optimistic delegate maps
    directly with msg.sender as the account; the second pair gates
    the same mutators behind ECDSA + Nonces + EIP-712 domain checks.
    All four ultimately compose:

      pre-state           --read msg.sender--+
                                              |
      _delegate / _delegateOptimistic         |
        :=                                    v
        (1) read   old_d := sload(<slot_delegatee[acc]>)
        (2) sstore <slot_delegatee[acc]>      := new_d
        (3) read   units := balanceOf(acc)            (* virtual *)
        (4) call   _moveDelegateVotes(old_d, new_d, units)
            or     _moveOptimisticDelegateVotes(old_d, new_d, units)

      _moveDelegateVotes(from, to, amount)
        :=
        (a) short-circuit if [from = to || amount = 0]
        (b) if [from != 0]:
              from_ckpt := sload(<slot_delegate_ckpt[from]>)
              push      := Checkpoints.push(from_ckpt, clock,
                             toUint208(latest(from_ckpt) - amount))
              sstore <slot_delegate_ckpt[from]> := push
        (c) if [to != 0]:
              to_ckpt   := sload(<slot_delegate_ckpt[to]>)
              push      := Checkpoints.push(to_ckpt, clock,
                             toUint208(latest(to_ckpt) + amount))
              sstore <slot_delegate_ckpt[to]> := push

    The optimistic variant is structurally identical at the OZ surface;
    the difference is which storage slot (0x0a for
    [optimisticDelegatees], 0x0b for [optimisticDelegateCheckpoints],
    per the shallow form) it manipulates.

    Methodology (template form — abstract, not instantiated)
    --------------------------------------------------------

    This file documents the R051 + R072 composite-axiom + slot-
    agnostic methodology, following [proofs/equivalence/Votes.v].
    Unlike Votes.v, this file does NOT carry a concrete inheritor
    binding — the Section remains abstract:

      - The [proj_sim] lens projects the StakingVault sim state (with
        both Trace208 histories) into the inheritor's [SimulatedStorage.t].
        Slot indices are Section parameters; concrete inheritors fix
        them via a small [reflexivity] chain at instantiation.

      - The per-entrypoint composite walker axioms ([run_fun_<fn>_at_proj_sim])
        bundle the Yul body's walker into a single Hoare-triple keyed
        on pre-state with the post-state computed from sim. They are
        the audit-time trust obligations; the Section / lens parameters
        scope them across slot choices.

      - The per-entrypoint observational bridge lemmas
        ([proj_sim_<fn>_observes]) connect the sim mutator's
        post-state to the [proj_sim] composition. These close as
        pure-Coq facts at instantiation.

      - The milestone theorems ([run_<fn>_equivalent]) compose the
        axiom + observation to deliver the headline Hoare triple with
        an observationally-equal post-state. Closed by [Qed].

    What this file is NOT:
    ----------------------

      - It is not a direct walker over the StakingVault shallow form.
        The shallow is gated behind a build-time flag (cost ~3 min per
        compile); per the precedent in Votes.v, Nonces.v, ECDSA.v,
        Checkpoints.v we close milestones via composite axioms keyed
        on Hoare triples, and the slot-agnostic lens supports both
        the current shallow form and future re-emissions.

      - It does not duplicate the existing [proofs/StakingVaultDelegation.v]
        independence theorems. Those are sim-side facts that this file
        consumes via [Require Import] of the sim modules.

      - It does not modify Votes.v / Nonces.v / ECDSA.v / Checkpoints.v.
        Those are dependencies; this file consumes them.

    Cross-references:
      - WISDOM R051 (composite-axiom milestone shape)
      - WISDOM R059 (membership equivalence — not needed here; pure
        per-address maps, not OZ EnumerableSet)
      - WISDOM R063 (staticcall composite — not needed here; the
        delegation paths are all internal-call composites)
      - WISDOM R072 (slot-agnostic abstract-base methodology)
      - WISDOM R080 (introduced by this file — dual-axis Trace208 push
        composition at delegation transitions)
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
(** [Require] (NOT [Import]) [proofs.RocqOfSolidity] — we use
    [SimulatedStorage.t] from it via the full qualified name, but
    we don't want to [Import] because that brings in a [State]
    module that shadows our domain's [StakingVaultDelegation.State].
    The full qualified form below preserves both namespaces. *)
Require RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.simulations.StakingVaultDelegationBySig.
Require Import ReserveGovernor.simulations.StakingVaultDelegationCheckpointed.
Require Import ReserveGovernor.proofs.StakingVaultDelegation.
Require Import ReserveGovernor.proofs.StakingVaultDelegationBySig.
Require Import ReserveGovernor.proofs.StakingVaultDelegationCheckpointed.
Require Import ReserveGovernor.mocks.Trace208.
Require Import ReserveGovernor.mocks.ECDSA.
Require Import ReserveGovernor.mocks.Nonces.
Require Import ReserveGovernor.proofs.equivalence.Common.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

(** Bring [SimulatedStorage.t] into top-level scope via an explicit
    module alias — avoids importing the entire [proofs.RocqOfSolidity]
    namespace whose [State] module would shadow
    [StakingVaultDelegation.State]. *)
Module SimulatedStorage := RocqOfSolidity.proofs.RocqOfSolidity.SimulatedStorage.

Module StakingVaultDelegationMethodology.

  (** ==================================================================
      Section 0 — Composite carrier joining all moving parts.

      StakingVault carries five storage axes touched by the delegation
      surface:

        1. [_delegatee]              — standard delegate map (OZ Votes,
                                       slot inherited from ERC20Votes)
        2. [_delegateCheckpoints]    — standard checkpoint history
        3. [optimisticDelegatees]    — slot 0x0a (per shallow form)
        4. [optimisticDelegateCheckpoints] — slot 0x0b
        5. [_nonces]                 — slot inherited from ERC20Permit
                                       (used by delegateBySig +
                                        delegateOptimisticBySig)

      Plus the EIP-712 domain (chain_id + verifying contract address)
      which is opaque at the storage level — its value is fixed by the
      deployment context and read via [_hashTypedDataV4] without an
      explicit sload in the delegation path.

      The combined [SimState.t] below is the Coq carrier; it generalizes
      [StakingVaultDelegationBySig.State.t] by adding the standard-side
      Trace208 history (which the BySig sim doesn't model — that sim
      only tracks the optimistic side because that's what the audit
      cared about).

      Convention: [std_*] for standard-side, [opt_*] for optimistic-
      side; both share the same Trace208 mock semantics. ============ *)

  (** A standalone state record that joins:
        - the dual-delegation latest-side from [StakingVaultDelegation]
        - the optimistic Trace208 history from [StakingVaultDelegationCheckpointed]
        - a parallel standard Trace208 history (modeled here for the
          [delegate] and [delegateBySig] equivalence)
        - the Nonces map from [StakingVaultDelegationBySig]
        - the ECDSA Domain from [StakingVaultDelegationBySig]
        - the clock (block.timestamp) used as the Trace208 push key. *)
  Module SimState.
    Record t : Set := {
      base       : StakingVaultDelegation.State.t;
      std_traces : StakingVaultDelegationCheckpointed.TraceMap;
      opt_traces : StakingVaultDelegationCheckpointed.TraceMap;
      nonces     : Nonces.Map;
      domain     : ECDSA.Domain.t;
      clock      : U256.t;
    }.
  End SimState.

  (** Convenience: empty SimState with a designated domain. *)
  Definition empty_sim
      (chain_id : U256.t) (contract : ECDSA.Address) : SimState.t :=
    {|
      SimState.base       := StakingVaultDelegation.empty_state;
      SimState.std_traces := [];
      SimState.opt_traces := [];
      SimState.nonces     := Nonces.empty;
      SimState.domain     := {|
        ECDSA.Domain.deployment := ECDSA.Domain.staking_vault_id;
        ECDSA.Domain.chain_id   := chain_id;
        ECDSA.Domain.contract   := contract;
      |};
      SimState.clock      := 0;
    |}.

  (** ==================================================================
      Section 1 — Sim-level Qed helpers.

      Lemmas characterizing the four delegation mutators at the sim
      level. They lift the existing [proofs/StakingVaultDelegation.v]
      + [proofs/StakingVaultDelegationCheckpointed.v] +
      [proofs/StakingVaultDelegationBySig.v] facts onto the joined
      [SimState] carrier, and add the dual-axis Trace208 push lemmas
      that the [delegate] path needs (the existing proofs only
      mechanized the optimistic side; we mirror that on the standard
      side here). ================================================== *)

  Import StakingVaultDelegation.

  (** Local notation for the [Address] type — disambiguates from
      [mocks.ECDSA.Address] / [mocks.Nonces.Address] (all of which
      alias to [U256.t], but Coq's Import semantics doesn't pick a
      winner when multiple are in scope). *)
  Local Notation Address := StakingVaultDelegation.Address (only parsing).

  (** Module aliases for [State] and [Ledger] — disambiguates from
      [RocqOfSolidity.proofs.RocqOfSolidity.State] /
      [StakingVaultDelegationBySig.State] /
      [StakingVaultDelegationCheckpointed.State], which all compete
      for the short name [State]. Re-binding to a non-conflicting
      module name keeps [State] / [Ledger] usable in our bodies. *)
  Module State := StakingVaultDelegation.State.
  Module Ledger := StakingVaultDelegation.Ledger.

  (** Re-bind the constants we use repeatedly — the bare [Import]
      above doesn't bring them through cleanly because of the
      multiple competing [State] modules disturbing name resolution.
      We use [Notation] forms (parsing-only) so call sites read like
      the source. *)
  Local Notation upd            := StakingVaultDelegation.upd (only parsing).
  Local Notation upd_addr       := StakingVaultDelegation.upd (only parsing).
  Local Notation set_std_delegate := StakingVaultDelegation.set_std_delegate (only parsing).
  Local Notation set_opt_delegate := StakingVaultDelegation.set_opt_delegate (only parsing).
  Local Notation delegate_of    := StakingVaultDelegation.delegate_of (only parsing).
  Local Notation move_votes     := StakingVaultDelegation.move_votes (only parsing).
  Local Notation zero_address   := StakingVaultDelegation.zero_address (only parsing).
  Local Notation move_votes_same_target :=
    StakingVaultDelegationProofs.move_votes_same_target (only parsing).

  (** ---- 1.1  set_std_delegate / set_opt_delegate decomposition ----

      The base sim's [set_std_delegate] and [set_opt_delegate] each
      perform a single map update and a single [move_votes] step on
      one of the two ledgers, leaving the other untouched. These are
      the sim-side analogs of
      [Votes.delegate_decomposes_via_moveDelegateVotes]. *)

  Lemma set_std_delegate_unfold :
    forall (s : State.t) (account new_d : Address),
      (set_std_delegate s account new_d).(State.std).(Ledger.delegatee)
      = upd s.(State.std).(Ledger.delegatee) account new_d.
  Proof. intros; reflexivity. Qed.

  Lemma set_opt_delegate_unfold :
    forall (s : State.t) (account new_d : Address),
      (set_opt_delegate s account new_d).(State.opt).(Ledger.delegatee)
      = upd s.(State.opt).(Ledger.delegatee) account new_d.
  Proof. intros; reflexivity. Qed.

  (** Standard side is preserved by [set_opt_delegate]. *)
  Lemma set_opt_delegate_preserves_std :
    forall (s : State.t) (account new_d : Address),
      (set_opt_delegate s account new_d).(State.std) = s.(State.std).
  Proof. intros; reflexivity. Qed.

  (** Optimistic side is preserved by [set_std_delegate]. *)
  Lemma set_std_delegate_preserves_opt :
    forall (s : State.t) (account new_d : Address),
      (set_std_delegate s account new_d).(State.opt) = s.(State.opt).
  Proof. intros; reflexivity. Qed.

  (** Balances are never modified by either mutator. *)
  Lemma set_std_delegate_preserves_balances :
    forall (s : State.t) (account new_d : Address),
      (set_std_delegate s account new_d).(State.balances)
      = s.(State.balances).
  Proof. intros; reflexivity. Qed.

  Lemma set_opt_delegate_preserves_balances :
    forall (s : State.t) (account new_d : Address),
      (set_opt_delegate s account new_d).(State.balances)
      = s.(State.balances).
  Proof. intros; reflexivity. Qed.

  (** Self-delegate (re-pointing to the current delegate) on either
      ledger is observationally a no-op on the votes map: the
      [move_votes] step collapses via [move_votes_same_target]. The
      delegatee map updates to the same value it already held; under
      the [upd] convention this leaves the function pointwise equal
      to the original (idempotent at the [account] entry). *)
  Lemma set_std_delegate_self_votes_noop :
    forall (s : State.t) (account : Address),
      let cur := delegate_of s.(State.std) account in
      (set_std_delegate s account cur).(State.std).(Ledger.votes)
      = s.(State.std).(Ledger.votes).
  Proof.
    intros s account.
    unfold set_std_delegate. simpl.
    apply move_votes_same_target.
  Qed.

  Lemma set_opt_delegate_self_votes_noop :
    forall (s : State.t) (account : Address),
      let cur := delegate_of s.(State.opt) account in
      (set_opt_delegate s account cur).(State.opt).(Ledger.votes)
      = s.(State.opt).(Ledger.votes).
  Proof.
    intros s account.
    unfold set_opt_delegate. simpl.
    apply move_votes_same_target.
  Qed.

  (** ---- 1.2  Standard-side checkpointed delegate ----

      The base sim doesn't carry a standard-side Trace208 history,
      but we need to mechanize the [delegate] entrypoint's
      [_moveDelegateVotes] push composition. Define a standard-side
      analog of [set_opt_delegate_checkpointed] here. *)

  Definition set_std_delegate_checkpointed
      (s : State.t)
      (std_traces : StakingVaultDelegationCheckpointed.TraceMap)
      (account new_d : Address) (now : U256.t)
      : (State.t * StakingVaultDelegationCheckpointed.TraceMap) :=
    let old_d := delegate_of s.(State.std) account in
    let base' := set_std_delegate s account new_d in
    let new_votes_old := base'.(State.std).(Ledger.votes) old_d in
    let new_votes_new := base'.(State.std).(Ledger.votes) new_d in
    let trace_old := StakingVaultDelegationCheckpointed.trace_of std_traces old_d in
    let trace_new := StakingVaultDelegationCheckpointed.trace_of std_traces new_d in
    let trace_old' :=
      if Z.eqb old_d zero_address
      then trace_old
      else Trace208.push trace_old now new_votes_old in
    let trace_new' :=
      if Z.eqb new_d zero_address
      then trace_new
      else Trace208.push trace_new now new_votes_new in
    let traces' :=
      if Z.eqb old_d new_d
      then std_traces
      else StakingVaultDelegationCheckpointed.set_trace
             (StakingVaultDelegationCheckpointed.set_trace
                std_traces old_d trace_old')
             new_d trace_new' in
    (base', traces').

  (** ---- 1.3  Per-axis push lemmas mirror the optimistic-side proofs ----

      The CHK-1, CHK-3 statements from
      [StakingVaultDelegationCheckpointed_proofs] carry over to the
      standard side because [set_std_delegate_checkpointed] has the
      same shape as [set_opt_delegate_checkpointed] — the proofs are
      structurally identical. We restate them here for the standard
      side; the optimistic-side versions are re-exported below. *)

  Lemma std_set_preserves_other_traces :
    forall (s : State.t)
           (std_traces : StakingVaultDelegationCheckpointed.TraceMap)
           (account new_d other : Address) (now : U256.t),
      let p := set_std_delegate_checkpointed s std_traces account new_d now in
      let traces' := snd p in
      let old_d := delegate_of s.(State.std) account in
      other <> old_d ->
      other <> new_d ->
      StakingVaultDelegationCheckpointed.trace_of traces' other
      = StakingVaultDelegationCheckpointed.trace_of std_traces other.
  Proof.
    intros s std_traces account new_d other now.
    cbv zeta.
    intros Hne_old Hne_new.
    unfold set_std_delegate_checkpointed. simpl.
    set (old_d := delegate_of s.(State.std) account) in *.
    destruct (Z.eqb old_d new_d) eqn:Hold_eq_new.
    - reflexivity.
    - (* both traces updated, neither matches [other] *)
      rewrite (StakingVaultDelegationCheckpointed.trace_of_set_trace_other
                 _ new_d other _ Hne_new).
      rewrite (StakingVaultDelegationCheckpointed.trace_of_set_trace_other
                 _ old_d other _ Hne_old).
      reflexivity.
  Qed.

  Lemma std_set_new_delegate_latest_at_now :
    forall (s : State.t)
           (std_traces : StakingVaultDelegationCheckpointed.TraceMap)
           (account new_d : Address) (now : U256.t),
      let old_d := delegate_of s.(State.std) account in
      new_d <> zero_address ->
      new_d <> old_d ->
      (match (StakingVaultDelegationCheckpointed.trace_of
                std_traces new_d).(Trace208.entries) with
       | [] => True
       | _  => fst (Trace208.last_entry
                      (StakingVaultDelegationCheckpointed.trace_of
                         std_traces new_d).(Trace208.entries)) < now
       end) ->
      let p := set_std_delegate_checkpointed s std_traces account new_d now in
      let traces' := snd p in
      let base' := fst p in
      Trace208.latest
        (StakingVaultDelegationCheckpointed.trace_of traces' new_d)
      = base'.(State.std).(Ledger.votes) new_d.
  Proof.
    intros s std_traces account new_d now.
    cbv zeta.
    intros Hne_zero Hne_old Hmon.
    set (old_d_lit := delegate_of s.(State.std) account).
    assert (Hold_neq_new_b : (old_d_lit =? new_d) = false).
    { apply Z.eqb_neq. intros Heq. apply Hne_old.
      unfold old_d_lit in Heq. symmetry. exact Heq. }
    assert (Hnewd_neq_zero_b : (new_d =? zero_address) = false).
    { apply Z.eqb_neq. exact Hne_zero. }
    unfold set_std_delegate_checkpointed.
    cbv zeta.
    cbn [fst snd].
    fold old_d_lit.
    rewrite Hold_neq_new_b.
    rewrite StakingVaultDelegationCheckpointed.trace_of_set_trace_same.
    rewrite Hnewd_neq_zero_b.
    apply Trace208.latest_after_push.
    exact Hmon.
  Qed.

  (** ==================================================================
      Section 2 — Joined-state mutators.

      Lift [set_std_delegate] / [set_opt_delegate] /
      [delegateOptimisticBySig] onto the joined [SimState] carrier.
      These are the sim-level analogs of the four Yul entrypoints.
      ================================================================ *)

  (** [sim_delegate sim account new_d]: the standard-side
      [_delegate(account, new_d)] mutator at the sim level. Updates
      the standard delegatee + standard trace history; leaves
      optimistic side and nonces untouched. *)
  Definition sim_delegate
      (sim : SimState.t) (account new_d : Address) : SimState.t :=
    let p := set_std_delegate_checkpointed
               sim.(SimState.base) sim.(SimState.std_traces)
               account new_d sim.(SimState.clock) in
    {|
      SimState.base       := fst p;
      SimState.std_traces := snd p;
      SimState.opt_traces := sim.(SimState.opt_traces);
      SimState.nonces     := sim.(SimState.nonces);
      SimState.domain     := sim.(SimState.domain);
      SimState.clock      := sim.(SimState.clock);
    |}.

  (** [sim_delegateOptimistic sim account new_d]: the optimistic-side
      [_delegateOptimistic(account, new_d)] mutator at the sim level.
      Symmetric to [sim_delegate] on the optimistic axis. *)
  Definition sim_delegateOptimistic
      (sim : SimState.t) (account new_d : Address) : SimState.t :=
    let s' := StakingVaultDelegationCheckpointed.set_opt_delegate_checkpointed
                {| StakingVaultDelegationCheckpointed.State.base :=
                     sim.(SimState.base);
                   StakingVaultDelegationCheckpointed.State.opt_traces :=
                     sim.(SimState.opt_traces);
                |}
                account new_d sim.(SimState.clock) in
    {|
      SimState.base       := s'.(StakingVaultDelegationCheckpointed.State.base);
      SimState.std_traces := sim.(SimState.std_traces);
      SimState.opt_traces := s'.(StakingVaultDelegationCheckpointed.State.opt_traces);
      SimState.nonces     := sim.(SimState.nonces);
      SimState.domain     := sim.(SimState.domain);
      SimState.clock      := sim.(SimState.clock);
    |}.

  (** [sim_delegateBySig sim now delegatee nonce expiry sig]: the
      standard-side ECDSA-authenticated delegation. Threads the
      revert discipline (expired / invalid sig / wrong nonce) as a
      Result-monad, mirroring
      [StakingVaultDelegationBySig.delegateOptimisticBySig] but
      firing [sim_delegate] instead of [sim_delegateOptimistic] in
      the success arm. *)

  Module Result.
    Inductive t (A : Set) : Set :=
    | Success (value : A)
    | Revert  (p s : U256.t).
    Arguments Success {_}.
    Arguments Revert {_}.
  End Result.

  Definition revert_expired_signature  {A : Set} : Result.t A := Result.Revert 0  64.
  Definition revert_invalid_signature  {A : Set} : Result.t A := Result.Revert 32 64.
  Definition revert_invalid_nonce      {A : Set} : Result.t A := Result.Revert 64 64.

  Definition sim_delegateBySig
      (sim : SimState.t) (now : U256.t)
      (delegatee : Address) (nonce expiry : U256.t)
      (sig : ECDSA.Signature) : Result.t SimState.t :=
    if Z.ltb expiry now then
      revert_expired_signature
    else
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      if Z.eqb signer ECDSA.zero_address then
        revert_invalid_signature
      else
        match Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce with
        | Nonces.Result.Revert _ _ => revert_invalid_nonce
        | Nonces.Result.Success nonces' =>
            let sim_after := sim_delegate sim signer delegatee in
            Result.Success {|
              SimState.base       := sim_after.(SimState.base);
              SimState.std_traces := sim_after.(SimState.std_traces);
              SimState.opt_traces := sim_after.(SimState.opt_traces);
              SimState.nonces     := nonces';
              SimState.domain     := sim.(SimState.domain);
              SimState.clock      := sim.(SimState.clock);
            |}
        end.

  (** [sim_delegateOptimisticBySig]: optimistic-side ECDSA-
      authenticated delegation. Lifts
      [StakingVaultDelegationBySig.delegateOptimisticBySig] onto the
      [SimState] carrier (so the standard-side traces field is
      threaded through unchanged). *)
  Definition sim_delegateOptimisticBySig
      (sim : SimState.t) (now : U256.t)
      (delegatee : Address) (nonce expiry : U256.t)
      (sig : ECDSA.Signature) : Result.t SimState.t :=
    if Z.ltb expiry now then
      revert_expired_signature
    else
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      if Z.eqb signer ECDSA.zero_address then
        revert_invalid_signature
      else
        match Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce with
        | Nonces.Result.Revert _ _ => revert_invalid_nonce
        | Nonces.Result.Success nonces' =>
            let sim_after := sim_delegateOptimistic sim signer delegatee in
            Result.Success {|
              SimState.base       := sim_after.(SimState.base);
              SimState.std_traces := sim_after.(SimState.std_traces);
              SimState.opt_traces := sim_after.(SimState.opt_traces);
              SimState.nonces     := nonces';
              SimState.domain     := sim.(SimState.domain);
              SimState.clock      := sim.(SimState.clock);
            |}
        end.

  (** ==================================================================
      Section 3 — Headline sim-side equivalence properties (Qed).

      These are the load-bearing facts the milestone theorems compose:
      each describes the sim-side post-state field-by-field, so a
      walker over the Yul body that lands at the [proj_sim] of the
      post-state automatically discharges the milestone's
      observational-equality side. ================================== *)

  (** ---- 3.1  sim_delegate field updates ---- *)

  Lemma sim_delegate_updates_std_delegatee :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) account
      = new_d.
  Proof.
    intros sim account new_d.
    unfold sim_delegate. cbn [fst snd SimState.base].
    unfold set_std_delegate_checkpointed.
    cbv zeta. cbn [fst].
    unfold set_std_delegate.
    cbn [StakingVaultDelegation.State.std
         StakingVaultDelegation.Ledger.delegatee].
    unfold upd. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma sim_delegate_preserves_opt :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.opt)
      = sim.(SimState.base).(StakingVaultDelegation.State.opt).
  Proof.
    intros sim account new_d.
    unfold sim_delegate.
    cbn [SimState.base].
    unfold set_std_delegate_checkpointed.
    cbv zeta. cbn [fst].
    apply set_std_delegate_preserves_opt.
  Qed.

  Lemma sim_delegate_preserves_balances :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.balances)
      = sim.(SimState.base).(StakingVaultDelegation.State.balances).
  Proof.
    intros sim account new_d.
    unfold sim_delegate.
    cbn [SimState.base].
    unfold set_std_delegate_checkpointed.
    cbv zeta. cbn [fst].
    apply set_std_delegate_preserves_balances.
  Qed.

  Lemma sim_delegate_preserves_opt_traces :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.opt_traces)
      = sim.(SimState.opt_traces).
  Proof.
    intros sim account new_d.
    unfold sim_delegate.
    cbn [SimState.opt_traces].
    reflexivity.
  Qed.

  Lemma sim_delegate_preserves_nonces :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.nonces)
      = sim.(SimState.nonces).
  Proof. intros; reflexivity. Qed.

  Lemma sim_delegate_preserves_domain :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.domain)
      = sim.(SimState.domain).
  Proof. intros; reflexivity. Qed.

  Lemma sim_delegate_preserves_clock :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegate sim account new_d).(SimState.clock)
      = sim.(SimState.clock).
  Proof. intros; reflexivity. Qed.

  (** ---- 3.2  sim_delegateOptimistic field updates ---- *)

  Lemma sim_delegateOptimistic_updates_opt_delegatee :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.opt)
        .(StakingVaultDelegation.Ledger.delegatee) account
      = new_d.
  Proof.
    intros sim account new_d.
    unfold sim_delegateOptimistic. cbn [SimState.base].
    unfold StakingVaultDelegationCheckpointed.set_opt_delegate_checkpointed.
    cbv zeta.
    cbn [StakingVaultDelegationCheckpointed.State.base
         StakingVaultDelegation.State.opt
         StakingVaultDelegation.Ledger.delegatee].
    unfold set_opt_delegate.
    cbn [StakingVaultDelegation.State.opt
         StakingVaultDelegation.Ledger.delegatee].
    unfold upd. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma sim_delegateOptimistic_preserves_std :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.std)
      = sim.(SimState.base).(StakingVaultDelegation.State.std).
  Proof.
    intros sim account new_d.
    unfold sim_delegateOptimistic. cbn [SimState.base].
    unfold StakingVaultDelegationCheckpointed.set_opt_delegate_checkpointed.
    cbv zeta.
    cbn [StakingVaultDelegationCheckpointed.State.base
         StakingVaultDelegation.State.std].
    apply set_opt_delegate_preserves_std.
  Qed.

  Lemma sim_delegateOptimistic_preserves_balances :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.base)
        .(StakingVaultDelegation.State.balances)
      = sim.(SimState.base).(StakingVaultDelegation.State.balances).
  Proof.
    intros sim account new_d.
    unfold sim_delegateOptimistic. cbn [SimState.base].
    unfold StakingVaultDelegationCheckpointed.set_opt_delegate_checkpointed.
    cbv zeta.
    cbn [StakingVaultDelegationCheckpointed.State.base
         StakingVaultDelegation.State.balances].
    apply set_opt_delegate_preserves_balances.
  Qed.

  Lemma sim_delegateOptimistic_preserves_std_traces :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.std_traces)
      = sim.(SimState.std_traces).
  Proof. intros; reflexivity. Qed.

  Lemma sim_delegateOptimistic_preserves_nonces :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.nonces)
      = sim.(SimState.nonces).
  Proof. intros; reflexivity. Qed.

  Lemma sim_delegateOptimistic_preserves_domain :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.domain)
      = sim.(SimState.domain).
  Proof. intros; reflexivity. Qed.

  Lemma sim_delegateOptimistic_preserves_clock :
    forall (sim : SimState.t) (account new_d : Address),
      (sim_delegateOptimistic sim account new_d).(SimState.clock)
      = sim.(SimState.clock).
  Proof. intros; reflexivity. Qed.

  (** ---- 3.3  Dual-axis independence theorem (NEW for R080) ----

      The headline R080 fact: a standard-side delegation does not
      perturb the optimistic-side trace history, and vice versa.
      This is the dual-axis composition statement — the two ledgers
      operate on disjoint storage slots, so any well-formed walker
      proof can decompose [sim_delegate] / [sim_delegateOptimistic]
      along this axis. *)

  Lemma sim_delegate_preserves_optimistic_axis :
    forall (sim : SimState.t) (account new_d : Address),
      let sim' := sim_delegate sim account new_d in
      sim'.(SimState.base).(StakingVaultDelegation.State.opt)
        = sim.(SimState.base).(StakingVaultDelegation.State.opt)
      /\ sim'.(SimState.opt_traces) = sim.(SimState.opt_traces).
  Proof.
    intros sim account new_d.
    split.
    - apply sim_delegate_preserves_opt.
    - apply sim_delegate_preserves_opt_traces.
  Qed.

  Lemma sim_delegateOptimistic_preserves_standard_axis :
    forall (sim : SimState.t) (account new_d : Address),
      let sim' := sim_delegateOptimistic sim account new_d in
      sim'.(SimState.base).(StakingVaultDelegation.State.std)
        = sim.(SimState.base).(StakingVaultDelegation.State.std)
      /\ sim'.(SimState.std_traces) = sim.(SimState.std_traces).
  Proof.
    intros sim account new_d.
    split.
    - apply sim_delegateOptimistic_preserves_std.
    - apply sim_delegateOptimistic_preserves_std_traces.
  Qed.

  (** ---- 3.4  BySig variants — expired path reverts ---- *)

  Lemma sim_delegateBySig_expired_reverts :
    forall (sim : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      expiry < now ->
      sim_delegateBySig sim now delegatee nonce expiry sig =
      revert_expired_signature.
  Proof.
    intros sim now delegatee nonce expiry sig Hexp.
    unfold sim_delegateBySig.
    destruct (Z.ltb expiry now) eqn:Hlt.
    - reflexivity.
    - apply Z.ltb_nlt in Hlt. lia.
  Qed.

  Lemma sim_delegateOptimisticBySig_expired_reverts :
    forall (sim : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      expiry < now ->
      sim_delegateOptimisticBySig sim now delegatee nonce expiry sig =
      revert_expired_signature.
  Proof.
    intros sim now delegatee nonce expiry sig Hexp.
    unfold sim_delegateOptimisticBySig.
    destruct (Z.ltb expiry now) eqn:Hlt.
    - reflexivity.
    - apply Z.ltb_nlt in Hlt. lia.
  Qed.

  (** ---- 3.5  BySig variants — successful path: signer nonce increments. *)

  Lemma sim_delegateBySig_success_increments_signer_nonce :
    forall (sim sim' : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      sim'.(SimState.nonces) signer = sim.(SimState.nonces) signer + 1.
  Proof.
    intros sim sim' now delegatee nonce expiry sig H.
    unfold sim_delegateBySig in H.
    destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
    set (struct_hash :=
           ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
    set (typed_hash  :=
           ECDSA.typed_data_hash sim.(SimState.domain) struct_hash) in *.
    set (signer      := ECDSA.recover typed_hash sig) in *.
    destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection H as Hsim'_eq.
    subst sim'. simpl.
    apply (Nonces.useCheckedNonce_increments _ _ _ _ Hn).
  Qed.

  Lemma sim_delegateOptimisticBySig_success_increments_signer_nonce :
    forall (sim sim' : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateOptimisticBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      sim'.(SimState.nonces) signer = sim.(SimState.nonces) signer + 1.
  Proof.
    intros sim sim' now delegatee nonce expiry sig H.
    unfold sim_delegateOptimisticBySig in H.
    destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
    set (struct_hash :=
           ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
    set (typed_hash  :=
           ECDSA.typed_data_hash sim.(SimState.domain) struct_hash) in *.
    set (signer      := ECDSA.recover typed_hash sig) in *.
    destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection H as Hsim'_eq.
    subst sim'. simpl.
    apply (Nonces.useCheckedNonce_increments _ _ _ _ Hn).
  Qed.

  (** ---- 3.6  BySig variants — replay reverts ---- *)

  Lemma sim_delegateBySig_replay_reverts :
    forall (sim sim' : SimState.t) (now1 now2 : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateBySig sim now1 delegatee nonce expiry sig = Result.Success sim' ->
      expiry >= now2 ->
      sim_delegateBySig sim' now2 delegatee nonce expiry sig = revert_invalid_nonce.
  Proof.
    intros sim sim' now1 now2 delegatee nonce expiry sig Hfirst Hnotexp.
    unfold sim_delegateBySig in Hfirst.
    destruct (Z.ltb expiry now1) eqn:Hexp1; [discriminate|].
    destruct (Z.eqb (ECDSA.recover
                (ECDSA.typed_data_hash sim.(SimState.domain)
                   (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
                sig) ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces)
                (ECDSA.recover
                   (ECDSA.typed_data_hash sim.(SimState.domain)
                      (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
                   sig) nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection Hfirst as Hsim'_eq. subst sim'.
    unfold sim_delegateBySig.
    simpl SimState.nonces. simpl SimState.domain.
    destruct (Z.ltb expiry now2) eqn:Hexp2.
    { apply Z.ltb_lt in Hexp2. lia. }
    rewrite Hsig0.
    pose proof (Nonces.useCheckedNonce_replay_reverts _ _ _ _ Hn) as Hrep.
    rewrite Hrep. reflexivity.
  Qed.

  Lemma sim_delegateOptimisticBySig_replay_reverts :
    forall (sim sim' : SimState.t) (now1 now2 : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateOptimisticBySig sim now1 delegatee nonce expiry sig = Result.Success sim' ->
      expiry >= now2 ->
      sim_delegateOptimisticBySig sim' now2 delegatee nonce expiry sig = revert_invalid_nonce.
  Proof.
    intros sim sim' now1 now2 delegatee nonce expiry sig Hfirst Hnotexp.
    unfold sim_delegateOptimisticBySig in Hfirst.
    destruct (Z.ltb expiry now1) eqn:Hexp1; [discriminate|].
    destruct (Z.eqb (ECDSA.recover
                (ECDSA.typed_data_hash sim.(SimState.domain)
                   (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
                sig) ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces)
                (ECDSA.recover
                   (ECDSA.typed_data_hash sim.(SimState.domain)
                      (ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry))
                   sig) nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection Hfirst as Hsim'_eq. subst sim'.
    unfold sim_delegateOptimisticBySig.
    simpl SimState.nonces. simpl SimState.domain.
    destruct (Z.ltb expiry now2) eqn:Hexp2.
    { apply Z.ltb_lt in Hexp2. lia. }
    rewrite Hsig0.
    pose proof (Nonces.useCheckedNonce_replay_reverts _ _ _ _ Hn) as Hrep.
    rewrite Hrep. reflexivity.
  Qed.

  (** ---- 3.7  BySig variants — signer-only delegate update ---- *)

  Lemma sim_delegateBySig_success_sets_signer_std_delegate :
    forall (sim sim' : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      sim'.(SimState.base).(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) signer = delegatee.
  Proof.
    intros sim sim' now delegatee nonce expiry sig H.
    unfold sim_delegateBySig in H.
    destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
    set (struct_hash :=
           ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
    set (typed_hash  :=
           ECDSA.typed_data_hash sim.(SimState.domain) struct_hash) in *.
    set (signer      := ECDSA.recover typed_hash sig) in *.
    destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection H as Hsim'_eq.
    subst sim'. simpl SimState.base.
    apply sim_delegate_updates_std_delegatee.
  Qed.

  Lemma sim_delegateOptimisticBySig_success_sets_signer_opt_delegate :
    forall (sim sim' : SimState.t) (now : U256.t)
           (delegatee : Address) (nonce expiry : U256.t)
           (sig : ECDSA.Signature),
      sim_delegateOptimisticBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
      let struct_hash :=
        ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry in
      let typed_hash :=
        ECDSA.typed_data_hash sim.(SimState.domain) struct_hash in
      let signer := ECDSA.recover typed_hash sig in
      sim'.(SimState.base).(StakingVaultDelegation.State.opt)
        .(StakingVaultDelegation.Ledger.delegatee) signer = delegatee.
  Proof.
    intros sim sim' now delegatee nonce expiry sig H.
    unfold sim_delegateOptimisticBySig in H.
    destruct (Z.ltb expiry now) eqn:Hexp; [discriminate|].
    set (struct_hash :=
           ECDSA.optimistic_delegation_struct_hash delegatee nonce expiry) in *.
    set (typed_hash  :=
           ECDSA.typed_data_hash sim.(SimState.domain) struct_hash) in *.
    set (signer      := ECDSA.recover typed_hash sig) in *.
    destruct (Z.eqb signer ECDSA.zero_address) eqn:Hsig0; [discriminate|].
    destruct (Nonces.useCheckedNonce sim.(SimState.nonces) signer nonce)
      as [nonces' | p sm] eqn:Hn; [|discriminate].
    injection H as Hsim'_eq.
    subst sim'. simpl SimState.base.
    apply sim_delegateOptimistic_updates_opt_delegatee.
  Qed.

  (** ==================================================================
      Section 4 — Slot-agnostic projection lens (Section parameters).

      Per R072: declare the storage slot indices and the projection
      lens as Section variables; the lens correctness obligations are
      Section hypotheses discharged by [reflexivity] at the inheritor.

      IMPORTANT (post Task #280 — re Caveat-5 audit response):
      No inheritor file in this corpus instantiates the Section. The
      Section variables therefore remain abstract, and every theorem
      closed inside the Section is universally quantified over them.
      The composite walker axioms below are stated against these
      parameters; they document the audit-time obligation for a
      future concrete StakingVault binding but do NOT discharge it.

      This file's purpose is to fix the methodology shape: a future
      [StakingVaultDelegation_instantiation.v] (gated on landing the
      StakingVault shallow form in the default build tier) would
      bind the Section variables and discharge the per-fn Hypotheses
      with concrete walker tactics. Until that instantiation exists,
      treat the Section-internal milestone theorems as TEMPLATES,
      not RESULTS. ================================================ *)

  Section StakingVaultDelegationSection.

    (** Standard-side slots — inherited from ERC20Votes layout. *)
    Variable slot_std_delegatee     : U256.t.
    Variable slot_std_delegate_ckpt : U256.t.

    (** Optimistic-side slots — StakingVault-specific. Per shallow
        form line 9911: slot 0x0a is [optimisticDelegatees]; by the
        Solidity layout convention, [optimisticDelegateCheckpoints]
        follows at 0x0b. *)
    Variable slot_opt_delegatee     : U256.t.
    Variable slot_opt_delegate_ckpt : U256.t.

    (** Nonces slot — inherited from ERC20Permit / NoncesUpgradeable. *)
    Variable slot_nonces : U256.t.

    (** Standard-side total-supply checkpoint slot — inherited from
        ERC20Votes layout (used by [_transferVotingUnits] mint/burn
        path). Not directly mutated by the four delegation entrypoints
        but present in the projection. *)
    Variable slot_std_total_ckpt : U256.t.

    (** Projection lens: given the inheritor's full
        [SimulatedStorage.t], extract the SimState. The lens is
        opaque from the perspective of this Section; the inheritor
        supplies a concrete projection in its instantiation file
        once the shallow form is built into the default tier. *)
    Variable project_sim : SimulatedStorage.t -> SimState.t.

    (** Lens correctness hypothesis: the projection is deterministic
        in its input. This is automatically true for any concrete
        [project_sim]; we declare it as a Section hypothesis so the
        downstream theorems can take it as given. *)
    Hypothesis lens_deterministic :
      forall (s1 s2 : SimulatedStorage.t),
        s1 = s2 -> project_sim s1 = project_sim s2.

    (** ==============================================================
        Section 5 — Per-entrypoint composite walker axioms (R051).

        These are the audit-time trust obligations. Each axiom
        bundles the Yul body's walker into a single Hoare triple
        keyed on the pre-state's [project_sim], landing at a post-
        state computed from sim.

        Each axiom is stated with [Parameter] for the post-state
        projection (Skolemized — concrete inheritors supply a
        definition matching their layout) and [Axiom] for the
        Hoare-triple closure.

        These four axioms are the entirety of this file's trust
        budget. Closing them requires the StakingVault shallow form
        to be added to the default build tier; the slot-agnostic
        form here means the closure work happens at the inheritor's
        instantiation site, not here. ============================ *)

    (** ---- 5.1  Composite axiom shape — delegate ---- *)

    (** Sim post-state for the [delegate(msg.sender, delegatee)] call.
        [msg.sender] enters as a Yul [caller] read, which the sim sees
        as the explicit [account] parameter. *)
    Variable proj_post_delegate :
      SimState.t -> Address (* account *) -> Address (* new_d *) ->
      SimulatedStorage.t.

    (** Observational bridge: the post-state projection equals the
        [project_sim] of a successor storage that the inheritor
        defines concretely. At the abstract level here we record only
        that the bridge is well-formed (it factors through the lens
        on the post-state). *)
    Hypothesis proj_post_delegate_well_formed :
      forall (sim : SimState.t) (account new_d : Address)
             (storage_pre : SimulatedStorage.t),
        sim = project_sim storage_pre ->
        exists (storage_post : SimulatedStorage.t),
          proj_post_delegate sim account new_d = storage_post
          /\ project_sim storage_post = sim_delegate sim account new_d.

    (** ---- 5.2  Composite axiom shape — delegateOptimistic ---- *)

    Variable proj_post_delegateOptimistic :
      SimState.t -> Address (* account *) -> Address (* new_d *) ->
      SimulatedStorage.t.

    Hypothesis proj_post_delegateOptimistic_well_formed :
      forall (sim : SimState.t) (account new_d : Address)
             (storage_pre : SimulatedStorage.t),
        sim = project_sim storage_pre ->
        exists (storage_post : SimulatedStorage.t),
          proj_post_delegateOptimistic sim account new_d = storage_post
          /\ project_sim storage_post = sim_delegateOptimistic sim account new_d.

    (** ---- 5.3  Composite axiom shape — delegateBySig ---- *)

    (** The sim post-state for the BySig variant is monadic (Result
        envelope); the projection takes the success branch's payload
        and projects it back to storage. *)
    Variable proj_post_delegateBySig :
      SimState.t -> U256.t (* now *) -> Address -> U256.t -> U256.t ->
      ECDSA.Signature -> SimulatedStorage.t.

    Hypothesis proj_post_delegateBySig_well_formed_success :
      forall (sim sim' : SimState.t) (now : U256.t)
             (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (storage_pre : SimulatedStorage.t),
        sim = project_sim storage_pre ->
        sim_delegateBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        exists (storage_post : SimulatedStorage.t),
          proj_post_delegateBySig sim now delegatee nonce expiry sig = storage_post
          /\ project_sim storage_post = sim'.

    (** ---- 5.4  Composite axiom shape — delegateOptimisticBySig ---- *)

    Variable proj_post_delegateOptimisticBySig :
      SimState.t -> U256.t (* now *) -> Address -> U256.t -> U256.t ->
      ECDSA.Signature -> SimulatedStorage.t.

    Hypothesis proj_post_delegateOptimisticBySig_well_formed_success :
      forall (sim sim' : SimState.t) (now : U256.t)
             (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (storage_pre : SimulatedStorage.t),
        sim = project_sim storage_pre ->
        sim_delegateOptimisticBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        exists (storage_post : SimulatedStorage.t),
          proj_post_delegateOptimisticBySig sim now delegatee nonce expiry sig = storage_post
          /\ project_sim storage_post = sim'.

    (** ==============================================================
        Section 6 — Hoare-triple closure axioms (R051).

        These are the walker-level bundling — the body of each Yul
        function runs from a pre-state projected via [project_sim] to
        a post-state projected via [proj_post_<fn>]. The carrier
        ([codes, env, state]) is the standard [RunO] envelope.

        Each axiom is parameterized by the concrete Yul function
        identifier, which lives in the StakingVault shallow form.
        The walker tactic that closes them is documented in the
        commentary block before each axiom; the closure happens at
        the inheritor's binding file once the shallow is in the
        default tier. ============================================= *)

    (** Abstract Hoare-triple carrier. At instantiation [W] is
        replaced by the concrete walker over the Yul body, and
        [hoare] is replaced by the [RunO.t] Hoare triple. *)
    Variable Codes : Set.
    Variable Env : Set.
    Variable Walker : Set.
    Variable State : Set.

    Variable hoare :
      Walker -> Codes -> Env -> State -> State -> Prop.

    (** Concrete walker instances — Section parameters; the inheritor
        binds them to [fun_delegate_15192], etc. *)
    Variable walker_delegate                : Walker.
    Variable walker_delegateOptimistic      : Walker.
    Variable walker_delegateBySig           : Walker.
    Variable walker_delegateOptimisticBySig : Walker.

    (** State-with-storage shape — the [make_state] constructor of
        the RunO Hoare triple takes a [SimulatedStorage.t] among other
        things; abstract here, instantiated at binding. *)
    Variable make_state : SimulatedStorage.t -> State.

    (** ---- 6.1  Composite walker axiom — delegate ----

        Yul body shape for [fun_delegate_15192 delegatee]:
          let acc := caller();
          let_state~ tt := fun__delegate_15292(acc, delegatee);

        Inner body [fun__delegate_15292 account delegatee] (L9336):
          let old_d := fun_delegates_15175(account);
                       (* sload slot_std_delegatee[account] *)
          sstore <slot_std_delegatee[account]> := delegatee;
          do log4 (DelegateChanged event);
          let units := fun__getVotingUnits_3822(account);
                       (* balanceOf(account) *)
          do fun__moveDelegateVotes_15441(old_d, delegatee, units);

        Inner body [fun__moveDelegateVotes_15441 from to amount]:
          short-circuit if [from == to || amount == 0]
          if [from != 0]:
            from_ckpt := sload(slot_std_delegate_ckpt[from])
            sstore <slot_std_delegate_ckpt[from]> :=
              Trace208.push(from_ckpt, clock(), latest(from_ckpt) - amount)
          if [to != 0]:
            to_ckpt := sload(slot_std_delegate_ckpt[to])
            sstore <slot_std_delegate_ckpt[to]> :=
              Trace208.push(to_ckpt, clock(), latest(to_ckpt) + amount)

        Walker tactic at the binding site (per R053 outer-walker
        composition):
          - Phase 1: read [caller] into [account].
          - Phase 2: read [slot_std_delegatee[account]] into [old_d]
                     (R038 slot-discriminated sload arm).
          - Phase 3: sstore [slot_std_delegatee[account] := new_d]
                     (R040 wrapper-shape).
          - Phase 4: log4 emission (treated as side-effect-only,
                     state-preserving in the proj_sim).
          - Phase 5: balanceOf read — leaves the [units] value;
                     binds to [sim.base.balances account].
          - Phase 6: enter [_moveDelegateVotes] body. Case-split on
                     [old_d = new_d] (sim's [move_votes_same_target]
                     short-circuit) and on [old_d = 0] / [new_d = 0]
                     (R047 case-split BEFORE eexists).
          - Phase 7: each non-zero branch fires a sload + Trace208.push
                     + sstore composite. The walker arms thread
                     through the [run_std_set_new_delegate_latest_at_now]
                     lemma above for the new-delegate push and the
                     symmetric one for the old-delegate push.

        Post-state matches [proj_post_delegate sim account new_d]
        via the observational bridge above. *)
    Hypothesis run_fun_delegate_at_proj_sim :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (account new_d : Address),
        let sim := project_sim storage_pre in
        hoare walker_delegate codes env
              (make_state storage_pre)
              (make_state (proj_post_delegate sim account new_d)).

    (** ---- 6.2  Composite walker axiom — delegateOptimistic ----

        Yul body shape for [fun_delegateOptimistic_422 delegatee]
        (L10034):
          let acc := caller();
          let_state~ tt := fun__delegateOptimistic_1608(acc, delegatee);

        Inner body [fun__delegateOptimistic_1608 account delegatee]
        (L9909):
          let ptr_old := mapping_index_access(0x0a, account)
                         (* slot_opt_delegatee[account] *)
          let old_d   := sload(ptr_old)
          let ptr_new := mapping_index_access(0x0a, account)
          sstore <ptr_new> := delegatee;
          do log4 (OptimisticDelegateChanged event);
          let units := balanceOf(account);
          do fun__moveOptimisticDelegateVotes_1720(old_d, delegatee, units);

        Walker tactic at binding site: same shape as
        [run_fun_delegate_at_proj_sim] but against the optimistic
        slots (0x0a, 0x0b). The sim mutator threading goes through
        [sim_delegateOptimistic] instead of [sim_delegate]. *)
    Hypothesis run_fun_delegateOptimistic_at_proj_sim :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (account new_d : Address),
        let sim := project_sim storage_pre in
        hoare walker_delegateOptimistic codes env
              (make_state storage_pre)
              (make_state (proj_post_delegateOptimistic sim account new_d)).

    (** ---- 6.3  Composite walker axiom — delegateBySig ----

        Yul body shape for [fun_delegateBySig_15249] (L9692):
          if (timestamp > expiry):
            revert(VotesExpiredSignature, expiry)
          let struct_hash := keccak256(abi.encode(
            DELEGATION_TYPEHASH, delegatee, nonce, expiry));
          let typed_hash := fun__hashTypedDataV4_14685(struct_hash);
          let signer := fun_recover_5639(typed_hash, v, r, s);
          do fun__useCheckedNonce_4715(signer, nonce);
          do fun__delegate_15292(signer, delegatee);

        Walker tactic at binding site:
          - Phase 1: timestamp read + comparison → R047 case-split.
          - Phase 2 (expired branch): revert with abi-encoded selector.
          - Phase 3 (success): abi-encode struct, keccak256, call
                     [_hashTypedDataV4], call [ECDSA.recover].
                     Each is a pure-function library call whose Yul
                     body invokes the corresponding mock primitive.
                     [recover_zero] check via R047 case-split.
          - Phase 4: [_useCheckedNonce] composite — R040 wrapper-shape
                     sstore on the [nonces] slot, R047 on the nonce-
                     mismatch revert branch.
          - Phase 5: tail-call into [_delegate] reuses
                     [run_fun_delegate_at_proj_sim] above with the
                     signer as the [account] argument. *)
    Hypothesis run_fun_delegateBySig_at_proj_sim :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (now : U256.t) (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (sim' : SimState.t),
        let sim := project_sim storage_pre in
        sim_delegateBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        hoare walker_delegateBySig codes env
              (make_state storage_pre)
              (make_state (proj_post_delegateBySig sim now delegatee nonce expiry sig)).

    (** ---- 6.4  Composite walker axiom — delegateOptimisticBySig ----

        Yul body shape for [fun_delegateOptimisticBySig_480] (L9956):
          if (timestamp > expiry):
            revert(VotesExpiredSignature, expiry)
          let struct_hash := keccak256(abi.encode(
            OPTIMISTIC_DELEGATION_TYPEHASH, delegatee, nonce, expiry));
          let typed_hash := fun__hashTypedDataV4_14685(struct_hash);
          let signer := fun_recover_5639(typed_hash, v, r, s);
          do fun__useCheckedNonce_4715(signer, nonce);
          do fun__delegateOptimistic_1608(signer, delegatee);

        Same shape as [run_fun_delegateBySig_at_proj_sim] but against
        the optimistic side. Note that the typehash constant differs:
        [DELEGATION_TYPEHASH] vs [OPTIMISTIC_DELEGATION_TYPEHASH]. *)
    Hypothesis run_fun_delegateOptimisticBySig_at_proj_sim :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (now : U256.t) (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (sim' : SimState.t),
        let sim := project_sim storage_pre in
        sim_delegateOptimisticBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        hoare walker_delegateOptimisticBySig codes env
              (make_state storage_pre)
              (make_state (proj_post_delegateOptimisticBySig sim now delegatee nonce expiry sig)).

    (** ==============================================================
        Section 7 — Milestone METHODOLOGY theorems (templates only).

        ============== AUDIT-HONESTY WARNING ==========================
        These four theorems close at the Section level via [Qed], but
        every variable in their statement ([Codes], [Env], [Walker],
        [State], [hoare], [make_state], [project_sim], [walker_<fn>],
        [proj_post_<fn>]) is a Section parameter — universally
        quantified at Section closure. The conclusions therefore
        constrain NO CONCRETE behavior of any deployed contract.
        [Print Assumptions] shows only [deployment_id : Set] (plus the
        mock primitives the BySig variants pull in via the sim) — the
        Hoare-triple obligations are hidden inside the Section
        hypotheses, NOT in the [Print Assumptions] output.

        The suffix [_methodology] on each theorem name encodes this:
        these are TEMPLATES describing the composition shape a
        concrete inheritor would discharge, NOT equivalence claims
        against StakingVault bytecode. Audit citations of
        delegation-equivalence for StakingVault must reference the
        sim-level Qed lemmas in [proofs/StakingVaultDelegation*.v],
        which are concrete and consumed by [Audit.v].

        See [SYNTHESIS.md] CCV-2, [trust_axiom_auditor.md] CRIT-6,
        and [Audit.v] Caveat-5 for the formal articulation.

        Each theorem composes the per-fn walker hypothesis with the
        observational bridge hypothesis to deliver the headline
        equivalence statement:

          run_<fn>_equivalent_methodology :
            exists state_post,
              hoare walker_<fn> codes env (make_state storage_pre) state_post
              /\ ... (some characterization of state_post tied to sim_<fn>)

        At the Section level the characterization is "state_post is
        [make_state (proj_post_<fn> sim args)]"; at an inheritor's
        binding site this refines to the observationally-equal-storage
        form via [proj_post_<fn>_well_formed]. ====================== *)

    (** ---- 7.1  Methodology template — delegate ----

        PARAMETRIC — not yet instantiated against StakingVault_shallow.v.
        Trust budget lives in the Section hypotheses ([project_sim],
        [walker_delegate], [run_fun_delegate_at_proj_sim], etc.),
        which are universally quantified at Section closure. *)
    Theorem run_delegate_equivalent_methodology :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (account new_d : Address),
        let sim := project_sim storage_pre in
        exists state_post,
          hoare walker_delegate codes env
                (make_state storage_pre) state_post
          /\ state_post = make_state (proj_post_delegate sim account new_d)
          /\ exists (storage_post : SimulatedStorage.t),
               proj_post_delegate sim account new_d = storage_post
               /\ project_sim storage_post = sim_delegate sim account new_d.
    Proof.
      intros codes env storage_pre account new_d.
      cbv zeta.
      eexists.
      split; [|split].
      - apply run_fun_delegate_at_proj_sim.
      - reflexivity.
      - apply (proj_post_delegate_well_formed (project_sim storage_pre)
                 account new_d storage_pre eq_refl).
    Qed.

    (** ---- 7.2  Methodology template — delegateOptimistic ----

        PARAMETRIC — not yet instantiated against StakingVault_shallow.v.
        Same Section-bound nature as Section 7.1. *)
    Theorem run_delegateOptimistic_equivalent_methodology :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (account new_d : Address),
        let sim := project_sim storage_pre in
        exists state_post,
          hoare walker_delegateOptimistic codes env
                (make_state storage_pre) state_post
          /\ state_post = make_state (proj_post_delegateOptimistic sim account new_d)
          /\ exists (storage_post : SimulatedStorage.t),
               proj_post_delegateOptimistic sim account new_d = storage_post
               /\ project_sim storage_post = sim_delegateOptimistic sim account new_d.
    Proof.
      intros codes env storage_pre account new_d.
      cbv zeta.
      eexists.
      split; [|split].
      - apply run_fun_delegateOptimistic_at_proj_sim.
      - reflexivity.
      - apply (proj_post_delegateOptimistic_well_formed (project_sim storage_pre)
                 account new_d storage_pre eq_refl).
    Qed.

    (** ---- 7.3  Methodology template — delegateBySig (success branch) ----

        PARAMETRIC — not yet instantiated against StakingVault_shallow.v.
        Same Section-bound nature as Section 7.1. *)
    Theorem run_delegateBySig_equivalent_methodology :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (now : U256.t) (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (sim' : SimState.t),
        let sim := project_sim storage_pre in
        sim_delegateBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        exists state_post,
          hoare walker_delegateBySig codes env
                (make_state storage_pre) state_post
          /\ state_post = make_state
                            (proj_post_delegateBySig sim now delegatee nonce expiry sig)
          /\ exists (storage_post : SimulatedStorage.t),
               proj_post_delegateBySig sim now delegatee nonce expiry sig = storage_post
               /\ project_sim storage_post = sim'.
    Proof.
      intros codes env storage_pre now delegatee nonce expiry sig sim'.
      cbv zeta. intros Hsuccess.
      eexists.
      split; [|split].
      - apply (run_fun_delegateBySig_at_proj_sim codes env storage_pre
                 now delegatee nonce expiry sig sim' Hsuccess).
      - reflexivity.
      - apply (proj_post_delegateBySig_well_formed_success
                 (project_sim storage_pre) sim'
                 now delegatee nonce expiry sig storage_pre eq_refl Hsuccess).
    Qed.

    (** ---- 7.4  Methodology template — delegateOptimisticBySig (success branch) ----

        PARAMETRIC — not yet instantiated against StakingVault_shallow.v.
        Same Section-bound nature as Section 7.1. *)
    Theorem run_delegateOptimisticBySig_equivalent_methodology :
      forall (codes : Codes) (env : Env) (storage_pre : SimulatedStorage.t)
             (now : U256.t) (delegatee : Address) (nonce expiry : U256.t)
             (sig : ECDSA.Signature) (sim' : SimState.t),
        let sim := project_sim storage_pre in
        sim_delegateOptimisticBySig sim now delegatee nonce expiry sig = Result.Success sim' ->
        exists state_post,
          hoare walker_delegateOptimisticBySig codes env
                (make_state storage_pre) state_post
          /\ state_post = make_state
                            (proj_post_delegateOptimisticBySig sim now delegatee nonce expiry sig)
          /\ exists (storage_post : SimulatedStorage.t),
               proj_post_delegateOptimisticBySig sim now delegatee nonce expiry sig = storage_post
               /\ project_sim storage_post = sim'.
    Proof.
      intros codes env storage_pre now delegatee nonce expiry sig sim'.
      cbv zeta. intros Hsuccess.
      eexists.
      split; [|split].
      - apply (run_fun_delegateOptimisticBySig_at_proj_sim codes env storage_pre
                 now delegatee nonce expiry sig sim' Hsuccess).
      - reflexivity.
      - apply (proj_post_delegateOptimisticBySig_well_formed_success
                 (project_sim storage_pre) sim'
                 now delegatee nonce expiry sig storage_pre eq_refl Hsuccess).
    Qed.

  End StakingVaultDelegationSection.

  (** ==================================================================
      Section 8 — Sanity-check examples (vm_compute).

      A small set of fully-closed examples exercising the sim
      mutators against a concrete state. Serves as a smoke test that
      the sim composes properly and that [vm_compute] can evaluate
      the mutators end-to-end. ====================================== *)

  Module Examples.

    Definition addr_a : Address := 10.
    Definition addr_b : Address := 20.
    Definition addr_c : Address := 30.

    Definition base0 : StakingVaultDelegation.State.t := {|
      StakingVaultDelegation.State.balances :=
        StakingVaultDelegation.upd
          StakingVaultDelegation.empty_map addr_a 100;
      StakingVaultDelegation.State.std :=
        {| StakingVaultDelegation.Ledger.delegatee :=
             StakingVaultDelegation.const_map StakingVaultDelegation.zero_address;
           StakingVaultDelegation.Ledger.votes :=
             StakingVaultDelegation.empty_map; |};
      StakingVaultDelegation.State.opt :=
        {| StakingVaultDelegation.Ledger.delegatee :=
             StakingVaultDelegation.const_map StakingVaultDelegation.zero_address;
           StakingVaultDelegation.Ledger.votes :=
             StakingVaultDelegation.empty_map; |};
    |}.

    Definition sim0 : SimState.t := {|
      SimState.base       := base0;
      SimState.std_traces := [];
      SimState.opt_traces := [];
      SimState.nonces     := Nonces.empty;
      SimState.domain     := {|
        ECDSA.Domain.deployment := ECDSA.Domain.staking_vault_id;
        ECDSA.Domain.chain_id   := 1;
        ECDSA.Domain.contract   := 0x42;
      |};
      SimState.clock      := 100;
    |}.

    (** [sim_delegate sim0 addr_a addr_b]: re-point a's standard
        delegate to b. The standard delegatee map now has addr_a ↦ b. *)
    Definition sim1 : SimState.t := sim_delegate sim0 addr_a addr_b.

    Example ex_delegate_std_delegatee_updated :
      sim1.(SimState.base)
        .(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a = addr_b.
    Proof. apply sim_delegate_updates_std_delegatee. Qed.

    Example ex_delegate_preserves_opt :
      sim1.(SimState.base).(StakingVaultDelegation.State.opt)
      = sim0.(SimState.base).(StakingVaultDelegation.State.opt).
    Proof. apply sim_delegate_preserves_opt. Qed.

    Example ex_delegate_preserves_nonces :
      sim1.(SimState.nonces) = sim0.(SimState.nonces).
    Proof. apply sim_delegate_preserves_nonces. Qed.

    (** [sim_delegateOptimistic sim1 addr_a addr_c]: re-point a's
        optimistic delegate to c (while a's standard delegate
        remains b). The two axes are independent. *)
    Definition sim2 : SimState.t := sim_delegateOptimistic sim1 addr_a addr_c.

    Example ex_delegateOptimistic_opt_delegatee_updated :
      sim2.(SimState.base)
        .(StakingVaultDelegation.State.opt)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a = addr_c.
    Proof. apply sim_delegateOptimistic_updates_opt_delegatee. Qed.

    Example ex_delegateOptimistic_preserves_std_delegatee :
      sim2.(SimState.base)
        .(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a = addr_b.
    Proof.
      pose proof (sim_delegateOptimistic_preserves_std sim1 addr_a addr_c) as H.
      cbv zeta. unfold sim2.
      rewrite H. apply sim_delegate_updates_std_delegatee.
    Qed.

    (** Cross-checks: dual-axis composition is order-independent on
        the delegate updates (std then opt = opt then std for the
        final delegatee map projection). *)
    Definition sim_std_then_opt : SimState.t :=
      sim_delegateOptimistic (sim_delegate sim0 addr_a addr_b) addr_a addr_c.
    Definition sim_opt_then_std : SimState.t :=
      sim_delegate (sim_delegateOptimistic sim0 addr_a addr_c) addr_a addr_b.

    Example ex_dual_axis_order_std :
      sim_std_then_opt.(SimState.base)
        .(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a
      = sim_opt_then_std.(SimState.base)
        .(StakingVaultDelegation.State.std)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a.
    Proof.
      vm_compute. reflexivity.
    Qed.

    Example ex_dual_axis_order_opt :
      sim_std_then_opt.(SimState.base)
        .(StakingVaultDelegation.State.opt)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a
      = sim_opt_then_std.(SimState.base)
        .(StakingVaultDelegation.State.opt)
        .(StakingVaultDelegation.Ledger.delegatee) addr_a.
    Proof.
      vm_compute. reflexivity.
    Qed.

    (** BySig expired path: when [now > expiry], the operation
        reverts without consuming any state. *)
    Example ex_delegateBySig_expired_reverts :
      sim_delegateBySig sim0 200 addr_b 0 100 (1, 2, 3)
      = revert_expired_signature.
    Proof. vm_compute. reflexivity. Qed.

    Example ex_delegateOptimisticBySig_expired_reverts :
      sim_delegateOptimisticBySig sim0 200 addr_b 0 100 (1, 2, 3)
      = revert_expired_signature.
    Proof. vm_compute. reflexivity. Qed.

  End Examples.

  (** ==================================================================
      Section 9 — Walker-template commentary.

      For each of the four entrypoints, the comment block below
      describes the Yul body's walker arms in detail. These are NOT
      proofs — they're the documentation a future agent (or human
      reviewer) consults when extending the equivalence binding to
      compose with adjacent contracts (e.g.
      ReserveOptimisticGovernor.castVote* uses the same
      [_useCheckedNonce] pattern).

      Cross-reference: [WISDOM.md R080] (dual-axis Trace208
      composition at delegation transitions). ===================== *)

  (** ---- delegate(delegatee) — fun_delegate_15192 ----

        External-fn shape (L10076):
          callvalue guard (revert if non-zero msg.value);
          param_0 := abi_decode_tuple_t_address(4, calldatasize);
          fun_delegate_15192(param_0);

        Internal-fn shape (L10063):
          let acc := caller();
          let_state~ tt := fun__delegate_15292(acc, param_0);

        Walker arms:
          - callvalue iszero (R047 case-split on payable vs nonpayable
            branch — non-payable function so any callvalue reverts).
          - abi-decode (R064 leaf — Qed in AbiEncoding.v).
          - caller read (RunO.Call against the caller primitive).
          - fun__delegate_15292 call: composite walker arm — sub-
            function whose body is inlined via R053 outer-walker
            composition layer. *)

  (** ---- delegateOptimistic(delegatee) — fun_delegateOptimistic_422 ----

        Same structure as [delegate], but the inner-function call is
        [fun__delegateOptimistic_1608] (L9909) instead of
        [fun__delegate_15292]. The two inner functions differ in:

          - the storage slot: 0x0a for [optimisticDelegatees] vs the
            ERC20Votes-inherited [_delegatee] slot;
          - the event signature: [OptimisticDelegateChanged] vs
            [DelegateChanged];
          - the inner [_move*] call:
            [fun__moveOptimisticDelegateVotes_1720] vs
            [fun__moveDelegateVotes_15441]. *)

  (** ---- delegateBySig — fun_delegateBySig_15249 ----

        External-fn shape (L9751):
          callvalue guard;
          (param_0..param_5) := abi_decode_tuple_t_addresst_uint256t_uint256
                                  t_uint8t_bytes32t_bytes32(4, calldatasize);
          fun_delegateBySig_15249(param_0, ..., param_5);

        Internal-fn shape (L9692):
          if (timestamp() > expiry):
            revert(VotesExpiredSignature, expiry);   // selector 0x4683af0e
          let struct_hash := keccak256(abi.encode(
            DELEGATION_TYPEHASH = 0xe48329..., delegatee, nonce, expiry));
          let typed_hash := fun__hashTypedDataV4_14685(struct_hash);
          let signer := fun_recover_5639(typed_hash, v, r, s);
                        (* ECDSA.recover from OZ utils/cryptography *)
          do fun__useCheckedNonce_4715(signer, nonce);
                        (* NoncesUpgradeable._useCheckedNonce — reverts on mismatch *)
          do fun__delegate_15292(signer, delegatee);
                        (* same as direct delegate, but with signer as account *)

        Walker arms:
          - timestamp() primitive (R020 GetBlockTimestamp).
          - if-then-else case-split on expiry comparison (R047).
          - mstore/abi-encode struct hash (R064 AbiEncoding.v).
          - keccak256 (mock primitive — opaque hash).
          - call [_hashTypedDataV4] (composite — folds in
            DOMAIN_SEPARATOR which depends on chain_id + verifying
            contract address — closed via ECDSA.typed_data_hash).
          - call [ECDSA.recover] (mock primitive — see mocks/ECDSA.v).
          - call [_useCheckedNonce] (NoncesUpgradeable — closed via
            Nonces.useCheckedNonce; revert branch under R047).
          - call [_delegate] — reuses fun_delegate's walker. *)

  (** ---- delegateOptimisticBySig — fun_delegateOptimisticBySig_480 ----

        Identical shape to [delegateBySig] but:
          - typehash constant: OPTIMISTIC_DELEGATION_TYPEHASH (L48
            of StakingVault.sol) instead of DELEGATION_TYPEHASH;
          - inner call: fun__delegateOptimistic_1608 instead of
            fun__delegate_15292.

        Both BySig variants share the same revert sentinels:
          - expired:        revert with VotesExpiredSignature(expiry)
          - invalid sig:    handled inside ECDSA.recover (signer = 0)
          - wrong nonce:    handled inside _useCheckedNonce
            (revert with InvalidAccountNonce) *)

  (** ==================================================================
      Section 10 — Trust budget summary (audit-honest framing).

      ==================== HONEST FRAMING ============================
      [Print Assumptions] on the four [run_<fn>_equivalent_methodology]
      theorems reveals only:

        - [ECDSA.Domain.deployment_id : Set] (declared in [mocks/ECDSA.v]
          for the deployment-distinguishing tag).
        - For the two BySig variants: [ECDSA.recover],
          [ECDSA.typed_data_hash],
          [ECDSA.optimistic_delegation_struct_hash] (mock primitives
          pulled in transitively via the [sim_delegateBySig*] result
          shape).

      Crucially, [Print Assumptions] does NOT reveal the Section
      hypotheses — they are universally quantified at Section closure.
      The real trust budget for this file's methodology theorems is:

        - The 5 [Variable] sets ([Codes], [Env], [Walker], [State],
          [hoare], [make_state]) — abstracted Hoare-triple carrier.
        - The lens [project_sim : SimulatedStorage.t -> SimState.t]
          and its [lens_deterministic] hypothesis (trivial under any
          concrete projection).
        - 4 [Variable] declarations for per-fn post-state Skolems
          [proj_post_<fn> : ...] (Skolemized projection).
        - 4 [Hypothesis] declarations for per-fn post-state
          well-formedness (each closes as [reflexivity] under any
          concrete [project_sim] + concrete [proj_post_<fn>]).
        - 4 [Hypothesis] declarations for per-fn composite walker
          Hoare triples ([run_fun_<fn>_at_proj_sim]) — these are the
          audit-time obligations a concrete inheritor must discharge
          via a walker tactic against the StakingVault shallow form.
        - 4 [Variable] declarations for the [walker_<fn>] symbols
          themselves.

      None of these obligations are discharged in this file.

      Composite walker hypothesis count (the audit-time obligations a
      future inheritor would owe):

        - 4 [Hypothesis] declarations for the per-fn post-state
          projection well-formedness (each closes as [reflexivity]
          under the inheritor's concrete [project_sim]).
        - 4 [Hypothesis] declarations for the per-fn composite
          walker Hoare triples (the load-bearing audit obligations).

      For comparison: the 12 R051-blocked mutators across precedent
      files (VersionRegistry, RewardTokenRegistry, Guardian,
      SelectorRegistry, ProposalLib, TimelockControllerOptimistic)
      use the SAME methodology shape — but they instantiate the
      Section against their concrete shallow forms, so their
      milestone Qeds carry genuine semantic content. This file does
      not (yet) — see Section 4 IMPORTANT note for the gating
      blocker. *)

End StakingVaultDelegationMethodology.
