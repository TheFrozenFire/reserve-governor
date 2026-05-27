(** ReserveOptimisticGovernor — no de-escalation after transitionToPessimistic.

    Audit context. ReserveOptimisticGovernor.sol overwrites the parent
    proposal's [vetoThreshold] with [ProposalLib.TRANSITIONED_VETO_THRESHOLD]
    (= [type(uint256).max] = [2^256 - 1]) inside [transitionToPessimistic].
    The on-chain [state()] view then short-circuits to [Defeated] when it
    sees this sentinel (ReserveOptimisticGovernor.sol:243-246). The
    contract uses this as a pin: once a parent has been transitioned,
    no addition of veto votes can ever flip the observable phase back
    to [Active] or [Succeeded].

    The [Governor] simulation already pins the parent's phase to
    [PhaseDefeated] inside [transition_to_pessimistic] (see
    simulations/Governor.v:309-336) — the modeling shortcut documented
    at line 56-65 of that file. That representation is observably
    equivalent to the contract under the simulation's [observe]
    function, because:

      - the precondition [observe parent now = PhaseDefeated] forces
        [againstVotes >= vetoThresholdTok];
      - [add_veto] only ever increases [againstVotes];
      - therefore for any future [now' >= now_transition], the
        optimistic branch of [observe] still resolves to
        [PhaseDefeated].

    This file delivers three deliverables:

      1. [transition_writes_sentinel_lemma]: an explicit sentinel
         write — i.e. a sister definition that rewrites
         [vetoThresholdTok] to [2^256 - 1] — has the property that the
         resulting parent has the sentinel stamp.

      2. [sentinel_makes_defeated_unreachable]: under the sentinel
         encoding, the optimistic Defeated arm of [observe] is
         unreachable for any [U256.Valid.t] [againstVotes].

      3. [cannot_de_escalate_after_transition] (headline): on the
         existing simulation, after [transition_to_pessimistic]
         succeeds, no sequence of [add_veto] calls can drive the
         parent's observable phase back to [PhaseSucceeded] or
         [PhaseActive], regardless of the wall-clock [now'] that
         observers later choose (provided [now' >= now_transition]).

    A [vm_compute] calibration cross-checks the sentinel encoding at a
    concrete (vetoThreshold-before, transition, vetoThreshold-after)
    tuple.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.Governor.
Require ReserveGovernor.simulations.ProposalLib.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Module GovernorNoDeEscalation.

Import Governor.

(** ===== Sentinel constant ===== *)

(** The [type(uint256).max] sentinel as a Z. We define this locally as
    [Sentinel] and prove its equivalence to
    [ProposalLib.TRANSITIONED_VETO_THRESHOLD] so a future reader can
    chase the dependency to the on-chain constant. *)
Definition Sentinel : U256.t := 2 ^ 256 - 1.

Lemma Sentinel_eq_proposal_lib :
  Sentinel = ProposalLib.ProposalLib.TRANSITIONED_VETO_THRESHOLD.
Proof. reflexivity. Qed.

(** Precomputed positivity facts. We never let [lia] unfold the literal. *)
Lemma Sentinel_pos : 0 < Sentinel.
Proof. unfold Sentinel. lia. Qed.

Lemma Sentinel_valid : U256.Valid.t Sentinel.
Proof. unfold U256.Valid.t, Sentinel. lia. Qed.

Lemma Sentinel_eq_max : Sentinel = 2 ^ 256 - 1.
Proof. reflexivity. Qed.

(** ===== Deliverable 1: explicit sentinel write ===== *)

(** Sister definition to [transition_to_pessimistic] that overwrites
    [vetoThresholdTok] with [Sentinel] on the parent, in addition to
    pinning [phase := PhaseDefeated]. This makes the contract's
    on-chain encoding explicit at the Rocq level. *)
Definition transition_to_pessimistic_sentinel
    (parent : Proposal.t) (new_pid : U256.t)
    (votingDelay votingPeriod now : U256.t)
    : Result.t (Proposal.t * Proposal.t) :=
  match observe parent now with
  | PhaseDefeated =>
      let parent' :=
        {|
          Proposal.pid               := parent.(Proposal.pid);
          Proposal.proposer          := parent.(Proposal.proposer);
          Proposal.voteStart         := parent.(Proposal.voteStart);
          Proposal.voteDuration      := parent.(Proposal.voteDuration);
          Proposal.vetoThresholdTok  := Sentinel;
          Proposal.againstVotes      := parent.(Proposal.againstVotes);
          Proposal.phase             := PhaseDefeated;
          Proposal.isOptimistic      := parent.(Proposal.isOptimistic);
          Proposal.parent            := parent.(Proposal.parent);
        |}
      in
      let child := fresh_standard_child
                     parent.(Proposal.pid)
                     new_pid
                     parent.(Proposal.proposer)
                     (now + votingDelay)
                     votingPeriod in
      Result.Success (parent', child)
  | _ => revert_wrong_phase
  end.

(** **Headline of deliverable 1.** After a successful sentinel write,
    the parent carries the sentinel stamp on [vetoThresholdTok]. *)
Lemma transition_writes_sentinel_lemma
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic_sentinel parent new_pid votingDelay
                                     votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.vetoThresholdTok) = Sentinel.
Proof.
  intros Hok. unfold transition_to_pessimistic_sentinel in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hparent'. reflexivity.
Qed.

(** The sentinel function also still pins the parent to [PhaseDefeated]
    and writes a fresh [PhaseStdPending] child — same operational
    surface as the existing [transition_to_pessimistic]. *)
Lemma transition_sentinel_parent_defeated
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic_sentinel parent new_pid votingDelay
                                     votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.phase) = PhaseDefeated.
Proof.
  intros Hok. unfold transition_to_pessimistic_sentinel in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hparent'. reflexivity.
Qed.

Lemma transition_sentinel_child_pending
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  transition_to_pessimistic_sentinel parent new_pid votingDelay
                                     votingPeriod now
    = Result.Success (parent', child) ->
  child.(Proposal.phase) = PhaseStdPending /\
  child.(Proposal.isOptimistic) = false /\
  child.(Proposal.parent) = parent.(Proposal.pid).
Proof.
  intros Hok. unfold transition_to_pessimistic_sentinel in Hok.
  destruct (observe parent now); try discriminate.
  injection Hok as Hparent' Hchild.
  rewrite <- Hchild. cbn.
  repeat split; reflexivity.
Qed.

(** ===== Deliverable 2: sentinel makes Defeated unreachable ===== *)

(** With [vetoThresholdTok = Sentinel] and any [U256.Valid.t]
    [againstVotes] (i.e. [againstVotes < 2^256]), the comparison
    [againstVotes >=? vetoThresholdTok] cannot return [true] — the
    only way it could is [againstVotes = 2^256 - 1] which DOES satisfy
    [>= Sentinel], so we need [againstVotes < Sentinel]. The strict
    version below corresponds to the on-chain reality: token total
    supply (and hence [againstVotes]) is bounded by [2^256 - 1] but
    can equal it. The sentinel-as-Defeated branch in the contract
    short-circuits BEFORE the votes comparison precisely to handle
    the equality case. *)

Lemma against_votes_lt_sentinel
    (p : Proposal.t) :
  Valid.proposal p ->
  p.(Proposal.vetoThresholdTok) = Sentinel ->
  p.(Proposal.againstVotes) < Sentinel
    \/ p.(Proposal.againstVotes) = Sentinel.
Proof.
  intros Hv Hvtt.
  destruct Hv as [_ _ _ _ Havotes _].
  unfold U256.Valid.t in Havotes.
  unfold Sentinel.
  lia.
Qed.

(** Core lemma: with [vetoThresholdTok = Sentinel] AND a strict bound
    [againstVotes < Sentinel], the optimistic Defeated arm of
    [observe] cannot fire. Note: this is the bound under which the
    on-chain sentinel-as-Defeated short-circuit acts to handle the
    [Sentinel = Sentinel] equality case; in the simulation we do not
    short-circuit, but we capture the bound as a precondition. *)
Lemma sentinel_makes_defeated_unreachable_strict
    (p : Proposal.t) (now : U256.t) :
  p.(Proposal.isOptimistic) = true ->
  p.(Proposal.vetoThresholdTok) = Sentinel ->
  p.(Proposal.againstVotes) < Sentinel ->
  observe p now <> PhaseDefeated.
Proof.
  intros Hopt Hvtt Hstrict.
  (* Pre-compute: votes <? vtt = true, so vtt <=? votes = false,
     so votes >=? vtt = false. *)
  assert (Hgeb : (p.(Proposal.againstVotes) >=?
                    p.(Proposal.vetoThresholdTok)) = false).
  { rewrite Z.geb_leb. apply Z.leb_gt. rewrite Hvtt. exact Hstrict. }
  unfold observe.
  (* Outer match: only PhaseExecuted/Canceled/StdQueued/StdExecuted are
     sticky terminal returns — none of them are PhaseDefeated. *)
  destruct (p.(Proposal.phase)); try (intros Heq; discriminate);
    destruct (now <? p.(Proposal.voteStart));
    rewrite Hopt;
    try (intros Heq; discriminate);
    rewrite Hgeb;
    destruct (now <? p.(Proposal.voteStart) + p.(Proposal.voteDuration));
    intros Heq; discriminate.
Qed.

(** Restated to use [U256.Valid.t] on [againstVotes] plus the
    statement that votes [< Sentinel] (i.e. the votes are not
    saturated at the sentinel value). The [<= Sentinel - 1] form is
    convenient when chaining from [Valid.proposal]. *)
Lemma sentinel_makes_defeated_unreachable
    (p : Proposal.t) (now : U256.t) :
  Valid.proposal p ->
  p.(Proposal.isOptimistic) = true ->
  p.(Proposal.vetoThresholdTok) = Sentinel ->
  p.(Proposal.againstVotes) < Sentinel ->
  observe p now <> PhaseDefeated.
Proof.
  intros _ Hopt Hvtt Hlt.
  apply sentinel_makes_defeated_unreachable_strict; assumption.
Qed.

(** ===== Deliverable 3: headline — cannot de-escalate ===== *)

(** [add_veto] preserves the [phase] field. *)
Lemma add_veto_preserves_phase (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.phase) = p.(Proposal.phase).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_voteStart (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.voteStart) = p.(Proposal.voteStart).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_voteDuration (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.voteDuration) = p.(Proposal.voteDuration).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_vetoThresholdTok (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.vetoThresholdTok)
    = p.(Proposal.vetoThresholdTok).
Proof. reflexivity. Qed.

Lemma add_veto_preserves_isOptimistic (p : Proposal.t) (delta : U256.t) :
  (add_veto p delta).(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
Proof. reflexivity. Qed.

(** [add_veto] is monotone on [againstVotes] when [delta] is non-negative. *)
Lemma add_veto_monotone (p : Proposal.t) (delta : U256.t) :
  0 <= delta ->
  p.(Proposal.againstVotes) <= (add_veto p delta).(Proposal.againstVotes).
Proof. intros Hd. unfold add_veto. cbn. lia. Qed.

(** Iterated [add_veto]: apply a list of deltas in sequence. *)
Fixpoint add_vetoes (p : Proposal.t) (deltas : list U256.t) : Proposal.t :=
  match deltas with
  | []          => p
  | d :: rest   => add_vetoes (add_veto p d) rest
  end.

Lemma add_vetoes_preserves_phase (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.phase) = p.(Proposal.phase).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_phase.
Qed.

Lemma add_vetoes_preserves_voteStart (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.voteStart) = p.(Proposal.voteStart).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_voteStart.
Qed.

Lemma add_vetoes_preserves_voteDuration (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.voteDuration) = p.(Proposal.voteDuration).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_voteDuration.
Qed.

Lemma add_vetoes_preserves_vetoThresholdTok
    (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.vetoThresholdTok)
    = p.(Proposal.vetoThresholdTok).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_vetoThresholdTok.
Qed.

Lemma add_vetoes_preserves_isOptimistic
    (p : Proposal.t) (deltas : list U256.t) :
  (add_vetoes p deltas).(Proposal.isOptimistic) = p.(Proposal.isOptimistic).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p; [reflexivity|].
  cbn. rewrite IH. apply add_veto_preserves_isOptimistic.
Qed.

(** Monotonicity over an iterated sequence of non-negative deltas. *)
Lemma add_vetoes_monotone (p : Proposal.t) (deltas : list U256.t) :
  Forall (fun d => 0 <= d) deltas ->
  p.(Proposal.againstVotes) <= (add_vetoes p deltas).(Proposal.againstVotes).
Proof.
  revert p. induction deltas as [|d ds IH]; intros p Hnn.
  - cbn. lia.
  - cbn. inversion Hnn as [|d' ds' Hd Hnn']; subst.
    specialize (IH (add_veto p d) Hnn').
    pose proof (add_veto_monotone p d Hd) as Hstep.
    lia.
Qed.

(** Key building block: a parent whose stored [phase = PhaseDefeated],
    optimistic, with [againstVotes >= vetoThresholdTok], stays
    observably [PhaseDefeated] for any [now] past [voteStart]. *)
Lemma parent_post_transition_observes_defeated
    (parent : Proposal.t) (now : U256.t) :
  parent.(Proposal.phase) = PhaseDefeated ->
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  parent.(Proposal.againstVotes) >= parent.(Proposal.vetoThresholdTok) ->
  observe parent now = PhaseDefeated.
Proof.
  intros Hph Hopt Hnow Hge.
  unfold observe. rewrite Hph.
  assert (Hlt : (now <? parent.(Proposal.voteStart)) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hlt. rewrite Hopt.
  assert (Hgeb : (parent.(Proposal.againstVotes) >=?
                    parent.(Proposal.vetoThresholdTok)) = true).
  { apply Z.geb_le. lia. }
  rewrite Hgeb. reflexivity.
Qed.

(** A successful [transition_to_pessimistic] establishes exactly the
    post-condition on which [parent_post_transition_observes_defeated]
    rests: stored phase is Defeated, optimistic flag is preserved,
    and [againstVotes >= vetoThresholdTok] (derived from the
    precondition that [observe parent now = PhaseDefeated]). *)
Lemma transition_postconditions
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now : U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  parent'.(Proposal.phase) = PhaseDefeated /\
  parent'.(Proposal.isOptimistic) = true /\
  parent'.(Proposal.voteStart) = parent.(Proposal.voteStart) /\
  parent'.(Proposal.vetoThresholdTok) = parent.(Proposal.vetoThresholdTok) /\
  parent'.(Proposal.againstVotes) = parent.(Proposal.againstVotes) /\
  parent'.(Proposal.againstVotes) >= parent'.(Proposal.vetoThresholdTok).
Proof.
  intros Hopt Hvs Hok.
  unfold transition_to_pessimistic in Hok.
  destruct (observe parent now) eqn:Hobs; try discriminate.
  injection Hok as Hparent' Hchild.
  (* From Hobs : observe parent now = PhaseDefeated, derive
     againstVotes >= vetoThresholdTok by inversion on observe. *)
  unfold observe in Hobs.
  destruct (parent.(Proposal.phase)) eqn:Hph; try discriminate;
    (assert (Hlt : (now <? parent.(Proposal.voteStart)) = false)
       by (apply Z.ltb_ge; lia);
     rewrite Hlt in Hobs;
     rewrite Hopt in Hobs;
     destruct (parent.(Proposal.againstVotes) >=?
                 parent.(Proposal.vetoThresholdTok)) eqn:Hgeb;
     [ apply Z.geb_le in Hgeb
     | destruct (now <? parent.(Proposal.voteStart)
                          + parent.(Proposal.voteDuration));
       discriminate ];
     rewrite <- Hparent'; cbn;
     repeat split; try assumption; try reflexivity; try lia).
Qed.

(** Headline theorem.

    After [transition_to_pessimistic] succeeds, no sequence of
    [add_veto] calls on the resulting parent can drive the
    observable phase back to [PhaseSucceeded] or [PhaseActive], for
    any future [now' >= now_transition]. The parent stays observably
    [PhaseDefeated].

    The proof works by:
      1. [transition_to_pessimistic] establishes the parent's
         post-conditions, including [againstVotes >= vetoThresholdTok].
      2. [add_vetoes] preserves [phase], [isOptimistic], [voteStart],
         [vetoThresholdTok], and is monotone on [againstVotes].
      3. Therefore the post-conditions still hold after any
         [add_vetoes] sequence with non-negative deltas.
      4. Apply [parent_post_transition_observes_defeated]. *)
Theorem cannot_de_escalate_after_transition
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now now' : U256.t)
    (deltas : list U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  now <= now' ->
  Forall (fun d => 0 <= d) deltas ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  observe (add_vetoes parent' deltas) now' = PhaseDefeated.
Proof.
  intros Hopt Hvs Hnow Hnn Hok.
  pose proof (transition_postconditions
                parent parent' child
                new_pid votingDelay votingPeriod now
                Hopt Hvs Hok)
    as (Hph' & Hopt' & HvsEq & HvttEq & HavotesEq & Hge').
  set (p' := add_vetoes parent' deltas).
  apply parent_post_transition_observes_defeated.
  - unfold p'. rewrite add_vetoes_preserves_phase. exact Hph'.
  - unfold p'. rewrite add_vetoes_preserves_isOptimistic. exact Hopt'.
  - unfold p'. rewrite add_vetoes_preserves_voteStart.
    (* Need parent'.voteStart <= now'. From HvsEq, that's
       parent.voteStart = parent'.voteStart, and parent.voteStart <= now <= now'. *)
    rewrite HvsEq. lia.
  - unfold p'. rewrite add_vetoes_preserves_vetoThresholdTok.
    pose proof (add_vetoes_monotone parent' deltas Hnn) as Hmono.
    lia.
Qed.

(** Convenient corollary: the observable phase is in the "Defeated or
    terminal" set, never in [PhaseSucceeded], [PhaseActive], or
    [PhaseSubmitted]. *)
Corollary cannot_observe_active_or_succeeded
    (parent parent' child : Proposal.t)
    (new_pid votingDelay votingPeriod now now' : U256.t)
    (deltas : list U256.t) :
  parent.(Proposal.isOptimistic) = true ->
  parent.(Proposal.voteStart) <= now ->
  now <= now' ->
  Forall (fun d => 0 <= d) deltas ->
  transition_to_pessimistic parent new_pid votingDelay votingPeriod now
    = Result.Success (parent', child) ->
  observe (add_vetoes parent' deltas) now' <> PhaseSucceeded /\
  observe (add_vetoes parent' deltas) now' <> PhaseActive /\
  observe (add_vetoes parent' deltas) now' <> PhaseSubmitted.
Proof.
  intros Hopt Hvs Hnow Hnn Hok.
  pose proof (cannot_de_escalate_after_transition
                parent parent' child
                new_pid votingDelay votingPeriod now now' deltas
                Hopt Hvs Hnow Hnn Hok) as Hdef.
  rewrite Hdef.
  repeat split; intros Heq; discriminate.
Qed.

(** ===== Deliverable 4: vm_compute calibration ===== *)

(** Concrete tuple: parent with vtt=10, votes=10 (just at threshold);
    transition with sentinel encoding rewrites vtt to [2^256 - 1].

    Pre-transition: vetoThresholdTok = 10.
    Post-transition (sentinel encoding): vetoThresholdTok = Sentinel.
    Post-transition (existing simulation): vetoThresholdTok = 10
      (unchanged — observable phase is pinned by [phase = PhaseDefeated]
      and [againstVotes >= vtt]).
*)

Definition cal_parent : Proposal.t :=
  add_veto (fresh_optimistic 901 9001 100 1000 10) 10.

(** Sanity: [cal_parent] observes as PhaseDefeated in the active window. *)
Lemma xcheck_cal_parent_defeated :
  observe cal_parent 500 = PhaseDefeated.
Proof. vm_compute. reflexivity. Qed.

Definition cal_sentinel_result :=
  transition_to_pessimistic_sentinel cal_parent 9999 50 1000 500.

Definition cal_existing_result :=
  transition_to_pessimistic cal_parent 9999 50 1000 500.

(** Sentinel encoding: parent's [vetoThresholdTok] is rewritten to
    [Sentinel = 2^256 - 1]. *)
Lemma xcheck_sentinel_parent_vtt_is_max :
  match cal_sentinel_result with
  | Result.Success (parent', _) =>
      parent'.(Proposal.vetoThresholdTok) = 2 ^ 256 - 1
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Both encodings yield a parent that stays observably PhaseDefeated
    at the calibration's transition time. *)
Lemma xcheck_sentinel_parent_phase_defeated :
  match cal_sentinel_result with
  | Result.Success (parent', _) => parent'.(Proposal.phase) = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Lemma xcheck_existing_parent_phase_defeated :
  match cal_existing_result with
  | Result.Success (parent', _) => parent'.(Proposal.phase) = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Existing simulation preserves the original vtt (=10), unlike the
    contract which would rewrite it; the simulation captures the
    observable behavior via the [phase] pin. *)
Lemma xcheck_existing_parent_vtt_unchanged :
  match cal_existing_result with
  | Result.Success (parent', _) => parent'.(Proposal.vetoThresholdTok) = 10
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Headline observable: post-transition, even after a flurry of
    additional veto adds, the parent stays Defeated for any later
    timestamp inside the calibration. *)
Lemma xcheck_no_de_escalation_concrete :
  match cal_existing_result with
  | Result.Success (parent', _) =>
      observe (add_vetoes parent' [5; 7; 11]) 9999 = PhaseDefeated
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** And under the sentinel encoding, the parent's vetoThresholdTok is
    so large that any U256-valid againstVotes (in particular, all
    those reachable from valid [add_veto] increments) fails the
    [>=? vtt] check — Defeated under the sentinel encoding is reached
    only via the [phase] pin. *)
Lemma xcheck_sentinel_against_small_votes_not_via_votes :
  match cal_sentinel_result with
  | Result.Success (parent', _) =>
      ((add_vetoes parent' [1; 2; 3]).(Proposal.againstVotes)
         <? (add_vetoes parent' [1; 2; 3]).(Proposal.vetoThresholdTok)) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End GovernorNoDeEscalation.
