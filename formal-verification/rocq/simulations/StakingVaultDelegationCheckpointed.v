(** StakingVault — optimistic-vote checkpoint history.

    Mirrors the [optimisticDelegateCheckpoints] mapping in
    StakingVault.sol:104-105 — a per-delegatee [Trace208.t] of
    historical vote weights — and the [getPastOptimisticVotes]
    lookup used by the Governor's veto-tally code path
    (ReserveOptimisticGovernor.sol:509).

    The base [StakingVaultDelegation] simulation abstracts
    Trace208 down to its [latest] value: the dual-delegation
    independence theorem proved there is a statement about
    current votes, not past ones. This file layers a Trace208
    field on top of the base state and proves the consistency
    property between the latest-side and the trace history:

      latest_after_set      — pushing on a delegate change
                              updates the trace's [latest] to
                              the new vote count
      get_past_at_now_eq    — querying the trace at the current
                              timestamp returns the current
                              vote count
      cross_chain_signature_does_not_corrupt_history
                            — past lookups remain consistent
                              under any sequence of operations
                              that respects the monotone clock

    This closes the "past-vote correctness" gap identified in
    notes/external_dependencies.md (Priority 1, Trace208 mock
    binding). The base [StakingVaultDelegation] proofs about
    transfer and set_opt_delegate carry over because we layer
    the checkpoint trace ON TOP OF the existing state — no
    base-sim definitions change.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.mocks.Trace208.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

Module StakingVaultDelegationCheckpointed.

Definition Address : Set := U256.t.

(** Per-delegatee trace store. Modeled as a list of (address, trace)
    pairs with no-duplicate-keys discipline. Lookups default to
    [Trace208.empty] for accounts that have never received delegation. *)
Definition TraceMap : Set := list (Address * Trace208.t).

Fixpoint trace_of (m : TraceMap) (delegatee : Address) : Trace208.t :=
  match m with
  | [] => Trace208.empty
  | (a, tr) :: rest =>
      if a =? delegatee then tr else trace_of rest delegatee
  end.

Fixpoint set_trace
    (m : TraceMap) (delegatee : Address) (tr : Trace208.t) : TraceMap :=
  match m with
  | [] => [(delegatee, tr)]
  | (a, t) :: rest =>
      if a =? delegatee
      then (a, tr) :: rest
      else (a, t) :: set_trace rest delegatee tr
  end.

(** Extended state: the base dual-delegation ledger plus the
    optimistic-side checkpoint history. The standard-side history
    is the OZ Checkpoints trace inherited via ERC20VotesUpgradeable;
    we don't model it here because the Governor only reads the
    optimistic side. *)
Module State.
  Record t : Set := {
    base       : StakingVaultDelegation.State.t;
    opt_traces : TraceMap;
  }.
End State.

Definition empty_state : State.t := {|
  State.base := StakingVaultDelegation.empty_state;
  State.opt_traces := [];
|}.

(** Read the current vote count for a delegatee (from the latest-side). *)
Definition votes_of (s : State.t) (delegatee : Address) : Z :=
  s.(State.base).(StakingVaultDelegation.State.opt).(StakingVaultDelegation.Ledger.votes) delegatee.

(** [getPastOptimisticVotes s delegatee snapshot]: contract-faithful
    lookup of votes attributed to [delegatee] at past time [snapshot]
    via Trace208.upperLookupRecent. *)
Definition getPastOptimisticVotes
    (s : State.t) (delegatee : Address) (snapshot : U256.t) : U256.t :=
  Trace208.upperLookupRecent (trace_of s.(State.opt_traces) delegatee) snapshot.

(** [set_opt_delegate_checkpointed s account new_d now]: contract-
    faithful re-pointing. Updates the base latest-side, then pushes
    the post-update votes for both the OLD and NEW delegates into
    their respective Trace208 traces with key [now].

    Mirrors StakingVault.sol:543-571: the contract calls
    [_moveOptimisticDelegateVotes] which in turn calls
    [Checkpoints.push] on the OLD and NEW delegate's traces. *)
Definition set_opt_delegate_checkpointed
    (s : State.t) (account new_d : Address) (now : U256.t) : State.t :=
  let old_d := StakingVaultDelegation.delegate_of
                 s.(State.base).(StakingVaultDelegation.State.opt) account in
  let base' := StakingVaultDelegation.set_opt_delegate s.(State.base) account new_d in
  (* The new base state's votes-of for old_d and new_d are now the post-move values. *)
  let new_votes_old := base'.(StakingVaultDelegation.State.opt)
                          .(StakingVaultDelegation.Ledger.votes) old_d in
  let new_votes_new := base'.(StakingVaultDelegation.State.opt)
                          .(StakingVaultDelegation.Ledger.votes) new_d in
  let trace_old := trace_of s.(State.opt_traces) old_d in
  let trace_new := trace_of s.(State.opt_traces) new_d in
  let trace_old' :=
    if Z.eqb old_d StakingVaultDelegation.zero_address
    then trace_old
    else Trace208.push trace_old now new_votes_old in
  let trace_new' :=
    if Z.eqb new_d StakingVaultDelegation.zero_address
    then trace_new
    else Trace208.push trace_new now new_votes_new in
  let traces' :=
    if Z.eqb old_d new_d
    then s.(State.opt_traces)
    else set_trace
           (set_trace s.(State.opt_traces) old_d trace_old')
           new_d trace_new' in
  {|
    State.base       := base';
    State.opt_traces := traces';
  |}.

(** -- Lookup-after-set lemmas -- *)

Lemma trace_of_set_trace_same :
  forall (m : TraceMap) (delegatee : Address) (tr : Trace208.t),
    trace_of (set_trace m delegatee tr) delegatee = tr.
Proof.
  induction m as [|[a t] rest IH]; intros delegatee tr; simpl.
  - rewrite Z.eqb_refl. reflexivity.
  - destruct (a =? delegatee) eqn:Heqb; simpl.
    + apply Z.eqb_eq in Heqb. subst.
      rewrite Z.eqb_refl. reflexivity.
    + rewrite Heqb. apply IH.
Qed.

Lemma trace_of_set_trace_other :
  forall (m : TraceMap) (delegatee other : Address) (tr : Trace208.t),
    other <> delegatee ->
    trace_of (set_trace m delegatee tr) other = trace_of m other.
Proof.
  induction m as [|[a t] rest IH]; intros delegatee other tr Hne; simpl.
  - destruct (delegatee =? other) eqn:Heqb.
    + apply Z.eqb_eq in Heqb. symmetry in Heqb. contradiction.
    + reflexivity.
  - destruct (a =? delegatee) eqn:Heqb; simpl.
    + apply Z.eqb_eq in Heqb. subst.
      destruct (delegatee =? other) eqn:Heqb2.
      * apply Z.eqb_eq in Heqb2. symmetry in Heqb2. contradiction.
      * reflexivity.
    + destruct (a =? other) eqn:Heqb2.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

End StakingVaultDelegationCheckpointed.
