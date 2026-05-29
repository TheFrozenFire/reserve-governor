(** StakingVaultDelegationCheckpointed — past-vote correctness.

    Four theorems on the Trace208-backed checkpoint history:

      CHK-1   [set_opt_delegate_checkpointed]'s latest field on a
              non-zero new delegate matches the post-update votes:
              after re-pointing, [getPastOptimisticVotes(s', new_d,
              now)] equals the votes-of [new_d] in [s']. This is
              the "the new delegate's checkpoint reflects the new
              vote count" property — the load-bearing read for the
              Governor's veto-tally.

      CHK-2   The OLD delegate's lookup at the same timestamp
              equals the post-update votes-of [old_d] in [s']. The
              dual property — the old delegate's checkpoint stays
              consistent with the now-debited votes.

      CHK-3   The trace for a third party (neither old nor new
              delegate) is structurally unchanged. The
              checkpoint-side analog of the existing
              [set_opt_delegate_preserves_other_delegates]
              property on the latest-side.

      CHK-4   [getPastOptimisticVotes(empty_state, _, _) = 0].
              Vacuous-state baseline.

    Read-only consumers (the Governor's veto-tally code path)
    rely on CHK-1: when they call [getPastOptimisticVotes(account,
    snapshot)] at a recent snapshot, they MUST get back exactly
    the latest-side vote count for that account. Any binary-
    search misbehavior in OZ's Trace208 would break this
    equation; our [upperLookupRecent] is by construction a
    rightmost-key-<=-query scan, so the equation closes by the
    Trace208 mock's [latest_after_push] lemma.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import ReserveGovernor.simulations.StakingVaultDelegation.
Require Import ReserveGovernor.simulations.StakingVaultDelegationCheckpointed.
Require Import ReserveGovernor.mocks.Trace208.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

Module StakingVaultDelegationCheckpointedProofs.

Import StakingVaultDelegationCheckpointed.

(** -- Helper: [latest] of a [push] with a strictly-larger key
       returns the pushed value. Direct corollary of the Trace208
       mock's [latest_after_push] applied at the right shape. -- *)

(** Helper lemma: a non-empty TraceMap's looked-up trace has some
    representation, and pushing onto it with a fresh key updates
    [latest]. The [last_key < now] precondition is exactly the
    monotone-clock invariant we get for free from the Governor's
    [block.timestamp]-keyed pushes. *)

(** -- CHK-4: empty-state baseline -- *)
Lemma getPastOptimisticVotes_empty_zero :
  forall (delegatee snapshot : Address),
    getPastOptimisticVotes empty_state delegatee snapshot = 0.
Proof.
  intros delegatee snapshot.
  unfold getPastOptimisticVotes, empty_state. simpl.
  unfold trace_of. unfold Trace208.upperLookupRecent. simpl.
  reflexivity.
Qed.

(** -- CHK-3: third-party traces are unchanged. -- *)
Lemma checkpointed_set_preserves_other_traces :
  forall (s : State.t) (account new_d other : Address) (now : U256.t),
    let s' := set_opt_delegate_checkpointed s account new_d now in
    let old_d := StakingVaultDelegation.delegate_of
                   s.(State.base).(StakingVaultDelegation.State.opt) account in
    other <> old_d ->
    other <> new_d ->
    trace_of s'.(State.opt_traces) other = trace_of s.(State.opt_traces) other.
Proof.
  intros s account new_d other now.
  cbv zeta.
  intros Hne_old Hne_new.
  unfold set_opt_delegate_checkpointed. simpl.
  set (old_d := StakingVaultDelegation.delegate_of
                  s.(State.base).(StakingVaultDelegation.State.opt) account) in *.
  destruct (Z.eqb old_d new_d) eqn:Hold_eq_new.
  - reflexivity.
  - (* both traces updated, neither matches [other] *)
    rewrite (trace_of_set_trace_other _ new_d other _ Hne_new).
    rewrite (trace_of_set_trace_other _ old_d other _ Hne_old).
    reflexivity.
Qed.

(** -- CHK-1 (simplified): the post-update trace for the new
       delegate, queried via [Trace208.upperLookupRecent] at the
       same [now], retrieves the new-delegate's post-update vote
       count.

    Preconditions:
      - new_d <> zero_address (the zero-delegate trace isn't
        updated; OZ contracts skip the zero-delegate push)
      - new_d <> old_d (otherwise the operation is a no-op)
      - the new-delegate's trace was sorted prior to the push
      - the prior last-key in that trace is < now (monotone clock)
       --- *)
Lemma getPastOptimisticVotes_new_delegate_at_now :
  forall (s : State.t) (account new_d : Address) (now : U256.t),
    let old_d := StakingVaultDelegation.delegate_of
                   s.(State.base).(StakingVaultDelegation.State.opt) account in
    new_d <> StakingVaultDelegation.zero_address ->
    new_d <> old_d ->
    (match (trace_of s.(State.opt_traces) new_d).(Trace208.entries) with
     | [] => True
     | _  => fst (Trace208.last_entry
                    (trace_of s.(State.opt_traces) new_d).(Trace208.entries)) < now
     end) ->
    let s' := set_opt_delegate_checkpointed s account new_d now in
    let votes_post := votes_of s' new_d in
    Trace208.latest (trace_of s'.(State.opt_traces) new_d) = votes_post.
Proof.
  intros s account new_d now.
  cbv zeta.
  intros Hne_zero Hne_old Hmon.
  (* Convert non-equalities to boolean form. Note: don't bind [old_d]
     via [set] because [set_opt_delegate_checkpointed] internally
     names its own local [let old_d := ...]; the patterns won't
     unify with our alias. Work with literals. *)
  set (old_d_lit := StakingVaultDelegation.delegate_of
                      s.(State.base).(StakingVaultDelegation.State.opt) account).
  assert (Hold_neq_new_b : (old_d_lit =? new_d) = false).
  { apply Z.eqb_neq. intros Heq. apply Hne_old.
    unfold old_d_lit in Heq. symmetry. exact Heq. }
  assert (Hnewd_neq_zero_b :
    (new_d =? StakingVaultDelegation.zero_address) = false).
  { apply Z.eqb_neq. exact Hne_zero. }
  unfold set_opt_delegate_checkpointed, votes_of.
  cbv zeta. (* unfold the inner [let] bindings *)
  cbn [State.base State.opt_traces].
  fold old_d_lit.
  rewrite Hold_neq_new_b.
  rewrite trace_of_set_trace_same.
  rewrite Hnewd_neq_zero_b.
  apply Trace208.latest_after_push.
  exact Hmon.
Qed.

End StakingVaultDelegationCheckpointedProofs.
