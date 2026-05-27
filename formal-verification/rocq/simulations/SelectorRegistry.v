(** OptimisticSelectorRegistry simulation.

    Mirrors contracts/governance/OptimisticSelectorRegistry.sol — a
    [(target, selector)] allowlist with two coupled set views:

      _targets          : Set<address>
      _allowedSelectors : address -> Set<bytes32>

    The contract maintains the cross-invariant

      target in _targets  <->  _allowedSelectors[target] is non-empty

    by adding to [_targets] only when an actual selector was newly
    inserted, and by removing from [_targets] only when the per-target
    set hits length 0.

    Forbidden targets ([self, governor, timelock, token]) and the
    zero-bytes-4 selector are checked at the add boundary and cause
    reverts.

    The simulation models both sets as lists with no-duplicate
    discipline, and prunes empty per-target entries so structural
    equality matches set-theoretic equality (otherwise the lemma
    [add_remove_restores] wouldn't hold).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module SelectorRegistry.

Definition Address  : Set := U256.t.
Definition Selector : Set := U256.t.   (** bytes4 modeled as small U256.t *)
Definition zero_selector : Selector := 0.

(** State: targets list + per-target selector lists. Both are kept
    duplicate-free; per-target entries with empty selector lists are
    pruned. *)
Module State.
  Record t : Set := {
    targets          : list Address;
    allowedSelectors : list (Address * list Selector);
  }.
End State.

Definition empty_state : State.t := {|
  State.targets := [];
  State.allowedSelectors := [];
|}.

Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

Definition revert_invalid_target   {A : Set} : Result.t A := Result.Revert 0 32.
Definition revert_invalid_selector {A : Set} : Result.t A := Result.Revert 32 32.

(** ----- List helpers ----- *)

Fixpoint list_contains (lst : list U256.t) (x : U256.t) : bool :=
  match lst with
  | [] => false
  | y :: rest => if y =? x then true else list_contains rest x
  end.

Fixpoint list_remove (lst : list U256.t) (x : U256.t) : list U256.t :=
  match lst with
  | [] => []
  | y :: rest => if y =? x then list_remove rest x else y :: list_remove rest x
  end.

Fixpoint allowed_for (mp : list (Address * list Selector)) (target : Address)
    : list Selector :=
  match mp with
  | [] => []
  | (t, sels) :: rest => if t =? target then sels else allowed_for rest target
  end.

Fixpoint set_allowed_for
    (mp : list (Address * list Selector))
    (target : Address) (new_sels : list Selector)
    : list (Address * list Selector) :=
  match mp with
  | [] => [(target, new_sels)]
  | (t, sels) :: rest =>
      if t =? target
      then (t, new_sels) :: rest
      else (t, sels) :: set_allowed_for rest target new_sels
  end.

Fixpoint prune_allowed (mp : list (Address * list Selector))
    : list (Address * list Selector) :=
  match mp with
  | [] => []
  | (t, []) :: rest => prune_allowed rest
  | (t, sels) :: rest => (t, sels) :: prune_allowed rest
  end.

(** Forbidden-target check: in [forbidden] iff equal to one of
    [self_addr, gov_addr, timelock_addr, token_addr]. *)
Definition is_forbidden (forbidden : list Address) (target : Address) : bool :=
  list_contains forbidden target.

(** ----- Operations ----- *)

Definition addSelector
    (s : State.t) (forbidden : list Address)
    (target : Address) (selector : Selector)
    : Result.t State.t :=
  if is_forbidden forbidden target then revert_invalid_target
  else if selector =? zero_selector then revert_invalid_selector
  else
    let sels := allowed_for s.(State.allowedSelectors) target in
    if list_contains sels selector then
      Result.Success s
    else
      let new_sels := selector :: sels in
      let allowed' := set_allowed_for s.(State.allowedSelectors) target new_sels in
      let targets' :=
        if list_contains s.(State.targets) target
        then s.(State.targets)
        else target :: s.(State.targets) in
      Result.Success {|
        State.targets := targets';
        State.allowedSelectors := allowed';
      |}.

Definition removeSelector
    (s : State.t) (target : Address) (selector : Selector)
    : Result.t State.t :=
  let sels := allowed_for s.(State.allowedSelectors) target in
  if list_contains sels selector then
    let new_sels := list_remove sels selector in
    let allowed' := prune_allowed
      (set_allowed_for s.(State.allowedSelectors) target new_sels) in
    let targets' :=
      match new_sels with
      | [] => list_remove s.(State.targets) target
      | _ => s.(State.targets)
      end in
    Result.Success {|
      State.targets := targets';
      State.allowedSelectors := allowed';
    |}
  else
    Result.Success s.

Definition isAllowed (s : State.t) (target : Address) (selector : Selector) : bool :=
  list_contains (allowed_for s.(State.allowedSelectors) target) selector.

(** Cross-invariant: target in [_targets] iff its allowed list is
    non-empty in [_allowedSelectors]. *)
Definition cross_invariant (s : State.t) : Prop :=
  forall target,
    (list_contains s.(State.targets) target = true)
    <-> (length (allowed_for s.(State.allowedSelectors) target) > 0)%nat.

(** Storage-level validity: targets list duplicate-free, every
    per-target selector list duplicate-free, the key list of the
    allowed-selectors map is duplicate-free, and pruning has been
    applied (no empty allowed-entries).

    The [keys_nd] field is required to keep [cross_invariant]
    preserved by [removeSelector]: without it, two map entries for
    the same target could carry independent selector lists, and
    pruning the first to empty would surface the second on lookup,
    breaking the bicondition [target in targets <-> non-empty
    allowed list]. *)
Module Valid.
  Definition no_dup_targets (s : State.t) : Prop :=
    NoDup s.(State.targets).

  Definition no_dup_keys (s : State.t) : Prop :=
    NoDup (map fst s.(State.allowedSelectors)).

  Definition no_dup_selectors (s : State.t) : Prop :=
    Forall (fun ts => NoDup (snd ts)) s.(State.allowedSelectors).

  Definition pruned (s : State.t) : Prop :=
    Forall (fun ts => (length (snd ts) > 0)%nat) s.(State.allowedSelectors).

  Record state (s : State.t) : Prop := {
    targets_nd  : no_dup_targets s;
    keys_nd     : no_dup_keys s;
    sels_nd     : no_dup_selectors s;
    is_pruned   : pruned s;
    cross_inv   : cross_invariant s;
  }.
End Valid.

End SelectorRegistry.
