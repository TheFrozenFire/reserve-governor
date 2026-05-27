(** RewardTokenRegistry simulation.

    Mirrors contracts/staking/RewardTokenRegistry.sol — a role-gated
    allowlist of ERC20 tokens that StakingVault is permitted to register
    as reward tokens.

      _rewardTokens : Set<address>

    The contract wraps an OpenZeppelin EnumerableSet.AddressSet behind
    two role-gated mutators and two view functions:

      registerRewardToken(addr)      onlyOwner
      unregisterRewardToken(addr)    onlyOwnerOrEmergencyCouncil
      rewardTokens() view -> address[]
      isRegistered(addr) view -> bool

    Critical asymmetry vs OptimisticSelectorRegistry: register/unregister
    REVERT on the "no-op" path. The contract uses `require(set.add(...))`
    and `require(set.remove(...))`, where EnumerableSet returns false to
    signal that the element was already in / out of the set. The Rocq
    model surfaces these as Result.Revert rather than silently returning
    the prior state.

    Boundary checks at register:
      msg.sender owner-check (modeled as a [is_owner : bool] flag)
      rewardToken == address(0)  -> ZeroAddress revert

    At unregister:
      msg.sender owner-or-emergency-council check
      (modeled as [is_owner_or_council : bool] flag)

    The simulation models the set as a duplicate-free list. Validity is
    a single [NoDup] property (no cross-invariant between coupled sets,
    so this is structurally simpler than SelectorRegistry). List helpers
    are reproduced locally rather than imported across domain boundaries
    — matches the project convention of self-contained simulations and
    avoids a cross-file dependency on SelectorRegistry's selector-typed
    helpers (the helpers are uniform in [U256.t], but importing
    SelectorRegistry to reuse them would leak unrelated types and the
    forbidden-target machinery into this module's namespace).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.Lists.List.
Import ListNotations.

Module RewardTokenRegistry.

Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** State: the duplicate-free list of registered reward tokens. *)
Module State.
  Record t : Set := {
    rewardTokens : list Address;
  }.
End State.

Definition empty_state : State.t := {|
  State.rewardTokens := [];
|}.

Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Placeholder revert tags; Yul offsets are pinned during equivalence. *)
Definition revert_invalid_caller       {A : Set} : Result.t A := Result.Revert 0  32.
Definition revert_zero_address         {A : Set} : Result.t A := Result.Revert 32 32.
Definition revert_already_registered   {A : Set} : Result.t A := Result.Revert 64 32.
Definition revert_not_registered       {A : Set} : Result.t A := Result.Revert 96 32.

(** ----- List helpers (set semantics over [Address = U256.t]). ----- *)

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

(** ----- Operations ----- *)

(** [registerRewardToken s token is_owner].

    Reverts if:
      - caller is not owner ([is_owner = false])
      - token is the zero address
      - token is already in the set (mirrors [require(set.add(...))]).

    Otherwise appends the token to the registered list. *)
Definition registerRewardToken
    (s : State.t) (token : Address) (is_owner : bool)
    : Result.t State.t :=
  if negb is_owner then revert_invalid_caller
  else if token =? zero_address then revert_zero_address
  else if list_contains s.(State.rewardTokens) token then revert_already_registered
  else
    Result.Success {|
      State.rewardTokens := token :: s.(State.rewardTokens);
    |}.

(** [unregisterRewardToken s token is_owner_or_council].

    Reverts if:
      - caller is neither owner nor emergency council
      - token is not in the set (mirrors [require(set.remove(...))]).

    Otherwise drops every occurrence of [token] (NoDup keeps that at
    most one). *)
Definition unregisterRewardToken
    (s : State.t) (token : Address) (is_owner_or_council : bool)
    : Result.t State.t :=
  if negb is_owner_or_council then revert_invalid_caller
  else if list_contains s.(State.rewardTokens) token then
    Result.Success {|
      State.rewardTokens := list_remove s.(State.rewardTokens) token;
    |}
  else revert_not_registered.

(** View functions. *)
Definition isRegistered (s : State.t) (token : Address) : bool :=
  list_contains s.(State.rewardTokens) token.

Definition rewardTokens (s : State.t) : list Address :=
  s.(State.rewardTokens).

(** Storage-level validity: the underlying [EnumerableSet] never holds
    duplicates. The contract preserves this by construction: [set.add]
    refuses inserts of an existing element (here surfaced as the
    [AlreadyRegistered] revert), and [set.remove] only drops what is
    already present. *)
Module Valid.
  Definition no_dup_tokens (s : State.t) : Prop :=
    NoDup s.(State.rewardTokens).

  Record state (s : State.t) : Prop := {
    tokens_nd : no_dup_tokens s;
  }.
End Valid.

End RewardTokenRegistry.
