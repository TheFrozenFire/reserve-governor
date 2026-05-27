(** StakingVault — dual delegation surface simulation.

    Mirrors contracts/staking/StakingVault.sol's overlay of an
    *optimistic* delegate set on top of OZ's standard ERC20Votes
    checkpoints. The contract carries TWO parallel ledgers:

      - standard delegatees / votes — inherited from
        [ERC20VotesUpgradeable]; the contract code does not duplicate
        the bookkeeping but its [_update] hook invokes the OZ
        machinery first (via [super._update]).

      - optimistic delegatees / votes — additional storage
        ([optimisticDelegatees], [optimisticDelegateCheckpoints]),
        manipulated by [_delegateOptimistic] and
        [_moveOptimisticDelegateVotes], called *after* the OZ side in
        every [_update].

    Both ledgers update on every transfer; neither perturbs the other.
    This simulation models both ledgers as parallel address->Z maps so
    we can reason about their independence directly. The OZ-internal
    Trace208 checkpoint history is abstracted to just its [latest]
    value — independence and conservation are statements about that
    latest value, and the OZ side is audited separately by the
    upstream rocq-of-solidity corpus.

    What is NOT modeled here:
      - The full Trace208 checkpoint stack (historical [getVotes] /
        [getPastVotes]). Those are pure OZ surface; their correctness
        is independent of the optimistic overlay.
      - The signature-based [delegateOptimisticBySig] auth path — that
        ties to the broader OZ permit / EIP-712 layer.
      - block.timestamp / clock(). Both ledgers timestamp their pushes
        with the same clock; equality of "latest" values across
        scenarios doesn't depend on the timestamp.

    Source references (StakingVault.sol):
      - L104-L105   optimisticDelegatees / optimisticDelegateCheckpoints
      - L499-L506   _update (transfer entry, both ledgers move)
      - L543-L549   _delegateOptimistic
      - L551-L571   _moveOptimisticDelegateVotes
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module StakingVaultDelegation.

(** Address model — opaque [U256.t], with [zero_address = 0]
    representing [address(0)] (the mint/burn sink/source and the
    "undelegated" default). *)
Definition Address : Set := U256.t.
Definition zero_address : Address := 0.

(** A total-function map from addresses to votes / delegatees. Concrete
    impl: total function [Address -> Z]. Updated pointwise via [upd].
    [vm_compute] handles these readily without us writing a Finite
    Map machinery. *)
Definition Map : Set := Address -> Z.

Definition empty_map : Map := fun _ => 0.

(** [const_map c]: every address maps to [c]. For the default
    delegatee map we use [const_map zero_address] — every account
    starts "undelegated", i.e. delegates to [address(0)], which is
    exactly the OZ default before any [delegate(...)] call. *)
Definition const_map (c : Z) : Map := fun _ => c.

(** Pointwise update. Uses [Z.eqb] so it's decidable for vm_compute. *)
Definition upd (m : Map) (k : Address) (v : Z) : Map :=
  fun k' => if Z.eqb k' k then v else m k'.

(** One ledger's worth of state: a delegatee map (account -> delegate)
    and a vote-count map (delegate -> current votes). The shape is
    identical for [StdDelegate] and [OptDelegate]; we package it as
    one [Ledger.t] used twice. *)
Module Ledger.
  Record t : Set := {
    delegatee : Map;   (** account -> delegate                *)
    votes     : Map;   (** delegate -> current vote count    *)
  }.
End Ledger.

Definition empty_ledger : Ledger.t := {|
  Ledger.delegatee := const_map zero_address;
  Ledger.votes     := empty_map;
|}.

(** The two parallel ledgers are structurally distinct so we name them
    after their roles. Same shape, different mappings on transfer. *)
Module StdDelegate.
  Definition t : Set := Ledger.t.
End StdDelegate.

Module OptDelegate.
  Definition t : Set := Ledger.t.
End OptDelegate.

(** Combined contract storage: balances plus both ledgers. *)
Module State.
  Record t : Set := {
    balances : Map;              (** account -> {share} balance *)
    std      : StdDelegate.t;
    opt      : OptDelegate.t;
  }.
End State.

Definition empty_state : State.t := {|
  State.balances := empty_map;
  State.std      := empty_ledger;
  State.opt      := empty_ledger;
|}.

(** ---- The move-votes primitive ----
    Direct port of [_moveOptimisticDelegateVotes] (StakingVault.sol
    L551-L571). The same code shape is used by OZ's
    [ERC20Votes._moveDelegateVotes] — we share one definition for
    both ledgers.

    Short-circuit: [from = to] OR [amount = 0]   -> no-op.
    Otherwise:
      [from != 0x0] -> [votes from] -= amount
      [to   != 0x0] -> [votes to]   += amount
*)
Definition move_votes (v : Map) (from to : Address) (amount : Z) : Map :=
  if orb (Z.eqb from to) (Z.eqb amount 0) then v
  else
    let v1 := if Z.eqb from zero_address then v
              else upd v from (v from - amount) in
    let v2 := if Z.eqb to   zero_address then v1
              else upd v1 to (v1 to + amount) in
    v2.

(** ---- Transfer (mint / burn / peer-to-peer) ----
    Mirrors [StakingVault._update] (L499-L506):
      1. update [balances]
      2. invoke OZ side via [super._update] -> std ledger move
      3. invoke [_moveOptimisticDelegateVotes] -> opt ledger move

    [from = 0x0]   is mint (no balance debit on [from]).
    [to   = 0x0]   is burn (no balance credit on [to]).
*)
Definition apply_balance (b : Map) (from to : Address) (amount : Z) : Map :=
  let b1 := if Z.eqb from zero_address then b
            else upd b from (b from - amount) in
  let b2 := if Z.eqb to   zero_address then b1
            else upd b1 to (b1 to + amount) in
  b2.

(** Resolve "the delegate of an account, or zero_address if the
    account is itself zero_address". Matches the contract's behavior:
    [optimisticDelegatees[address(0)] = address(0)] by default, and
    we never look up a non-zero account's missing delegate (we use
    the OZ default of zero_address). *)
Definition delegate_of (l : Ledger.t) (account : Address) : Address :=
  if Z.eqb account zero_address then zero_address
  else l.(Ledger.delegatee) account.

Definition transfer (s : State.t) (from to : Address) (amount : Z) : State.t :=
  let b' := apply_balance s.(State.balances) from to amount in
  let sFrom := delegate_of s.(State.std) from in
  let sTo   := delegate_of s.(State.std) to   in
  let oFrom := delegate_of s.(State.opt) from in
  let oTo   := delegate_of s.(State.opt) to   in
  {|
    State.balances := b';
    State.std :=
      {| Ledger.delegatee := s.(State.std).(Ledger.delegatee);
         Ledger.votes := move_votes s.(State.std).(Ledger.votes) sFrom sTo amount |};
    State.opt :=
      {| Ledger.delegatee := s.(State.opt).(Ledger.delegatee);
         Ledger.votes := move_votes s.(State.opt).(Ledger.votes) oFrom oTo amount |};
  |}.

(** ---- Delegation re-pointing ----
    Mirrors [_delegateOptimistic] (L543-L549) — and structurally OZ's
    [_delegate]. The full current [balanceOf(account)] migrates from
    the old delegate's votes to the new. *)
Definition set_opt_delegate (s : State.t) (account new_d : Address) : State.t :=
  let old_d := delegate_of s.(State.opt) account in
  let bal   := s.(State.balances) account in
  {|
    State.balances := s.(State.balances);
    State.std := s.(State.std);
    State.opt :=
      {| Ledger.delegatee := upd s.(State.opt).(Ledger.delegatee) account new_d;
         Ledger.votes := move_votes s.(State.opt).(Ledger.votes) old_d new_d bal |};
  |}.

Definition set_std_delegate (s : State.t) (account new_d : Address) : State.t :=
  let old_d := delegate_of s.(State.std) account in
  let bal   := s.(State.balances) account in
  {|
    State.balances := s.(State.balances);
    State.opt := s.(State.opt);
    State.std :=
      {| Ledger.delegatee := upd s.(State.std).(Ledger.delegatee) account new_d;
         Ledger.votes := move_votes s.(State.std).(Ledger.votes) old_d new_d bal |};
  |}.

(** ---- Validity ----
    Both ledgers carry the same structural invariant: every votes
    entry is a non-negative U256, and the delegate map points to
    U256-valid addresses. Beyond shape, the headline invariant is
    that the *sum* of votes over non-zero delegates equals the sum
    of balances over accounts whose delegate is non-zero. That's the
    conservation lemma proved in [proofs/StakingVaultDelegation.v]
    rather than baked in here. *)
Module Valid.
  Record ledger (l : Ledger.t) : Prop := {
    (** Every votes entry is non-negative (no underflow). *)
    votes_nn : forall a, 0 <= l.(Ledger.votes) a;
  }.

  Record state (s : State.t) : Prop := {
    balances_nn : forall a, 0 <= s.(State.balances) a;
    std_valid   : ledger s.(State.std);
    opt_valid   : ledger s.(State.opt);
  }.
End Valid.

End StakingVaultDelegation.
