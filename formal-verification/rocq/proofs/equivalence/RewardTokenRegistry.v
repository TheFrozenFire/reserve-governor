(** Phase 3.2 (task #181) — RewardTokenRegistry equivalence scaffold.

    Storage layout (the `roleRegistry` field is `immutable`):

      slot 0+: EnumerableSet.AddressSet _rewardTokens

    The on-chain layout is governed by OpenZeppelin's EnumerableSet:

      struct AddressSet {
        bytes32[] _values;                  (* uint256[] in memory *)
        mapping(bytes32 => uint256) _positions;  (* index+1, 0 = absent *)
      }

    Inlined into slot 0, this means:

      slot 0: length of _values array (uint256)
      slot keccak256(0) + i: _values[i] (one address per slot, lower 160 bits)
      slot 1: _positions mapping base

    Equivalence with OZ EnumerableSet is its own workstream — the OZ
    contract maintains an O(1) add/remove invariant via the
    [_positions] map, and the sim abstracts it as a duplicate-free
    [list Address.t]. Closing the equivalence requires:

      1. A projection of the sim's [rewardTokens : list Address.t] into
         BOTH on-chain shapes simultaneously (the [_values] array and
         the [_positions] map).
      2. Invariant preservation across [add] / [remove] (specifically
         the swap-and-pop pattern that OZ uses on remove).
      3. An equivalence proof for each of [registerRewardToken] /
         [unregisterRewardToken] that walks the OZ library code, not
         just the contract's wrapper.

    This file scaffolds the projection target and documents the gap.
    The full OZ-equivalence work is parked under Phase 4 (heavyweight
    contracts decision). *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.
Require Import ReserveGovernor.simulations.RewardTokenRegistry.
Require Import Coq.Lists.List.
Import ListNotations.

Module RewardTokenRegistryEquivalence.

  Import RewardTokenRegistry.

  (** ----- Per-shape projections of the sim's set -----

      [values_array_length] mirrors slot 0 (the array's length).
      [values_array_get] mirrors the i-th element slot.
      [positions_map] mirrors the [_positions] mapping.

      Convention: the sim's [rewardTokens] list stores tokens in
      registration order (most recent at the head). OZ EnumerableSet
      stores them in the [_values] array in the same order; the
      [_positions] map then sends each token to its index+1. *)

  Definition values_array_length (sim : State.t) : U256.t :=
    Z.of_nat (List.length sim.(State.rewardTokens)).

  Fixpoint values_array_get_aux
      (tokens : list Address) (i : nat) : option Address :=
    match tokens with
    | []          => None
    | t :: rest   =>
        match i with
        | O    => Some t
        | S i' => values_array_get_aux rest i'
        end
    end.

  Definition values_array_get (sim : State.t) (i : nat) : option Address :=
    values_array_get_aux sim.(State.rewardTokens) i.

  Fixpoint positions_map_aux
      (tokens : list Address) (i : nat) : Dict.t U256.t U256.t :=
    match tokens with
    | []          => []
    | t :: rest   => (t, Z.of_nat (S i)) :: positions_map_aux rest (S i)
    end.

  Definition positions_map (sim : State.t) : Dict.t U256.t U256.t :=
    positions_map_aux sim.(State.rewardTokens) 0.

  (** ----- Projection scaffold -----

      The full storage projection lives across multiple slots due to
      the [_values] array's keccak-based addressing. Since the array
      length and the positions map fit individual [StorableValue]
      variants, we expose them here; the per-index array reads need
      either a custom variant or per-slot hypotheses (similar to
      ThrottleLib's legacy [storage_slot_value] form).

      Slot 0: length of the [_values] array.
      Slot 1: [_positions] mapping.

      Per-index array slots:
        keccak256(0) + i: [_values[i]] = the i-th registered token.

      The projection below covers the directly-addressable slots; the
      per-index array slots get expressed as a separate hypothesis in
      any equivalence theorem. *)
  Definition proj_sim_directly_addressable (sim : State.t) : SimulatedStorage.t := [
    StorableValue.U256 (values_array_length sim);
    StorableValue.Map (positions_map sim)
  ].

  (** ----- Well-formedness sanity ----- *)
  Lemma proj_sim_length (sim : State.t) :
    List.length (proj_sim_directly_addressable sim) = 2%nat.
  Proof. reflexivity. Qed.

  Lemma values_array_length_empty :
    values_array_length empty_state = 0.
  Proof. reflexivity. Qed.

  Lemma positions_map_empty :
    positions_map empty_state = [].
  Proof. reflexivity. Qed.

  (** ----- Equivalence-theorem scaffolds (Admitted) -----

      Full closure requires:
        - OZ EnumerableSet.add behavioural correspondence with sim's
          list-cons.
        - OZ EnumerableSet.remove (swap-and-pop) correspondence with
          sim's list-remove.
        - Per-slot sload hypothesis or a new [StorableValue] variant
          for the [_values] array indexing.

      Both adds and removes touch multiple slots: length, positions,
      array slot at the swapped position. The proof is mechanical
      once the OZ library is mechanized; parked behind the Phase 4
      decision on heavyweight contracts. *)

End RewardTokenRegistryEquivalence.
