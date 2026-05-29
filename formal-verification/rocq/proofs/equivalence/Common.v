(** Phase 3.4 (task #183) — shared helpers for equivalence proofs.

    Centralizes the apparatus reused across per-contract files under
    [proofs/equivalence/]:

      - WISDOM.md R022 unblocker: [Dict_Eq_eqb_ZZ_pair_unfold].
        Definitional unfolding of the [Dict.Eq.ITuple2] instance at
        [(Z * Z)]-keyed dictionaries. Closes [reflexivity] at the
        kernel level so manual [rewrite] reaches the [Z.eqb] form
        without invoking [simpl] / [cbn] / [hauto] (which all anomaly
        on the typeclass-projection reduction).

    Each per-contract file under [proofs/equivalence/] should
    [Require Import ReserveGovernor.proofs.equivalence.Common] at the
    top to access these helpers. *)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import RocqOfSolidity.proofs.RocqOfSolidity.

Module EquivalenceCommon.

  (** R022 unblocker — closes by [reflexivity] because the kernel
      reduces the typeclass-instance projection at definition time. *)
  Lemma Dict_Eq_eqb_ZZ_pair_unfold (a1 a2 b1 b2 : Z) :
    @Dict.Eq.eqb (Z * Z) Dict.Eq.ITuple2 (a1, b1) (a2, b2)
    = andb (Z.eqb a1 a2) (Z.eqb b1 b2).
  Proof. reflexivity. Qed.

  (** [Dict.get] over a [Z]-keyed dict reduces via [Z.eqb], not
      through the typeclass projection. Manual [change] succeeds
      here too. *)
  Lemma Dict_Eq_eqb_Z_unfold (a b : Z) :
    @Dict.Eq.eqb Z Dict.Eq.IZ a b = Z.eqb a b.
  Proof. reflexivity. Qed.

  (** One-step [map_get_u256] unfolding on a pair-keyed cons. The
      [Dict.get] Fixpoint's body is definitionally equal to the
      [if]-form below; [change] exposes it without triggering [simpl]
      / [cbn], and then [Dict_Eq_eqb_ZZ_pair_unfold] gets us to the
      [Z.eqb] form. Essential rewrite rule for closing
      [map_get_u256 (some_packed_map sim) (key, offset)] lookups. *)
  Lemma map_get_u256_pair_cons
      (rest : Dict.t (U256.t * U256.t) U256.t)
      (a c b d v : U256.t) :
    StorableValue.map_get_u256 (((c, d), v) :: rest) (a, b)
    = if andb (Z.eqb a c) (Z.eqb b d) then v
      else StorableValue.map_get_u256 rest (a, b).
  Proof.
    unfold StorableValue.map_get_u256.
    change (Dict.get (((c, d), v) :: rest) (a, b))
      with (if @Dict.Eq.eqb _ Dict.Eq.ITuple2 (a, b) (c, d)
            then Some v else Dict.get rest (a, b)).
    rewrite Dict_Eq_eqb_ZZ_pair_unfold.
    destruct (Z.eqb a c && Z.eqb b d); reflexivity.
  Qed.

  (** One-step [map_get_u256] unfolding on a Z-keyed cons (the
      [Map U256→U256] flavour). Similar pattern, simpler Eq. *)
  Lemma map_get_u256_Z_cons
      (rest : Dict.t U256.t U256.t)
      (a c v : U256.t) :
    StorableValue.map_get_u256 ((c, v) :: rest) a
    = if Z.eqb a c then v else StorableValue.map_get_u256 rest a.
  Proof.
    unfold StorableValue.map_get_u256.
    change (Dict.get ((c, v) :: rest) a)
      with (if @Dict.Eq.eqb _ Dict.Eq.IZ a c
            then Some v else Dict.get rest a).
    rewrite Dict_Eq_eqb_Z_unfold.
    destruct (Z.eqb a c); reflexivity.
  Qed.

End EquivalenceCommon.
