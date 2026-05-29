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

End EquivalenceCommon.
