(** PRBMath mock — axiomatic interface for [UD60x18.powu].

    Captures the surface of
      @prb/math/src/UD60x18.sol::powu
    that the Reserve Governor's [StakingVault._calculateHandout]
    depends on (StakingVault.sol:490):

      uint256 handoutPercentage =
        1e18 - UD60x18.wrap(1e18 - rewardRatio).powu(elapsed).unwrap() - 1;

    This is the discrete-exponential decay kernel
      handoutPct = 1 - (1 - r)^n     with r in [0, 1), n = elapsed.

    Why axiomatic instead of a full simulation:
      - [powu] uses 60.18-decimal fixed-point repeated squaring with
        floor rounding at every step. Replicating the bit-exact
        semantics in Rocq is a large undertaking; the CAS corpus in
        [cas/staking_vault/] already validates the closed-form
        equivalence numerically.
      - The downstream proof only needs FOUR properties (identity at
        zero exponent, base-zero passthrough, boundedness, monotone
        decay). Axiomatizing exactly those keeps the trust surface
        minimal and observable: every downstream theorem that depends
        on [powu] must explicitly cite one of these axioms.

    Convention: all values are D18 fixed-point integers, i.e. the
    real value [x] is represented as [Z.to_z (x * 10^18)]. The
    "logical one" is [10^18 = ONE_D18].

    Used by:
      - [StakingVaultRewards.v] (reward-accounting proof — boundedness
        is the load-bearing fact: [handout <= balance]).
      - [StakingVaultExchange.v] (rate-handout integration — uses
        identity-at-zero to prove "no rewards accrued at t=0").
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module PRBMath.

(** D18 unit: 1.0 in 60.18-decimal fixed-point. *)
Definition ONE_D18 : Z := 10 ^ 18.

Lemma ONE_D18_pos : 0 < ONE_D18.
Proof. unfold ONE_D18. lia. Qed.

(** [powu base exponent]: the discrete exponential. Both arguments are
    [U256.t] integers; [base] is interpreted as a D18 fraction (so
    [base = ONE_D18] is "x^1 = x" identity), [exponent] is a plain
    non-negative integer count. The result is a D18 fraction. *)
Parameter powu : U256.t -> U256.t -> U256.t.

(** Axiom 1: [powu base 0 = ONE_D18].

    Rationale: identity element of exponentiation. Any nonzero number
    raised to the 0th power is the multiplicative identity, which in
    D18 fixed-point is [10^18]. Even [0^0 = 1] by the PRB convention
    (matching standard mathematical convention for empty product).

    Used to prove: "at [elapsed = 0], handoutPercentage = 0" in
    [StakingVault._calculateHandout]. *)
Axiom powu_zero_exp :
  forall (base : U256.t),
    powu base 0 = ONE_D18.

(** Axiom 2: [powu 0 n = 0] when [n > 0].

    Rationale: zero to any positive power is zero. In context, this
    says: if the reward ratio is *exactly* 100% (so the "remaining
    fraction" [1e18 - r = 0]), then after any positive elapsed time,
    the remaining fraction is still 0, i.e. the handout is the entire
    unaccounted balance.

    Used to prove edge-case behavior in the reward decay (the case
    where halfLife = 0 is rejected at construction; we never see
    [base = 0] from the production caller, but the axiom documents
    the mathematical structure). *)
Axiom powu_zero_base :
  forall (n : U256.t),
    0 < n ->
    powu 0 n = 0.

(** Axiom 3: [base <= ONE_D18 -> powu base n <= ONE_D18].

    Rationale: a number in [0, 1] (as D18: [0, 10^18]) raised to any
    power stays in [0, 1]. This is the load-bearing safety bound for
    [_calculateHandout]: it guarantees [handoutPercentage >= 0] (the
    formula is [1e18 - powu(..., elapsed)], and we want this to be
    non-negative so we don't underflow / produce a phantom payout).

    Used in: [StakingVaultRewards.v] correctness proof — the "no
    over-payment" invariant [handout <= balance]. *)
Axiom powu_bounded :
  forall (base n : U256.t),
    base <= ONE_D18 ->
    powu base n <= ONE_D18.

(** Axiom 4: monotonicity in the exponent — for [base <= ONE_D18],
    [n1 <= n2 -> powu base n1 >= powu base n2].

    Rationale: a number in [0, 1] gets *smaller* as you exponentiate.
    This captures the "decay shape" of the handout: as elapsed time
    grows, the remaining-fraction shrinks. The complementary statement
    [handoutPercentage] grows monotonically with elapsed time, which
    is what stakers see ("reward accrual is monotone increasing in
    time").

    Used in: cross-checks against CAS-validated decay curves
    ([cas/staking_vault/decay_monotonicity.gp]). *)
Axiom powu_monotone_in_exp :
  forall (base n1 n2 : U256.t),
    base <= ONE_D18 ->
    n1 <= n2 ->
    powu base n1 >= powu base n2.

(** Axiom 5: [powu ONE_D18 n = ONE_D18].

    Rationale: the multiplicative identity raised to any power is
    itself. In production this is the "reward ratio is zero" case:
    [1e18 - 0 = 1e18] is the base; [1e18^elapsed = 1e18]; so the
    handout is [1e18 - 1e18 - 1 = -1], which Solidity then clamps
    to zero via the unsigned-subtract revert path. Documenting the
    identity here makes the underflow boundary explicit. *)
Axiom powu_one_base :
  forall (n : U256.t),
    powu ONE_D18 n = ONE_D18.

(** -- Derived corollaries (these are *not* axioms; they're proved
    from the axioms above and used in downstream theorems). -- *)

(** Corollary: [powu] of a sub-one base is non-negative.

    Strictly follows from [powu_bounded] composed with the monotone
    chain at [n_large -> infinity] (the limit is 0). For our
    purposes, the floor is the lower bound from boundedness; the
    upper bound for a single fixed [n] gives non-negativity once
    we observe [powu] returns a [U256.t] (so [>= 0] is structural,
    not an axiom). We state it explicitly for use in callers. *)
Lemma powu_nonneg :
  forall (base n : U256.t),
    U256.Valid.t (powu base n) ->
    0 <= powu base n.
Proof.
  intros base n Hv. unfold U256.Valid.t in Hv. lia.
Qed.

(** Corollary: [powu_bounded] + [powu_zero_exp] combine to give the
    "handout at t=0 is zero" fact in one step. *)
Lemma powu_zero_exp_eq_one_d18 :
  forall (base : U256.t),
    base <= ONE_D18 ->
    powu base 0 = ONE_D18.
Proof.
  intros base _. apply powu_zero_exp.
Qed.

(** -- Validity wrappers -- *)

Module Valid.
  (** A "decay base" is a D18 value strictly between 0 and ONE_D18,
      exclusive. This is the production invariant on [1e18 - rewardRatio]
      (rewardRatio is bounded so that 1e18 - rewardRatio is strictly
      positive and at most 1e18). *)
  Record decay_base (b : U256.t) : Prop := {
    base_pos : 0 < b;
    base_le_one : b <= ONE_D18;
  }.
End Valid.

End PRBMath.
