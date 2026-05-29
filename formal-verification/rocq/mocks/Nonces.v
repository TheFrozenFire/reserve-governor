(** OpenZeppelin Nonces mock — per-account replay-protection counters.

    Captures the surface of
      @openzeppelin/contracts-upgradeable/utils/NoncesUpgradeable.sol
    that StakingVault.[delegateOptimisticBySig] depends on via
    [_useCheckedNonce] (StakingVault.sol:212):

      address signer = ECDSA.recover(..., v, r, s);
      _useCheckedNonce(signer, nonce);
      _delegateOptimistic(signer, delegatee);

    OZ semantics:

      mapping(address account => uint256) private _nonces;

      function _useCheckedNonce(address owner, uint256 nonce)
          internal virtual {
        uint256 current = _useNonce(owner);
        if (nonce != current) {
          revert InvalidAccountNonce(owner, current);
        }
      }

      function _useNonce(address owner) internal virtual returns (uint256) {
        unchecked {
          return _nonces[owner]++;
        }
      }

    So [_useCheckedNonce(owner, n)] succeeds iff [nonces[owner] == n]
    AT ENTRY, and increments [nonces[owner]] by 1. The [unchecked]
    block makes overflow possible at uint256 max; we model unbounded
    [Z] and discharge the bound at the [Valid.t] boundary instead.

    Why mock rather than abstract: replay protection is exactly the
    property we want to verify, so the increment-on-success semantics
    must be visible in the simulation. A bare axiom set (e.g.
    "useCheckedNonce returns success only if nonce matches") would
    permit a model where consecutive successful calls returned the
    same nonce, defeating the replay-protection theorem.

    Used by:
      - [simulations/StakingVaultDelegationBySig.v]
      - [proofs/StakingVaultDelegationBySig.v]
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.ZArith.ZArith.

Local Open Scope Z_scope.

Module Nonces.

Definition Address : Set := U256.t.

(** Total function from address to current next-expected nonce.
    Default is 0 — fresh accounts begin at nonce 0, matching the
    OZ default. *)
Definition Map : Set := Address -> Z.

Definition empty : Map := fun _ => 0.

(** Pointwise update — same shape as the delegation sim's [upd]. *)
Definition upd (m : Map) (k : Address) (v : Z) : Map :=
  fun k' => if Z.eqb k' k then v else m k'.

(** ---- The Result-monad wrapper used by callers ----
    Mirrors the existing simulation convention (see
    [SelectorRegistry.Result.t]). A [_useCheckedNonce] call either
    succeeds and returns the updated map, or reverts with the OZ
    selector for [InvalidAccountNonce(owner, currentNonce)]. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert  (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Sentinel for InvalidAccountNonce — we don't model the exact
    selector encoding, just the kind. Two arbitrary U256.t values
    suffice to distinguish reverts of different kinds from one
    another at proof level. *)
Definition revert_invalid_nonce {A : Set} : Result.t A := Result.Revert 0 64.

(** [useCheckedNonce m owner nonce]:
      - if [m owner = nonce], succeed with [m' = upd m owner (nonce + 1)]
      - else, revert. *)
Definition useCheckedNonce (m : Map) (owner : Address) (nonce : Z)
    : Result.t Map :=
  if Z.eqb (m owner) nonce
  then Result.Success (upd m owner (nonce + 1))
  else revert_invalid_nonce.

(** ---- Validity ---- *)

Module Valid.
  (** Nonces are bounded in U256 (OZ uses uint256 internally). The
      bound is enforced via [U256.Valid.t]; outside that, no shape
      invariant is required.

      We don't carry [forall a, U256.Valid.t (m a)] eagerly — that
      would be cumbersome with a total-function map. Callers thread
      the bound for the specific addresses they touch. *)
  Definition account_in_range (m : Map) (owner : Address) : Prop :=
    0 <= m owner.
End Valid.

(** ---- Headline lemmas ---- *)

(** [useCheckedNonce] succeeds iff the supplied nonce matches the
    stored value. Captures the exact semantics; downstream proofs
    pattern-match on this. *)
Lemma useCheckedNonce_success_iff_match :
  forall (m : Map) (owner : Address) (nonce : Z) (m' : Map),
    useCheckedNonce m owner nonce = Result.Success m' ->
    m owner = nonce.
Proof.
  intros m owner nonce m' H.
  unfold useCheckedNonce in H.
  destruct (Z.eqb (m owner) nonce) eqn:Heqb.
  - apply Z.eqb_eq in Heqb. exact Heqb.
  - discriminate.
Qed.

(** Successful [useCheckedNonce] increments [m owner] by exactly 1. *)
Lemma useCheckedNonce_increments :
  forall (m : Map) (owner : Address) (nonce : Z) (m' : Map),
    useCheckedNonce m owner nonce = Result.Success m' ->
    m' owner = m owner + 1.
Proof.
  intros m owner nonce m' H.
  unfold useCheckedNonce in H.
  destruct (Z.eqb (m owner) nonce) eqn:Heqb.
  - apply Z.eqb_eq in Heqb.
    injection H as Hm'_eq.
    subst m'.
    unfold upd.
    rewrite Z.eqb_refl.
    lia.
  - discriminate.
Qed.

(** Successful [useCheckedNonce] leaves OTHER accounts' nonces
    untouched. The per-account-isolation property. *)
Lemma useCheckedNonce_preserves_other_accounts :
  forall (m : Map) (owner other : Address) (nonce : Z) (m' : Map),
    owner <> other ->
    useCheckedNonce m owner nonce = Result.Success m' ->
    m' other = m other.
Proof.
  intros m owner other nonce m' Hne H.
  unfold useCheckedNonce in H.
  destruct (Z.eqb (m owner) nonce) eqn:Heqb.
  - injection H as Hm'_eq.
    subst m'.
    unfold upd.
    destruct (Z.eqb other owner) eqn:Heqb2.
    + apply Z.eqb_eq in Heqb2. subst other. contradiction.
    + reflexivity.
  - discriminate.
Qed.

(** Replay protection: calling [useCheckedNonce] a second time with
    the SAME (owner, nonce) reverts, because the first call
    incremented the stored value. *)
Lemma useCheckedNonce_replay_reverts :
  forall (m : Map) (owner : Address) (nonce : Z) (m' : Map),
    useCheckedNonce m owner nonce = Result.Success m' ->
    useCheckedNonce m' owner nonce = revert_invalid_nonce.
Proof.
  intros m owner nonce m' Hfirst.
  pose proof (useCheckedNonce_increments m owner nonce m' Hfirst) as Hinc.
  pose proof (useCheckedNonce_success_iff_match m owner nonce m' Hfirst) as Hmatch.
  unfold useCheckedNonce.
  destruct (Z.eqb (m' owner) nonce) eqn:Heqb.
  - apply Z.eqb_eq in Heqb.
    rewrite Hinc in Heqb.
    rewrite Hmatch in Heqb.
    lia.
  - reflexivity.
Qed.

(** Monotonicity: nonces are non-decreasing across any successful
    sequence of [useCheckedNonce] calls. This is the structural form
    of replay protection — once a nonce N has been "consumed", the
    stored value strictly exceeds N forever. *)
Lemma useCheckedNonce_monotone :
  forall (m : Map) (owner : Address) (nonce : Z) (m' : Map),
    useCheckedNonce m owner nonce = Result.Success m' ->
    m owner < m' owner.
Proof.
  intros m owner nonce m' H.
  pose proof (useCheckedNonce_increments m owner nonce m' H).
  lia.
Qed.

End Nonces.
