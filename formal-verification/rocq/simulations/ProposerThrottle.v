(** ProposerThrottle simulation.

    Mirrors contracts/governance/lib/ThrottleLib.sol — a per-account
    D18-normalized proposal-frequency throttle with a 12-hour full
    recovery period.

    Production exposes two external functions:
      consumeProposalCharge(storage, account)
      getProposalsAvailable(storage, account)        (view)

    Both delegate to the private
      _getProposalsAvailable(storage, account)
    which is the actual time-dependent computation.

    [block.timestamp] is read on-chain; here it is passed as an
    explicit [now : U256.t] parameter so the simulation is pure. The
    on-chain function mutates storage; we return a fresh [Throttle.t]
    (or [Result.Revert] when the proposer is throttled).

    Calibration:
      PROPOSAL_THROTTLE_PERIOD = 12 hours = 43200 seconds
      D18 fixed-point throughout: 1.0 = 10^18

    Revert coverage:
      Modeled:  [revert_throttled] when proposalsAvailable < 1
                (production: ThrottleLib.sol#L20).
      Not modeled: storage-access auth (production-side restricted to
                the calling Governor; not part of the library math).

    Rounding note:
      [consume] subtracts [1e18 / capacity] using integer division.
      When [capacity] doesn't divide 10^18, each consume removes slightly
      less than one full proposal-slot worth of charge — a discarded
      remainder of [(10^18) mod capacity] D18 per consume. This is a
      real divergence from "exact one-slot consumption" and is captured
      by INV-6 in the CAS witness corpus.
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.

Module ProposerThrottle.

Definition PROPOSAL_THROTTLE_PERIOD : Z := 12 * 3600.   (** 43200 *)
Definition FIX_ONE                   : Z := 10 ^ 18.
Definition UINT256_MAX               : Z := 2 ^ 256 - 1.

(** Per-account, mutable storage slot. The contract holds these in a
    [mapping(address => ProposalThrottle)]; here the simulation reasons
    over a single account's slot. The calling contract iterates per
    account. *)
Module Throttle.
  Record t : Set := {
    currentCharge : U256.t;   (** D18, in [0, 10^18] *)
    lastUpdated   : U256.t;   (** {seconds} *)
  }.
End Throttle.

(** Two-constructor result, mirroring the upstream ERC20 simulation,
    so the eventual run-* equivalence proof can match Yul revert
    offsets directly. The numeric fields are placeholders here. *)
Module Result.
  Inductive t (A : Set) : Set :=
  | Success (value : A)
  | Revert (p s : U256.t).
  Arguments Success {_}.
  Arguments Revert {_}.
End Result.

(** Placeholder revert for "OptimisticGovernor__ProposalThrottleExceeded".
    Yul offsets get pinned during equivalence. *)
Definition revert_throttled {A : Set} : Result.t A :=
  Result.Revert 0 32.

(** Read-side charge: applies the time-decayed refill and clips to
    [FIX_ONE]. Source: ThrottleLib.sol#L48-L53. *)
Definition readCharge (t : Throttle.t) (now : U256.t) : U256.t :=
  let elapsed := now - t.(Throttle.lastUpdated) in
  let raw := t.(Throttle.currentCharge) + (elapsed * FIX_ONE) / PROPOSAL_THROTTLE_PERIOD in
  Z.min FIX_ONE raw.

(** Read-side conversion to integer proposal slots. Source:
    ThrottleLib.sol#L55. *)
Definition proposalsAvailable
    (t : Throttle.t) (capacity : U256.t) (now : U256.t) : U256.t :=
  let c := readCharge t now in
  (capacity * c) / FIX_ONE.

(** [consume(throttle, capacity, now)]. Source: ThrottleLib.sol#L18-L27.

    Successful consume:
      throttle' = {| currentCharge := readCharge - (FIX_ONE / capacity);
                     lastUpdated   := now |}

    The [1e18 / capacity] uses integer division; the modulus is silently
    discarded — see the file header for the rounding-leak discussion. *)
Definition consume
    (t : Throttle.t) (capacity : U256.t) (now : U256.t)
    : Result.t Throttle.t :=
  let c := readCharge t now in
  let avail := (capacity * c) / FIX_ONE in
  if avail <? 1 then
    revert_throttled
  else
    let slot := FIX_ONE / capacity in
    Result.Success {|
      Throttle.currentCharge := c - slot;
      Throttle.lastUpdated   := now;
    |}.

(** Validity predicate: the storage invariants the contract preserves
    by construction. [currentCharge] is capped at [FIX_ONE] by every
    write path: refill via [readCharge] clips to [FIX_ONE], and
    [consume] only writes [readCharge - slot] which is therefore also
    [<= FIX_ONE]. *)
Module Valid.
  Record throttle (t : Throttle.t) : Prop := {
    charge_u256   : U256.Valid.t t.(Throttle.currentCharge);
    charge_capped : t.(Throttle.currentCharge) <= FIX_ONE;
    lastUpd_u256  : U256.Valid.t t.(Throttle.lastUpdated);
  }.

  (** Capacity must be positive on-chain; the contract has no zero
      guard but a zero capacity would brick the throttle (proposals
      available always zero AND the [FIX_ONE / 0] would revert
      Solidity-side as division by zero). *)
  Definition capacity (c : U256.t) : Prop :=
    0 < c <= UINT256_MAX.
End Valid.

End ProposerThrottle.
