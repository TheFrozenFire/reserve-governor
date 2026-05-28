(** Project-wide conventions and documented assumptions.

    This file is the single canonical home for cross-cutting
    invariants the simulations and proofs all rely on. Each
    convention is stated once, with the audit rationale, and is
    available for downstream proofs to cite by name.

    The convention list is intentionally small. Anything that varies
    per-domain belongs in the per-domain simulation or its [Valid.t]
    record, not here. Anything controlled by external libraries
    (PRBMath, OZ, etc.) belongs in [mocks/] with the matching
    differential-test backing (see e.g. [test/PRBMathPowuAxioms.t.sol]).
*)

Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require Import Coq.ZArith.ZArith.

Module Conventions.

(** ===== Convention 1: block.timestamp monotonicity =====

    The EVM guarantees that [block.timestamp] is non-decreasing
    within a single chain — successive blocks satisfy
    [block.timestamp(b_{n+1}) >= block.timestamp(b_n)]. Out-of-order
    timestamps would require reordering finalized blocks, which the
    consensus layer rules out.

    Multiple proofs across the tree carry this as an explicit local
    hypothesis:

      - UnstakingManager.claim_then_claim_reverts (now1 <= now2)
      - Governor.cannot_de_escalate_after_transition (block-time ordering)
      - ProposerThrottle charge evolution (charge refills monotone in elapsed)
      - Timelock op_done_sticky (Done state survives time advance)

    Rather than re-stating the precondition in each lemma, this
    convention is the central reference. New proofs that need it
    can cite [Conventions.timestamp_monotone] directly.

    NOTE: We expose this as a [Definition] of the property rather
    than as an [Axiom] because every existing proof already
    discharges it by accepting it as a hypothesis at the call site.
    A future refactor could lift this into a global axiom and
    eliminate the per-lemma hypotheses — but that's an invasive
    change to the proof tree and is tracked separately. *)

(** Type alias: a "now" stamp is the [block.timestamp] value
    observed at the boundary of a contract call. *)
Definition Timestamp : Set := U256.t.

(** The convention itself, stated as a predicate over two
    timestamps. Used as a hypothesis form by proofs that thread
    multiple call boundaries. *)
Definition timestamp_monotone (now1 now2 : Timestamp) : Prop :=
  now1 <= now2.

(** Sub-second timestamps. On mainnet Ethereum, [block.timestamp]
    advances by at least 1 between consecutive blocks. Some L2s and
    sidechains (Arbitrum's old non-realtime mode, some Avalanche
    subnets) can produce same-second blocks. Proofs that depend on
    "stamp strictly increases per block" should cite
    [Conventions.timestamp_strict] and accept the L2-deployment
    caveat. Proofs that only need "stamp doesn't go backwards" are
    safe on every chain — they cite [timestamp_monotone] only. *)
Definition timestamp_strict (now1 now2 : Timestamp) : Prop :=
  now1 < now2.

(** ===== Convention 2: validated U256 storage =====

    Production storage is [uint256], so every storage slot's value
    is bounded by [U256_MAX = 2^256 - 1] and non-negative. The
    simulations carry this discipline via per-domain [Valid.t]
    records on every field that gets written. New simulations
    should follow the same convention: every [U256.t] storage slot
    appears under a [U256.Valid.t] guard inside its containing
    [Valid.t].

    No global Axiom here — this is purely a coding convention
    enforced at simulation-writing time. *)

(** ===== Convention 3: External library trust assumptions =====

    The Reserve Governor depends on two external libraries we do
    not Yul-mechanize:

      - PRBMath (UD60x18.powu): axioms in
        [mocks/PRBMath.v], differential-tested in
        [test/PRBMathPowuAxioms.t.sol].
      - OpenZeppelin (AccessControlEnumerable, ERC20, Checkpoints,
        ERC4626, ERC20Votes, etc.): the relevant surfaces are
        captured per-domain in [mocks/] and the upstream
        rocq-of-solidity corpus is treated as the audit witness for
        the rest.

    The trust boundary is documented per dependency in
    [notes/external_dependencies.md]. Proofs cite per-mock axioms,
    not this convention directly. *)

End Conventions.
