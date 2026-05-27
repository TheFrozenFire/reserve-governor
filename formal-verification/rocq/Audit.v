(** ============================================================
    Reserve Governor — formal verification Audit index.

    Audit-facing re-export surface. The goal is to give an auditor a
    single file to read top-to-bottom that surfaces every
    decision-relevant theorem with the calibration / context needed to
    interpret it.

    The audit is organized by component:

      1. StakingVault — ERC4626 vault with dual delegation and
         multi-token rewards.
      2. UnstakingManager — time-locked withdrawal queue.
      3. ReserveOptimisticGovernor — hybrid optimistic/standard
         governance.
      4. OptimisticSelectorRegistry — (target, selector) whitelist.
      5. TimelockControllerOptimistic — execution queue with
         bypass-for-optimistic path.
      6. ProposerThrottle (ProposalLib) — per-account proposal
         frequency cap.

    Each section will import its component's [_validity] /
    [_chain] proofs and re-export them via [Notation] under
    [audit_<feature>] names. Sections are added incrementally as the
    simulations land.

    See [../README.md] for the dual-track Rocq + CAS verification
    rationale and [../notes/simulation_fidelity_audit.md] for the
    catalog of known divergences between this simulation and the
    production contracts.
*)

(* Imports land here as components are modeled. *)
