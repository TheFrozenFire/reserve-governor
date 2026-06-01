# Print Assumptions snapshot

This directory holds a per-milestone snapshot of Coq's `Print Assumptions`
output for every equivalence-layer milestone Theorem. Driven by
[`scripts/print-assumptions-snapshot`](../../scripts/print-assumptions-snapshot).

## Why this exists

The audit story for the equivalence-proof tier ([`rocq/Audit.v`](../Audit.v)
Caveat-5) depends on each milestone closing against a small, *named* set of
trust axioms. `Print Assumptions <Theorem>` is the kernel-level oracle for
that — it lists exactly the `Axiom`s, `Parameter`s, and `Hypothesis`es a
proof transitively depends on. Without a snapshot, audit reviewers have to
run the command ad-hoc per milestone; with one, every commit produces a
diff a reviewer can scan in seconds.

This is honest-engineering infrastructure rather than a content-bearing
proof artefact. Its value comes from making the audit story
**falsifiable**: if a future commit introduces a new trust axiom or
silently widens an existing one's signature, the diff catches it.

## Layout

```
print_assumptions_snapshot/
├── README.md                              # this file
├── .gitignore                             # excludes `current/`
├── baseline/                              # CHECKED IN — drift target
│   ├── summary.csv                        # one row per milestone
│   ├── summary.md                         # human-readable view
│   └── <File>__<Module>__<theorem>.txt    # raw Print Assumptions output
└── current/                               # gitignored — per-run output
    └── ... (same shape as baseline/)
```

The naming convention `<File>__<Module>__<theorem>.txt` keeps every
milestone in one flat directory while preserving the source location and
the Coq qualified name. The double-underscore separator avoids collision
with Coq's `.`-qualified names.

## Usage

```sh
# Run the snapshot — diffs against the checked-in baseline.
# Exit 0 if no drift, 1 if drift is detected.
OPAM_SWITCH=rocq820 bash formal-verification/scripts/print-assumptions-snapshot

# Refresh the baseline (e.g. after intentionally discharging or
# adding an axiom). Review the resulting git diff before committing.
OPAM_SWITCH=rocq820 bash formal-verification/scripts/print-assumptions-snapshot --refresh-baseline
```

Per-coqc timeout: `PA_TIMEOUT=<seconds>` (default 120).
Custom output directory: `--out=<path>` (default `current/`).

The script reuses cached `.vo` files from `scripts/rocq-build`, so a
prior green build is the prerequisite. If a `.vo` is missing, coqc
recompiles it; the heavyweight shallow forms
(`StakingVault_shallow`, `ReserveOptimisticGovernor_shallow`) add
~3 min each on a cold run.

Typical wall-clock on a warm cache:

```
==> AccessControlEnumerable.v: 2 milestone(s)
==> Guardian.v: 5 milestone(s)
==> ProposalLib.v: 6 milestone(s)
...
==> wrote 57 per-theorem files + summary.{csv,md}
```

≈ 1-2 minutes total.

## When to refresh the baseline

Refresh whenever the diff is **intentional**:

- A milestone Qed was discharged with a real proof, dropping its axiom
  footprint (good — fewer load-bearing axioms is a win).
- A milestone Qed was *promoted* with a tighter axiom shape (e.g.
  closed-form `proj_post` instead of a Skolem). The total count may
  stay the same but the per-axiom text will change.
- A new milestone Theorem was added (the snapshot extracts every
  `Theorem run_*_equivalent[*]` / `run_*_make_state` / `run_*_observed_behavior`).
- A walker-axiom retirement closed a CCV-class trust item — diff
  surfaces *which* axioms went away.

Do NOT refresh blindly: if the diff shows a *new* trust axiom you
didn't expect to add, that's a regression worth investigating first.
The diff is the audit feedback loop.

## What the snapshot captures, what it doesn't

**Captures:**

- Every `Theorem` (not `Lemma`) under `proofs/equivalence/*.v` whose
  name matches the milestone convention.
- The full `Print Assumptions` block per milestone — axiom names,
  type signatures, the `Theory:` footer.
- A summary CSV row per milestone with total + load-bearing axiom
  counts.

**Does NOT capture:**

- Lemma-level axioms (deliberately — leaves and helpers are scaffolding
  and would obscure the milestone signal).
- Files in `SKIP_FILES` in
  [`scripts/print_assumptions_snapshot_impl.py`](../../scripts/print_assumptions_snapshot_impl.py)
  (`Sandbox.v`, `Common.v`, `StaticCallBridge.v`, `ThrottleLib_Leaves.v`,
  `AbiEncoding.v`) — these are infrastructure, not milestones.
- Anything under `proofs/` outside `equivalence/` — the equivalence
  tier is the audit's vapor-vs-content frontier; the rest of the
  proof tree is `Qed` against the hand-written sim and not the place
  where trust axioms accumulate.

## Audit-value framing

The snapshot is the mechanical complement to
[`notes/adversarial_review_2026_05_31/trust_axiom_auditor.md`](../../notes/adversarial_review_2026_05_31/trust_axiom_auditor.md),
which catalogues the current trust-axiom landscape. That review was a
human read; this snapshot is the machine read that re-runs every time
the proof tree changes.

The two artefacts are complementary:

- **Trust-axiom auditor doc** — explains *why* each axiom is what it
  is, categorises it (CRITICAL / HIGH / MEDIUM), and points at the
  remediation.
- **This snapshot** — *detects* axiom-level change. If the diff is
  green, the trust-axiom auditor's catalog is still current. If the
  diff has new lines, the catalog needs an update.

When the equivalence tier is fully tightened (Tier 1+Tier 2 from the
adversarial-review remediation plan land), the load-bearing axiom
count column in `summary.csv` will be the headline number to track.
Today's baseline establishes the reference for that trajectory.

## What the load-bearing count means

`axioms_load_bearing = axioms_total - kernel primitives`, where kernel
primitives are listed in `KERNEL_AXIOM_PREFIXES` in
[`print_assumptions_snapshot_impl.py`](../../scripts/print_assumptions_snapshot_impl.py):

- `PrimInt63.*` — Coq's native 63-bit integer machinery, underlying
  the U256 representation.
- `RocqOfSolidity.Memory.of_u256_list` — framework lifting from a
  `list U256` into the memory record-update form.
- `RocqOfSolidity.Storage.of_storable_values` (+ the `SimulatedXxx`
  aliases) — framework lifting from `StorableValue.t` list into the
  storage record-update form.

These are NOT trust axioms in the audit sense — they're the lifting
layer between Coq's stdlib and rocq-of-solidity's domain types. They
appear in nearly every milestone and contribute no per-milestone
content; subtracting them gives the milestone-specific trust budget.

**Caveat**: a kernel-primitive change WILL still surface as a diff
(the axiom text is in the per-theorem `.txt`), even though it won't
move the load-bearing count. The diff is the signal; the count is a
quick-look summary.

## Drift-detection semantics

The wrapper compares `current/` against `baseline/` file-by-file. Any
of the following counts as drift:

- **NEW** — a milestone file exists in `current/` but not in `baseline/`.
  Usually means a new Theorem was added; refresh the baseline if intended.
- **GONE** — a milestone file exists in `baseline/` but not in `current/`.
  Usually means a Theorem was deleted or renamed.
- **DRIFT** — both files exist but their contents differ. This is the
  important case: an axiom was added, removed, or its signature changed.

`summary.csv` is also diffed — drift there is the quick-look indicator
that something changed even before you look at per-file diffs.
