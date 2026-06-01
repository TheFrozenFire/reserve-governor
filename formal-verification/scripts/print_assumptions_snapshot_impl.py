#!/usr/bin/env python3
"""print_assumptions_snapshot_impl.py — runner for the print-assumptions-snapshot
bash wrapper.

This script is invoked by `scripts/print-assumptions-snapshot` after the
wrapper has verified coqc / opam / timeout are available. It:

1. Walks `formal-verification/rocq/proofs/equivalence/*.v` and extracts
   every `Theorem` whose name matches the milestone naming convention
   (run_*_equivalent[*], run_*_make_state[*], run_*_observed_behavior).
   It tracks the enclosing `Module` for each theorem so the
   fully-qualified Coq name is available for `Print Assumptions`.

2. For each equivalence file, generates a Coq driver file that
   `Require Import`s the module and runs `Print Assumptions
   <ModuleName>.<theorem>` for each milestone in that file.

3. Invokes `coqc` on each driver, parsing the stdout into per-theorem
   blocks. The output of `Print Assumptions X` always starts with
   `Axioms:` (or `Closed under the global context` if there are none)
   and ends with `Theory:` (which is always present, listing
   `Set is impredicative` for our impredicative-set build).

4. Writes one `.txt` per milestone under `<out>/<File>__<theorem>.txt`,
   and a `summary.csv` row per milestone with: file, module, theorem,
   line, total_axiom_count, load_bearing_count. Load-bearing means
   total minus "kernel primitives" — see KERNEL_AXIOM_PREFIXES below.

5. Also emits `summary.md`, a human-readable summary table grouped by
   file.

Failure mode: any per-theorem extraction error (coqc rejects the name,
times out, etc.) is captured into the per-theorem file as an
`# ERROR:` block plus reported on stderr, so partial snapshots are
still useful for diffing.

This file is NOT meant to be run directly — go through the wrapper.
"""
from __future__ import annotations

import argparse
import csv
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator

# ---------------------------------------------------------------------------
# Milestone naming convention. A milestone is a `Theorem` (not Lemma)
# whose name matches one of these stem patterns. Helpers and leaf
# lemmas are filtered out at the Theorem-vs-Lemma layer; the regex
# adds milestone-only stems.
# ---------------------------------------------------------------------------
MILESTONE_THEOREM_RE = re.compile(
    r"""^\s*Theorem\s+
        (?P<name>
          run_[A-Za-z0-9_]+_(?:equivalent(?:_make_state|_scaffold|_methodology)?
                              |make_state
                              |observed_behavior)
        )
        \b
    """,
    re.VERBOSE,
)

# Module boundary regexes. We track only "real" module definitions
# (`Module Foo.`), not module aliases (`Module Foo := Bar.`) or
# functor-style headers — milestone theorems are always inside a
# real module body.
MODULE_OPEN_RE = re.compile(r"^\s*Module\s+(?P<name>[A-Z][A-Za-z0-9_]*)\s*\.\s*$")
MODULE_CLOSE_RE = re.compile(r"^\s*End\s+(?P<name>[A-Z][A-Za-z0-9_]*)\s*\.\s*$")

# Files under proofs/equivalence/ that do NOT carry milestone Qeds.
# These are infrastructure / leaf-lemma containers / sandbox files.
SKIP_FILES = {
    "Sandbox.v",            # Toy proofs of method
    "Common.v",             # Cross-cutting helpers
    "StaticCallBridge.v",   # Bridge axioms — no Theorems
    "ThrottleLib_Leaves.v", # Leaf lemmas (Lemma, not Theorem)
    "AbiEncoding.v",        # ABI helper lemmas (Lemma, not Theorem)
    "README.md",
}

# Kernel-primitive axiom prefixes. These show up in nearly every
# milestone (PrimInt63 underlies the U256 representation, and the
# Memory/Storage of_X_list constructors are framework-level). They
# do NOT change between runs and are not "trust" axioms in the
# audit sense — they're the lifting axioms from Coq's stdlib /
# rocq-of-solidity baseline.
KERNEL_AXIOM_PREFIXES = (
    "PrimInt63.",
    "RocqOfSolidity.Memory.of_u256_list",
    "RocqOfSolidity.Storage.of_storable_values",
    "RocqOfSolidity.SimulatedMemory.of_u256_list",
    "RocqOfSolidity.SimulatedStorage.of_storable_values",
    # `Set is impredicative` is the Theory: line, not an axiom — we
    # parse it separately, but include the prefix here as a safety net
    # in case future Print Assumptions output formats list it under Axioms:.
    "Set is impredicative",
)


@dataclass(frozen=True)
class Milestone:
    file: str           # basename, e.g. "Guardian.v"
    module_path: str    # dotted, e.g. "GuardianEquivalence"
    name: str           # bare theorem name
    lineno: int         # 1-based source line

    @property
    def coq_qualified(self) -> str:
        """Coq name to feed `Print Assumptions`, assuming the
        equivalence module has been `Require Import`ed but its inner
        module is NOT opened. Format: `<Module>.<theorem>`."""
        if self.module_path:
            return f"{self.module_path}.{self.name}"
        return self.name

    @property
    def slug(self) -> str:
        """Filesystem-safe identifier for the per-theorem snapshot file."""
        # Strip ".v" from file; mod_path is already dotted-identifier-safe.
        base = self.file[:-2] if self.file.endswith(".v") else self.file
        if self.module_path:
            return f"{base}__{self.module_path}__{self.name}"
        return f"{base}__{self.name}"


def iter_milestones(equiv_dir: Path) -> Iterator[Milestone]:
    """Walk equivalence .v files and yield milestones in source order.

    Module nesting is tracked via a stack. Sections and functor-style
    `Module Foo : T := ...` are intentionally NOT tracked — they're
    not part of the qualified name Print Assumptions expects.
    """
    for path in sorted(equiv_dir.iterdir()):
        if path.name in SKIP_FILES:
            continue
        if not path.name.endswith(".v"):
            continue
        stack: list[str] = []
        with path.open() as fh:
            for lineno, line in enumerate(fh, 1):
                # Module aliases / functor instantiations contain `:=`
                # before the period — skip them via the strict
                # MODULE_OPEN_RE which requires the line to end in `.`.
                m_open = MODULE_OPEN_RE.match(line)
                if m_open and ":=" not in line:
                    stack.append(m_open.group("name"))
                    continue
                m_close = MODULE_CLOSE_RE.match(line)
                if m_close and stack and stack[-1] == m_close.group("name"):
                    stack.pop()
                    continue
                th = MILESTONE_THEOREM_RE.match(line)
                if th:
                    yield Milestone(
                        file=path.name,
                        module_path=".".join(stack),
                        name=th.group("name"),
                        lineno=lineno,
                    )


# Mapping from .v filename to the Coq `Require Import` path. All
# equivalence files live under `ReserveGovernor.proofs.equivalence`.
def coq_require_path(filename: str) -> str:
    stem = filename[:-2] if filename.endswith(".v") else filename
    return f"ReserveGovernor.proofs.equivalence.{stem}"


def build_driver_v(file: str, milestones: list[Milestone]) -> str:
    """Generate a Coq driver file that Require Imports the equivalence
    module and runs Print Assumptions for each milestone in it.

    The driver emits one `Print Assumptions <Module>.<theorem>` per
    milestone in source order. coqc in non-interactive mode does not
    echo `Definition X is defined` lines to stdout, so we cannot rely
    on inline sentinel banners; instead, the parser splits the
    captured stdout by `Theory:` (Coq's deterministic terminator for
    every Print Assumptions block) and assigns blocks to milestones
    in declaration order.
    """
    parent = coq_require_path(file).rsplit(".", 1)
    lines = [
        "(* Auto-generated by print-assumptions-snapshot. Do not edit. *)",
        f"From {parent[0]} Require Import {parent[1]}.",
        "",
    ]
    for m in milestones:
        # Bare Print Assumptions per milestone — Coq's stdout already
        # emits a deterministic Axioms:/Theory: framing per block,
        # which the parser uses to split.
        lines.append(f"(* milestone: {m.coq_qualified} *)")
        lines.append(f"Print Assumptions {m.coq_qualified}.")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Output parser.
#
# coqc in batch (non-interactive) mode does NOT echo `Definition X is
# defined` lines for plain Definitions. We tried emitting sentinel
# Definitions and discovered they're silent. So instead we rely on
# the deterministic block shape of Print Assumptions itself:
#
#     Axioms:                              (or "Closed under the global context.")
#     ...zero+ axiom lines (possibly multi-line)...
#     Theory:
#     Set is impredicative
#
# Each milestone produces exactly one block ending in `Theory:` +
# one or more theory lines. We split the output by walking lines and
# accumulating into the current block; whenever we see `Axioms:` or
# `Closed under the global context.` we start a new block, and we
# associate the freshly-completed block with the next milestone in
# source order.
# ---------------------------------------------------------------------------
def parse_coq_output(stdout: str, milestones: list[Milestone]) -> dict[str, str]:
    """Return slug -> raw print-assumptions-block.

    Splits stdout into one block per milestone by recognising the
    deterministic `Axioms:` / `Closed under the global context.` headers
    each `Print Assumptions` invocation produces. Assignment is by
    source order of `milestones` (which matches the driver order).
    """
    lines = stdout.splitlines()
    # Find each block's start line index. A block starts with either
    # `Axioms:` or `Closed under the global context.` at column 0.
    starts: list[int] = []
    for i, line in enumerate(lines):
        if line == "Axioms:" or line.startswith("Closed under the global context"):
            starts.append(i)
    blocks: dict[str, str] = {}
    if len(starts) != len(milestones):
        # Don't fail outright — record what we can; the caller will
        # see empty blocks for the missing milestones and emit an
        # ERROR stub for each.
        print(f"  warning: expected {len(milestones)} blocks, found "
              f"{len(starts)} in coqc output", file=sys.stderr)
    for idx, m in enumerate(milestones):
        if idx >= len(starts):
            blocks[m.slug] = ""
            continue
        start = starts[idx]
        end = starts[idx + 1] if idx + 1 < len(starts) else len(lines)
        body = "\n".join(lines[start:end]).rstrip("\n")
        blocks[m.slug] = body
    return blocks


def count_axioms(block: str) -> tuple[int, int]:
    """Return (total_axiom_count, load_bearing_count) for a Print
    Assumptions block.

    Print Assumptions output format:
      Axioms:
      <name1> : <type spread over zero+ lines>
      <name2> : ...
      Theory:
      Set is impredicative

    We count "top-level" axiom names — lines that look like `Foo.bar :`
    at column 0 (continuation lines for type signatures are indented).
    """
    lines = block.splitlines()
    in_axioms = False
    total = 0
    load_bearing = 0
    for line in lines:
        stripped = line.rstrip()
        if stripped == "Axioms:":
            in_axioms = True
            continue
        if stripped == "Theory:":
            in_axioms = False
            continue
        if stripped.startswith("Closed under the global context"):
            # No axioms — Coq emits this single line instead of Axioms:.
            in_axioms = False
            continue
        if not in_axioms:
            continue
        # Top-level axiom lines start at column 0 with `<name> :`.
        # Continuation lines are indented (typically 2+ spaces).
        if line and not line[0].isspace() and " :" in line:
            name = line.split(" :", 1)[0].strip()
            total += 1
            if not any(name.startswith(p) for p in KERNEL_AXIOM_PREFIXES):
                load_bearing += 1
    return total, load_bearing


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    ap.add_argument("--repo", required=True, help="Repository root (REPO_TREE).")
    ap.add_argument("--rocq-tree", required=True, help="rocq-of-solidity checkout root.")
    ap.add_argument("--out", required=True, help="Output directory for snapshot files.")
    ap.add_argument("--timeout", type=int, default=120, help="Per-coqc timeout (s).")
    ap.add_argument("--timeout-cmd", default="timeout", help="Wrapper command (timeout / gtimeout).")
    args = ap.parse_args()

    repo = Path(args.repo).resolve()
    equiv_dir = repo / "formal-verification" / "rocq" / "proofs" / "equivalence"
    governor_rocq = repo / "formal-verification" / "rocq"
    rocq_tree = Path(args.rocq_tree).resolve()
    out_dir = Path(args.out).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    # Wipe stale per-theorem files so a removed milestone doesn't
    # leave its old snapshot lying around. summary.* is overwritten
    # explicitly below.
    for p in out_dir.glob("*.txt"):
        p.unlink()

    print(f"==> scanning {equiv_dir} for milestone theorems")
    milestones = list(iter_milestones(equiv_dir))
    print(f"    found {len(milestones)} milestones across "
          f"{len({m.file for m in milestones})} files")

    if not milestones:
        print("error: no milestones found — check MILESTONE_THEOREM_RE and SKIP_FILES.",
              file=sys.stderr)
        return 6

    # Group by file. We compile one driver per equivalence file so a
    # parse error in one doesn't poison the rest.
    by_file: dict[str, list[Milestone]] = {}
    for m in milestones:
        by_file.setdefault(m.file, []).append(m)

    # CSV rows accumulate as we process each file.
    csv_rows: list[dict[str, str | int]] = []
    error_files: list[str] = []

    drivers_tmp = out_dir / "_drivers"
    drivers_tmp.mkdir(exist_ok=True)

    for file, ms in by_file.items():
        print(f"==> {file}: {len(ms)} milestone(s)")
        driver_v = build_driver_v(file, ms)
        driver_path = drivers_tmp / f"_pa_driver_{file}"
        driver_path.write_text(driver_v)

        # coqc invocation mirrors rocq-build's flag set.
        cmd = [
            args.timeout_cmd,
            "--kill-after=5",
            str(args.timeout),
            "coqc",
            "-R", str(rocq_tree / "rocq" / "RocqOfSolidity"), "RocqOfSolidity",
            "-R", str(governor_rocq), "ReserveGovernor",
            "-impredicative-set",
            "-w", "-stdlib-vector",
            str(driver_path),
        ]
        try:
            res = subprocess.run(cmd, check=False, capture_output=True, text=True)
        except FileNotFoundError as e:
            print(f"  error: command not found: {e}", file=sys.stderr)
            return 8
        stdout = res.stdout or ""
        if res.returncode != 0:
            print(f"  ERROR coqc exit={res.returncode} on {file}", file=sys.stderr)
            # Still try to parse partial output. Stderr is often where
            # error messages land; keep it alongside as a debugging aid.
            stderr_path = drivers_tmp / f"_pa_driver_{file}.stderr"
            stderr_path.write_text(res.stderr or "")
            error_files.append(file)

        blocks = parse_coq_output(stdout, ms)

        for m in ms:
            block = blocks.get(m.slug, "")
            if not block:
                # No output captured — emit an explicit error stub so
                # the diff catches the regression.
                out_text = (
                    f"# ERROR: Print Assumptions {m.coq_qualified} "
                    f"produced no output\n"
                    f"# Driver: {driver_path.name}\n"
                    f"# coqc exit: {res.returncode}\n"
                )
                total, load = 0, 0
                status = "ERROR"
            else:
                out_text = (
                    f"# Theorem: {m.coq_qualified}\n"
                    f"# Source:  {m.file}:{m.lineno}\n"
                    f"# Module:  {m.module_path}\n"
                    f"#\n"
                    f"{block}\n"
                )
                total, load = count_axioms(block)
                status = "OK"
            (out_dir / f"{m.slug}.txt").write_text(out_text)
            csv_rows.append({
                "file": m.file,
                "module": m.module_path,
                "theorem": m.name,
                "lineno": m.lineno,
                "axioms_total": total,
                "axioms_load_bearing": load,
                "status": status,
            })

    # Sort CSV rows for stable output.
    csv_rows.sort(key=lambda r: (r["file"], r["lineno"]))
    csv_path = out_dir / "summary.csv"
    with csv_path.open("w", newline="") as fh:
        writer = csv.DictWriter(
            fh,
            fieldnames=["file", "module", "theorem", "lineno",
                        "axioms_total", "axioms_load_bearing", "status"],
        )
        writer.writeheader()
        for row in csv_rows:
            writer.writerow(row)

    # Markdown summary, grouped by file.
    md_path = out_dir / "summary.md"
    with md_path.open("w") as fh:
        fh.write("# Print Assumptions snapshot — milestone roster\n\n")
        fh.write(f"Captured for {len(csv_rows)} milestones across "
                 f"{len({r['file'] for r in csv_rows})} files.\n\n")
        fh.write("Counts:\n\n")
        fh.write(f"- **axioms_total** — every entry under `Axioms:` for the milestone.\n")
        fh.write(f"- **axioms_load_bearing** — total minus kernel primitives "
                 f"(`PrimInt63.*`, `of_u256_list`, `of_storable_values`).\n\n")
        fh.write("| File | Theorem | Module | total | load-bearing | status |\n")
        fh.write("|---|---|---|---:|---:|---|\n")
        current_file = None
        for row in csv_rows:
            fh.write(
                f"| {row['file']} | `{row['theorem']}` "
                f"| {row['module']} | {row['axioms_total']} "
                f"| {row['axioms_load_bearing']} | {row['status']} |\n"
            )

    print(f"==> wrote {len(csv_rows)} per-theorem files + summary.{{csv,md}} to {out_dir}")
    if error_files:
        print(f"warning: {len(error_files)} file(s) had coqc errors — "
              f"see {drivers_tmp}/*.stderr", file=sys.stderr)
        return 9

    # On success, remove the intermediate driver build artefacts. The
    # `.v` / `.vo` / `.vos` / `.vok` / `.glob` files are not part of
    # the snapshot — keeping them around would bloat the baseline and
    # cause spurious diffs on every run (coqc embeds timestamps in
    # the `.vo` header). Leave them in place on error so the failure
    # is debuggable.
    for p in drivers_tmp.iterdir():
        try:
            p.unlink()
        except OSError:
            pass
    try:
        drivers_tmp.rmdir()
    except OSError:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
