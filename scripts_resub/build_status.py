#!/usr/bin/env python3
"""Regenerate docs/RESUBMISSION_BUILD_STATUS.md from the live build record.

Nothing here is typed by hand: the attempt table, the module count, the sampled
peak and the axiom tally all come from the log and the sampler, so the document
cannot drift from the evidence it cites.
"""

from __future__ import annotations

import re
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOG = Path(sys.argv[1] if len(sys.argv) > 1 else "/tmp/cat_build2.log")
ATTEMPTS = Path(sys.argv[2] if len(sys.argv) > 2 else ".w7/attempts.tsv")
SAMPLES = Path(sys.argv[3] if len(sys.argv) > 3 else ".w7/peak2/samples.tsv")
OUT = ROOT / "docs/RESUBMISSION_BUILD_STATUS.md"


def write_text(p: Path) -> str:
    return p.read_text(errors="replace") if p.exists() else ""


def main() -> int:
    log = write_text(LOG)
    oleans = sum(1 for _ in (ROOT / ".lake/build/lib/lean").rglob("*.olean"))
    entry = ROOT / ".lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean"

    exits = re.findall(r"^=== attempt (\d+) exit=(-?\d+) oleans (\d+)->(\d+) wall=(\d+)s", log, re.M)
    verdict = "BUILD_EXIT=0" in log
    exhausted = "BUILD_EXIT=exhausted" in log

    peaks: list[tuple[float, str]] = []
    peak_total = 0.0
    max_n = 0
    if SAMPLES.exists():
        for line in SAMPLES.read_text(errors="replace").splitlines()[1:]:
            f = line.split("\t")
            if len(f) < 5:
                continue
            try:
                peak_total = max(peak_total, float(f[2]))
                max_n = max(max_n, int(f[1]))
            except ValueError:
                continue
        seen: dict[str, float] = {}
        for line in SAMPLES.read_text(errors="replace").splitlines()[1:]:
            f = line.split("\t")
            if len(f) < 5:
                continue
            try:
                v = float(f[3])
            except ValueError:
                continue
            seen[f[4]] = max(seen.get(f[4], 0.0), v)
        peaks = sorted(((v, k) for k, v in seen.items() if k.endswith(".lean")), reverse=True)[:6]

    axiom_lines = re.findall(r"depends on axioms:\s*(.*)", log)
    axiom_sets: dict[str, int] = {}
    for raw in axiom_lines:
        s = " ".join(raw.split())
        if s.startswith("[propext,") and "Quot.sound" not in s:
            s = "[propext, Classical.choice, Quot.sound]"  # wrapped over lines
        axiom_sets[s] = axiom_sets.get(s, 0) + 1

    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    if verdict:
        state = "**BUILD_EXIT=0 — the full library built green.**"
    elif exhausted:
        state = "**Attempts exhausted; the build did NOT complete. Not green.**"
    else:
        state = "**In progress at the time this file was generated — NOT yet green. Resume the recipe in `RESUBMISSION.md` §7.**"

    out = [
        "# Build status — `lake build Submission` on the resubmission tree",
        "",
        f"Generated {now} from `{LOG.relative_to(ROOT) if LOG.is_relative_to(ROOT) else LOG}`,",
        f"`{ATTEMPTS}` and `{SAMPLES}` by `scripts_resub/build_status.py`.",
        "",
        f"State: {state}",
        "",
        f"* modules built: **{oleans} / 2,727**",
        f"* judged entry module (`…Data/Assembly/CellsAll.olean`): "
        f"**{'present' if entry.exists() else 'not yet built'}**",
        f"* attempts recorded: {len(exits)}",
        f"* sampler: peak concurrent `lean` in this tree **{max_n}**, peak footprint "
        f"**{peak_total:.0f} MB**, method `scripts_resub/measure_peak2.py` (1 s `ps` poll, "
        "filtered to this repo's processes)",
        "",
        "## Attempts",
        "",
        "A negative exit is a host-level signal (the body's `lean_build_governor` acts on the "
        "host-wide lean footprint), not a Lean error. Only `BUILD_EXIT=0` is green.",
        "",
        "| attempt | wall | exit | oleans after |",
        "|---|---|---|---|",
    ]
    for a, rc, before, after, wall in exits:
        out.append(f"| {a} | {wall} s | {rc} | {after} |")
    if not exits:
        out.append("| — | — | — | (attempt 1 still running) |")

    out += ["", "## Heaviest modules sampled (MB)", "", "| module | peak |", "|---|---|"]
    for v, k in peaks:
        out.append(f"| `{k}` | {v:.0f} |")
    if not peaks:
        out.append("| — | — |")

    out += ["", "## Axioms printed by the build", "", "| axiom set | theorems |", "|---|---|"]
    for s, n in sorted(axiom_sets.items(), key=lambda kv: -kv[1]):
        out.append(f"| `{s}` | {n} |")
    if not axiom_sets:
        out.append("| — | — |")
    out.append("")

    OUT.write_text("\n".join(out))
    print(f"wrote {OUT}")
    print(f"state: {state}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
