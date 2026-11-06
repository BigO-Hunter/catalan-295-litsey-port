#!/usr/bin/env python3
"""Elaborate the wrapper theorem against the built library — the comparator step.

`lake env lean Solution.lean` type-checks
`CatalanIrrationalityMeasure.catalan_irrationalityMeasure_410` — the wrapper that
RE-STATES the full `∀ᶠ b, ∀ a, …` formula and proves it from
`CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410` imported from the
cured mirror — and prints that theorem's axiom set via the `#print axioms` line
the file already carries.

So the verdict is structural, not a proxy: a statement that had drifted in either
tree could not elaborate, and a proof that picked up a non-permitted axiom shows
up in the printed set. A missing entry olean means the build is not done; this
script refuses rather than reporting anything.

Usage: run_comparator.py <out-json>
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENTRY = ROOT / ".lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean"
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    out = Path(sys.argv[1])
    if not ENTRY.exists():
        print(f"REFUSED: {ENTRY.relative_to(ROOT)} missing — the library build is not complete")
        return 2
    t0 = time.time()
    proc = subprocess.run(
        ["lake", "env", "lean", "Solution.lean"],
        cwd=ROOT, capture_output=True, text=True,
        env={**os.environ, "LEAN_NUM_THREADS": "1"},
    )
    wall = time.time() - t0
    combined = proc.stdout + proc.stderr
    axioms = [m.group(1).strip() for m in re.finditer(r"depends on axioms:\s*(.*)", combined)]
    errors = [ln for ln in combined.splitlines() if ln.startswith("error") or ": error:" in ln]
    verdict = {
        "comparator_exit": proc.returncode,
        "wall_s": round(wall, 1),
        "error_lines": errors[:10],
        "axioms_reported": axioms,
        "axioms_are_permitted": bool(axioms) and all(
            set(a.strip("[] ").split(", ")) <= PERMITTED for a in axioms
        ),
        "stdout": proc.stdout[-4000:],
        "stderr": proc.stderr[-4000:],
    }
    out.write_text(json.dumps(verdict, indent=1) + "\n")
    print(json.dumps({k: v for k, v in verdict.items() if k not in {"stdout", "stderr"}}, indent=1))
    print(f"COMPARATOR_EXIT={proc.returncode}")
    return 0 if proc.returncode == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
