#!/usr/bin/env python3
"""Resumable, supervised `lake build Submission`.

Why a loop and not one command: the body's ``lean_build_governor`` freezes and
kills lean processes when the HOST-WIDE lean footprint crosses its aggregate
ceiling, which sibling campaign builds push it over independently of this
build. Measured: one clean attempt ran 221 s and was SIGTERM'd with zero Lean
errors in the log. The governor's ceiling is host-wide (24,576 MB at the time of
writing), not a property of this tree, so no single long invocation is safe
here. Lake resumes from existing oleans, so retrying loses at most one module.

Every attempt appends to one log with an attempt header, and the final line of
that log is ``BUILD_EXIT=<code>`` so a caller can grep the verdict instead of
inferring it. Exit code 0 is the only success; a SIGTERM attempt (negative code)
is never reported as green.

Usage: build_supervised.py <logfile> <attempts.tsv> [max_attempts]
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENV = {**os.environ, "LEAN_NUM_THREADS": "1", "LAKE_JOBS": "1"}
ENTRY_OLEAN = ROOT / ".lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean"


def oleans() -> int:
    return sum(1 for _ in (ROOT / ".lake/build/lib/lean").rglob("*.olean"))


def main() -> int:
    log = Path(sys.argv[1])
    tsv = Path(sys.argv[2])
    max_attempts = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    tsv.write_text("attempt\tstart\tend\twall_s\texit\toleans\n")
    for attempt in range(1, max_attempts + 1):
        before = oleans()
        start = time.time()
        with log.open("a") as lf:
            lf.write(f"\n=== attempt {attempt} start {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(start))}"
                     f" oleans={before} ===\n")
            lf.flush()
            proc = subprocess.Popen(
                ["lake", "build", "Submission"],
                cwd=ROOT, stdout=lf, stderr=subprocess.STDOUT,
                start_new_session=True, env=ENV,
            )
            rc = proc.wait()
        wall = time.time() - start
        after = oleans()
        tsv.open("a").write(f"{attempt}\t{start:.0f}\t{time.time():.0f}\t{wall:.0f}\t{rc}\t{after}\n")
        with log.open("a") as lf:
            lf.write(f"=== attempt {attempt} exit={rc} oleans {before}->{after} "
                     f"wall={wall:.0f}s entry_olean={ENTRY_OLEAN.exists()} ===\n")
        if rc == 0:
            with log.open("a") as lf:
                lf.write("BUILD_EXIT=0\n")
            return 0
        time.sleep(15)
    with log.open("a") as lf:
        lf.write(f"BUILD_EXIT=exhausted({max_attempts} attempts)\n")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
