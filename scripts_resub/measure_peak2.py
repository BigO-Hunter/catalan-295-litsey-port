#!/usr/bin/env python3
"""Sample only the lean processes belonging to THIS build root.

The host runs many sibling campaign builds, so a process-wide RSS sum is not a
measurement of this submission. Every lean child Lake spawns here names this
repo's absolute path on its command line, so filtering on that path attributes
samples correctly.

Records, per sample: number of lean processes, their summed RSS (the quantity
the verifier's per-cgroup cap limits), and the per-module peak seen.

Stops when <log> contains "Error" or the build's lake process is gone.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

BUILD_ROOT = os.environ["BUILD_ROOT"]
INTERVAL = float(os.environ.get("PEAK_INTERVAL", "0.5"))


def mine() -> list[tuple[int, int, str]]:
    out = subprocess.run(["ps", "-axo", "pid=,rss=,args="], capture_output=True, text=True).stdout
    procs = []
    for line in out.splitlines():
        parts = line.split(None, 2)
        if len(parts) < 3:
            continue
        pid, rss, args = parts
        if BUILD_ROOT not in args:
            continue
        if "measure_peak2" in args or "measure_build" in args:
            continue
        exe = os.path.basename(args.split()[0])
        if not exe.startswith("lean"):
            continue
        if "--server" in args:
            continue
        procs.append((int(pid), int(rss), args))
    return procs


def module_of(args: str) -> str:
    for tok in args.split():
        if tok.endswith(".lean"):
            return tok.replace(BUILD_ROOT + "/", "")
    return "?"


def main() -> int:
    outdir = Path(sys.argv[1])
    log = Path(sys.argv[2])
    outdir.mkdir(parents=True, exist_ok=True)
    samples = (outdir / "samples.tsv").open("w")
    samples.write("t\tn\ttotal_mb\tpeak_proc_mb\tmodule\n")
    per_mod: dict[str, float] = {}
    peak_total = 0.0
    max_n = 0
    t0 = time.time()
    stale = 0
    while True:
        procs = mine()
        total = sum(r for _, r, _ in procs) / 1024.0
        peak_total = max(peak_total, total)
        max_n = max(max_n, len(procs))
        cur_mod, cur_peak = "?", 0.0
        for _, rss, args in procs:
            m = module_of(args)
            mb = rss / 1024.0
            if mb > per_mod.get(m, 0.0):
                per_mod[m] = mb
            if mb > cur_peak:
                cur_mod, cur_peak = m, mb
        samples.write(f"{time.time()-t0:.1f}\t{len(procs)}\t{total:.0f}\t{cur_peak:.0f}\t{cur_mod}\n")
        samples.flush()
        text = log.read_text(errors="replace") if log.exists() else ""
        if "BUILD_EXIT" in text or "error: " in text:
            stale = 99
        if not procs:
            stale += 1
            if stale > int(os.environ.get("PEAK_STALE", "20")):
                break
        else:
            stale = 0
        time.sleep(INTERVAL)
    samples.close()
    summary = {
        "wall_s": round(time.time() - t0, 1),
        "peak_concurrent_total_mb": round(peak_total, 1),
        "max_concurrent_lean": max_n,
        "modules_sampled": len(per_mod),
        "top_module_peaks_mb": [
            [m, round(v, 1)] for m, v in sorted(per_mod.items(), key=lambda kv: -kv[1])[:20]
        ],
    }
    (outdir / "peak2.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
