#!/usr/bin/env python3
"""Launch a build fully detached and sample the footprint of every lean process.

Detached launch: survives the harness bash watchdog, which kills the whole
process group of a foreground command (AGENTS.md rule 19).

Sampling: `ps -axo pid=,rss=,args=` every INTERVAL s. Records the SUM of RSS
across lean processes (the quantity the verifier's 14 GiB cgroup cap limits)
and the per-PID max, attributed to the .lean file on the command line.

Writes <outdir>/samples.tsv (one row per sample) and <outdir>/summary.json.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from pathlib import Path

INTERVAL = float(os.environ.get("PEAK_INTERVAL", "0.5"))


def lean_procs() -> list[tuple[int, int, str]]:
    out = subprocess.run(
        ["ps", "-axo", "pid=,rss=,args="], capture_output=True, text=True
    ).stdout
    procs = []
    for line in out.splitlines():
        parts = line.split(None, 2)
        if len(parts) < 3:
            continue
        pid, rss, args = parts
        if "lean" not in os.path.basename(args.split()[0]):
            continue
        if "--server" in args or "watchdog" in args:
            continue
        procs.append((int(pid), int(rss), args))
    return procs


def module_of(args: str) -> str:
    for tok in args.split():
        if tok.endswith(".lean"):
            return tok
    return "?"


def main() -> int:
    outdir = Path(sys.argv[1])
    log = sys.argv[2]
    outdir.mkdir(parents=True, exist_ok=True)
    samples = (outdir / "samples.tsv").open("w")
    samples.write("t\tprocs\ttotal_mb\tmodules\n")
    per_mod: dict[str, float] = {}
    peak_total = 0.0
    t0 = time.time()
    with open(log, "w") as lf:
        proc = subprocess.Popen(
            ["lake", "build", "Submission"],
            cwd=os.environ["BUILD_ROOT"],
            stdout=lf,
            stderr=subprocess.STDOUT,
            start_new_session=True,  # detached: the watchdog's group kill misses it
            env={
                **os.environ,
                "LEAN_NUM_THREADS": "1",
                "LAKE_JOBS": "1",
            },
        )
        print(f"pid={proc.pid} log={log}", flush=True)
        while proc.poll() is None:
            procs = lean_procs()
            total = sum(r for _, r, _ in procs) / 1024.0
            peak_total = max(peak_total, total)
            mods = []
            for _, rss, args in procs:
                m = module_of(args)
                mods.append(m)
                mb = rss / 1024.0
                if mb > per_mod.get(m, 0.0):
                    per_mod[m] = mb
            samples.write(
                f"{time.time()-t0:.1f}\t{len(procs)}\t{total:.0f}\t{','.join(mods[:4])}\n"
            )
            samples.flush()
            time.sleep(INTERVAL)
        rc = proc.returncode
    samples.close()
    summary = {
        "build_exit": rc,
        "wall_s": round(time.time() - t0, 1),
        "peak_concurrent_total_mb": round(peak_total, 1),
        "modules_sampled": len(per_mod),
        "top_module_peaks_mb": sorted(per_mod.items(), key=lambda kv: -kv[1])[:25],
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
