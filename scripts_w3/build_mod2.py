"""Compile the transitive import closure of a live-tree module into the lake build dir.

Usage: python3 build_mod.py <Module.Name> [workers]
Topological, small worker pool (default 3) — the pool is for the BUILD only;
peak-RSS measurements are always taken in a separate single-threaded run.
"""
import re
import subprocess
import sys
import os
import time
from pathlib import Path

REPO = Path("/Users/dmitri.arkhipov/bigo-campaign/cat-chunk-W3/repo")
OUT = REPO / ".lake/build/lib/lean"
SKIP_TOPS = {".lake", "archive", "Submission", "docbuild", "test", "scripts_split", "phase0"}
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 3

imp_re = re.compile(r"^\s*(?:public\s+)?import\s+([\w.]+)", re.M)

mods = {}
for p in REPO.rglob("*.lean"):
    rel = p.relative_to(REPO)
    if rel.parts[0] in SKIP_TOPS:
        continue
    mods[str(rel.with_suffix("")).replace("/", ".")] = p

target = sys.argv[1]
deps = {}
seen = set()


def visit(m):
    if m in seen:
        return
    seen.add(m)
    p = mods.get(m)
    if p is None:
        return
    ds = [d for d in imp_re.findall(p.read_text(encoding="utf-8", errors="replace")) if d in mods]
    deps[m] = ds
    for d in ds:
        visit(d)


visit(target)
LAKE_PATHS = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=REPO,
                            capture_output=True, text=True).stdout.strip()
env = dict(os.environ, LEAN_PATH=LAKE_PATHS, LEAN_NUM_THREADS="1", LAKE_JOBS="1")

todo = set(deps)
done = set()
running = {}  # module -> (proc, t0, logfile)
t_all = time.time()
while todo or running:
    for m in list(running):
        proc, t0, log = running[m]
        if proc.poll() is None:
            continue
        dt = time.time() - t0
        del running[m]
        if proc.returncode != 0:
            print(f"FAIL {m} after {dt:.0f}s\n{Path(log).read_text()[-3000:]}", flush=True)
            sys.exit(1)
        done.add(m)
        if dt > 5:
            print(f"[{len(done)}/{len(deps)}] {dt:6.1f}s {m}", flush=True)
    for m in list(todo):
        if len(running) >= WORKERS:
            break
        if not all(d in done or d not in deps for d in deps[m]):
            continue
        src = mods[m]
        olean = OUT / src.relative_to(REPO).with_suffix(".olean")
        todo.discard(m)
        if olean.exists() and olean.stat().st_mtime >= src.stat().st_mtime:
            done.add(m)
            continue
        olean.parent.mkdir(parents=True, exist_ok=True)
        log = f"/tmp/w3build_{m}.log"
        f = open(log, "w")
        proc = subprocess.Popen(["lean", "-R", str(REPO), "-o", str(olean), str(src)],
                                cwd=REPO, env=env, stdout=f, stderr=subprocess.STDOUT)
        running[m] = (proc, time.time(), log)
    time.sleep(1.0)
print(f"closure built OK in {time.time()-t_all:.0f}s ({len(deps)} modules)", flush=True)
