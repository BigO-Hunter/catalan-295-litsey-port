#!/usr/bin/env python3
"""Serial dependency-ordered Lean builder for governor-hostile machines.

Computes the import closure of target modules, topologically sorts the UNBUILT
local modules, and builds them strictly one at a time (`lake build <module>`,
LAKE_JOBS=1, LEAN_NUM_THREADS=1) so peak memory = ONE module's peak instead of
lake's parallel fan-out. Oleans are the ledger: skip what exists. Each lake
invocation runs in its own session so a host SIGTERM aimed at the lean tree
kills at most the module in flight — the loop resumes at the next unbuilt
module. No attempt cap: pass `--passes` or wrap in a shell loop; time-budgeted.

Reusable for any lean tree: `serial_build.py --root <repo> --entry Mod.Name`.

Usage: serial_build.py --root DIR --entry Mod [--entry Mod2 ...]
            [--budget-s N] [--passes N] [--log FILE] [--defer-modules M1,M2]
Exit 0 = closure complete. Exit 3 = budget/passes exhausted, resumable.
"""
from __future__ import annotations
import argparse, os, re, subprocess, sys, time
from pathlib import Path

IMPORT_RE = re.compile(r"^(?:public\s+|private\s+)?import\s+([A-Za-z_][\w.']*)", re.M)
FOREIGN = ("Mathlib", "Std", "Batteries", "Lake", "Init", "Lean", "LeanElab", "Lexer", "Parser")


def module_file(root: Path, mod: str) -> Path | None:
    parts = mod.split(".")
    for base in [root, root / "Submission"]:
        p = base.joinpath(*parts[:-1]) / (parts[-1] + ".lean")
        if p.exists():
            return p
    return None


def olean_path(root: Path, mod: str) -> Path:
    parts = mod.split(".")
    return root / ".lake/build/lib/lean" / Path(*parts[:-1]) / (parts[-1] + ".olean")


def parse_imports(f: Path) -> list[str]:
    try:
        return IMPORT_RE.findall(f.read_text(errors="replace"))
    except OSError:
        return []


def collect(root: Path, entries: list[str]):
    seen, unknown, stack = set(), set(), list(entries)
    edges: dict[str, list[str]] = {}
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        f = module_file(root, mod)
        if f is None:
            if not mod.startswith(FOREIGN):
                unknown.add(mod)
            continue
        imps = parse_imports(f)
        edges[mod] = imps
        stack.extend(imps)
    return seen, edges, unknown


def topo(todo: set[str], edges: dict[str, list[str]]) -> list[str]:
    order, state = [], {}

    def visit(mod: str):
        if state.get(mod):
            return
        state[mod] = 1
        for dep in edges.get(mod, []):
            if dep in todo:
                visit(dep)
        state[mod] = 2
        order.append(mod)

    for m in sorted(todo):
        visit(m)
    return order


def build_one(root: Path, mod: str, env: dict, timeout_s: int) -> tuple[str, str]:
    """Returns (verdict, detail): verdict in {ok, fail, kill, timeout}."""
    t0 = time.time()
    try:
        # own session: host SIGTERMs aimed at the lean tree cannot reach this loop
        p = subprocess.Popen(["lake", "build", mod], cwd=root, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
        out, _ = p.communicate(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), 9)
        except OSError:
            pass
        return "timeout", f"{time.time()-t0:.0f}s"
    wall = time.time() - t0
    errs = [l for l in out.splitlines() if ": error" in l]
    if p.returncode == 0 and not errs:
        return "ok", f"{wall:.0f}s"
    if p.returncode < 0:
        return "kill", f"sig {-p.returncode} after {wall:.0f}s"
    return "fail", f"rc={p.returncode} {errs[:2]}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument("--entry", action="append", required=True)
    ap.add_argument("--budget-s", type=int, default=12 * 3600)
    ap.add_argument("--passes", type=int, default=1)
    ap.add_argument("--timeout-s", type=int, default=3 * 3600, help="per-module cap")
    ap.add_argument("--log", default=None)
    ap.add_argument("--defer-modules", default="", help="comma-separated module suffixes to build last")
    args = ap.parse_args()
    root = Path(args.root).resolve()
    logf = open(args.log, "a") if args.log else None

    def log(msg: str):
        line = f"[{time.strftime('%m-%d %H:%M:%S')}] {msg}"
        print(line, flush=True)
        if logf:
            logf.write(line + "\n")
            logf.flush()

    defer_suffixes = [s.strip() for s in args.defer_modules.split(",") if s.strip()]
    t_end = time.time() + args.budget_s
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "LAKE_JOBS": "1"}
    kills = fails = built = 0

    for run in range(1, args.passes + 1):
        seen, edges, unknown = collect(root, args.entry)
        local = {m for m in seen if module_file(root, m) is not None}
        if unknown:
            log(f"WARNING non-local unknown modules: {sorted(unknown)[:5]}")
        todo = {m for m in local if not olean_path(root, m).exists()}
        log(f"pass {run}: closure local={len(local)} todo={len(todo)}")
        if not todo:
            log("NOTHING TO BUILD — closure complete")
            return 0
        order = topo(todo, edges)
        deferred = [m for m in order if any(m.endswith(s) for s in defer_suffixes)]
        if deferred:
            rest = [m for m in order if m not in set(deferred)]
            log(f"deferring {len(deferred)} giant-class modules to end: {deferred}")
            order = rest + deferred
        for i, mod in enumerate(order):
            if time.time() > t_end:
                log(f"TIME BUDGET reached at {i}/{len(order)} — resumable")
                return 3
            verdict, detail = build_one(root, mod, env, args.timeout_s)
            if verdict == "ok":
                built += 1
                log(f"[{i+1}/{len(order)}] ok {mod} ({detail})")
            elif verdict == "kill":
                kills += 1
                log(f"[{i+1}/{len(order)}] KILLED {mod} ({detail})")
            elif verdict == "timeout":
                kills += 1
                log(f"[{i+1}/{len(order)}] TIMEOUT {mod} ({detail})")
            else:
                fails += 1
                log(f"[{i+1}/{len(order)}] FAIL {mod} ({detail})")
                if fails >= 5:
                    log("5 hard failures — stopping for inspection")
                    return 1
    seen, _, _ = collect(root, args.entry)
    left = sum(1 for m in seen if module_file(root, m) is not None and not olean_path(root, m).exists())
    log(f"passes done: built={built} kills={kills} fails={fails} remaining={left}")
    return 0 if left == 0 else 3


if __name__ == "__main__":
    sys.exit(main())
