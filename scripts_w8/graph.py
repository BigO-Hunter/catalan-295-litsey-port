"""W8 dependency-closure audit: parse Lean import graph, compute minimal closure.

Reads only text .lean files. Emits JSON + human summary to stdout.
"""

from __future__ import annotations

import json
import re
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMP_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+|Meta\s+|noncomputable\s+)*import\s+([A-Za-z0-9_.'\-]+)", re.M)


def module_of(p: Path) -> str:
    rel = p.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def main() -> None:
    files: dict[str, Path] = {}
    dups: dict[str, list[str]] = {}
    for p in ROOT.rglob("*.lean"):
        if ".git" in p.parts or "scripts_w8" in p.parts:
            continue
        m = module_of(p)
        if m in files:
            dups.setdefault(m, [str(files[m].relative_to(ROOT))]).append(str(p.relative_to(ROOT)))
        files[m] = p

    graph: dict[str, list[str]] = {}
    external: dict[str, int] = {}
    for m, p in files.items():
        try:
            txt = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            txt = ""
        deps = IMP_RE.findall(txt)
        internal = []
        for d in deps:
            if d in files:
                internal.append(d)
            else:
                external[d] = external.get(d, 0) + 1
        graph[m] = internal

    def closure(roots: list[str]) -> set[str]:
        seen: set[str] = set()
        dq = deque(roots)
        while dq:
            m = dq.popleft()
            if m in seen or m not in graph:
                continue
            seen.add(m)
            dq.extend(graph[m])
        return seen

    # Direct external (mathlib etc.) imports reachable from each closure root.
    def ext_from(mods: set[str]) -> dict[str, int]:
        out: dict[str, int] = {}
        for m in mods:
            p = files[m]
            for d in IMP_RE.findall(p.read_text(encoding="utf-8", errors="replace")):
                if d not in files:
                    out[d] = out.get(d, 0) + 1
        return out

    sol = closure(["Solution"])
    sub = closure(["Submission"])
    chal = closure(["Challenge"])
    sol_ext = ext_from(sol)
    sub_ext = ext_from(sub)

    def size(mods: set[str]) -> int:
        return sum(files[m].stat().st_size for m in mods)

    def tree_counts(mods: set[str]) -> dict[str, int]:
        c: dict[str, int] = {}
        for m in mods:
            top = m.split(".")[0]
            c[top] = c.get(top, 0) + 1
        return dict(sorted(c.items(), key=lambda kv: -kv[1]))

    all_top: dict[str, int] = {}
    for m in files:
        top = m.split(".")[0]
        all_top[top] = all_top.get(top, 0) + 1

    print(f"total .lean modules: {len(files)}")
    print(f"total top dirs: {dict(sorted(all_top.items(), key=lambda kv: -kv[1]))}")
    print(f"duplicate module names: {len(dups)}")
    print()
    print(f"Solution closure:  {len(sol)} internal modules, {size(sol)/1048576:.1f} MB, by tree {tree_counts(sol)}")
    print(f"Submission closure:{len(sub)} internal modules, {size(sub)/1048576:.1f} MB, by tree {tree_counts(sub)}")
    print(f"Challenge closure: {len(chal)} internal modules, {size(chal)/1048576:.1f} MB")
    print(f"Solution closure external imports: {len(sol_ext)} distinct")
    print(f"Submission closure external imports: {len(sub_ext)} distinct")
    print()
    print(f"Solution closure ext (all): {sorted(sol_ext)}")
    print(f"NOT in Solution closure but in Submission closure: {len(sub - sol)}")
    print(f"NOT in Submission closure (unreachable from lib root): {len(set(files) - sub)}")

    out = {
        "total_modules": len(files),
        "solution_closure": sorted(sol),
        "submission_closure": sorted(sub),
        "challenge_closure": sorted(chal),
        "solution_external": sorted(sol_ext),
        "submission_external": sorted(sub_ext),
        "out_of_solution_closure": sorted(set(files) - sol),
    }
    (ROOT / "scripts_w8" / "graph.json").write_text(json.dumps(out, indent=1))
    # full import edges for per-file analysis
    (ROOT / "scripts_w8" / "edges.json").write_text(
        json.dumps({m: graph[m] for m in files}, indent=0)
    )


if __name__ == "__main__":
    sys.exit(main())
