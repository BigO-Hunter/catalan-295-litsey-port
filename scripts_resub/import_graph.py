#!/usr/bin/env python3
"""Import-graph audit for the catalan-410 resubmission.

Resolves every internal import in the tree and reports, for a set of roots,
the transitive closure and anything reachable OUTSIDE the Submission/ dir.
Static only: no Lean, no build.

Usage: python3 scripts_resub/import_graph.py [--json out.json]
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

IMPORT_RE = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)?import\s+([A-Za-z0-9_.'«»]+)")


def scan() -> dict[str, Path]:
    """module name -> file for every .lean in the tree."""
    mods: dict[str, Path] = {}
    for p in ROOT.rglob("*.lean"):
        rel = p.relative_to(ROOT).with_suffix("")
        if rel.parts[0] in {".lake", ".git", ".w6"}:
            continue
        mods[".".join(rel.parts)] = p
    return mods


def imports_of(path: Path) -> list[str]:
    out = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def closure(mods: dict[str, Path], roots: list[str]) -> dict[str, set[str]]:
    """root -> set of internal modules reachable (roots included)."""
    result = {}
    for root in roots:
        seen: set[str] = set()
        stack = [root]
        missing: set[str] = set()
        while stack:
            cur = stack.pop()
            if cur in seen:
                continue
            seen.add(cur)
            f = mods.get(cur)
            if f is None:
                if "." in cur and cur.split(".")[0] in {
                    "CatalanMeasure", "Submission", "OAI", "CatalanCore",
                    "CatalanFrames", "CatalanLambda", "PrimeNumberTheoremAnd",
                }:
                    missing.add(cur)
                continue
            for dep in imports_of(f):
                if dep not in seen:
                    stack.append(dep)
        result[root] = seen
        if missing:
            result[root + "#missing"] = missing
    return result


def main() -> int:
    mods = scan()
    print(f"modules on disk: {len(mods)}")
    trees: dict[str, int] = {}
    for name in mods:
        trees[name.split(".")[0]] = trees.get(name.split(".")[0], 0) + 1
    for k in sorted(trees, key=lambda x: -trees[x]):
        print(f"  {k:24s} {trees[k]:6d}")

    roots = ["Solution", "Challenge", "Submission"]
    cl = closure(mods, roots)
    external_top: set[str] = set()
    for root in roots:
        reach = cl[root]
        outside = {m for m in reach if mods.get(m) and mods[m].relative_to(ROOT).parts[0] != "Submission" and "." in m and mods[m].relative_to(ROOT).parts[0] != ""}
        # roots Solution/Challenge are top-level files; count only those that live in a tree dir
        outside = {
            m for m in outside
            if mods[m].relative_to(ROOT).parts[0] not in {"Solution.lean", "Challenge.lean"}
            and mods[m].name not in {"Solution.lean", "Challenge.lean"}
        }
        print(f"\nroot {root}: {len(reach)} internal modules reachable")
        print(f"  outside Submission/: {len(outside)}")
        for m in sorted(outside)[:20]:
            print(f"    {m}"
                  f"  ({mods[m].relative_to(ROOT)})")
        if len(outside) > 20:
            print(f"    ... {len(outside)-20} more")
        external_top |= outside
        if root + "#missing" in cl:
            print(f"  UNRESOLVED internal imports: {sorted(cl[root + '#missing'])[:10]}")

    # which non-Submission files are imported by anything that survives?
    print(f"\nTOTAL modules outside Submission/ needed by the judged roots: {len(external_top)}")

    if "--json" in sys.argv:
        out = sys.argv[sys.argv.index("--json") + 1]
        Path(out).write_text(json.dumps({k: sorted(v) for k, v in cl.items()}, indent=1))
        print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
