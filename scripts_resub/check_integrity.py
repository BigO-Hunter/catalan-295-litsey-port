#!/usr/bin/env python3
"""Post-deletion integrity check: every internal import must resolve to a file.

Internal prefixes are the repo's own top-level module roots. A surviving file
that imports a deleted module would fail to elaborate, so this must be zero
before any build is attempted.

Exit 1 if any dangling import exists.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from import_graph import ROOT, closure, scan  # noqa: E402

INTERNAL_ROOTS = {
    "CatalanMeasure", "CatalanCore", "OAI", "CatalanFrames", "CatalanLambda",
    "PrimeNumberTheoremAnd", "Submission",
}


def main() -> int:
    mods = scan()
    print(f"modules on disk: {len(mods)}")

    dangling: list[tuple[str, str]] = []
    for name, path in sorted(mods.items()):
        from import_graph import imports_of
        for dep in imports_of(path):
            if dep.split(".")[0] in INTERNAL_ROOTS and dep not in mods:
                dangling.append((name, dep))

    print(f"dangling internal imports: {len(dangling)}")
    for src, dep in dangling[:20]:
        print(f"  {src} -> {dep}")

    roots = ["Solution", "Challenge", "Submission", "SolutionHybrid", "ChallengeHybrid"]
    cl = closure(mods, roots)
    for r in roots:
        outside = {
            m for m in cl[r]
            if (p := mods.get(m)) is not None
            and p.relative_to(ROOT).parts[0] not in {"Submission", }
            and p.name not in {"Solution.lean", "Challenge.lean", "SolutionHybrid.lean", "ChallengeHybrid.lean"}
        }
        print(f"{r}: {len(cl[r])} import names, {len(outside)} files outside Submission/")
        if r + "#missing" in cl:
            print(f"  UNRESOLVED: {sorted(cl[r + '#missing'])}")
    return 1 if dangling else 0


if __name__ == "__main__":
    raise SystemExit(main())
