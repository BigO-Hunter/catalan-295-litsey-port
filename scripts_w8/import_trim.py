"""W8 import-trim audit: find transitively-redundant imports in the LIVE trees.

An import X is "can drop" iff another import Y of the same file already reaches X
transitively: names stay resolvable through Y, so removal cannot break resolution.
Conservative: reported, not applied.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMP_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+|private[ \t]+|meta[ \t]+|Meta[ \t]+)*import[ \t]+([A-Za-z0-9_.'\-]+)",
    re.M,
)
LIVE = ("Submission", "CatalanMeasure", "OAI", "CatalanCore", "PrimeNumberTheoremAnd")


def main() -> None:
    edges: dict[str, list[str]] = json.loads((ROOT / "scripts_w8" / "edges.json").read_text())
    mods: dict[str, Path] = {}
    for p in ROOT.rglob("*.lean"):
        if ".git" in p.parts:
            continue
        mods[".".join(p.relative_to(ROOT).with_suffix("").parts)] = p

    memo: dict[str, set[str]] = {}

    def reach(m: str, stack: frozenset[str] = frozenset()) -> set[str]:
        if m in memo:
            return memo[m]
        if m in stack:
            return set()
        out: set[str] = set()
        for d in edges.get(m, []):
            out.add(d)
            out |= reach(d, stack | {m})
        memo[m] = out
        return out

    total_red = total_imports = 0
    per_file: list[tuple[str, int, int, list[str]]] = []
    for m, p in mods.items():
        if not m.split(".")[0] in LIVE:
            continue
        txt = p.read_text(encoding="utf-8", errors="replace")
        direct = [d for d in IMP_RE.findall(txt) if d in edges]
        if len(direct) < 2:
            continue
        total_imports += len(direct)
        red: list[str] = []
        for d in direct:
            others = [o for o in direct if o != d]
            if any(d in reach(o) for o in others) and d not in red:
                red.append(d)
        if red:
            total_red += len(red)
            per_file.append((m, len(direct), len(red), red))

    per_file.sort(key=lambda r: -r[2])
    print(f"live modules with >=2 internal imports: analysed")
    print(f"internal import lines: {total_imports}; transitively redundant: {total_red}")
    print(f"files affected: {len(per_file)}\n")
    print("top 20 by redundant count:")
    for m, n, r, red in per_file[:20]:
        print(f"  {r:2}/{n:2}  {m}")
        if r <= 4:
            for d in red:
                print(f"         drop {d}")

    # largest live files + their import counts
    big = sorted(
        ((p.stat().st_size, m, len(IMP_RE.findall(p.read_text(encoding='utf-8', errors='replace'))))
         for m, p in mods.items() if m.split(".")[0] in LIVE),
        reverse=True,
    )[:15]
    print("\n15 largest LIVE files (size, module, import lines):")
    for size, m, n in big:
        print(f"  {size/1048576:7.2f} MB  imports={n:3}  {m}")

    (ROOT / "scripts_w8" / "redundant.json").write_text(
        json.dumps([{"module": m, "imports": n, "redundant": red} for m, n, _, red in per_file], indent=1)
    )


if __name__ == "__main__":
    main()
