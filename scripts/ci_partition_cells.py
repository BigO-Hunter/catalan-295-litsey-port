#!/usr/bin/env python3
"""Partition the submission's Lean modules for a sharded CI build.

WHY THIS EXISTS. The first sharded workflow built every non-cell module in one
job and the generated cells in eight round-robin shards. Measured from the
cancelled six-hour run (job 139286340691) and an import census of the tree:

  * 20 non-cell modules reach the cells through their imports, so the "small"
    job elaborated the cells itself and was cut off sixteen jobs short;
  * 1187 of 1189 cells import other cells (3460 edges, longest chain 22), so
    round-robin shards rebuilt each cell 2.80 times over.

Three stages follow from that: BASE (non-cell modules with no cell in their
import closure), CELLS (sharded), TOP (the non-cell modules that import cells).

HOW CELLS ARE SHARDED. Cells are visited in a deterministic topological order.
Each joins the shard that already holds the most of its imported cells, unless
that shard is overloaded beyond its fair share by more than the cost of
rebuilding those imports: work is duplicated only when duplicating it is
cheaper than the imbalance it avoids. Costs come from measured build times in a
previous run (scripts/ci_cell_costs.json); an unmeasured cell takes the median.

  ci_partition_cells.py base                     one module name per line
  ci_partition_cells.py top                      one module name per line
  ci_partition_cells.py cells --shard K --shards N
  ci_partition_cells.py report --shards N       balance and duplication, by cost

Runs anywhere the repository is checked out; needs only the standard library.
"""
from __future__ import annotations

import argparse
import json
import re
import statistics
import sys
from collections import Counter, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CELL_DIR = "Submission/CatalanMeasure/GenD/Signed/Data/Cells/"
# `public import` is how these files spell it; a bare `import` regex sees none.
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+(\S+)", re.M)
COSTS = ROOT / "scripts" / "ci_cell_costs.json"


def load_graph() -> tuple[dict[str, str], dict[str, list[str]]]:
    files = sorted(ROOT.glob("Submission/**/*.lean"))
    where = {".".join(p.relative_to(ROOT).with_suffix("").parts): p.relative_to(ROOT).as_posix() for p in files}
    imports = {}
    for name, rel in where.items():
        text = (ROOT / rel).read_text(errors="replace")
        imports[name] = [m for m in IMPORT.findall(text) if m in where]
    return where, imports


def split(where: dict[str, str], imports: dict[str, list[str]]) -> tuple[list[str], set[str], list[str]]:
    cells = {m for m, rel in where.items() if rel.startswith(CELL_DIR)}
    non_cells = sorted(set(where) - cells)

    def reaches_cell(start: str) -> bool:
        seen: set[str] = set()
        queue = deque(imports[start])
        while queue:
            m = queue.popleft()
            if m in cells:
                return True
            if m not in seen:
                seen.add(m)
                queue.extend(imports[m])
        return False

    top = [m for m in non_cells if reaches_cell(m)]
    base = [m for m in non_cells if m not in set(top)]
    return base, cells, top


def topo(cells: set[str], imports: dict[str, list[str]]) -> list[str]:
    cell_deps = {c: [i for i in imports[c] if i in cells] for c in cells}
    indegree = {c: len(cell_deps[c]) for c in cells}
    dependents: dict[str, list[str]] = {c: [] for c in cells}
    for c, deps in cell_deps.items():
        for d in deps:
            dependents[d].append(c)
    ready = sorted(c for c in cells if indegree[c] == 0)
    out: list[str] = []
    while ready:
        ready.sort()  # deterministic: name order among the ready cells
        c = ready.pop(0)
        out.append(c)
        for n in dependents[c]:
            indegree[n] -= 1
            if indegree[n] == 0:
                ready.append(n)
    if len(out) != len(cells):  # a cycle would strand cells; refuse rather than drop them
        raise SystemExit(f"REFUSED: import graph among cells is not acyclic ({len(cells) - len(out)} cells stranded)")
    return out


def costs_for(modules: list[str]) -> tuple[dict[str, float], float]:
    measured = json.loads(COSTS.read_text()) if COSTS.exists() else {}
    known = [measured[m] for m in modules if m in measured]
    default = statistics.median(known) if known else 1.0
    return {m: float(measured.get(m, default)) for m in modules}, default


def partition(cells: set[str], imports: dict[str, list[str]], shards: int) -> tuple[dict[str, int], list[list[str]], dict[str, float]]:
    order = topo(cells, imports)
    cost, _default = costs_for(order)
    total = sum(cost.values())
    fair = total / shards
    assign: dict[str, int] = {}
    load = [0.0] * shards
    lists: list[list[str]] = [[] for _ in range(shards)]
    for c in order:
        held = Counter()
        for dep in imports[c]:
            if dep in assign:
                held[assign[dep]] += cost[dep]
        # Affinity wins unless the holder is overloaded beyond its final fair
        # share by more than the cost of rebuilding what it holds for this cell.
        # Judging overload against the running mean instead was measured and
        # is worse on both counts: at 16 shards duplication rose from 1.35 to
        # 2.29 and the heaviest shard from 2.9 h to 4.3 h. Keep the final share.
        best = max(
            range(shards),
            key=lambda s: (held.get(s, 0.0) - max(0.0, load[s] - fair), -load[s], -s),
        )
        assign[c] = best
        load[best] += cost[c]
        lists[best].append(c)
    return assign, lists, cost


def closure_cost(own: list[str], cells: set[str], imports: dict[str, list[str]], cost: dict[str, float]) -> float:
    seen: set[str] = set()
    stack = list(own)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(i for i in imports[x] if i in cells)
    return sum(cost[x] for x in seen)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    for name in ("base", "top"):
        sub.add_parser(name)
    p_cells = sub.add_parser("cells")
    p_cells.add_argument("--shard", type=int, required=True)
    p_cells.add_argument("--shards", type=int, required=True)
    p_rep = sub.add_parser("report")
    p_rep.add_argument("--shards", type=int, action="append", required=True)
    args = parser.parse_args()

    where, imports = load_graph()
    base, cells, top = split(where, imports)
    if args.cmd == "base":
        print("\n".join(base))
    elif args.cmd == "top":
        print("\n".join(top))
    elif args.cmd == "cells":
        if not 0 <= args.shard < args.shards:
            raise SystemExit(f"REFUSED: --shard {args.shard} outside 0..{args.shards - 1}")
        _assign, lists, _cost = partition(cells, imports, args.shards)
        print("\n".join(lists[args.shard]))
    else:
        print(json.dumps({"base": len(base), "cells": len(cells), "top": len(top), "cell_import_edges": sum(len([i for i in imports[c] if i in cells]) for c in cells)}))
        _order_cost, default = costs_for(sorted(cells))
        for n in args.shards:
            _assign, lists, cost = partition(cells, imports, n)
            built = [closure_cost(own, cells, imports, cost) for own in lists]
            own_cost = sum(cost[c] for c in cells)
            print(
                json.dumps(
                    {
                        "shards": n,
                        "cells_built_including_duplicates": round(sum(built) / max(own_cost, 1.0) * len(cells)),
                        "duplication": round(sum(built) / max(own_cost, 1.0), 2),
                        "heaviest_shard_hours": round(max(built) / 3600, 2),
                        "lightest_shard_hours": round(min(built) / 3600, 2),
                        "shard_cell_counts": [len(x) for x in lists],
                        "unmeasured_cells_take_median_s": default,
                    }
                )
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
