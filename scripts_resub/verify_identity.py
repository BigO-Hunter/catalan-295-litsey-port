#!/usr/bin/env python3
"""Produce the equivalence receipts for the repoint, from git objects.

The claim being proved: the file `Solution.lean` now imports is the byte-identical
theorem that the previous submission judged, modulo the `Submission.` module prefix
that item 4 of NOTICE introduced. Nothing here is a diff heuristic: the comparison
is `bytes == bytes` after removing the prefix, and the judged statement is compared
as exact source lines. If any of this fails, exit 1.

BASE is the commit the previous submission was made from (bfa20018).
"""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

BASE = "bfa20018"
ROOT = Path(__file__).resolve().parent.parent

PAIRS = [
    "CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean",
    "CatalanMeasure/GenD/Signed/Theorem410.lean",
]


def sh(*args: str) -> str:
    return subprocess.run(args, cwd=ROOT, capture_output=True, text=True, check=True).stdout


def blob(rev: str, path: str) -> bytes | None:
    p = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True)
    return p.stdout if p.returncode == 0 else None


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def main() -> int:
    ok = True

    print("## 1. Solution.lean")
    before = blob(BASE, "Solution.lean")
    after = (ROOT / "Solution.lean").read_bytes()
    assert before is not None
    print(f"before {BASE}: sha256 {sha(before)}")
    print(f"after  shipped: sha256 {sha(after)}")
    b_lines = before.decode().splitlines()
    a_lines = after.decode().splitlines()
    diff = [(i, x, y) for i, (x, y) in enumerate(zip(b_lines, a_lines), 1) if x != y]
    print(f"differing lines: {len(diff)} (file length {len(b_lines)} -> {len(a_lines)})")
    for i, x, y in diff:
        print(f"  line {i}:")
        print(f"    -{x}")
        print(f"    +{y}")
    if len(diff) != 1 or len(b_lines) != len(a_lines):
        print("FAIL: more than the single import line changed")
        ok = False

    print("\n## 2. Entry module: byte equality modulo the `Submission.` prefix")
    print("(compared as committed blobs, i.e. what a fresh clone checks out; the local")
    print(" worktree here is CRLF because this checkout has core.autocrlf, git blobs are LF)")
    for path in PAIRS:
        top = blob(BASE, path)
        mirror_rel = "Submission/" + path
        mirror = blob("HEAD", mirror_rel)
        if top is None:
            print(f"{path}: ABSENT at {BASE}")
            ok = False
            continue
        if mirror is None:
            print(f"{mirror_rel}: MISSING at HEAD")
            ok = False
            continue
        norm = re.sub(rb"\bSubmission\.", b"", mirror)
        same = norm == top
        print(f"{path}")
        print(f"  top-level @{BASE}: {len(top)} B sha256 {sha(top)}")
        print(f"  {mirror_rel} @HEAD: {len(mirror)} B sha256 {sha(mirror)}")
        print(f"  prefix-stripped == top-level: {same}")
        if not same:
            import difflib
            d = list(difflib.unified_diff(
                top.decode().splitlines(), norm.decode().splitlines(), lineterm="", n=0))
            print(f"  differing lines: {len([x for x in d if x[:1] in '+-' and not x.startswith(('+++', '---'))])}")
            for line in d[:12]:
                print(f"    {line}")
        ok = ok and same

    print("\n## 3. Judged statement, both trees (exact lines)")
    stmt_re = re.compile(r"^theorem catalan_irrationalityMeasure_410")
    for path in PAIRS[:1]:
        for label, text in (
            (f"top-level @{BASE}", blob(BASE, path)),
            ("shipped Submission/", blob("HEAD", "Submission/" + path)),
        ):
            lines = text.decode().splitlines()
            for idx, line in enumerate(lines):
                if stmt_re.match(line):
                    print(f"{label}  line {idx + 1}:")
                    for k in range(idx, min(idx + 5, len(lines))):
                        print(f"    {lines[k]}")
                    break

    print("\n## 4. Module accounting")
    n_all = sum(1 for x in sh("git", "ls-tree", "-r", "--name-only", BASE).splitlines() if x.endswith(".lean"))
    n_head = sum(1 for x in sh("git", "ls-files").splitlines() if x.endswith(".lean"))
    print(f"modules at {BASE}: {n_all}")
    print(f"modules shipped now: {n_head}")

    print("\n## 5. The pre-cure monolith is gone from the shipped tree")
    for p in (ROOT / "CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1.lean",
              ROOT / "OAI", ROOT / "archive"):
        print(f"  {p.relative_to(ROOT)}: {'PRESENT' if p.exists() else 'absent'}")
        if p.exists():
            ok = False
    old = blob(BASE, "CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1.lean")
    new = (ROOT / "Submission/CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1.lean").read_bytes()
    print(f"  EvalRefE1 @{BASE} (what the verifier built): "
          f"{len(old.splitlines())} lines, {old.count(b'decide')} decide sites")
    print(f"  EvalRefE1 shipped (cured): "
          f"{len(new.splitlines())} lines, {new.count(b'decide')} decide sites")

    print(f"\nRESULT: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
