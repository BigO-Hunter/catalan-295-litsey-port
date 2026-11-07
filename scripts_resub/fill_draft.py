#!/usr/bin/env python3
"""Fill the resubmission issue draft + comment — one command before `gh issue create`.

Refuses to fill unless the tree is actually green: the entry olean exists AND
comparator.json reports exit 0 with only permitted axioms. Embeds the board's
exact body regex (bigospeedrun/verifier scripts/submissions.py, parse_body) so
the four-field form is verified mechanically, not by eye — the #173 lesson.

Usage:
  fill_draft.py [--check]            # verify current form only, fill nothing
  fill_draft.py [--sha SHA] [--build-exit N] [--dry-run]

Outputs: POST_DRAFT.md (root, byte-copy of the filled canonical
docs/RESUBMISSION_ISSUE_DRAFT.md), POST_COMMENT.md (placeholders replaced),
docs/FILL_RECEIPT.txt (audit trail). Never posts anything.
"""
from __future__ import annotations

import argparse
import datetime
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DRAFT = ROOT / "docs/RESUBMISSION_ISSUE_DRAFT.md"
POST = ROOT / "POST_DRAFT.md"
COMMENT = ROOT / "POST_COMMENT.md"
RECEIPT = ROOT / "docs/FILL_RECEIPT.txt"
COMPARATOR = ROOT / ".w7/comparator.json"
OLEAN = ROOT / ".lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean"
CANONICAL_REPO = "BigO-Hunter/catalan-irrationality-measure-410"

# Verbatim from bigospeedrun/verifier scripts/submissions.py parse_body (trailing-\n allowance kept).
BODY_RE = re.compile(
    r"\A### Problem\n\n([^\n]+)\n\n### Repository URL\n\n([^\n]+)\n\n"
    r"### Commit SHA\n\n([^\n]+)\n\n### Bound\n\n([^\n]+)\n*\Z"
)
SHA_RE = re.compile(r"\A[0-9a-f]{40}\Z")
REPO_URL = f"https://github.com/{CANONICAL_REPO}"
BOUND = "410"


def body_with(sha: str) -> str:
    return (
        f"### Problem\n\ncatalan\n\n### Repository URL\n\n{REPO_URL}\n\n"
        f"### Commit SHA\n\n{sha}\n\n### Bound\n\n{BOUND}\n"
    )


def resolve_sha(override: str | None) -> str:
    if override:
        return override.strip().lower()
    out = subprocess.run(
        ["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        sys.exit(f"REFUSED: cannot resolve HEAD SHA: {out.stderr.strip()}")
    return out.stdout.strip()


def sha_on_remote(sha: str) -> bool:
    out = subprocess.run(
        ["gh", "api", f"repos/{CANONICAL_REPO}/commits/{sha}", "--jq", ".sha"],
        capture_output=True, text=True,
    )
    return out.returncode == 0 and out.stdout.strip().startswith(sha)


def comparator_state() -> tuple[int, str, bool]:
    if not COMPARATOR.exists():
        return 1, "comparator has not run yet (.w7/comparator.json missing)", False
    import json
    v = json.loads(COMPARATOR.read_text())
    axioms = "; ".join(v.get("axioms_reported", [])) or "(none printed)"
    ok = v.get("comparator_exit") == 0 and v.get("axioms_are_permitted") is True
    return int(v.get("comparator_exit", 1)), axioms, ok


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="verify form only; fill nothing")
    ap.add_argument("--sha", default=None, help="commit SHA (default: git rev-parse HEAD)")
    ap.add_argument("--build-exit", type=int, default=None, help="override BUILD_EXIT (default: from comparator)")
    ap.add_argument("--dry-run", action="store_true", help="fill nothing, print what would happen")
    args = ap.parse_args()

    comp_exit, axioms, comp_ok = comparator_state()
    build_exit = args.build_exit if args.build_exit is not None else comp_exit
    if args.check:
        body = DRAFT.read_text()
        m = BODY_RE.match(body)
        if not m:
            sys.exit("FORM INVALID: body does not match the board's exact four-field pattern")
        problem, repo, sha, bound = m.groups()
        print(f"FORM OK: 4 fields — problem={problem} bound={bound} sha={sha or '(empty)'}")
        print(f"build_exit={build_exit} comparator_exit={comp_exit} axioms={axioms} green={comp_ok and OLEAN.exists()}")
        return 0
    if not OLEAN.exists():
        sys.exit(f"REFUSED: {OLEAN.relative_to(ROOT)} missing — build not complete, nothing may be filled")
    if not comp_ok:
        sys.exit(f"REFUSED: comparator not green (exit {comp_exit}, axioms {axioms!r}) — the post waits")

    sha = resolve_sha(args.sha)
    if not SHA_RE.match(sha):
        sys.exit(f"REFUSED: {sha!r} is not a 40-char lowercase commit SHA")
    pushed = sha_on_remote(sha)
    new_body = body_with(sha)
    if not BODY_RE.match(new_body):
        sys.exit("REFUSED: filled body failed the board regex — file nothing")
    new_comment = COMMENT.read_text().replace("{{BUILD_EXIT}}", str(build_exit)).replace("{{AXIOMS}}", axioms)
    if "{{" in new_comment:
        sys.exit("REFUSED: a placeholder survived the fill — inspect POST_COMMENT.md")

    if args.dry_run:
        print(f"DRY RUN: would fill sha={sha} build_exit={build_exit} (pushed={pushed})")
        return 0
    DRAFT.write_text(new_body)
    POST.write_text(new_body)
    COMMENT.write_text(new_comment)
    RECEIPT.write_text(
        f"filled {datetime.datetime.now(datetime.timezone.utc).isoformat()}\n"
        f"sha={sha} pushed={pushed}\nbuild_exit={build_exit} comparator_exit={comp_exit}\n"
        f"axioms={axioms}\nfiles: docs/RESUBMISSION_ISSUE_DRAFT.md POST_DRAFT.md POST_COMMENT.md\n"
    )
    print(f"FILLED: sha={sha} build_exit={build_exit} (pushed={pushed})")
    print(f"POST IT: gh issue create --repo bigospeedrun/verifier --title "
          f"'[Lean submission] catalan: irrationality exponent of G at most 410 "
          f"(resubmission of the OOM report run)' --body-file POST_DRAFT.md")
    if not pushed:
        print("WARNING: sha is NOT on the canonical remote yet — push resub/v2 BEFORE posting")
    return 0


if __name__ == "__main__":
    sys.exit(main())
