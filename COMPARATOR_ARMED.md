# COMPARATOR ARMED — auto-fire status + the one-command post

Written 2026-11-07 by the packaging lane. State: **armed**.

## Auto-fire status

* Watcher: `scripts_resub/comparator_watcher.sh`, running detached (own session, immune to
  harness process-group kills) as of 2026-11-07 14:02 — verify with
  `pgrep -fl comparator_watcher.sh`.
* Fires when `.lake/build/lib/lean/Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.olean`
  appears — the entry olean is terminal in the import topo order, so its existence means the
  closure `Solution.lean` needs is built and it is safe to elaborate (memory-wise: the serial
  build's remaining modules cannot collide with one single-process `lean`).
* On fire it runs `scripts_resub/run_comparator.py .w7/comparator.json` (120 s poll, 60 s settle,
  lockfile + verdict-exists guard, log at `.w7/comparator_watcher.log`). The fire path was
  proven end-to-end in a sandbox: detect → fire → verdict written → double-fire refused.
* The real comparator has **not** run yet; `.w7/comparator.json` does not exist (build at
  ~174/1540 when armed).
* Stop it if ever needed: `touch .w7/comparator_watcher.stop` (watcher exits within 120 s).

## Manual trigger (exact command, if the watcher is dead)

```bash
cd ~/bigo-campaign/catalan-resub && python3 scripts_resub/run_comparator.py .w7/comparator.json
```

Exit 0 = comparator accepted; the verdict JSON carries `comparator_exit`, `axioms_reported`,
`axioms_are_permitted`. The script REFUSES (exit 2) while the entry olean is missing.

## One command to finish the package once green

```bash
cd ~/bigo-campaign/catalan-resub && python3 scripts_resub/fill_draft.py
```

* Refuses while the entry olean is missing or `comparator.json` is not green (exit 0 + permitted
  axioms only). Fills `Commit SHA` (default: `git rev-parse HEAD`, or `--sha`), `{{BUILD_EXIT}}`
  and `{{AXIOMS}}` in the comment, writes the root `POST_DRAFT.md` byte-identical to the
  canonical `docs/RESUBMISSION_ISSUE_DRAFT.md`, and stamps `docs/FILL_RECEIPT.txt`.
* Then the coordinator posts (their call, nobody else's):

```bash
gh issue create --repo bigospeedrun/verifier \
  --title '[Lean submission] catalan: irrationality exponent of G at most 410 (resubmission of the OOM report run)' \
  --body-file ~/bigo-campaign/catalan-resub/POST_DRAFT.md
```

and immediately follows up with `POST_COMMENT.md` as the first comment
(`gh issue comment <N> --body-file POST_COMMENT.md`). The body carries nothing but the four
fields — the #173 lesson: `submissions.py` accepts exactly `### Problem / ### Repository URL /
### Commit SHA / ### Bound`, one-line values, no prose; everything human lives in the comment.

Form verification at any time: `python3 scripts_resub/fill_draft.py --check` (checks the body
against the board's exact regex, verbatim from `bigospeedrun/verifier scripts/submissions.py`).

## Coordinator notes (read before posting)

1. **Repository URL**: the canonical repo is `BigO-Hunter/catalan-irrationality-measure-410`.
   The local `origin` remote still names the dead `darkhipo/catalan-irrational-measure-410`
   (404); `darkhipo/catalan-irrationality-measure-410` GitHub-redirects to BigO-Hunter. The
   draft uses the canonical URL so the fetch does not depend on a redirect surviving.
2. **Commit SHA**: local branch `resub/v2` (8f5f64ce) is **not on the remote yet**, and it is
   NOT an ancestor of the remote `main` (acf3d9f1, which carries peer cure commits: namespace
   shards, dead-weight deletion, heavy-module serialization). Two candidate trees exist; the
   build + comparator receipt being produced here certifies **local resub/v2**. If the
   coordinator prefers the remote-main tree, that tree needs its own build+comparator receipt
   before its SHA may be filed. Push the chosen tree, then pass the pushed tip explicitly:
   `fill_draft.py --sha <pushed tip>` — the script warns (in its output and the receipt) when
   the SHA is not found on the canonical remote.
3. The build is ~174/1540 modules with the YM0xx giant-class tail deferred; the watcher will sit
   for hours. Nothing else in this package needs the build.
