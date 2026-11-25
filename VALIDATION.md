# Validation status — explicitly unverified

Source under review: merge commit `0738347daeba402dc1315e1d01467301e0e1be29` (`main`, PR #3).

**This repository does not currently carry a completed build-plus-documentation validation claim for that commit.** The source is published so another researcher can inspect or validate it; publication is not a Lean Verified result.

## Evidence that exists

- `scripts/check-lean-sources.py` passes locally at the merge commit.
- The two metadata CI gates pass: `Check metadata and Apache licence default` and `Check where the README sends a submitter`.
- `Check statement against solution` fails because the pinned Lean v4.34.1 toolchain does not bundle the comparator's required `leanexport`. That comparator is intentionally `continue-on-error` at this board pin and is not a required status check. Do not bump judged content merely to silence it.

## Outstanding verification

1. **Full Lean build:** `LAKE_JOBS=1 LEAN_NUM_THREADS=1 lake build Submission` has not completed successfully at the merge commit.
2. **API documentation:** `cd docbuild && lake build Submission:docs` has not completed successfully at the merge commit.
3. No independent strict numerical oracle is claimed from this package.

Until both build commands complete, treat the merged code as **unverified source**, not as an accepted proof artifact.

## Failure/autopsy record

- Main hosted run `44836274821`: the original Build with Lean job ended with runner-lost-communication during `lean-action`, while Build API documentation was cancelled. These are infrastructure outcomes, not Lean elaboration diagnostics.
- A bounded local attempt reached `Qq.Macro` at `[363/369]` and exited 143 (SIGTERM). The host's `memory_admission_reaps.jsonl` records the corresponding lake PID killed under the `free_low` pressure arm at 2026-11-21T09:19:31. This was a memory-governor shed, not a compiler failure.
- A hosted Build with Lean rerun was started on 2026-11-24 as job `138851813665`. At the time this note was written it remained **in progress**; the documentation job had not been rerun. A detached watcher will rerun docs only if that build genuinely passes.

Current run: <https://github.com/BigO-Hunter/catalan-irrationality-measure-410/actions/runs/44836274821>

## Provenance and local cleanup

The complete merge commit is already on `origin/main`. This note is published on `validation/unverified-0738347` so the temporary local checkout can be removed without losing either the source or its outstanding-verification status. Update this file or supersede it only with actual build and docs receipts.
