# OOM / elaboration engineering — the catalan 410 research record

The superseded 410 port (now [`archive/410/`](../archive/410/)) could not complete a hosted build:
the verifier sandbox caps memory at 14 GiB, and single Lean modules in the certificate data
approach or exceed it. This page integrates the research; the byte-exact originals live in the
subtree and on the preserved `archive/410/*` refs ([branch map](../archive/410-BRANCHES.md)).

## Measured constraint (2026-11-05 investigation)

From [`archive/410/OOM_INVESTIGATION.md`](../archive/410/OOM_INVESTIGATION.md) (verifier #157
receipt): cgroup cap 15,032,385,536 B = 14 GiB, swap 0, tasks limit 4096; both the build and the
verify jobs were OOM-kill at exactly the cap (build died at [4255/5858], verify at [4296/5858]).

Single-module peaks measured with `/usr/bin/time -l lake env lean <file>`:

| module | wall | max RSS |
|---|---|---|
| GenD/Signed/Data/Consts/EvalRefE1 (30 lines, `decide +kernel`) | 1066 s | **13.75 GB** |
| GenD/Signed/Data/Cells/Q2/SpiB007 (344 lines) | 1328 s | 3.31 GB |
| OAI/…/FixedModularPlusProductRows40To41 (original) | 159 s | 2.01 GB |
| …/P1 (split) | 9.9 s | 1.50 GB |
| …/P2 (split) | 169 s | 1.94 GB |

**Conclusion of the investigation:** the peak is one atomic kernel decision (EvalRefE1-class,
~98% of the whole cap before co-scheduled modules or page cache). File splitting alone cannot
fix it; the 74-module split reduced some 150–300 s modules only marginally. A resubmission at a
new SHA would very likely OOM again without (a) proof engineering on the `decide +kernel`
monoliths (EvalRefE1/E2/X12/LinkSlope), or (b) a maintainer-granted larger cap / re-dispatch.

## Research lanes (preserved refs in this repo)

- `archive/410/oom-memory-split` — 71 modules split into part files + import shims (declaration
  sets verified identical), 3 orphan-docstring repairs; full `lake build Submission` green on the
  lane (BUILD_EXIT=0). Much of this work later landed on 410 main: dead-weight deletion,
  EvalRef.X01/X12 namespace shards, SheetNear sharding.
- `archive/410/chunk/W5` and `archive/410/home-cat-chunk-W*/…` — chunked-build lane snapshots
  W1–W8 (W6 on the resub lane), each a full-tree variant of the port.
- `archive/410/substrate-catalan-157-oom-wt-2466c292a4/*` and
  `archive/410/substrate-catalan-fix-f5cb097db3/*` — the OOM worktree lanes, including the
  `r2125608574-elab-async-off` elaboration-async-off full-tree snapshots.
- `archive/410/validation/unverified-0738347` — `VALIDATION.md`: the 410 head `0738347d` is
  explicitly **unverified source**. Full build and API docs never completed at that commit
  (hosted run 44836274821 lost runner communication; a bounded local attempt reached
  `Qq.Macro` [363/369] and was shed by the host memory governor, exit 143 — not a compiler
  failure). Publication is not a Lean Verified result.
- Tooling: [`archive/410/scripts_split/`](../archive/410/scripts_split/) (`split_hot.py`,
  `verify_split.py`) and [`archive/410/chain_survey.txt`](../archive/410/chain_survey.txt)
  (import-chain survey of the split modules).

## Successor work: CI sharding (411 PR #1)

[catalan-irrationality-measure-411](https://github.com/BigO-Hunter/catalan-irrationality-measure-411)
is a byte-identical twin of 410 main (`0738347d`) created to land the build fix. Its PR #1 shards
the Lean build into a cone job (the 1,554 non-cell modules, uploading oleans) plus 8 cell shards
(the 1,111 `Submission.CatalanMeasure.GenD.Signed.Data.Cells` modules = 79,029 of 85,108 measured
module CPU-seconds, 93%) to fit the 6-hour hosted cap. Evidence cited in the PR: run 44836274821 /
job 138851813665 — 5,028 of 6,147 targets in 5h57m on a 4-vCPU runner, runner saturated; prebuilt
Mathlib cache works (8,908 files fetched, zero Mathlib modules compiled).

The PR head is preserved here as `archive/411/ci-sharded-lean-build-2125613832` (`295044b`).
When PR #1 is green and merged, 411 folds into this archive and the shell retires
(consolidation E3 verdict: 411 carries no distinct bound — it is 410 + CI engineering).
