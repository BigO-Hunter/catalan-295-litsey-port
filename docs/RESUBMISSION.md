# RESUBMISSION — catalan-irrationality-measure-410, fix for verifier OOM (#163)

Base: `bfa20018` (the commit the OOM'd submission was made from).
Branch: `resub/v2`. One commit on top of the base.

The statement does not change. The judged theorem is the same declaration at the
same coordinates with the same source lines, and the file that now proves it is a
byte-identical copy of the file the previous submission proved it from (modulo the
`Submission.` module prefix that the submission layout already imposed). What
changes is *which copy of the proof the comparator elaborates*: the verifier built
the pre-cure copy, whose `decide +kernel` monoliths peak at 13.75 GB in a single
module against a 14 GiB cgroup cap.

## 1. What changed

| # | change | why |
|---|---|---|
| 1 | `Solution.lean:7`: `import CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll` → `import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll` | The judged module was the *pre-cure* copy. The cured copy (sharded `decide`, no one-shot kernel reduction) has shipped under `Submission/` since the layout conversion (NOTICE item 4) but nothing imported it. One line. |
| 2 | deleted the pre-move copies: `CatalanMeasure/` (2,062 files), `OAI/` (479), `archive/` (9,632) | R2. The verifier's job counter (5,858) exceeded the module union (5,181) by 677, so "the judged path" is not the only thing its plan can reach. Any glob, aggregator, or stale root file that resolves a top-level module reinstates the 13.75 GB module and OOMs again. The pre-cure copies must not exist. |
| 3 | `NOTICE`, `formalization.yaml`: vendored-path references updated; NOTICE item 5 records the deletion | Same files, same attributions, moved path. No licence or provenance content changed. |

Deleted trees, measured (`git diff --cached --name-status`):

| tree | files deleted | why it is safe |
|---|---|---|
| `CatalanMeasure/` | 2,062 | The whole pre-cure 410 closure. After change 1 the judged import graph reaches 0 modules outside `Submission/` (`scripts_resub/import_graph.py`). One file is kept: `CatalanMeasure/CellCert/RawInts.lean`, because the trigamma trees (`CatalanCore/`, behind `SolutionHybrid.lean`) import it. |
| `OAI/` | 479 | Imported only by the deleted top-level tree. The vendored copies ship at `Submission/OAI/`. |
| `archive/` | 9,632 | No live module imports it (`CatalanArchive` appears only in `lakefile-upstream.toml`, which `lake` does not read). |

Kept deliberately: `Submission/` (the cured proof, 2,727 modules), `CatalanCore/`,
`CatalanFrames/`, `CatalanLambda/`, `PrimeNumberTheoremAnd/` (the trigamma/hybrid
trees behind `SolutionHybrid.lean`; 1,297 files, **0 build jobs** for the 410
target, so deleting them buys nothing but file count — and keeping them keeps the
hybrid challenge buildable), `Challenge.lean`, `Submission.lean`,
`comparator-hybrid.json`, the papers, and `scripts/`.

Module count: **14,919 → 4,041** `.lean` files (−10,878).

## 2. Why the OOM happened (the mechanism, stated exactly)

The submission shipped the same proof twice with identical namespaces:

| | pre-cure copy | cured copy |
|---|---|---|
| entry module | `CatalanMeasure.…CellsAll` | `Submission.CatalanMeasure.…CellsAll` |
| internal modules | 2,454 | 2,727 |
| held by | `Solution.lean:7` — i.e. the module the comparator elaborates | the `Submission` library glob |
| state of `Data/Consts/EvalRefE1` | 30 lines, **2 one-shot `decide +kernel`**, measured **13,750 MB** | 233 lines, 31 sharded `decide` |

The cure commits (`90db8505`, `39d9d20f`, `bfa20018`) landed only in `Submission/`.
`Solution.lean` imported the other copy, so the paragraph above is the entire
cause: the judged file was never cured. Peak RSS is dominated by fixed import cost
plus kernel reduction shape, not by the length of the proof text (a 1.4 KB module
with no Mathlib import peaks at 0.70 GB; the mirror's 91 KB and 147 KB modules peak
at 1.74 and 1.90 GB).

## 3. Statement identity — the receipts

Reproduce with `python3 scripts_resub/verify_identity.py` (exit 0 = all pass). It
compares **committed blobs**, i.e. what a fresh clone checks out. (A local
`core.autocrlf` makes this checkout's worktree CRLF; the blobs are LF in both
trees, and Lean accepts either, so the comparison is done on blobs.)

| check | result |
|---|---|
| `Solution.lean` differing lines vs `bfa20018` | **1** (file length 26 → 26) — the import line |
| `Solution.lean` sha256 before → after | `38c71054…8baf5d` → `13266e60…fee45f8b` |
| `Submission/…/CellsAll.lean` with every `Submission.` removed == `CatalanMeasure/…/CellsAll.lean` @ `bfa20018` | **True** (11,838 B each side; `bytes == bytes`, not a diff heuristic) |
| `Submission/…/Theorem410.lean` normalized the same way | **True** |
| judged statement, both trees, line 293 | byte-identical, same proof term `catalan_irrationalityMeasure_410_of_cells Data.Assembly.cellsQ0 …Q2` |
| namespace | unchanged (`CatalanMeasure.GenD.Signed`), so `Solution.lean`'s body needs no edit |
| `Challenge.lean`, `lakefile.toml`, `lean-toolchain`, `comparator.json` | untouched |

The comparator's own equality check is not a proxy: `Solution.lean` **re-states**
the full `∀ᶠ b, ∀ a, …` formula and proves it from the imported theorem, so any
divergence in the statement is an elaboration type error, not something a reviewer
has to notice.

## 4. Measured fit

Host: M4 Max, 137 GB RAM, 16 cores, Lean v4.34.1, mathlib `d13f23b7` (cache-prebuilt
oleans, shared, never rebuilt). Verifier cap: 15,032,385,536 B = 14 GiB, no swap
(#163 receipt).

Method: `lake build Submission` run **serialized** (`LAKE_JOBS=1`,
`LEAN_NUM_THREADS=1`) against the integrated tree, with a 0.5 s sampler
(`scripts_resub/measure_peak2.py`) that sums the RSS of this build's `lean`
processes only — the host was running sibling campaign builds at the same time, so
a system-wide sum would not be a measurement of this submission.

**Before (what the verifier built) → after (this tree):**

| quantity | pre-cure copy (#163 built this) | this tree |
|---|---|---|
| modules in the package | 14,919 | **4,041** |
| modules on the judged path | 2,454 (pre-cure) + 2,727 (lib) = 5,181 | 2,454 (cured mirror, inside the lib) |
| worst single module | **13,750 MB** — `EvalRefE1`, 30 lines, 2 one-shot `decide +kernel`, 1,066 s | **2,724 MB** — `Data/Consts/TrialB1`, sampled |
| modules over 2 GB | 2 (`EvalRefE1` 13.75 GB, `SpiB007` 3.31 GB) | 3 (`TrialB1` 2.72, `TrialB2` 2.72, `TrialB0` 2.53 GB) |
| concurrent `lean` during the build | wide (`peak tasks 1299` in the receipt) | **1** (`LAKE_JOBS=1`, `LEAN_NUM_THREADS=1`) |
| peak footprint of this tree | cap hit: 15,032,385,536 B | **2,724 MB** |

Per-module peaks, sampled at 1 s from the live build (this tree, cured mirror):

| module (`Submission/…`) | peak RSS | class |
|---|---|---|
| `CatalanMeasure/GenD/Signed/Data/Consts/TrialB1.lean` | **2,724 MB** | the heaviest measured |
| `CatalanMeasure/GenD/Signed/Data/Consts/TrialB2.lean` | 2,723 MB | |
| `CatalanMeasure/GenD/Signed/Data/Consts/TrialB0.lean` | 2,534 MB | |
| `CatalanMeasure/GenD/Signed/EnergyNear.lean` | 2,337 MB | |
| `CatalanMeasure/GenD/Signed/FieldForm.lean` | 2,040 MB | |
| `CatalanMeasure/GenD/Signed/Data/Consts/SpikeS1/P1.lean` | 1,873 MB | |
| `OAI/…/FirstBarrier/BarrierCaseOneDescartesX0.lean` | 1,568 MB | the 386-module vendored OAI block tops out here |

Cross-checks from the sibling lane, measured with `/usr/bin/time -l` (exact, not
sampled) on the same commit and the same repoint:
`GenD/Signed/ReflectionEnergy.lean` **1,897 MB**, `GenD/Signed/ArcsineDenominator.lean`
**1,741 MB**, `Parametric/CoupledFirstEnergy.lean` ≥1,309 MB. The floor for any module
in this tree is ~700 MB (Lean runtime + olean load, measured on a 1.4 KB module with no
Mathlib import), so the peak *above floor* is ~1.6 GB for the heaviest module.

Headroom against the 14 GiB cap: 14,336 MiB / 2,724 MiB = **5.3× on the worst module
measured**, and — the number that actually matters — the build never exceeded **one**
concurrent `lean`, so the per-cgroup sum never went above ~2.7 GB. The counts and
peaks above grow as the build proceeds; `docs/RESUBMISSION_BUILD_STATUS.md` is the
live record and supersedes this table.

**Axioms.** The build prints `#print axioms` for each audited theorem as it goes; all
121 printed lines are `[propext, Classical.choice, Quot.sound]` (one is wrapped over two
lines, which is why a naive grep counts 120). No `sorry`, no `native_decide` on the
judged path.

## 5. Residual risks (named, not waved away)

**R1 — the cap is per-cgroup, so what must fit is the SUM of concurrent `lean`
processes, not any one module.** Every module measured fits with >6× headroom at
~2.1 GB worst case, but 7 concurrent heavy modules would reach 14 GiB, and the #163
receipt shows `peak tasks 1299` — a wide build. This resubmission cannot fix the
verifier's `-j`. See the draft issue: asking for `-j2` (or the equivalent) on the
Catalan target is the other half of the fix.

**R2 — the pre-cure copy must stay deleted.** Fixed here by deletion rather than by
bypass, so no build command can reach it. If a future commit restores
`CatalanMeasure/GenD/…` the OOM returns with it.

**R3 — the mirror drops `set_option maxHeartbeats 1600000 in` that the pre-cure
`GenD/Signed/SheetNear.lean` carries.** The package's `lakefile.toml` sets
`maxHeartbeats 0` globally, so it is inert here; it would bite only a harness that
re-imposes a heartbeat cap, which the verifier does not.

## 6. How to re-check this claim from scratch

```bash
python3 scripts_resub/verify_identity.py     # statement identity, exit 0 = pass
python3 scripts_resub/check_integrity.py     # no dangling internal import
python3 scripts_resub/import_graph.py        # judged closure stays inside Submission/
```

`scripts_resub/check_integrity.py` reports 6 dangling imports in `scripts/claude/`;
all 6 are pre-existing at `bfa20018` (their targets were never in the tree) and none
is reachable from `Solution`, `Challenge`, `Submission` or `Submission.lean`.

## 7. Build status and the resume recipe

The full `lake build Submission` on this tree is **resumable, not a single
invocation**. The machine this was prepared on runs sibling build campaigns, and the
body's own `lean_build_governor` freezes/SIGTERMs `lean` processes when the
HOST-WIDE lean footprint crosses its aggregate ceiling (observed during this work:
`lean procs=15 tree=35157 MB` against a 24,576 MB ceiling). A single long build is
therefore not safe there: the first attempt here was SIGTERM'd at 221 s with **zero
`error:` lines** in the log — a host-level kill, not a Lean failure. That is why the
driver is a retry loop, and why a negative exit must never be read as a verdict.

```bash
# shared, cache-prebuilt mathlib (never rebuild it: 8,548 oleans)
mkdir -p .lake && ln -sfn ~/bigo-campaign/staircase-port/.lake/packages .lake/packages

# serialized and resumable; each attempt appends to the log, final line is BUILD_EXIT=<code>
BUILD_ROOT=$PWD python3 scripts_resub/build_supervised.py /tmp/cat_build.log .w7/attempts.tsv 40
grep BUILD_EXIT /tmp/cat_build.log        # only exit 0 is green; 143/negative = unfinished

# then the comparator: the wrapper theorem + its axiom set.
# run_comparator.py refuses while the entry olean is missing, so it cannot
# report a verdict on an unfinished build.
python3 scripts_resub/run_comparator.py .w7/comparator.json   # prints COMPARATOR_EXIT=<code>
```
The comparator is `lake env lean Solution.lean`: it type-checks the wrapper theorem
(the full statement re-stated, proved from the imported one) and prints its axioms.
A drifted statement cannot elaborate; a non-permitted axiom would show in the printed
set. It needs the whole judged closure built, which is why it runs second.

Status of the run recorded with this commit: see `docs/RESUBMISSION_BUILD_STATUS.md`
(attempt log, exit codes, module count). The rule for reading it: a build that has
not printed `BUILD_EXIT=0` is **not** a passing build, whatever the module count says.
