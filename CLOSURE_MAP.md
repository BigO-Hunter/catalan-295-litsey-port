# CLOSURE_MAP — what the accepted statement actually needs

Static analysis of `bfa20018`: every `import` line (plain / `public` / `private` / `meta`)
in all **14,919** `.lean` modules was parsed, module names were resolved to files, and the
transitive closure was taken from the submission's entry points. No build was run (the box
has the v4.34.1 toolchain but no mathlib oleans); every number below is a graph measurement
on the committed tree.

## The entry the verifier checks

`comparator.json` → `challenge_module` `Challenge`, `solution_module` `Solution`,
theorem `CatalanIrrationalityMeasure.catalan_irrationalityMeasure_410`.
`Challenge.lean` is 17 lines and imports Mathlib only — closure = 1 internal module.
`Solution.lean:7` is the whole weight of the submission:

```
import CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll
```

## Headline: the submission ships the same proof twice, and the comparator gets the uncured copy

There are two complete copies of the μ(G) ≤ 410 proof in the tree, with **identical
namespaces**:

| | top-level tree | mirror tree |
|---|---|---|
| entry module | `CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll` | `Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll` |
| internal modules | **2,454** | **2,727** |
| bytes of `.lean` | 90.7 MB | 91.1 MB |
| imports of the other tree | none | none (self-contained) |
| theorem namespace | `CatalanMeasure.GenD.Signed` | `CatalanMeasure.GenD.Signed` (identical) |
| state of the `decide +kernel` monoliths | **pre-cure (one-shot)** | **cured (sharded)** |
| who builds it | `lake comparator` via `Solution` (job 2) | `lake build Submission`, lib glob (job 1) |

Union actually built per verification: **5,181 modules, 181.9 MB of source.**

The cure work (commits `90db8505`, `39d9d20f`, `bfa20018`) landed **only in `Submission/`**.
The top-level tree that `Solution.lean` imports still holds the measured 13.75 GB monoliths:

| module (top-level = what the comparator builds) | lines | `decide` sites |
|---|---|---|
| `GenD/Signed/Data/Consts/EvalRefE1.lean` | 30 | 2 one-shot |
| `…/EvalRefE0 · EvalRefE2` | 30 each | 2 one-shot each |
| `…/EvalRefX01 · EvalRefX12` | 26 each | 1 one-shot each |

| same module in the mirror (= cured) | lines | `decide` sites |
|---|---|---|
| `EvalRefE1` | 233 | 31 small |
| `EvalRefE0` | 172 | 18 |
| `EvalRefX01` | 190 | 24 |

**Consequence:** no amount of sharding in `Submission/` changes the peak of the job that
actually judges the statement, because `Solution` never touches that tree. Job 2 ("verify",
OOM in 5 m 06 s) is consistent with hitting a single one-shot kernel reduction early.

**The one-line fix:** point `Solution.lean` at the mirror —

```
import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll
```

The theorem name in the file body needs **no change** (same namespace), and the top-level
2,454-module closure then drops out of the build entirely: −47 % of the package's modules and
the comparator is judged against cured proofs. `Challenge.lean` is untouched, so the statement
surface stays exactly as accepted.

### Equivalence evidence for the swap (source-level, not build-verified)

* 2,372 of 2,726 mirror files are **byte-identical** to their top-level counterpart once the
  `Submission.` import prefix is removed; 63 are parent shims over split part files; 18 differ
  in proof body only — e.g. `GenD/Cert/Assembly.lean` differs by one term
  (`decide_eq_true_eq.mpr (of_decide_eq_true hPb)` vs `of_decide_eq_true hPb`, equivalent), and
  `GenD/Signed/SheetNear.lean` drops a `set_option maxHeartbeats 1600000 in`. Statements are
  unchanged in every diff inspected.
* The mirror closure covers **every** module of the top-level closure: the only top-level name
  missing from the mirror is `Solution` itself; the mirror adds 273 modules.
* `sorry` = 0, `native_decide` = 0, `axiom` = 0 in **both** trees (`CatalanCore/Frame/Spec.lean`
  is the repo's single `native_decide` file and is not in the 410 closure).
* Not verified: a build of `Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll`
  against `Challenge` (needs ~8.8 k mathlib modules; out of scope on this host). The coordinator
  should treat the swap as proven-by-inspection and confirm with one `lake comparator` run.

## Minimal closure of the accepted statement (top-level path)

**2,454 internal modules** (full list: `CLOSURE_MODULES.txt`):

| tree | modules |
|---|---|
| `CatalanMeasure/` | 2,055 |
| `OAI/` | 386 |
| `PrimeNumberTheoremAnd/` | 10 |
| `CatalanCore/` | 2 |
| `Solution.lean` | 1 |

External: **258** distinct Mathlib/Lean imports, whose closure is **8,783 mathlib modules**
(measured against the pinned mathlib `d13f23b7`, which is cache-prebuilt by
`lake exe cache get`).

The 386 `OAI/` modules are a useful cross-check: `formalization.yaml` states "479 files
vendored, of which the proof imports 386" — the graph reproduces 386 exactly, and the 93
unused ones are the comparison-constant certificates it says are not imported.

## Outside the closure — 12,465 modules / 458.9 MB

Droppable candidates, with the cost each removal actually buys:

| subtree | modules | on disk | imported by anything? | removal buys |
|---|---|---|---|---|
| `archive/` | 8,339 | 380 MB (9,633 tracked files) | **no** — no live module imports `CatalanArchive`; only `lakefile-upstream.toml` names it | −380 MB checkout, −9,633 files; **0** build jobs |
| `Submission/` | 2,727 | 97 MB | itself only | **nothing while `Solution` points at the top-level tree** — and it is the cure, so keep it |
| `CatalanCore/` (trigamma, 1,192 of 1,194) | 1,192 | 13.0 MB | not by the 410 proof; belongs to `SolutionHybrid` | 0 build jobs; −1,192 files |
| `OAI/` unused certificates | 93 | ~1 MB | no | 0 build jobs |
| `CatalanFrames/`, `CatalanLambda/` | 93 | 0.6 MB | hybrid/trigamma only | 0 build jobs |
| `scripts/` (Lean) | 12 | 0.1 MB | no | 0 build jobs |
| `CatalanMeasure/` dead files | 6 | — | no | 0 build jobs |

The six unreferenced `CatalanMeasure` modules are `CatalanMeasure.lean` (the upstream
aggregator), `GenD.Signed.Data.Cells.Q0.SmP007`, `GenD.Signed.Data.Consts.Audit`,
`GenD.Signed.Data.Consts.EvalNormT`, `GenD.Signed.LemmaTFree`, `GenD.Signed.SpikePoisson`.

Deleting `archive/` and the trigamma trees is **file-count** relief (relevant to the
derivation report's "Not computed: too many files"), not memory relief: Lake builds only
`lean_lib Submission`, and the top-level trees are built **only** because `Solution` imports
them. The build-cost lever is therefore exactly one: repoint `Solution`.

## Cost model, ranked

| lever | modules removed | MB removed | peak-RSS effect |
|---|---|---|---|
| 1. repoint `Solution` at the mirror, delete the top-level tree | **2,454** | **90.7** | removes the 13.75 GB one-shot reductions from the judged path |
| 2. delete `archive/` | 0 | 380 (checkout) | none directly (fewer files, smaller clone and checkout) |
| 3. delete trigamma/hybrid/frames trees | 0 | ~14 | none |
| 4. shard remaining one-shot `decide +kernel` (siblings' lane) | 0 | 0 | the actual peak driver |

## Where the sharding work actually stands

Files with `decide` occurrences ≤ 3 but a large literal (the signature of an *unsharded*
one-shot kernel reduction), live trees only:

| file | size | `decide` | tree |
|---|---|---|---|
| `GenD/D58/Cert590/XTab.lean` | 1,027 KB | 3 | top-level (pre-cure) |
| `GenD/D58/Cert590/YTab.lean` | 791 KB | 3 | top-level (pre-cure) |
| `GenD/D58/Cert590/RTab.lean` | 768 KB | 3 | top-level (pre-cure) |
| `…Signed/Data/Trial/T1Fields/P3.lean` (and `T2Fields`) | 113 KB | 2 | mirror |
| `…T1Fields/P1,P2` (and `T2Fields`) | 102 KB | 1 | mirror |

Only **nine** such files exist, and the three large ones are precisely the three the mirror
has *already sharded* (`XTab` → `P1..P12`, `YTab`/`RTab` → `P1..P9`). The largest unsharded
`decide` module left in the verifier-facing mirror is **113 KB**. So the chunking campaign is
effectively finished on the tree the build uses, while every giant the campaign was pointed at
(and the three above it has already replaced) still sits unsharded in the tree the comparator
uses.

## Open question feeding the budget draft

The receipt's work counter reads `[4255/5858]`; the package's own modules total 5,181 for
one verification (2,454 + 2,727), and mathlib's 8,783 are cache-prebuilt. So **679 of the
5,858 are unaccounted for** by this graph. Either the verifier counts modules in a way this
analysis does not model (root/aggregator files, both hybrid solutions, a partial mathlib
rebuild), or it builds something outside `Submission` + `Solution`. Worth one question to
the maintainer, because it is the denominator of every "how close did we get" claim.
