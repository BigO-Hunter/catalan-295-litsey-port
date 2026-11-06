# IMPORT_TRIM — per-file "can drop" lists, and why this is not the OOM lever

## Two premises in the brief are wrong; correcting them first

**1. The eight giant files are in `archive/`, which nothing imports.**
The sizes in the brief (XTab 12.7 MB, StreamRank/L0002_left 10.4 MB, SourceRank/L0002_left
8.5 MB, YTab 8.4 MB, RTab 8.3 MB, FullData 4.0 MB, Data027 2.8 MB, PilotPotential 2.5 MB,
MGNDefs) all resolve to `archive/CatalanArchive/…`, not to the live tree:

```
12659760 ./archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean
10426763 ./archive/CatalanArchive/CatalanMeasure/GenD/Uniform/Bank/StreamRank/L0002_left.lean
 8475706 ./archive/CatalanArchive/CatalanMeasure/GenD/Uniform/Bank/SourceRank/L0002_left.lean
```

`archive/` is 8,339 `.lean` files / 380 MB / 9,633 tracked files, and **no** module in
`Submission/`, `CatalanMeasure/`, `OAI/`, `CatalanCore/` or `PrimeNumberTheoremAnd/` imports
anything under `CatalanArchive`; the only reference in the repo is `lakefile-upstream.toml`.
The largest **live** file is 1.00 MB (`CatalanMeasure/GenD/D58/Cert590/XTab.lean`) and the
largest **live** files in the mirror are the split parts (~96 KB each). Chunking the archive
giants cannot move any verifier number.

**2. Excess imports do not inflate a Lean module's resident environment.**
In Lean, a module's environment already contains the transitive closure of what it imports.
Dropping a *redundant direct* import therefore changes nothing about what is loaded or how
much memory elaboration needs — the same modules and the same `.olean`s arrive through the
other import. The only import edit that removes build work is dropping an import of a module
that is **not otherwise reachable** — and at that point the lever is deleting the *file*, not
the import line (see `CLOSURE_MAP.md`, lever 1).

What import trimming does buy: a smaller, more honest dependency graph (rebuild granularity,
`lake`'s job plan, the derivation report's file count). It is hygiene, not RSS.

## Measured redundancy (live trees only: Submission, CatalanMeasure, OAI, CatalanCore, PrimeNumberTheoremAnd)

* Internal import lines: **14,163**
* Transitively redundant (safe to drop): **2,450 (17.3 %)** across **1,436** files
* 100 % of imports in these trees are `public import`, so a module reached through another
  public import is still re-exported downstream — dropping is name-resolution safe.

Full machine-readable list: `scripts_w8/can_drop.json` (`{module, imports, can_drop[]}`).

### Highest-redundancy live files (can-drop count / total internal imports)

| file | can drop | of |
|---|---|---|
| `Submission.…Data.Assembly.RowsQ1.P2` | 28 | 29 |
| `CatalanMeasure.…Data.Consts.Audit` | 27 | 37 |
| `Submission.…Data.Assembly.RowsQ2.P2` | 26 | 27 |
| `CatalanMeasure.GenD.Uniform.W.Slots.All` | 20 | 21 |
| `Submission.GenD.Uniform.W.Slots.All` | 20 | 21 |
| `CatalanMeasure.…Data.Assembly.CellsAll` | 12 | 63 |
| `Submission.…Data.Assembly.CellsAll` | 12 | 63 |
| `Submission.…D58.Cert590.XTab` | 11 | 12 |
| `Submission.…D58.Cert590.YTab` / `RTab` | 8 | 9 each |
| `CatalanMeasure.GenD.Signed.Energy` (+ mirror twin) | 5 | 11 |
| `Submission.…Signed.Data.Trial.T1Fields` / `T2Fields` | 5 | 6 each |

### The split-parent shims are redundancy by construction

Every `P`-chain parent in the mirror imports its parts in sequence, and part *n* already
imports part *n−1*, so almost every line is redundant:

```
Submission.…Cert590.XTab      imports P1..P12  -> 11 of 12 redundant
Submission.…Cert590.YTab      imports P1..P9   ->  8 of  9
Submission.…Cert590.RTab      imports P1..P9   ->  8 of  9
Submission.…Assembly.Budget   imports P1,P2    ->  1 of  2
```

Do **not** "fix" these. The flat import list is the point: each part is an independent kernel
check that a reader and the build plan can see at a glance, and the cost of nine redundant
import lines is zero milliseconds. Trimming them would only obscure the shard structure that
the peak-RSS cure depends on.

### What can be dropped from the largest live files

The live files above 300 KB are `decide`-heavy data modules with **2 imports each** — one
Mathlib module and one local predecessor. There is nothing redundant in them: e.g.
`CatalanMeasure/GenD/D58/Cert590/XTab.lean` (1.00 MB, `imports=2`),
`…/Trial/T1Fields.lean` (0.48 MB, `imports=2`), `…/Cells/Q0/SnP003.lean` (0.35 MB, `imports=2`).
Their cost is one kernel reduction over a large literal, which no import edit reaches.

## Safety rules if anyone applies the list

1. Only drop a line when the module is reachable through **another `public import` of the same
   file** (all 2,450 above were computed on public-import paths only).
2. Never drop the single import that carries a namespace the file uses — this list is
   resolution-safe, not reference-safe: an unqualified identifier can survive only because
   that module re-exports it. Compile before committing.
3. Never trim across the two trees: their namespaces are identical on purpose (see
   `CLOSURE_MAP.md`), so importing both would be a real conflict.
4. Expect **0 MB** and **0 s** of verified savings. The measured levers are: repoint
   `Solution` (−2,454 modules), delete `archive/` (−380 MB checkout), shard one-shot
   `decide +kernel` (peak RSS).
