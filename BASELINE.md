# W1 — `archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean`

**Verdict: the target is archived dead cargo. It is not in the verifier's build closure, it
cannot be elaborated at all, and no amount of chunking in it can change peak RSS of the
submission build.** No edit was made. Evidence below.

## 1. Classification (top-5 memory shapes)

File: 87 lines, 12,659,761 B.

| # | shape | lines | bytes | note |
|---|---|---|---|---|
| 1 | `LV_X : List (List (ℕ × ℕ))` — ONE term | 9–79 | **12,530,007 (99.0% of file)** | 70 rows, 131,637–222,004 B each |
| 2 | `B_X : List ℤ` — one list literal | 8 | 128,778 | 499 `ℤ` elements |
| 3 | `tab_X : … = true := by decide +kernel` | 83 | 139 | one atomic kernel decision over the whole table |
| 4 | `MGL_X : ℤ` | 81 | 328 | integer literal |
| 5 | `D_X : PolyData := ⟨B_X, LV_X, 1, 1099511627776⟩` | 80 | 56 | glue, small |

Shapes 1+2 are the only elaboration-peak candidates; shape 3 is the only kernel-peak candidate.
A natural split would have been 70 per-row `def LV_X_i : List (ℕ × ℕ)` plus a 70-name list
`LV_X := [LV_X_0, …, LV_X_69]` (glue tiny), leaving `B_X` (129 KB) as the largest term — but
that split is unverifiable (see §2).

## 2. Why no baseline can be measured (and no cut can be validated)

The file's own import does not exist:

```
$ LEAN_PATH=archive/CatalanArchive lean archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean
error: object file 'archive/CatalanArchive/CatalanMeasure/G728/CellW.olean'
       of module CatalanMeasure.G728.CellW does not exist
EXIT=1
```

`CellW.lean` exists nowhere in the tree under either namespace:

```
$ find . -name CellW.lean
./CatalanMeasure/CellCert/CellW.lean
./Submission/CatalanMeasure/CellCert/CellW.lean
```

The module the archive file wants (`CatalanMeasure.G728.CellW`) was renamed to
`CatalanMeasure.CellCert.CellW` by `3d13d68a` ("Rename generic cell/energy certificate namespace
CatalanMeasure.G728 to CatalanMeasure.CellCert") — *after* the whole G728 tree had already been
frozen into `archive/` by `7a9c59cd` ("Archive the 728 wrapper … CatalanMeasure.lean imports
D58.Main", a 0-line-changed rename of `CatalanMeasure/G728/Cert/XTab.lean` →
`archive/CatalanArchive/…`). The snapshot therefore points at a module layout that no longer
exists. `baseline_peak_rss`: **unmeasurable — the file does not parse its imports.**

## 3. Not reachable from anything the verifier builds

* `lakefile.toml` — the lakefile Lake actually reads — declares exactly one library:
  `[[lean_lib]] name = "Submission"`. The archive is not under `Submission/`.
* `lakefile-upstream.toml` *does* declare the archive (`name = "Archive"`, `srcDir = "archive"`,
  `roots = ["CatalanArchive"]`), explicitly "Not a default target; build with `lake build Archive`".
  That escape hatch is also dead: its declared root module has no source file.
  `find . -name CatalanArchive.lean` → nothing (`archive/` contains only `CatalanArchive/` and
  `legacy-configs/`), so `lake build Archive` cannot even start. And this lakefile is inert for
  the submission: the shipped `lakefile.toml` is what the verifier reads.
* Zero importers outside `archive/`:
  `grep -rln "^\(public \)\?import CatalanArchive" --include=*.lean . | grep -v '^./archive/'`
  → empty. `grep -rn CatalanArchive Submission/ Submission.lean Solution.lean Challenge.lean
  SolutionHybrid.lean ChallengeHybrid.lean` → 0 hits.
* CI builds `lake build CatalanMeasure:docs` (`.github/workflows/ci.yml:113`); nothing builds
  `archive/`.
* By contrast the **live** counterpart already ships chunked:
  `Submission/CatalanMeasure/GenD/D58/Cert590/XTab.lean` is 803 B, importing `XTab.P1 … P9`.

Largest `.lean` in the built closure is 300,126 B
(`Submission/CatalanMeasure/GenD/Uniform/Bank532/Pk/L0108_right.lean`) — 42× smaller than this
archive file. The premise "biggest single term in the submission" holds only if "the submission"
means "every file in the repo"; it is false for the submission build.

## 4. What would actually be needed before this file could matter

1. Resurrect the module layout (`G728/CellW` → `CellCert/CellW`) *and* put `archive/` on the
   Lean path or into a declared lib — i.e. a deliberate decision to build the archive; or
2. Repoint the archived snapshot at the renamed modules. Both mean editing a frozen archival
   snapshot, which is a maintainer decision, not a chunking task. Editing it now would trade
   archival fidelity for a memory win of zero.

## 5. Methodological note (the useful part)

Size-based assignment picked this file because it is the largest `.lean` in the repo. File size
is not the OOM predictor for this project — `OOM_INVESTIGATION.md` records
`GenD/Signed/Data/Consts/EvalRefE1` at **13.75 GB peak from 30 lines**, i.e. a monolithic
`by decide +kernel`, while a 2.2 MB data module measured 2.01 GB. Peak is driven by one-shot
kernel decisions over large terms, not by bytes on disk. Assignment should be driven by
`decide +kernel`/`native_decide` monoliths in the *Submission* closure (1,546 files still
contain `decide +kernel` at this SHA), measured per module, not by file size.
