# W1 — receipts: `archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean`

Branch `chunk/W1` from `bfa20018e0bd470805dac30a1916beefe586daa5`.
**No tracked file was modified.** Only this document and `BASELINE.md` are added.

```
$ shasum -a 256 archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean
0cd21f70625b15156645ad7790f71b51e765320222b5ab4a17b9ec33b66ecca8  (12,659,761 B, 87 lines)

$ git status --porcelain
?? BASELINE.md
?? RECEIPTS.md
$ git diff --stat HEAD -- archive/          # empty
```

## RSS table

| | wall | max RSS |
|---|---|---|
| baseline (original file, alone) | **not measurable** | **not measurable** |
| after (chunked) | n/a — no cut made | n/a |

Why the baseline is absent rather than estimated: the module cannot be elaborated.

```
$ LEAN_PATH=archive/CatalanArchive lean archive/CatalanArchive/CatalanMeasure/G728/Cert/XTab.lean
error: object file 'archive/CatalanArchive/CatalanMeasure/G728/CellW.olean'
       of module CatalanMeasure.G728.CellW does not exist
EXIT=1
```

`CellW.lean` does not exist under `G728` at all; it was renamed to `CellCert.CellW` (`3d13d68a`)
after G728 was frozen into `archive/` (`7a9c59cd`). Building the ~6 GB mathlib closure to obtain
an RSS number for a module that is not in any built library would have produced a number about
a build nobody runs.

## Declaration-type diff verdict

**IDENTICAL — trivially, because no declaration was touched.** There is no before/after pair to
diff: zero declarations changed, so the exported surface (`B_X`, `LV_X`, `D_X`, `MGL_X`, `Np_X`,
`tab_X`, `D_X_ok`) is bit-for-bit what it was at `bfa20018`
(sha256 above; `git diff HEAD -- archive/` empty).

A *proof* of type preservation through a split was impossible here: `#print`-ing the declarations
requires elaborating the module, which fails at import resolution. So the honest status is
"unchanged", not "verified stable under refactor".

## Reachability checks (why this file cannot affect the verifier's peak)

```
$ grep -rln '^\(public \)\?import CatalanArchive' --include=*.lean . | grep -v '^./archive/'
                                    (no output)
$ grep -rn 'CatalanArchive' Submission/ Submission.lean Solution.lean Challenge.lean \
      SolutionHybrid.lean ChallengeHybrid.lean | wc -l
0
$ grep -n 'lean_lib' lakefile.toml
[[lean_lib]]            # exactly one: name = "Submission"
$ grep -n 'Archive\|srcDir' lakefile-upstream.toml
[[lean_lib]] name = "Archive", srcDir = "archive", roots = ["CatalanArchive"]   # non-default target
$ find . -name 'CatalanArchive.lean' -not -path './.git/*'
                                    (no output — the declared root module has no source file,
                                     so `lake build Archive` cannot start either)
$ ls archive/
CatalanArchive  legacy-configs
$ grep -n 'lake build' .github/workflows/ci.yml
113:  lake build CatalanMeasure:docs
```

Live counterpart ships already chunked:

```
$ ls -l Submission/CatalanMeasure/GenD/D58/Cert590/XTab.lean
803 B,  importing XTab.P1 … XTab.P9
```

Largest in-closure `.lean`: 300,126 B (`Submission/CatalanMeasure/GenD/Uniform/Bank532/Pk/L0108_right.lean`).

## What was deliberately NOT done

1. **No chunking of the 12.53 MB `LV_X` term.** The split itself is mechanical (70 per-row defs
   + a 70-name list), but with the module unbuildable it can be neither type-verified nor
   memory-measured — it would be an unverifiable 12 MB edit to a frozen archival snapshot, for a
   memory effect of exactly zero.
2. **No import "fix"** (`G728/CellW` → `CellCert/CellW`). That is a resurrection decision for the
   archive tree (needs `archive/` on the Lean path or a declared lib), not a chunking task, and
   it would silently mutate a snapshot whose stated purpose is to be as-was.
3. **No mathlib build.** ~6 GB closure for a module no build target includes.

## Follow-up worth doing instead (for the coordinator)

At this SHA, 1,546 files in the **Submission** closure still contain `decide +kernel`, and
`OOM_INVESTIGATION.md` pins the real peak driver as one-shot kernel decisions (13.75 GB from a
30-line file), not bytes. Per-module measured RSS on `decide +kernel` monoliths inside
`Submission/` is the lane that can still move the verifier under 14 GiB.
