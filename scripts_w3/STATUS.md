# W3 campaign status (branch chunk/W3, repo @ bfa20018)

Target: `CatalanMeasure.GenD.Signed.Data.Consts.EvalRefX12` (the X12 `decide +kernel`
monolith named in OOM_INVESTIGATION.md).

## Retired target
`archive/CatalanArchive/.../SourceRank/L0002_left.lean` (8.5 MB) — classified but abandoned
on instruction: the archive tree is outside the verifier's build closure (dead cargo).
Classification kept: 295 decls; top 5 are giant `tapes m [ ... ]` list literals
(1.00 MB / 0.96 MB / 0.64 MB / 0.44 MB / 0.42 MB); no proof monoliths — 150 theorems,
112 `decide`. `transform.py` still holds the (working, uncommitted-to-archive) splitting
transform if the archive is ever revived.

## Environment
* .lake/packages seeded from a sibling's build cache (mathlib prebuilt), then aesop/Qq/
  batteries/proofwidgets/plausible/importGraph/LeanSearchClient/Cli built (481 jobs, green).
* import closure of X12 = 195 modules, built into .lake/build/lib/lean by build_mod2.py
  (topological, 3 workers; measurements always single-threaded).
* LEAN_NUM_THREADS=1, LAKE_JOBS=1 for all measurement runs.
