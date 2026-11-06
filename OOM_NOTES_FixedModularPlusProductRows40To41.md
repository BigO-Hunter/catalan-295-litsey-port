# FixedModularPlusProductRows40To41 — why the EvalRefE1 recipe does not transfer

Scope: `Submission/OAI/NumberTheory/Catalan/FiniteMatrices/`
`FixedModularPlusProductRows40To41` (+ its split family `P1`/`P2`), repo at
`bfa20018`. Measured on this host with `lake env lean <file>` under
`/usr/bin/time -l`, `LEAN_NUM_THREADS=1`, Mathlib from the pinned cache.

## 1. Classification (measured, not inferred)

| shape | peak RSS | wall | note |
|---|---|---|---|
| `P1` — 96 row defs + the two matrices, **no theorems** | **1.435 GB** | 9.9 s | reproduces `OOM_INVESTIGATION.md`'s 1.50 GB / 9.9 s |
| `P2` — same defs + 36 one-shot `decide +kernel` theorems | 1.94 GB | 169 s | `OOM_INVESTIGATION.md` |
| original single file (defs + 36 theorems) | 2.01 GB | 159 s | `OOM_INVESTIGATION.md` |

So **~1.44 GB is the Mathlib import floor** and the entire decision cost is
**~0.5 GB spread over 36 independent 48-wide decisions** (≈14 MB, ≈4.5 s each).

This is the opposite of the `EvalRefE1` case the repo already cured, where ONE
`decide +kernel` held every intermediate and the peak was the sum of them. Here
there is no monolith to split: the file split `P1`/`P2` barely moved the number
(2.01 → 1.94 GB) precisely because both halves keep their own decisions.

## 2. Shapes tried, with numbers

All keep the 36 exported theorem statements byte-identical and use only
`decide +kernel` (no `native_decide`, no new axioms).

| shape | peak RSS | wall | verdict |
|---|---|---|---|
| A: per-`k` sharding — `intro k; fin_cases k <;> decide +kernel` (48 one-entry decisions per theorem) | 2.026 GB | 266 s | **worse on both**: 1728 kernel checks, 48 live goals, no shared work |
| B: literalise both matrices, then rewrite each theorem to literal operands | — | — | blocked: the `M = litM` step is itself a 2304-entry decision |
| C: one matrix equality `M * I = 1` by `decide +revert +kernel`, then 36 `by rw` | 4.472 GB | 23 s | **kernel deep recursion** (`maxRecDepth`) at 2304-wide; peak 2.3× baseline |
| D (abandoned): `ext r k; fin_cases r <;> fin_cases k <;> rfl` for the matrix equalities | 4.327 GB | 211 s | 2304 live goals; abandoned |

The width→peak relation is direct and measured: 48-wide per theorem = 1.94 GB
module; 2304-wide = 4.47 GB and a kernel recursion failure. Narrower is cheaper
per decision (A confirms the per-check peak drops) but the *elaborator* side
(48 live goals × 36 theorems, each re-reducing its own copy of the term) costs
more than it saves.

## 3. Data cross-check (independent of Lean)

The 48×48 entries of `fixedLiteralModPlus` and `fixedLiteralInvPlus` were
extracted from the source text and multiplied in Z/101 in Python:
`M · I = I₄₈` on all 2304 entries, 0 mismatches. That confirms both the
statements and the extraction used by shapes B–D.

A fourth, separate floor probe: importing only the two row modules (no
`Mathlib.Tactic.FinCases`, no defs of its own) compiles the same file in
**1.407 GB / 11 s**, so the tactic import is not the cost either — the floor is
Mathlib's `Matrix`/`ZMod` closure.

## 4. Conclusion

For this module the achievable ceiling is the **~1.44 GB import floor** plus a
per-decision residual that no re-sharding removes, because the work is already
distributed one row per theorem. "Well under 1.5 GB" is not reachable from the
proof side at this row width; the remaining lever is the import cost itself
(`Mathlib.Tactic.FinCases` is imported only for `fin_cases`, which no proof
here needs — that is worth measuring separately).

Nothing in this note changes the tree; measurement scrap kept outside the repo
at `~/bigo-campaign/cat-chunk-W7/work/`.
