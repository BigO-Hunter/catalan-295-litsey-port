# REPOINT.md — Solution.lean → cured mirror (W6)

Repo: `~/bigo-campaign/cat-chunk-W6/repo` @ `bfa20018` , branch `chunk/W6`
Follows `cat-chunk-W8/CLOSURE_MAP.md` (the graph audit of what the accepted statement needs).

## The diff (whole change)

```diff
--- a/Solution.lean
+++ b/Solution.lean
@@ -4,7 +4,7 @@ public import Mathlib.Analysis.SpecialFunctions.Pow.Real
 public import Mathlib.Topology.Algebra.InfiniteSum.Real
 public import Mathlib.Order.Filter.AtTopBot.Basic

-import CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll
+import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll

 public section
```

Nothing else changed. `Challenge.lean`, `lakefile.toml`, `lean-toolchain` untouched.

Solution.lean sha256: before `f51f8a2603918992520c514486f0233b7aa41a8c019446aa24156936c295261f`
(after: see `receipts/repoint_sha.txt`).

## Why this is statement-preserving (static receipts, measured on this tree)

1. **The judged theorem is declared in both trees at the same name and the same
   coordinates**: `CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean:293` and
   `Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean:293`.
   The statement text is byte-identical::

       theorem catalan_irrationalityMeasure_410 :
           ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
             (b : ℝ) ^ (-(410 : ℝ)) <
               |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=

   The namespace is the same (`CatalanMeasure.GenD.Signed`), so `Solution.lean`'s body
   (`CatalanMeasure.GenD.Signed.catalan_irrationalityMeasure_410`) needs no edit — confirmed
   by the file compiling unmodified against the new import.

2. **Entry module is byte-identical modulo the tree prefix.**
   `Submission/…/Data/Assembly/CellsAll.lean` with every `Submission.` removed == the
   top-level `…/Data/Assembly/CellsAll.lean` (exact string equality, not a diff heuristic).
   Same for `GenD/Signed/Theorem410.lean` (0 diff lines under the same normalisation).

3. **Solution.lean's own statement is re-stated, not merely re-exported.** The file declares
   `theorem CatalanIrrationalityMeasure.catalan_irrationalityMeasure_410` with the full
   ∀ᶠ… statement and proves it by the mirror's theorem. A statement mismatch would be a
   type error at elaboration — this is the comparator's core check, not a proxy for it.

4. `Challenge.lean` (the module the comparator diffs against) is untouched and imports only
   Mathlib, so the accepted statement surface is unchanged.

## What the swap removes from the build

`lake build Submission` = the mirror lib (2,727 modules).
`Solution.lean` before the swap pulled the **top-level** 2,454-module closure (the
pre-cure one-shot `decide +kernel` copies, incl. the measured 13.75 GB `EvalRefE1`).
After the swap it pulls nothing new: the mirror closure is already inside the lib.
Union of modules built per verification: 5,181 → 2,727 (−47%).

## Comparator run (the confirmation the closure map asked for)

See `RECEIPTS.md` for the command, exit status and the `#print axioms` output.
