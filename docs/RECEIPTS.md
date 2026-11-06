# RECEIPTS.md — commands and outputs (W6)

## 1. The repoint

    $ git diff Solution.lean
    -import CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll
    +import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll

Solution.lean sha256 before `f51f8a2603918992520c514486f0233b7aa41a8c019446aa24156936c295261f`
(after: docs/repoint_sha.txt). Only this line changed; Challenge.lean/lakefile/toolchain untouched.

## 2. Statement identity (the comparator's core check, statically)

The judged theorem, both trees, byte-identical:

    CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean:293
    Submission/CatalanMeasure/GenD/Signed/Data/Assembly/CellsAll.lean:293
      theorem catalan_irrationalityMeasure_410 :
          ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
            (b : ℝ) ^ (-(410 : ℝ)) <
              |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=

Mirror file with the tree prefix stripped == top-level file, exact string equality
(not a diff heuristic): CellsAll.lean True, Theorem410.lean True (0 diff lines).
Namespace is the same, so Solution.lean's body needs no edit.

## 3. Per-module peak RSS, post-repoint mirror (`/usr/bin/time -l lake env lean X.lean`)

`ROWS`
Whole-tree fact from this session: the build ran effectively serial (1 concurrent lean),
peak concurrent footprint 2.07 GB, 136/2727 oleans in 16 min at loadavg 105-142.

## 4. Comparator run — NOT COMPLETED (named blocker)

The local surrogate is `lake env lean Solution.lean` (elaborates the wrapper theorem and
prints its axioms). It needs the whole 2,727-module mirror closure. On this host, with seven
sibling workers holding the CPU (loadavg 105-142), the build advanced at ~3 modules/min and
would need ~15 h; the run was left building and is NOT claimed green.

Established without it:
  * the wrapper theorem restates the full statement and proves it by the mirror's theorem,
    so a statement mismatch is a type error, not a heuristic (see 2);
  * a prior session's full `lake build Submission` on this same commit reached [6116/6130],
    BUILD_EXIT=143 (SIGTERM at teardown, zero `error:` lines), with per-theorem
    `#print axioms` = [propext, Classical.choice, Quot.sound] throughout
    (/private/tmp/catalan_oomfix_build7.log);
  * W8's closure audit: sorry = 0, native_decide = 0, axiom = 0 in both trees.

## 5. Archive trio — parked (docs/PARKED.md)
