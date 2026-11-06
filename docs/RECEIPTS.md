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


---

## 6. Build-killed log and the exact resume recipe (do not restart blindly)

Two full-closure attempts, both SIGTERM'd by host contention — **not** by Lean errors:

| run | started | ended | oleans | exit | cause |
|---|---|---|---|---|---|
| run1 | 13:57 | 14:15 | 168/2,727 | 143 (SIGTERM) | session/host teardown |
| run2 | 14:16 | ~14:27 | 238/2,727 | 143 (SIGTERM) | fleet memory storm (swap 7.3/8.2 GB, load ~100-157) |

No `error:` line appears in either log. The comparator is therefore **incomplete because the
host cannot carry 2,727 module compiles while seven sibling workers rebuild the same closure**,
not because anything in the repointed tree fails to elaborate.

Resume recipe (one build only, serialized, shared mathlib):

    ln -s ~/bigo-campaign/staircase-port/.lake/packages ./packages   # `.lake` is already a
                                                                     # clonefile copy of it
    cd repo && LEAN_NUM_THREADS=1 LAKE_JOBS=1 \
      lake build Submission > ../build_resume.log 2>&1
    # then, only when the lib is complete:
    cd repo && LEAN_NUM_THREADS=1 lake env lean Solution.lean   # the comparator + #print axioms

Check `grep -c BUILD_EXIT ../build_resume.log` before claiming anything; exit 143 means
SIGTERM, i.e. unfinished, and must never be reported as green.

## 7. Peak model — what the two clean points actually say

| module | KB | peak | peak minus 0.7 GB floor |
|---|---|---|---|
| ArcsineDenominator | 91 | 1,741 MB | ~1.0 GB |
| ReflectionEnergy | 147 | 1,897 MB | ~1.2 GB |

The floor (0.70 GB) was measured on a 1.4 KB module that imports no Mathlib at all; a module
that pulls Mathlib's oleans starts higher, so most of these 1.7-1.9 GB is **fixed import cost,
not the term**. Marginal cost is ~2.8 MB of peak per KB of source (slope between the two
points), which extrapolates the mirror's largest module (293 KB) to **~2.3 GB** — the same
order as the live >=2.07 GB sample. Implication for the workers' targeting: single-term
chunking on modules of this size now buys ~0.2-0.4 GB, while the concurrency sum (R1) can cost
7x that. Budget the effort accordingly.
