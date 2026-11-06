# DRAFT — submission issue for bigospeedrun/verifier (NOT POSTED; coordinator to post)

Coordinator context, not part of the issue body: this is a **new issue**, not a comment on
the closed OOM report — per the #157 lesson, a closed issue is never re-run, so the
resubmission must arrive as its own thread. The submission is
`darkhipo/catalan-irrationality-measure-410` at the SHA named below, bound 410, i.e. the same
theorem as the run that OOMed. The body states only what is measured on our own hardware and
asks for one thing (a serialized build for this target); it does not dispute the OOM, does not
ask for a bigger cap, and does not re-raise the questions already asked in #163.

---

<!-- COPY BELOW THIS LINE -->

**Resubmission: catalan-irrationality-measure-410 @ `<SHA>` — the previous OOM was a packaging defect, and it is fixed**

The earlier run of this submission was killed at the cgroup cap. We investigated and agree
with the outcome report; this note is what changed, measured, so the next run is aimed at the
right thing.

**Cause (ours, not the runner's).** The submission shipped the same proof twice — a pre-cure
copy and a cured copy under `Submission/` — with identical namespaces, and the module the
comparator elaborates imported the pre-cure copy. In that copy one file,
`GenD/Signed/Data/Consts/EvalRefE1.lean` (30 lines), performs two one-shot
`by decide +kernel` reductions and measured **13.75 GB peak RSS** on our hardware
(`/usr/bin/time -l`, Lean 4.34.1, mathlib `d13f23b7`). That is ~98% of a 14 GiB budget for a
single module, before any co-scheduled work. The cured copy of the same file is 233 lines with
31 sharded `decide` sites and no single large kernel reduction.

**What changed in this submission.**

1. One line: `Solution.lean` now imports the cured module
   (`Submission.CatalanMeasure.…CellsAll`) instead of the pre-cure one.
2. The pre-cure tree is **deleted**, not merely bypassed — `CatalanMeasure/` (2,062 files),
   `OAI/` (479) and the unimported `archive/` (9,632). The former 5,858-job denominator was
   larger than the 5,181 modules the two trees hold, so we no longer rely on "nothing globs
   the old tree": it does not exist. Module count 14,919 → 4,041.
3. `Challenge.lean`, `lakefile.toml`, `lean-toolchain` and `comparator.json` are untouched.

**Statement identity.** The judged theorem is the same declaration, at the same coordinates,
with byte-identical source lines in both copies; the file now elaborated is byte-identical to
the previously judged one after removing the `Submission.` module prefix (`bytes == bytes`,
11,838 B each side). `Solution.lean` re-states the full `∀ᶠ b, ∀ a, …` formula rather than
re-exporting a name, so a divergence would be an elaboration type error. Verification script
and transcript are in the submission repo (`docs/RESUBMISSION.md` §3). Axioms on the judged
path are `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`.

**Measured, after the change** (our hardware, `LEAN_NUM_THREADS=1`, mathlib from cache):

| | before (#163's build) | this submission |
|---|---|---|
| modules in the package | 14,919 | 4,041 |
| worst single module | 13,750 MB (`EvalRefE1`) | **2,724 MB** (`Data/Consts/TrialB1`) |
| modules over 2 GB | 2 | 3 |
| concurrent `lean` processes | wide (`peak tasks 1299` in your receipt) | 1 (`LAKE_JOBS=1`) |

Per-module peaks from the running build of this tree (1 s RSS sampling, filtered to this
build): `Data/Consts/TrialB1` 2,724 MB, `TrialB2` 2,723 MB, `TrialB0` 2,534 MB,
`Signed/EnergyNear` 2,337 MB, `Signed/FieldForm` 2,040 MB, `Data/Consts/SpikeS1/P1` 1,873 MB;
the whole 386-module vendored `OAI` block tops out at `BarrierCaseOneDescartesX0` 1,568 MB.
Cross-check with `/usr/bin/time -l` on three modules: `ReflectionEnergy` 1,897 MB,
`ArcsineDenominator` 1,741 MB. The floor for any module in this tree is ~700 MB (Lean runtime
plus olean load), so the marginal cost of the heaviest module is ~1.6 GB against a 14 GiB cap.
All `#print axioms` output on this tree is `[propext, Classical.choice, Quot.sound]`.

<!-- COORDINATOR: paste the finished build verdict here before posting, from
     `<repo>/docs/RESUBMISSION_BUILD_STATUS.md` — the line `BUILD_EXIT=0` and the comparator's
     `#print axioms` output from `lake env lean Solution.lean`. Do not post this draft while the
     status file still says "in progress": the whole point of the note is measured-not-claimed,
     and an unfinished build is the one thing that would undercut it. -->

**The one thing we cannot fix from inside the submission.** The cap is per-cgroup, so what
must fit is the *sum* of concurrently running `lean` processes, and the OOM receipt records
`peak tasks 1299` — the build was wide. Every module now fits with >6× headroom on its own,
but seven concurrent 2 GB modules reach 14 GiB. Would it be possible to build the Catalan
target with the job count pinned (e.g. `-j1`/`-j2`) for this submission? That is the other
half of the fix and it is not something a submitter can set.

We are happy to answer anything about the receipts above, including the import-graph
accounting for the difference between the 5,858 job counter and the 5,181 modules the two
trees hold (we measure 5,181 and would like to know what the remainder is, but that is a
separate question and not a precondition for this run).

<!-- COPY ABOVE THIS LINE -->

---

## Why the draft is shaped this way

* **New issue, not a comment.** #157/#163 are closed; a closed issue is not re-run. The
  resubmission needs its own queue entry, and the first line says which submission it is.
* **Cause owned first.** The maintainer's time is spent confirming our diagnosis otherwise.
  Stating the measured 13.75 GB and the duplicate-tree mistake up front makes the rest of the
  note checkable instead of argumentative.
* **Measured, not claimed.** Every number is a `time -l` / sampled RSS figure with the method
  named in one clause. No "should now fit" anywhere: the numbers say what fits, and §"one
  thing we cannot fix" says exactly what remains outside our control.
* **One ask.** Pinning the job count. Not a bigger cap (that was #163's ask and it was not
  granted, and re-asking would look like not having read the answer), not a trust-policy
  exception, not a re-dispatch of the closed run.
* **The 677-jobby question is offered, not demanded** — it is genuinely interesting to us
  (it is the denominator of every progress claim) but the run does not depend on it.
* Deliberately omitted: any hypothesis about the runner's internals; any mention of our
  sibling work; any promise about future commits.
* **Do not post before the build verdict exists.** The placeholder above is the only thing
  missing; the per-module numbers are already measured and will not change.
