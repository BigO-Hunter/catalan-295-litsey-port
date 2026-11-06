# PEAK_PROFILE.md — measured elaboration peaks, repointed tree (W6)

Host: M4 Max, 137 GB RAM, 16 cores, lean v4.34.1, mathlib `d13f23b7` (cache-prebuilt oleans).
Measurement: `/usr/bin/time -l lake env lean <file>` → "maximum resident set size" (bytes),
`LEAN_NUM_THREADS=1`. Run at loadavg 105–142 (7 of 8 sibling workers were building
simultaneously), so **wall times are inflated ~5-8x**; peak RSS is load-insensitive and is the
number that matters.

## A. Post-repoint judged path (the CURED mirror) — measured

| module (`Submission/…`) | KB | wall | peak RSS |
|---|---|---|---|
| `CatalanMeasure/GenD/Signed/ReflectionEnergy.lean` | 147 | 26.6 s | **1,897 MB** |
| `CatalanMeasure/GenD/Signed/ArcsineDenominator.lean` | 91 | 19.3 s | **1,741 MB** |
| `CatalanMeasure/GenD/Signed/EnergyNear.lean` | 60 | >150 s (still elaborating) | **≥2,067 MB** (live sample) |
| `CatalanMeasure/Parametric/CoupledFirstEnergy.lean` | 20 | – | ≥1,309 MB (sampled floor) |

Process floor for any module in this tree: ~700 MB (Lean runtime + olean load; measured on a
1.4 KB module with no Mathlib import at all). So the peak *above floor* is ~1.2-1.4 GB for the
147 KB class and >1.4 GB for `EnergyNear`.

## B. The pre-cure tree that the repoint REMOVES from the judged path

| module (top-level) | KB | decide sites | peak (cited) |
|---|---|---|---|
| `GenD/Signed/Data/Consts/EvalRefE1.lean` | 1.2 | 2 one-shot | **13,750 MB**, 1,066 s |
| `GenD/Signed/Data/Cells/Q2/SpiB007.lean` | 344 lines | – | 3,310 MB, 1,328 s |

Source: `OOM_INVESTIGATION.md` §"Measured single-module peaks (this machine)". Not re-measured
here — reproducing it costs 13.75 GB of RAM and ~18 min of a host already at load 140.

## C. Cure shape, verified statically on THIS tree (top-level vs mirror)

| module | top-level | mirror |
|---|---|---|
| `Data/Consts/EvalRefE1` | 1.2 KB, **2** decide, 4 thm | 49.9 KB, **31** decide, 46 thm |
| `Data/Consts/EvalRefE0` | 1.2 KB, **2** decide, 4 thm | 13.5 KB, **18** decide, 28 thm |
| `Data/Consts/EvalRefX01` | 0.9 KB, **1** decide, 2 thm | 39.1 KB, **24** decide, 35 thm |
| `Data/Trial/T1Fields/P3` | — (not in top-level) | 113 KB, 2 decide, 2 thm |

The mirror has **no** one-shot `decide` left on a large literal: the largest module in the whole
mirror is 293 KB (`GenD/Uniform/Bank532/Pk/L0108_right`, 15 decide sites) and the largest
decide-heavy module is 250 KB / 156 decides (`Data/Cells/Core`). By contrast the top-level tree
concentrates 13.75 GB of kernel reduction in a **1.2 KB** file.

## D. Whole-build evidence (prior session, same commit, logged)

`/private/tmp/catalan_oomfix_build7.log`: `lake build Submission` on the mirror reached
`[6116/6130]` and ended `BUILD_EXIT=143` — SIGTERM (session teardown), **not** a Lean error;
zero `error:` lines in the log. Per-theorem `#print axioms` audits all read
`[propext, Classical.choice, Quot.sound]` (e.g. `BernsteinSzego`, `ArcsinePhantom`,
`Bank532`), i.e. no `sorry`/`native_decide`/extra axiom on the mirror side.

## E. This session's build attempt (why the profile is partial)

`lake build Submission` on the repointed tree was launched detached at 13:57 and instrumented
with a 0.3 s RSS poller (`peakmon2.py`, per-PID → module). At loadavg 140 it advanced at
**~3 modules/min, effectively serial (1 concurrent `lean`)**: 136 of 2,727 oleans in 16 min,
peak concurrent footprint 2.07 GB. A full-library build is therefore ~15 h on this host while
seven sibling workers hold the CPU — out of scope. Module peaks in §A were taken with `time -l`
instead, which is accurate per module and does not need the whole build.
