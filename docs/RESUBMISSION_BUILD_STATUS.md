# Build status — `lake build Submission` on the resubmission tree

Generated 2026-11-06T23:23:09Z from `/tmp/cat_build2.log`,
`.w7/attempts.tsv` and `.w7/peak2/samples.tsv` by `scripts_resub/build_status.py`.

State: **In progress at the time this file was generated — NOT yet green. Resume the recipe in `RESUBMISSION.md` §7.**

* modules built: **356 / 2,727**
* judged entry module (`…Data/Assembly/CellsAll.olean`): **not yet built**
* attempts recorded: 2
* sampler: peak concurrent `lean` in this tree **1**, peak footprint **2724 MB**, method `scripts_resub/measure_peak2.py` (1 s `ps` poll, filtered to this repo's processes)

## Attempts

A negative exit is a host-level signal (the body's `lean_build_governor` acts on the host-wide lean footprint), not a Lean error. Only `BUILD_EXIT=0` is green.

| attempt | wall | exit | oleans after |
|---|---|---|---|
| 1 | 495 s | -15 | 176 |
| 2 | 1199 s | -15 | 356 |

## Heaviest modules sampled (MB)

| module | peak |
|---|---|
| `Submission/CatalanMeasure/GenD/Signed/Data/Consts/TrialB1.lean` | 2724 |
| `Submission/CatalanMeasure/GenD/Signed/Data/Consts/TrialB2.lean` | 2723 |
| `Submission/CatalanMeasure/GenD/Signed/Data/Consts/TrialB0.lean` | 2534 |
| `Submission/CatalanMeasure/GenD/Signed/EnergyNear.lean` | 2337 |
| `Submission/CatalanMeasure/GenD/Signed/FieldForm.lean` | 2040 |
| `Submission/CatalanMeasure/GenD/Signed/Data/Consts/SpikeS1/P1.lean` | 1873 |

## Axioms printed by the build

| axiom set | theorems |
|---|---|
| `[propext, Classical.choice, Quot.sound]` | 633 |
| `[propext, Quot.sound]` | 2 |
