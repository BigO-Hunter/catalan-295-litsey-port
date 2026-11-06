# EvalRefE1 — already converted; remaining cut designed, not landed

Target as reassigned: `GenD/Signed/Data/Consts/EvalRefE1` (30 lines, one atomic
`by decide +kernel`, 13.75 GB peak). **That description matches commit `f0df3c8f`, not HEAD.**
At `bfa20018` the live module is already sharded.

## 1. Status: the 13.75 GB figure is stale

Two files exist; only the second is built (`lakefile.toml` declares one lib, `Submission`):

| file | lines | state |
|---|---|---|
| `CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1.lean` | 30 | the monolith from `OOM_INVESTIGATION.md`; root tree, not in any built lib |
| `Submission/CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1.lean` | 233 | **the live one — already sharded** |

`39d9d20f` ("decompose decide +kernel monoliths to cut peak RSS (EvalRefE1-class)") did it,
with a measured receipt in its own message (this host, `/usr/bin/time -l lake env lean`):

* imports-only baseline: **1.63 GB, 10.5 s**  ← the floor any further cut can only approach
* before: **13.75 GB, 1066 s**   after: **2.88 GB, 127 s**
* shape: 26 independent kernel checks (18 `jobN_c0`/`jobN_ts`, `jobs_eq` rfl, `planLits_eq`,
  `c0_eq`/`ts_eq` via `c0_sumL`/`ts_sumL`, `merge_eq`, 5 `logN`, `enc_M`, `enc_eq` shared by
  both bounds), statements byte-identical, no `native_decide`.

`bfa20018` then did the same for `EvalRefE0/E2/X01/X12`. So "the single worst module in the
submission" is no longer E1, and its 13.75 GB cannot recur.

## 2. What is still heavy, and the exact next cut

The 18 job checks are the remaining hot spot. Unfolding:

```
Job.lf j              = (pairLF j.qa j.qb j.r).smul j.sg
pairLF qa qb r        = pieceFieldLF qa (fieldOf r qb)
pieceFieldLF q F      = (LF.const (massQ ⟨lo,hi,pmul q.p F.poly⟩)).add
                          (LF.sumL (F.plogs.map (fun s => fqLF (fieldQ ⟨lo,hi,pmul q.p s.1⟩) s.2)))
```

so `jobN_c0` is one 25×25 `pmul` reduction and `jobN_ts` is **four** of them in a single
kernel reduction — 45 distinct `pmul`s over 9 jobs. At 2.88 GB peak against a 1.63 GB import
floor, the largest single link adds ~1.25 GB.

Proposed chain (mechanically generable, glue never rebuilds a table):

```
-- one link per row of the left factor, literals emitted by exact ℚ arithmetic:
theorem pJN_k : pmul (as_k) (F.poly) = LIT_k := by
  rw [← ih]            -- definitional: pmul (a::as) b = vecAdd (b.map (fun t => a*t)) (0 :: pmul as b)
  decide +kernel       -- only 25 scalar products + vecAdd of two ≤50-entry literals
-- 25 links per chain, 45 chains ≈ 1125 small checks, each term ≪ the table
theorem job1_c0 : (Job.lf ⟨qT,qT,false,(-1)⟩).c0 = c1 := by
  unfold ...; rw [pJ1_poly]; decide +kernel     -- massQ over a literal list only
theorem job1_ts : (Job.lf ⟨qT,qT,false,(-1)⟩).ts = t1 := by
  unfold ...; rw [pJ1_l1, pJ1_l2, pJ1_l3, pJ1_l4]; decide +kernel
```

Expected module peak → the import floor (~1.7 GB), i.e. ~1.7× better than 2.88 GB and the
lowest this module can go without slimming imports. Wall time: the arithmetic is unchanged and
now shared (each `pmul` computed once, feeding both projections), but ~1125 extra elaborations
of small literals — net cost unknown, must be measured, not asserted.

**Not landed.** Writing it is mechanical but needs an iterate-and-measure loop, and no
measurement was possible today (below). Unverified Lean is worth nothing, so nothing was edited.

## 3. Why there is no baseline/after number from this session

The closure (199 local modules + mathlib) had to be built from scratch. Setup borrowed a peer's
built mathlib by symlink (8548 oleans, matching `v4.34.1`, no rebuild). Then:

* the background `lake build …EvalRefE1` reached 12 oleans and was **killed with no error**
  under host pressure: load average 110, swap **7.3 GB used of 8.0 GB total**;
* six sibling W-agents were concurrently rebuilding the *same* ~8 GB closure in private clones
  (observed: W2 building `EvalRefE2`, W4 and W6 both building `Signed/Energy`, plus a
  `lake build Submission` and an `/usr/bin/time -l lake build Submission`).

Measuring a 2.8 GB module on a swapping host would have produced a number dominated by
contention, and would have slowed every peer. Reported instead of fabricated.

## 4. The reframing that matters more than another per-module shave

Post-conversion, the known worst single modules are ~2–3.3 GB (E1 2.88, `SpiB007` 3.31,
`PlusRows40To41` 2.01 — `OOM_INVESTIGATION.md`) against a **14 GiB** cgroup cap, and that report
records the OOM at `peak cgroup = exactly the cap` with **peak tasks 1299**. A 14 GiB peak is not
explained by any single ≤3.3 GB module; it is explained by *concurrent* module builds (lake's
default job count = core count). Before more per-module shaving, measure the **compound** peak of
a full `lake build Submission` at default parallelism vs `LAKE_JOBS=1`/`2`. If the compound number
is the problem, no amount of further chunking fixes it — the scheduler does.

## 5. Branch state

* `chunk/W1` — `1f824315`: archive target proven dead cargo (BASELINE.md + RECEIPTS.md). Parked.
* `chunk/W1-eval` — this document. No Lean source modified.
