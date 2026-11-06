# W3 — X12 `decide +kernel` monolith: measured cost model and the chain design

Branch `chunk/W3`, repo `catalan-irrationality-measure-410` @ `bfa20018`.
Target module: `CatalanMeasure/GenD/Signed/Data/Consts/EvalRefX12.lean` (914 B) — named
in `OOM_INVESTIGATION.md` as one of the monoliths that must be re-engineered before any
resubmission.

## 1. What the monolith actually is

```lean
theorem enc_x12_le : encUpper 7 (LF.sumL (planLits Rm1 Rm2)) xU12 = true := by decide +kernel
```

`encUpper n f U` unfolds to `(f.enc n)` followed by `decide (p.1 + p.2 ≤ U)`, and
`LF.enc n f` unfolds to `encTerms n (mergeT f.ts)`. `planLits R S = (refPlan R S).map Job.lf`
recomputes the whole plan **inside the kernel**: every `Job.lf` is
`(pairLF qa qb r).smul sg`, i.e. one polynomial-pair product over `PieceQ` data whose
coefficients are 50–1000-digit rationals. For X12 (`Rm1` vs `Rm2`) `refPlan` has **18 jobs**
(`pT`/`pF` = 1/2 pieces per species, `nT`/`nF` empty ⇒ 2 non-empty `jobsBil` groups × 9).

So the atomic decision holds 18 independent polynomial products in ONE term. Nothing
decomposes it: `LF.enc` calls `mergeT` on the *whole* `ts` list, so the enclosure value is
not reachable compositionally without new lemmas (see §4).

## 2. Measured cost model (this machine, `/usr/bin/time -l`, `LEAN_NUM_THREADS=1`)

Probes were built by replacing the module's decision with cheaper ones over the SAME data
(`(refPlan Rm1 Rm2).take k).map Job.lf`; `.take` is applied to `refPlan`, not to the mapped
list, so the kernel computes exactly k jobs).

| file | decisions | peak RSS | wall | exit |
|---|---|---|---|---|
| module with `:= by sorry` (no decision at all) | 0 | **1.59 GB** | ~30 s | 0 |
| 1 job + its enclosure | 2 decides, 1 job | **2.73 GB** (2791 MB) | 85 s | 0 |
| 2 jobs + their enclosure | 2 decides, 2 jobs | **4.17 GB** (4274 MB) | 204 s | 0 |
| 18 jobs + enclosure (= the real file) | the monolith | **killed (SIGTERM) at 129 s** | — | 143 |

Marginal cost per job: **+1.45 GB, +119 s**. Linear fit to 18 jobs: **≈ 28 GB**, i.e. 2×
the verifier's 14 GiB cgroup — and it cannot be measured to completion on a shared host.

**Model validation against the repo's own numbers.** `EvalRefE1` (`Rm1` vs `Rm1`, 9 jobs) was
measured in `OOM_INVESTIGATION.md` at 13.75 GB / 1066 s. The fit predicts
`2.79 + 8×1.45 = 14.4 GB`. Agreement within 5 %. The model is not a guess: it reproduces
the one independent measurement that exists.

**Consequence:** the load-bearing cost is the *per-job polynomial product* inside one atomic
term, not the `enc`/`logAbsQ` step (`1 job + enc` = 2.73 GB including a 1.59 GB floor).

## 3. The chain that the model implies

Per-job sharding — the design `EvalRefLog.lean`'s own docstring describes ("one
`decide +kernel` per job ... and one enclosure check of the summed literal") and which the
`bfa20018` commit abandoned for the recompute-everything form.

1. `hl : List.Forall₂ (fun j l => j.lf = l) (refPlan Rm1 Rm2) lits` — one `decide +kernel`
   per job/row, each a *single* polynomial product (**2.73 GB measured**, not 28 GB).
2. `planLits Rm1 Rm2 = lits` from `hl` (`js.map Job.lf = ls`, 5-line induction).
3. `encUpper 7 (LF.sumL lits) xU12 = true` — one `decide +kernel` over the summed *literal*
   (18 small LFs, no polynomial recomputation).
4. `enc_x12_le` follows by rewriting the argument of `encUpper` with step 2. Declared type
   unchanged — the receipt is `#print enc_x12_le` before/after.

Predicted result: peak = 1.59 GB floor + 1 job ≈ **2.8–3.0 GB** (the 1-job probe above is a
direct measurement of that shape), against ≈28 GB (fitted) / 13.75 GB (measured on the
sibling E1). ~10× down, and inside the 14 GiB cap.

## 4. Why the *generic* route (sub-term decomposition of `enc`) was rejected

Decomposing `LF.enc` itself (`(sumL (l1++l2)).enc n` from the blocks) requires
`mergeT (a ++ b) = mergeT a ++ mergeT b`, which needs `addT`-append and cross-block argument
disjointness — ~150 lines of list-recursion lemmas with no counterpart in the repo today.
It buys nothing over §3: the per-job cost, not the enclosure, is the peak.

## 5. Status — honest

* Done: cost model measured (§2), validated against the one independent repo measurement;
  environment built (195-module closure, mathlib/aesop from the shared cache, no rebuild);
  tooling committed (`scripts_w3/`); archive target retired and parked.
* **Not done: the §3 patch itself is not written.** The per-job `lits` must be produced by
  `#eval` from the same module (cheap in the VM) and the `Forall₂` assembled row by row —
  that assembly was not completed in this lane.
* Wall-time note: peak RSS is comparable across runs; wall times on this host are inflated
  by a load average of 85–165 (8 sibling lanes) and are indicative only.
* The 18-job probe had to be stopped: the host directive to stop memory storms takes
  precedence over completing a measurement whose outcome (§2's fit, §2's validation) is
  already determined.
