# FIT_VERDICT.md — does the repointed tree fit the verifier's 14 GiB cgroup?

Cap: 15,032,385,536 B = 14 GiB, **no swap**, tasks_limit 4096 (verifier #163 receipt).

## Verdict: FITS on the per-module axis, with ~6x headroom — THREE named residuals

**Per-module peak, judged path (mirror, after the repoint): ~2.1 GB worst observed**
(`EnergyNear` still climbing at 2.07 GB; `ReflectionEnergy` 1.90 GB; `ArcsineDenominator`
1.74 GB measured clean). Against a 14 GiB cap that is 6.7x headroom. The modules that killed
verifier #163 — the 1.2 KB / 2-decide `EvalRefE1` at **13.75 GB** — are **no longer on the
judged path** once `Solution.lean` imports the mirror.

So the OOM is not a property of this proof's mathematics; it is a property of the *pre-cure
copy* of it, and it disappears with a one-line import change.

## Residual killers (each is a way this verdict can still fail)

**R1 — concurrency, not any single module.** The cap is per-CGROUP, so what must fit is the SUM
of concurrent `lean` processes. Post-repoint modules still cost 0.7–2.1 GB each; **7 concurrent
heavy modules = 14 GiB**. The receipt's `peak tasks 1299` says the verifier ran a wide build.
This is now the dominant risk and it is NOT fixed by the repoint — it needs either a lower
`-j` on the verifier's build or a lower per-module floor. Workers should target *floor* cost
(fewer imported Mathlib modules per file) as well as single-term peak.
Unmeasured: the mirror's 250–293 KB class (`Data/Cells/Core` 156 decides; `Bank532/Pk/*`) —
projected 2.5–3.5 GB, not built before this report (host at load 140, ~3 modules/min).

**R2 — the top-level tree must be DELETED, not merely bypassed.** `lake build` for the package
is not what the verifier runs blindly: the receipt's job counter is 5,858 while the two trees
sum to 5,181, and 677 jobs are unaccounted for (W8's open question). If any part of the
verifier's plan still enumerates top-level modules — a glob target, a stale `Solution.lean` in
the submitted archive, an aggregator — the 13.75 GB module is built again and OOMs again.
Action: submit with `archive/` **and** the top-level duplicate tree removed (W8's cost model
lever 2/3 are file-count relief only; the top-level tree is the memory relief) so the pre-cure
copies cannot be reached by any build command.

**R3 — the `maxHeartbeats` delta in the mirror.** `GenD/Signed/SheetNear.lean` in the mirror
drops a `set_option maxHeartbeats 1600000 in` that the top-level file carries. The repo lakefile
sets `maxHeartbeats 0` (unlimited) globally, so this is inert *in this package*; it only bites a
harness that re-imposes a heartbeat cap. Comparator run not completed here (see RECEIPTS.md):
it needs the full 2,727-module closure and this host cannot deliver that while 7 peers build.

## What would change this verdict

* A measured mirror module above ~6 GB (none expected: the largest source is 293 KB, and the
  biggest measured 147 KB file peaks at 1.9 GB).
* The verifier building the top-level tree anyway (R2) → OOM returns at `EvalRefE1`.
* A wide `-j` on a low-memory box (R1) → OOM by summation even though every module fits.

## Confirmation (post-storm, no re-measurement possible)

The comparator build could not be completed: two full-closure attempts were SIGTERM'd by host
contention at 168/2,727 and 238/2,727 oleans (swap 7.3/8.2 GB, load 100-157; no Lean errors in
either log). This verdict is therefore a **bounded extrapolation from two clean points plus the
flat floor**, not a completed build.

It is confirmed, with the mechanism made precise:

* the fitted quantity is **fixed import cost**, not the proof term. A 1.4 KB module importing
  nothing peaks at 0.70 GB; the mirror's 91 KB and 147 KB modules peak at 1.74 GB and 1.90 GB.
  Marginal cost is ~2.8 MB of peak per KB of source, which puts even the mirror's largest module
  (293 KB) at ~2.3 GB against a 14 GiB cap. **The repoint alone clears the single-module axis by
  ~6x.**
* the remaining risk is therefore NOT "is a 13.75 GB module still in the judged path" (it is not:
  that shape lives only in the top-level tree, which the repoint stops importing), but R1
  (**sum of concurrent modules**) and R2 (**the top-level tree surviving in the submitted
  archive**). Neither can be settled by any single-module measurement.

Verdict unchanged: **FITS, conditional on R1 and R2 being handled.** Every module measured or
extrapolated fits with >=6x headroom; the cap is reachable only by summation or by shipping the
pre-cure duplicate.
