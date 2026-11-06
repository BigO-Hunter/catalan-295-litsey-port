# EvalRefE2 — peak-RSS baseline vs after (W2, branch chunk/W2)

Target: `Submission/CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE2.lean`
(227 lines, 49 KB; the live build copy — the root `CatalanMeasure/` copy is a
1.2 KB unsharded leftover and is not in any lake lib).

## Build environment (no package rebuild)

mathlib v4.34.1 at rev `d13f23b7…` was **borrowed**, not rebuilt: `sp-corner`'s
already-built `.lake/packages` was `cp -al`-hardlinked in (7.6 GB, ~0 disk), and
only the 199 `Submission.*` modules in E2's own import closure (3.5 MB source)
were compiled, serialized (`LEAN_NUM_THREADS=1`, one `lean` process at a time).

## A/B pair

Both files are the same module; they differ **only** in the proof bodies of
`enc_en2_le` / `enc_en2_ge`:

* **baseline** `W2BaseE2.lean` — the original single decision:
  `theorem enc_en2_le : … := by decide +kernel` (whole `LF.sumL (planLits Rm2 Rm2)`
  materialised inside ONE kernel reduction).
* **after** `W2ShardE2.lean` — the branch's sharded form: 30 independent kernel
  checks (9 jobs × {c0, ts}, `c0_eq`, `ts_eq`, `merge_eq`, `log1..log5`,
  `enc_M`, `enc_eq`, then the two bounds), glued by `lf_eq_of` / `rw` / `Eq.trans`
  only — no glue term rebuilds the giant term.

| variant | peak RSS | wall |
|---|---|---|
| baseline (one atomic decision) | **5.49 GB, ABORTED** (watchdog killed at the 5 GB cap, still climbing, 185 s) | >185 s |
| after (30 sharded kernel checks) | **3.07 GB** | **107 s** |

Baseline is a **bounded lower bound**: it was still climbing at the cap when the
watchdog killed it. Unbounded it is E1-class — the repo's own
`OOM_INVESTIGATION.md` measured **13.75 GB** for `EvalRefE1`, the module this one
is named alongside.

## Import floor (why 3.07 GB is not "the proof")

A trivial module importing the same mathlib closure measures **1.17 GB** peak on
this machine. So the sharded module's own elaboration is ~1.9 GB
(3.07 − 1.17), not 3.07 GB.

**Verdict vs the <2 GB target: NOT met.** 3.07 GB is ~4.5× under the verifier's
14 GiB cap and ~4.5× better than the E1-class baseline, but the module-level
floor (mathlib import) plus the remaining atomics (`enc_M` and `enc_eq` still
accumulate 9 terms into a 462-/446-digit numerator in one each) keep it above
2 GB. To reach <2 GB the remaining work is (a) splitting the two accumulation
proofs into per-term steps, and (b) nothing this lane can do about the ~1.2 GB
leanole-an-load floor — that is a per-process cost the verifier pays anyway.
