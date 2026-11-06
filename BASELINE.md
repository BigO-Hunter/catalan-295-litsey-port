# BASELINE — LinkSlope.lean (W4)

Target: `Submission/CatalanMeasure/GenD/Signed/Data/Consts/LinkSlope.lean`
repo `darkhipo/catalan-irrationality-measure-410` @ `bfa20018`, branch `chunk/W4`.
Named in `OOM_INVESTIGATION.md` among the `decide +kernel` monoliths to be re-engineered.

## 1. Classification — top-5 memory shapes

File is 281 lines / 41,764 B, but the memory is **not** in the text: it is in the kernel
reduction of the `decide +kernel` proofs. Ranked by measured cost (see §2), 24 blocks:

| # | shape | line(s) | bytes | cells in one decide | class |
|---|---|---|---|---|---|
| 1 | `theorem covS0 : covM1P1 (slopeN PnS0 247) 4 cutsS0 = true := by decide +kernel` | L23 | 79 | **10** | atomic kernel decision over the whole cut chain |
| 2 | `covS1` (8 cells), `covS2`,`covS3` (6 cells) | L34, L45, L56 | 79 each | 8 / 6 / 6 | same class |
| 3 | `covS4`..`covS7` (4 cells) | L67,L78,L89,L100 | 79 each | 4 | same class |
| 4 | `covS8`..`covS14` (2 cells) | L111..L177 | 79 each | 2 | same class |
| 5 | `covS15`..`covS23` (`cutsSK = []`) | L188..L275 | 79 each | 1 | single atomic cell — **uncuttable** |
| — | `monoS0`..`monoS23` (`chebGen` over ℚ) | every 11th line | 102 each | — | measured cheap, left whole |

The polynomial argument (`PnS0`, 1,011 B at L20) and the cut list (`cutsS0`, 9 ints at L22)
are small; the peak comes from `zNonnegCheck` computing, *inside one term*, the Möbius
coefficient table `zCompS s A (B-A) c` of **every** cell of the chain
(`zNonnegCov` = `&&`-chain over the cuts, `ZPoly.lean:159`).

## 2. Component measurement (real LinkSlope data)

Probes in `W4Probe/` import the same closure and carry the S0 block verbatim (the upstream
helper defs `zMul`/`chebGen`/`slopeN` copied verbatim from `LinkP.lean`), so one decision
class can be measured alone. `./measure_peak.sh` = `lake env lean <file>` under
`/usr/bin/time -l`, `LEAN_NUM_THREADS=1`.

| probe | decision content | wall | peak RSS |
|---|---|---|---|
| `W4Probe/Floor.lean` | imports only, no decision | 4.57 s | 1435.3 MB |
| `W4Probe/OneMono.lean` | `monoS0` monolith | 5.89 s | 1795.9 MB |
| `W4Probe/OneCov.lean` | `covS0` monolith (10 cells, 1 decide) | 168.40 s | **2921.7 MB** |
| `W4Probe/OneCovSplit.lean` | `covS0` sliced (10 per-cell decides + glue) | 33.96 s | **1612.4 MB** |

Marginal cost of the decision alone:

| | peak above import floor | wall above import floor |
|---|---|---|
| `monoS0` monolith | +360.6 MB | +1.3 s |
| `covS0` monolith | **+1486.4 MB** | **+163.8 s** |
| `covS0` sliced | +177.1 MB | +29.4 s |

So the cov chain is the bomb (8.4× the mono cost, and superlinear in cells: the kernel builds
all ten coefficient tables before the `&&` collapses), and slicing it removes 45 % of the
peak and 80 % of the wall time.

## 3. Build discipline

* `LEAN_NUM_THREADS=1`, lake default (single job), every run detached (`start_new_session`)
  and logged; never foregrounded.
* The host is saturated (load 130–160 across 8 parallel campaigns) and long-lived `lean`
  processes are killed by harness restarts, so the dependency build is wrapped in
  `w4_build_loop.sh` which re-invokes `lake build` until it reports success.
* Mathlib oleans are borrowed, not rebuilt: `.lake/packages` was copied from an
  already-built checkout of the same pin (`cat-chunk-W6`, Lean v4.34.1).
