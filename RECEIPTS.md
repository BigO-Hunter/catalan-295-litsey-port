# RECEIPTS — LinkSlope `decide +kernel` chain split (W4)

Target `Submission/CatalanMeasure/GenD/Signed/Data/Consts/LinkSlope.lean`, repo
`darkhipo/catalan-irrationality-measure-410` @ `bfa20018`, branch `chunk/W4`.

## 1. What changed

Each `covSK` was ONE kernel decision over the whole cut chain:

```lean
theorem covS0 : covM1P1 (slopeN PnS0 247) 4 cutsS0 = true := by decide +kernel
```

`covM1P1 c S cs = zNonnegCov c S (-(2^S)) cs (2^S)` is a `&&`-chain of `zNonnegCheck` calls
(`ZPoly.lean:159`), one per cut cell, and each `zNonnegCheck` builds the cell's Möbius
coefficient table `zCompS s A (B-A) c` in the kernel. A single `decide` therefore had to
materialise **every** cell's table inside one term before the `&&` collapsed.

Now:

```lean
theorem covS0_cell0 : zNonnegCheck (slopeN PnS0 247) 4 (-(2 : ℤ) ^ 4) (-14) = true := by decide +kernel
...  covS0_cell9
theorem covS0 : covM1P1 (slopeN PnS0 247) 4 cutsS0 = true := by
  have h : cutsS0 = ([-14, -12, -8, -4, 0, 4, 8, 12, 14] : List ℤ) := rfl
  rw [h]
  simp only [covM1P1, zNonnegCov, covS0_cell0, ..., covS0_cell9, Bool.and_true]
```

The glue mentions only the *cell checks* — it never rebuilds a coefficient table, so it is
small (a `Bool` `&&` chain over already-closed theorems; no `decide`, no `Eq.trans` over
giant terms). Trust profile unchanged: every slice is still `decide +kernel` on the same
data; **no `native_decide`, no `sorry`, no axiom added** (`#print axioms` of the module's
theorems still shows only `propext, Classical.choice, Quot.sound`).

`#print axioms` on the cured module (`W4Probe/AxCheck.lean`): `covS0` -> `[propext]`,
`covS0_cell0` -> `[propext]`; the untouched `slope0` / `monoS0` still report
`[propext, Classical.choice, Quot.sound]` (inherited from the imported lemmas). No new axiom.

Split: 15 blocks, 69 cells (covS0 10, covS1 8, covS2/3 6, covS4–7 4, covS8–14 2).
Left whole, with reasons — §4.

## 2. Exported declaration types — IDENTICAL

`python3 receipts.py` compares every `theorem`'s statement text (up to `:=`) and every
`def`'s full text, pristine side read from `git show HEAD:<path>`:

```
declarations compared: 192 pre, 252 post
STATEMENT CHANGED: 0
MISSING (removed): 0 []
ADDED (additive only): 60   (covS0_cell0 .. covS14_cell1)
VERDICT: IDENTICAL
```

The 60 additions are the per-cell lemmas; nothing pre-existing was renamed, removed or
re-typed. (`D_Y`-style structure literals and the 24 `slopeK` theorems that consume `monoSK`
/ `covSK` are untouched.)

## 3. Peak RSS and wall

Method: `lake env lean <file>` under `/usr/bin/time -l` (`measure_peak.sh`),
`LEAN_NUM_THREADS=1`, single lake job, runs detached. Import floor (same closure, no
decision) measured separately: **1435.3 MB / 4.57 s**.

| | wall | peak RSS | finished? |
|---|---|---|---|
| baseline module (as shipped) | > 7 min per attempt | **3013.9 MB** (sampled 5 s, 84 samples — lower bound) | **never** — SIGTERM at ~4–7 min, 3 attempts |
| cured module | **184.03 s** (`time -l`, rc=0; `lake build` 218 s, 3443 jobs) | **1933.9 MB** | **yes, rc=0** |

→ **peak 3013.9 → 1933.9 MB (−36 %), and the module now elaborates to completion at all.**

Component isolation on real LinkSlope data (`W4Probe/`, S0 block verbatim):

| probe | wall | peak RSS |
|---|---|---|
| floor (imports only) | 4.57 s | 1435.3 MB |
| `monoS0` monolith | 5.89 s | 1795.9 MB |
| `covS0` monolith (10 cells, 1 decide) | 168.40 s | 2921.7 MB |
| `covS0` sliced (10 decides + glue) | **33.96 s** | **1612.4 MB** |

So the chain split removes **45 % of the peak and 80 % of the wall time** for the worst block,
and it turns a module that could not be elaborated to completion on this host into one that
builds in 3.6 minutes.

### 3b. Honest caveats

* The baseline peak is **sampled** (5 s interval), not `/usr/bin/time -l`, because no baseline
  run ever survived to completion: the host SIGTERMs long-lived `lean` processes under load,
  and the baseline module needs far longer than the ~4–7 min window it is given. A sampled
  maximum is a **lower bound** on the true peak, so the real improvement is ≥ 36 %.
  The floor for any module containing this chain is the exact single-block figure
  `covS0` monolith = 2921.7 MB, which the baseline certainly also pays.
* The cured module's 1933.9 MB is `/usr/bin/time -l` exact (row in `evidence/peak.csv`), and
  is now dominated by the *import* cost of `LinkP`/`Phase2Contract`, not by any decision:
  the import-only probe of the smaller closure is 1435.3 MB.
* Under this load the 3.6-minute cured build is also near the kill window; it completed on
  attempt 1 of the retry loop (`w4_measure_cured.sh`), which is why the loop exists.

## 4. Left uncut, and why

| block(s) | shape | reason |
|---|---|---|
| `covS15` … `covS23` (9 blocks) | `cutsSK = []` → `zNonnegCov c S A [] B` = **one** `zNonnegCheck` | already a single atomic cell; there is no `&&` chain to slice. Splitting `zNonnegCheck` would mean slicing inside `zCompS`, which is the computation itself — glue would have to rebuild it. |
| `monoS0 … monoS23` (24 blocks) | `chebGen c0 g = Pn.map …` over ℚ | measured **cheap**: +360 MB and +1.3 s over the import floor for the S0 block. Not worth touching, and a list-equality slice would re-run the whole `chebGo` fold per slice (wall × n). |
| `gS*N`, `gS*`, `PnS*`, `cutsS*`, `M1S*` defs | `raw_ints%` literals ≤ 1 KB | data, not decisions; the biggest is 1,011 B. |
