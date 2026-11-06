# PARKED.md — the archive trio (dead cargo, per the redirect)

The three assigned files are archival copies outside every build target:

* `lakefile.toml` declares exactly one lib, `[[lean_lib]] name = "Submission"`, so Lake globs
  `Submission/**` only; `lake build` with no target reports "no default targets". No live
  module imports `CatalanArchive` (W8's closure audit, reproduced here).
* They do not elaborate standalone either: their dep tree no longer exists.
  `archive/.../Optimization/Arithmetic.lean:3` does a plain `import`, so `SignedPilot` is
  never re-exported -> "unknown namespace" at FullData:10 (measured, exit 1).

Measured anyway — same corpus, so they calibrate the peak model (time -l, this host):

| file / variant | bytes | wall | peak RSS |
|---|---|---|---|
| `PilotPotential.lean` (full) | 2.5 MB | 78.8 s | **2,112 MB** |
| defs only (no theorems) | 2.4 MB | 24.7 s | 1,022 MB |
| defs + 474 one-line `by decide +kernel` | 2.4 MB | 10.9 s | 805 MB |
| + the 466-deep glue line (without the final 8 checks) | 2.4 MB | 15.4 s | 829 MB |
| full (adds the last 9 theorems) | 2.5 MB | 78.8 s | **2,112 MB** |
| `Data027.lean` | 2.8 MB | 15.1 s | 1,260 MB |

**Attribution (the transferable result):** the peak is NOT the 2.4 MB of integer literals
(1,022 MB alone; *lower* once the small decides are added). The last nine theorems add 68 s and
**+1.30 GB**, and they are exactly the two glue shapes the brief warns about: one 19.5 KB source
line that is a 466-deep nested `evalInputs_cons ...` **giant glue term**, plus eight `checkRows`
decides over a 483-entry table. Chunking literals would have bought nothing here. Block-composing
the 466-deep glue (blocks of ~32 + an `evalInputs_append` lemma) is where the reduction lives.
Left unmodified (dead cargo), but the shape is what to look for in the LIVE cure lane.
