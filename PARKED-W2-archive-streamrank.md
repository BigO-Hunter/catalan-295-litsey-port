# PARKED — archive/StreamRank/L0002_left (dead cargo)

Target deprecated: the `archive/CatalanArchive/` tree is outside the verifier's
build closure (largest live file is 1.00 MB). No changes retained here.

## Measured (kept because the negative result is reusable)

File: `archive/.../GenD/Uniform/Bank/StreamRank/L0002_left.lean`, 10.4 MB,
43 source decls, 32 `*_length` + 11 `*_dots` `by decide +kernel` monoliths.

Built standalone (mathlib closure hardlinked from a built tree, LEAN_NUM_THREADS=1):

| variant | peak RSS | wall |
|---|---|---|
| baseline (as committed) | 2.32 GB | 100.4 s |
| `*_dots` -> sorry | 1.58 GB | 39.3 s |
| `*_length` -> sorry | 2.31 GB | 57.8 s |
| both -> sorry | 1.49 GB | 57.3 s |
| **chunked via `intro; fin_cases <;> decide +kernel`** | **3.21 GB** | **151.3 s** |

## The reusable finding

Chunking a `by decide +kernel` monolith into per-goal goals **inside one
declaration** (`intro i; fin_cases i <;> decide +kernel`) *raises* peak
(+38%) and wall time (+51%). All N goal states and their `Decidable`
instances stay live simultaneously in the single declaration's tactic state,
whereas the monolith builds one instance, reduces it, and discards it.

=> To split a decision, use **separate top-level declarations** so each
instance is elaborated and freed independently; never a `fin_cases` fan-out
inside one decl. (Also: the giant `raw_ints%` literals are NOT the peak —
`Nat` literals live as GMP numbers, so 2.9 MB of source is ~500 KB of term.)
