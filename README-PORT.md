# catalan-295-litsey-port

Lean proof of the irrationality-exponent bound μ(G) ≤ 295 for Catalan's constant,
ported to the BigOSpeedrun Catalan profile.

**The construction and the proof are Sean Litsey's** —
https://github.com/slitsey/catalan-irrationality-measure at commit
`65cfcc216b2fd8a6c52f84a8ea41fb654b11eddb`. Our only contribution is the toolchain
port (Lean `v4.35.0-rc2` → `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`)
and the Submission-layout conversion prescribed by `docs/convert-layout.md` of
bigospeedrun/verifier. See NOTICE-PORT.md for the complete change list and NOTICE for
Litsey's own third-party credits (OpenAI's OAI library and 24 Sep 2026 preprint lineage,
PrimeNumberTheoremAnd, Cinna Davis's quadrature certificates).

## Build

```
lake exe cache get
lake build Submission
```

Toolchain `leanprover/lean4:v4.34.1`; Mathlib pin `d13f23b`. The upstream
v4.35.0-rc2 build files are kept as `*-upstream` and are not used.

## What the verifier reads

`Submission.lean` (bridge proving `Race.bound : BigOSpeedrun.Catalan.Bound ((295 : ℚ) / 1)`)
and the modules below `Submission/`. The verified receipt, from this tree:

```
info: Submission.lean:21:0: 'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (5372 jobs).
```
(PORT_BUILD.log is the build log.)

## Changes relative to Litsey's tree at 65cfcc21

`PORT_DIFF.txt` is the ledger. In short: four source roots (`OAI`,
`PrimeNumberTheoremAnd`, `CatalanMeasure`, `CatalanCore`) are copied under `Submission/`
with the `Submission.` import prefix, byte-preserving (line endings untouched), and two
elaborator-level adjustments are disclosed in NOTICE-PORT.md items 3c–3d. No statement
and no proof step is changed:

- `Submission/CatalanMeasure/GenD/Cert/Assembly.lean`: `of_decide_eq_true hPb` wrapped as
  `decide_eq_true_eq.mpr (of_decide_eq_true hPb)` inside `blockOK_ofS`.
- `Submission/CatalanMeasure/GenD/Signed/SheetNear.lean`: `set_option maxHeartbeats 1600000 in`
  before `near_Sterm_le`.

`Submission/CatalanStatement.lean` is a byte-for-byte copy of
`challenges/catalan/Statement.lean` of bigospeedrun/verifier.
