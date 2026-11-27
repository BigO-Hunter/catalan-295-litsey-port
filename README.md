# Catalan's constant: μ(G) ≤ 295 — Litsey port at the board pin

Lean 4 + Mathlib kernel-checked port of Sean Litsey's μ(G) ≤ 295 proof and fifteen
trigamma-difference measures to the Big O Speedrun board pin (Lean v4.34.1, Mathlib `d13f23b7`).
Construction + proof: Litsey @ `65cfcc21`; port: darkhipo swarm. This is the catalan cluster's
frontier repo.

> Board (Nov 26 2026): this repo verifies μ(G) ≤ 295 (Lean); the open race is currently led by S. Litsey's claimed μ(G) ≤ 270 (Nov 8) — see [bigospeedrun.com](https://bigospeedrun.com).

> **Theorem.** μ(G) ≤ 295; μ(G ± 5π²/48) ≤ 31.2876 (both signs); μ(L(2, χ₋₃)) ≤ 13.7046;
> μ(L(2, χ₋₃) ± π²/9) ≤ 9.4998 (both signs); μ(ψ′(a/5) − π²/6) ≤ 23.8272 (a = 1…4);
> μ(ψ′(a/7) − π²/6) ≤ 2207.8697 (a = 1…6); μ(π²) ≤ 6.5253 (completeness only).
> Standard axioms only (`propext`, `Quot.sound`, `Classical.choice`); no `native_decide`.

## Catalan lineage in this org

| repo | role |
|---|---|
| **catalan-295-litsey-port** (this repo) | frontier: the strongest Lean-verified Catalan bound in this org, ported at the board pin |
| [`archive/410/`](archive/410/) | the superseded μ(G) ≤ 410 conversion (former `catalan-irrationality-measure-410`), folded byte-exact with full history; its research branches are preserved as `archive/410/*` refs — [branch map](archive/410-BRANCHES.md) · [OOM engineering](docs/oom-engineering.md) |
| [catalan-constant-gen5](https://github.com/BigO-Hunter/catalan-constant-gen5) | distinct Davis-chain method (generated degree-130 Zolotarev polynomial, μ(G) ≤ 528.2315). This port imports Davis's quadrature nodes + 33 Lean files @ `3c45153` from that chain: [`CatalanMeasure/GenD/Signed/Davis/`](CatalanMeasure/GenD/Signed/Davis/), Apache-2.0, NOTICE + PROVENANCE.json |
| [catalan-irrationality-measure-411](https://github.com/BigO-Hunter/catalan-irrationality-measure-411) | byte-identical twin of the 410 main (`0738347d`) carrying the CI-sharding PR #1 (the OOM build fix) |

## What's in it

- `Challenge*.lean` / `Solution*.lean` — the sixteen statements and their proofs (the trusted surface).
- `CatalanMeasure/GenD/` — the μ(G) ≤ 295 proof; `CatalanCore/Uniform/` — the fifteen trigamma measures.
- `OAI/` (386 imported files) + `PrimeNumberTheoremAnd/` — vendored OpenAI formalization, ported ([`PORTING.md`](PORTING.md), [`NOTICE`](NOTICE)).
- `paper/`, `paper-trigamma/` — Litsey's LaTeX + PDFs ([hexagon:2610.00187](https://hexagonmath.org/2610.00187), [hexagon:2610.00401](https://hexagonmath.org/2610.00401)).
- `archive/` — Lean modules no theorem imports (incl. the folded 410 port); not part of the build.
- `docs/` — [full port companion](docs/port-companion.md) (proof structure, literature map, theorem names) · [OOM engineering](docs/oom-engineering.md).

## Status

Port complete at the board pin; CI green (license, README-link, Lean-source gate, build, docs).
The comparator job is `continue-on-error` at v4.34.1 (Palomar's comparator needs ≥ v4.35.0-rc2;
the board verifies at the pin). The archived 410 head is explicitly **unverified source** — see
`VALIDATION.md` on ref `archive/410/validation/unverified-0738347`.

## Next steps

Independent rebuilds; reruns of the other fifteen measures. OOM/build engineering:
[docs/oom-engineering.md](docs/oom-engineering.md) (411 PR #1 — cone + 8 cell shards).

## Reproduction

Needs [elan](https://github.com/leanprover/elan) and several GiB of free disk/RAM
(use `LEAN_NUM_THREADS=2` on memory-constrained machines):

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build Submission
ruby scripts/validate-formalization.rb
ruby scripts/validate-formalization.rb formalization-hybrid.yaml
./scripts/verify-comparator.sh   # Linux + bwrap; needs toolchain >= v4.35.0-rc2
```

## Authorship, submission, licence

Mathematics, formalization, certificates and text were produced by AI systems (Claude Opus/Sonnet/
Haiku 5.5 in Claude Code; GPT-6.1 Sol in Codex) at the author's direction; the underlying
G-irrationality proof and the vendored code are OpenAI's. Full disclosure:
[docs/port-companion.md](docs/port-companion.md). Palomar template; submissions go through the form
at https://submit.palomar-registry.org/. Apache License 2.0 — [`LICENSE`](LICENSE), [`NOTICE`](NOTICE).

---

[BigO-Hunter](https://github.com/BigO-Hunter) — the darkhipo swarm's tracking & packaging org for
[Big O Speedrun](https://bigospeedrun.com) contributions. [Org profile](https://github.com/BigO-Hunter/.github) ·
[bigo-hunter.github.io](https://bigo-hunter.github.io).
