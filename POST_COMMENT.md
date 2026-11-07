<!-- Follow-up comment for the resubmission issue. The issue body is the bare
     four-field form (parser requirement); this comment carries everything
     human. fill_draft.py replaces {{BUILD_EXIT}} and {{AXIOMS}}. Nothing here
     needs to parse — only the body does. -->

**Context for this resubmission** (the body above is bare because the parser requires it — all human context lives here): this is `catalan-irrationality-measure-410`, the same theorem and the same bound 410 as the run that was killed at the 14 GiB cgroup cap in the OOM report (#163). We agreed with that outcome, found the cause on our side, fixed it, and measured the fix.

**Cause (ours).** The #163 submission shipped the same proof twice with identical namespaces — a pre-cure copy and a cured copy — and the module the comparator elaborates imported the **pre-cure** one. In it, `GenD/Signed/Data/Consts/EvalRefE1.lean` performs two one-shot `decide +kernel` reductions and peaks at **13.75 GB RSS** on our hardware — ~98% of the cap for a single module, before any co-scheduled work. The cured copy of the same file (31 sharded `decide` sites) had shipped all along but nothing imported it.

**What changed.**

1. One line: `Solution.lean` now imports the cured module (`Submission.CatalanMeasure.GenD.Signed.Data.Assembly.CellsAll`) instead of the pre-cure one.
2. The duplicate pre-cure trees are **deleted**, not bypassed: `CatalanMeasure/` (2,062 files + its root stub), the top-level `OAI/` (479; the vendored copies remain at `Submission/OAI/`), and `archive/` (9,633) — **12,175 files** by `git diff --name-status`. Module count 14,919 → 4,041. Nothing globs a stale 13.75 GB module because it no longer exists.
3. `Challenge.lean`, `lakefile.toml`, `lean-toolchain` and `comparator.json` are untouched. The judged statement is byte-identical to the previously judged one after removing the `Submission.` module prefix (receipts: `docs/RESUBMISSION.md` §3, `verify_identity.py` output committed in the repo). `Solution.lean` re-states the full `∀ᶠ b, ∀ a, …` formula, so any drift would be an elaboration error, not a silent change.

**Measured fit.** Worst single module in this tree: **2,724 MB** (`Data/Consts/TrialB1`) against the 14 GiB (14,336 MiB) cap — **5.3× under**. Peak concurrent `lean` processes on our hardware: 1 (`LAKE_JOBS=1`, `LEAN_NUM_THREADS=1`). The build that produced the entry olean ran as a serial dependency-ordered build at exactly that concurrency; it absorbed the host kill wall that had exhausted 40 prior wide-build attempts (each `lake build` run SIGTERM'd by the host governor at wall level — `attempts.tsv`), by taking kills at module granularity and resuming at the next unbuilt module.

**Build + comparator on this tree:** build exit `{{BUILD_EXIT}}`; `lake env lean Solution.lean` reports the judged theorem depends on `{{AXIOMS}}` — no `sorry`, no `native_decide`, no additional axioms.

**The one thing we cannot set from inside the submission.** The cap is per-cgroup, so what must fit is the *sum* of concurrent `lean` processes. Every module now fits with 5.3× headroom alone; with the split build's build job running wide, seven concurrent 2 GB modules would still reach the cap. If it is possible to pin the job count (e.g. `-j1`/`-j2`) for this target's build job, that is the other half of the fix. No bigger cap is being asked for.

**Provenance and credit.** The tree vendors OpenAI's Lean formalization of the irrationality of Catalan's constant (`Submission/OAI/`, Apache-2.0, see `NOTICE`); the prime number theorem comes from the PrimeNumberTheoremAnd project through that vendoring; the mathematical source is Sean Litsey's companion paper (`paper/`), built on OpenAI's determinant construction. **AI disclosure** (`formalization.yaml` §automation): AI agents (Claude Opus/Sonnet/Haiku via Claude Code; GPT-6.1 Sol via Codex) wrote the mathematics, Lean proofs, certificate generators and text at the direction of and under the responsibility of the human author; new certificates use `decide +kernel` without `native_decide`.

Happy to provide any receipt: per-module RSS samples, the import-graph accounting of the deleted trees, or the byte-identity comparison.
