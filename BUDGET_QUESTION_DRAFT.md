# DRAFT — comment for verifier issue #163 (NOT POSTED; coordinator to post)

Context for the coordinator, not part of the comment: this submission is
`darkhipo/catalan-irrationality-measure-410` @ `bfa20018`, bound 410. The receipt quoted in
thread (`/tmp/bos157/receipt.json`, carried in the repo's `OOM_INVESTIGATION.md`) records a
cgroup cap of 15,032,385,536 B with swap 0, and both jobs dying exactly at the cap
([4255/5858] in the build job, [4296/5858] after 5 m 06 s in the verify job). Our own
single-module measurement on commodity hardware is 13.75 GB peak RSS for one module
(`CatalanMeasure/GenD/Signed/Data/Consts/EvalRefE1`, a single one-shot `decide +kernel`).
The draft below assumes that receipt is accurate for #157 and asks whether it still holds
for #163. House tone: courteous, precise, one question per item, no asks beyond information.

---

<!-- COPY BELOW THIS LINE -->

Thanks for the resource-outcome report on this run. We are not disputing the OOM; we would
like to make the next submission fit, and four facts would let us aim at the right thing.

1. **Memory budget.** Is the per-job limit still 14 GiB (15,032,385,536 B) with swap
   disabled, as recorded in the receipt we have from the earlier run of this submission? If
   it has changed for this dispatch, what is it now, and does the verify job share the build
   job's budget or get its own?

2. **Which file was elaborating.** Does the OOM record (or the log artifact linked in thread)
   name the module being elaborated when the cgroup was hit? We have a 13.75 GB measured peak
   for one module and it would confirm or refute our attribution directly.

3. **Work-counter denominator.** The progress counter read `[4255/5858]`. Our import-graph
   measurement of `bfa20018` accounts for 5,181 of the package's own modules for one
   verification (2,454 reachable from `Solution.lean`, 2,727 under the `Submission` library),
   with Mathlib prebuilt from cache. Could you say what the 5,858 counts — all modules
   including cached dependencies, or only work the runner performs?

4. **Trust policy for `decide +kernel`.** Our certificates are kernel reductions
   (`by decide +kernel`) — no `native_decide`, no axioms beyond `propext`,
   `Classical.choice`, `Quot.sound`. Is that acceptable under the runner's policy, and is
   there a per-module elaboration budget in addition to the memory cap that we should be
   designing against?

If a re-dispatch with a larger memory cap is possible for a submission of this size, we would
gladly take that path and say so explicitly; if not, we will re-engineer the remaining
one-shot reductions and resubmit. Thank you for the detailed outcome report either way.

<!-- COPY ABOVE THIS LINE -->

---

## Notes on the draft's choices

* Q1 states the number we hold instead of asking "what is the limit?" — a maintainer can
  confirm or correct in one word, and it cannot be read as us not having read the thread.
* Q3 is new information for the maintainer (a measured denominator) rather than a complaint;
  it is also the question whose answer changes how we report progress to ourselves.
* Q4 is asked as a policy question, not a permission request, because the derivation report
  did not mention trust; if `native_decide` *were* permitted it would be a large lever
  (native evaluation trades kernel reduction for compilation, typically an order of magnitude
  less memory at this literal size). We do not propose it unasked.
* Deliberately omitted: any request to change the cap as a *demand*, and any mention of the
  duplicate-tree finding — fixing that is our job, not the maintainer's.
