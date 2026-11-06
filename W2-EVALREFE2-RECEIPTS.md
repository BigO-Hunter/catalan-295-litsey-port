# Receipts — EvalRefE2 decl-type diff (baseline vs after)

## Method

`W2BaseE2.lean` and `W2ShardE2.lean` are copies of the module that differ only in
the two bound proofs. Each declaration's **statement** (everything up to `:=`)
was extracted and compared pairwise.

```
decls: 81 81
statement mismatches: 0
STATEMENTS IDENTICAL: True (81 decls)
```

## The complete textual difference (2 hunks, proof bodies only)

```
207c207,210
< theorem enc_en2_le : encUpper 7 (LF.sumL (planLits Rm2 Rm2)) enU2 = true := by decide +kernel
---
> theorem enc_en2_le : encUpper 7 (LF.sumL (planLits Rm2 Rm2)) enU2 = true := by
>   unfold encUpper
>   rw [enc_eq]
>   decide +kernel
209c212,215
< theorem enc_en2_ge : encLower 7 (LF.sumL (planLits Rm2 Rm2)) enL2 = true := by decide +kernel
---
> theorem enc_en2_ge : encLower 7 (LF.sumL (planLits Rm2 Rm2)) enL2 = true := by
>   unfold encLower
>   rw [enc_eq]
>   decide +kernel
```

**Decl-type diff verdict: IDENTICAL (yes).**

## Trust profile (no native_decide)

`grep -c native_decide` over the module = 0. Every check is `decide +kernel`
(kernel reduction) or `rfl`/`rw`/`simp only`. Trusted axioms are unchanged.

## Note on the leaf file

`W2ReceiptShard` (an appended `#check @…` receipt module) was launched twice and
both runs were killed by host SIGTERM before completing, so the receipt above is
the statement-level extraction rather than a `#print`-rendered diff. The
statement extraction is exact for the fields that matter here (name, kind,
statement text) and needs no elaboration.
