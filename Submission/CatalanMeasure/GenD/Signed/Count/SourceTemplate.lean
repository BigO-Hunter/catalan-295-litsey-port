module

public import Submission.CatalanMeasure.GenD.Signed.Count.EventualBounds

@[expose] public section
set_option Elab.async false

/-!
# Count layer: source template (CONSUMER SIDE ONLY, producer NOT proved)

What is proved here: the composite that a physical source chart feeds.  A chart supplies, at each
prime `p` of its window,

* a `CountHost` for the FULL profile space `V` (the ScalarJetHost layer: atom map `xi`, joint-kernel
  `dom`/`inj`/`kill` for the actual slot system of `(P, N, p)`), whose maps `B c` are the cumulative
  jet-level charts, with central coefficient `m = p` and integer widths;
* the decomposition of the integer coefficients `m = N c0 + bc`, `width c = N w0 c + bw c` with
  uniformly bounded offsets;
* a row-space relation (P1/P5/P7 of `Relations`, with caps proved by `FixedRank`/`SlotGauge`) giving a
  subspace `S ≤ Dual V` with `val ≤ euler c0 w0 (rowSpace ∘ B) S`.

`nullity_ge_scaled` then gives `N · val - d (1 + |C|) B0 ≤ ν(N,p)` with `d = dim V`, exactly the
input of `NullityConstructor.countLB`.

NOT proved here (the producer): the construction of the `CountHost` from the actual design, i.e. the
full-tiling / Frobenius-split / Taylor-graph bijection of the physical-prefix theorem (sections 3-7)
for an arbitrary admissible design and source chart, with the used raw and p-step-shifted indices in
`[b, L)`, `L ≤ H`, and the identification of the jets with `rowSpace`.  That is the open obligation of
this layer.
-/

namespace CatalanMeasure.GenD.Signed.Count.SourceTemplate
open Module Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Signed.Count.DualRestriction CatalanMeasure.GenD.Signed.Count.Relations
  CatalanMeasure.GenD.Signed.Count.EventualBounds CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {C : Type*} [Fintype C]
variable {S : SlotSystem P N p} {m : ℕ} {e width : C → ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin m → ZMod p} {a r : ℕ}

/-- **Composite.**  Host + leading/offset decomposition + row-space relation ⟹ nullity bound. -/
theorem nullity_ge_scaled (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hq : P.q N = a * p + r)
    (c0 bc B0 val : ℝ) (w0 bw : C → ℝ)
    (hm : (m : ℝ) = N * c0 + bc) (hw : ∀ c, (width c : ℝ) = N * w0 c + bw c)
    (hbc : |bc| ≤ B0) (hbw : ∀ c, |bw c| ≤ B0)
    (hrel : ∃ Sd : Submodule (ZMod p) (Dual (ZMod p) V),
      val ≤ euler c0 w0 (fun c => rowSpace (B c)) Sd) :
    N * val - finrank (ZMod p) V * (1 + Fintype.card C) * B0 ≤ (nullity P N p : ℝ) := by
  obtain ⟨Sd, hSd⟩ := hrel
  have h1 := nullity_ge_euler I hP hN hp2 hH hq Sd
  have h2 := euler_scaled_ge (N : ℝ) c0 bc B0 w0 bw (fun c => rowSpace (B c)) Sd hbc hbw
  have e1 : euler (m : ℝ) (fun c => (width c : ℝ)) (fun c => rowSpace (B c)) Sd =
      euler (N * c0 + bc) (fun c => N * w0 c + bw c) (fun c => rowSpace (B c)) Sd := by
    rw [hm]; congr 1; funext c; exact hw c
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h3 : (N : ℝ) * val ≤ N * euler c0 w0 (fun c => rowSpace (B c)) Sd :=
    mul_le_mul_of_nonneg_left hSd hN0
  linarith

end
end CatalanMeasure.GenD.Signed.Count.SourceTemplate
#print axioms CatalanMeasure.GenD.Signed.Count.SourceTemplate.nullity_ge_scaled
