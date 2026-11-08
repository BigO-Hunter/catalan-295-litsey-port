module

public import Submission.CatalanCore.Uniform.Content.UFMember.FullWit

@[expose] public section

/-! # Divided Schur complement of an actual mixed core

The primitive core may have different row and column nodes. Only their
residue colours agree. Distinctness is required of the REMAINING surplus
rows and columns, after the balanced pairs have been absorbed into the core.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFSimple.WrapSchur

variable {p : ℕ} [Fact p.Prime] {C B : Type}
  [Fintype C] [DecidableEq C] [Fintype B] [DecidableEq B]

/-- The actual mixed Schur numerator is divisible by p. -/
theorem mixed_schur_dvd (A : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X])
    (row col : C ⊕ B → ZMod p)
    (hcore : ∀ a : C, row (Sum.inl a) = col (Sum.inl a))
    (hzero : ∀ i j, row i ≠ col j → phiP p (A i j) = 0)
    (hdet : phiP p A.toBlocks₁₁.det ≠ 0)
    (hdist : ∀ i j : B, row (Sum.inr i) ≠ col (Sum.inr j)) (i j : B) :
    Polynomial.C ((p : ℕ) : LocRing p) ∣
      (A.toBlocks₁₁.det • A.toBlocks₂₂ -
        A.toBlocks₂₁ * A.toBlocks₁₁.adjugate * A.toBlocks₁₂) i j := by
  set Q := A.toBlocks₁₁
  rw [← phiP_eq_zero_iff]
  have hQ0 : ∀ a b : C, row (Sum.inl a) ≠ row (Sum.inl b) →
      (Q.map (phiP p)) a b = 0 := by
    intro a b hab
    exact hzero _ _ (by rwa [← hcore b])
  have hdetQ : (Q.map (phiP p)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet
  have hadj : ∀ a b : C, row (Sum.inl a) ≠ row (Sum.inl b) →
      phiP p (Q.adjugate a b) = 0 := by
    intro a b hab
    have hh := adjugate_eq_zero_of_color (Q.map (phiP p)) (fun a => row (Sum.inl a))
      hQ0 hdetQ a b hab
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate] at hh
    exact hh
  have hT : phiP p (A.toBlocks₂₂ i j) = 0 := hzero _ _ (hdist i j)
  have hS : ∀ a : C, row (Sum.inr i) ≠ row (Sum.inl a) →
      phiP p (A.toBlocks₂₁ i a) = 0 := by
    intro a ha
    exact hzero _ _ (by rwa [← hcore a])
  have hR : ∀ b : C, row (Sum.inl b) ≠ col (Sum.inr j) →
      phiP p (A.toBlocks₁₂ b j) = 0 := fun b hb => hzero _ _ hb
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
    hT, mul_zero, zero_sub, neg_eq_zero, Matrix.mul_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_mul, map_mul]
  by_cases h1 : row (Sum.inr i) = row (Sum.inl a)
  · by_cases h2 : row (Sum.inl a) = row (Sum.inl b)
    · have h3 : row (Sum.inl b) ≠ col (Sum.inr j) := by
        rw [← h2, ← h1]
        exact hdist i j
      rw [hR b h3, mul_zero]
    · rw [hadj a b h2, mul_zero, zero_mul]
  · rw [hS a h1, zero_mul, zero_mul]

/-- Divided actual Schur numerator, without a fictitious common core. -/
noncomputable def dividedSchur (A : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X]) :
    Matrix B B (LocRing p)[X] :=
  Matrix.of fun i j => quotP p
    ((A.toBlocks₁₁.det • A.toBlocks₂₂ -
      A.toBlocks₂₁ * A.toBlocks₁₁.adjugate * A.toBlocks₁₂) i j)

/-- Exact factorization needed by the existing three-level constructor. -/
theorem mixed_schur_eq (A : Matrix (C ⊕ B) (C ⊕ B) (LocRing p)[X])
    (row col : C ⊕ B → ZMod p)
    (hcore : ∀ a : C, row (Sum.inl a) = col (Sum.inl a))
    (hzero : ∀ i j, row i ≠ col j → phiP p (A i j) = 0)
    (hdet : phiP p A.toBlocks₁₁.det ≠ 0)
    (hdist : ∀ i j : B, row (Sum.inr i) ≠ col (Sum.inr j)) :
    A.toBlocks₁₁.det • A.toBlocks₂₂ -
      A.toBlocks₂₁ * A.toBlocks₁₁.adjugate * A.toBlocks₁₂ =
        Polynomial.C ((p : ℕ) : LocRing p) • dividedSchur A := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, dividedSchur, Matrix.of_apply,
    quotP_spec p (mixed_schur_dvd A row col hcore hzero hdet hdist i j)]

end CatalanCore.Uniform.Content.UFSimple.WrapSchur
