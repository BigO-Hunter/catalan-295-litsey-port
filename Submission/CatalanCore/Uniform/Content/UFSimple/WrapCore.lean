module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapGeometry
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPivot

@[expose] public section

/-! # Polynomial form of the actual reordered mixed core

Only the retained original common indices carry a spectral diagonal.
The actual balanced rows and columns are selected independently.
-/

open Matrix Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapCore

open WrapGeometry

variable {R F ι : Type*} [CommRing R] [Field F] [Fintype ι] [DecidableEq ι]

/-- Constant part of the actual mixed core. -/
noncomputable def constantCore (s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (K : Matrix (ι ⊕ Fin (s+l)) (ι ⊕ Fin (s+l)) R) :
    Matrix (ι ⊕ Fin (2*l-1)) (ι ⊕ Fin (2*l-1)) R :=
  K.submatrix (fun i => rowFullEquiv ι s l hl hls (Sum.inl i))
    (fun i => colFullEquiv ι s l hl hls (Sum.inl i))

/-- Core of the independently reordered original spectral lift. -/
noncomputable def liftCore (s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (K : Matrix (ι ⊕ Fin (s+l)) (ι ⊕ Fin (s+l)) R) :
    Matrix (ι ⊕ Fin (2*l-1)) (ι ⊕ Fin (2*l-1)) R[X] :=
  ((K.map C + Matrix.fromBlocks ((X : R[X]) • (1 : Matrix ι ι R[X])) 0 0 0).submatrix
    (rowFullEquiv ι s l hl hls) (colFullEquiv ι s l hl hls)).toBlocks₁₁

/-- Actual mixed core equals its constant part plus ONLY the original
common spectral diagonal. -/
theorem liftCore_eq (s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (K : Matrix (ι ⊕ Fin (s+l)) (ι ⊕ Fin (s+l)) R) :
    liftCore s l hl hls K = (constantCore s l hl hls K).map C +
      Matrix.fromBlocks ((X : R[X]) • (1 : Matrix ι ι R[X])) 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- Reduction of the actual core has a constant balanced block and a
characteristic common block, with unrelated mixed off-diagonal blocks. -/
theorem map_liftCore (phi : R →+* F) (s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (K : Matrix (ι ⊕ Fin (s+l)) (ι ⊕ Fin (s+l)) R) :
    (liftCore s l hl hls K).map (Polynomial.mapRingHom phi) =
      Matrix.fromBlocks
        ((X : F[X]) • (1 : Matrix ι ι F[X]) +
          ((constantCore s l hl hls K).toBlocks₁₁.map phi).map C)
        (((constantCore s l hl hls K).toBlocks₁₂.map phi).map C)
        (((constantCore s l hl hls K).toBlocks₂₁.map phi).map C)
        (((constantCore s l hl hls K).toBlocks₂₂.map phi).map C) := by
  rw [liftCore_eq]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i=j
    · subst j
      simp [Matrix.one_apply, add_comm, Matrix.toBlocks₁₁]
    · simp [Matrix.one_apply, hij, Matrix.toBlocks₁₁]
  · simp [Matrix.toBlocks₁₂]
  · simp [Matrix.toBlocks₂₁]
  · simp [Matrix.toBlocks₂₂]

/-- Nonzero balanced determinant proves actual mixed-core primitivity. -/
theorem det_map_liftCore_ne_zero (phi : R →+* F) (s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (K : Matrix (ι ⊕ Fin (s+l)) (ι ⊕ Fin (s+l)) R)
    (hD : ((constantCore s l hl hls K).toBlocks₂₂.map phi).det ≠ 0) :
    Polynomial.mapRingHom phi (liftCore s l hl hls K).det ≠ 0 := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_liftCore]
  exact WrapPivot.mixed_det_ne_zero _ _ _ _ hD

end CatalanCore.Uniform.Content.UFSimple.WrapCore
