module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Primitive mixed cores from constant balanced pivots

Only the original common block has the spectral diagonal. A constant
invertible balanced block leaves a characteristic matrix after elimination,
so the whole mixed core has nonzero polynomial determinant.
-/

open Matrix Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapPivot

variable {K ι κ : Type*} [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Augmenting a spectral common core by any invertible constant mixed block
preserves primitivity. The two off-diagonal blocks may be unrelated. -/
theorem mixed_det_ne_zero (A : Matrix ι ι K) (B : Matrix ι κ K)
    (E : Matrix κ ι K) (D : Matrix κ κ K) (hD : D.det ≠ 0) :
    (Matrix.fromBlocks ((X : K[X]) • (1 : Matrix ι ι K[X]) + A.map C)
      (B.map C) (E.map C) (D.map C)).det ≠ 0 := by
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hmap : (D.map C).det = C D.det := (RingHom.map_det C D).symm
  have hunit : IsUnit (D.map C).det := by
    rw [hmap]
    exact hu.map C
  letI : Invertible (D.map C) := Matrix.invertibleOfIsUnitDet _ hunit
  have hinv : ⅟(D.map C) = (D⁻¹).map C := by
    apply invOf_eq_right_inv
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv D hu,
      Matrix.map_one _ C.map_zero C.map_one]
  have hschur : (X : K[X]) • (1 : Matrix ι ι K[X]) + A.map C -
      B.map C * ⅟(D.map C) * E.map C =
      (X : K[X]) • (1 : Matrix ι ι K[X]) + (A - B * D⁻¹ * E).map C := by
    rw [hinv, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
    abel
  rw [Matrix.det_fromBlocks₂₂, hmap, hschur]
  apply mul_ne_zero (C_ne_zero.mpr hD)
  have hm : ((X : K[X]) • (1 : Matrix ι ι K[X]) +
      (A - B * D⁻¹ * E).map C).det.Monic :=
    Polynomial.leadingCoeff_det_X_one_add_C _
  exact hm.ne_zero


end CatalanCore.Uniform.Content.UFSimple.WrapPivot
