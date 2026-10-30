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

/-- The complete-period two-term increment cannot cancel when its
numerator is nonzero. -/
theorem reciprocal_step_ne_zero (a b q : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hnum : b - q * a ≠ 0) : a⁻¹ - q * b⁻¹ ≠ 0 := by
  intro hz
  apply hnum
  calc
    b - q * a = (a⁻¹ - q * b⁻¹) * (a * b) := by
      field_simp [ha, hb]
    _ = 0 := by rw [hz, zero_mul]

/-- The balanced-pair period increment is nonzero in every two-term frame.
The denominator nonvanishing hypotheses are precisely the single-level pole
conditions; the numerator uses only `1 ≤ j < q < p`. -/
theorem twoTerm_period_ne_zero {p q j h : ℕ} [Fact p.Prime]
    (hj : 1 ≤ j) (hjq : j < q) (hqp : q < p) (bit : Bool)
    (ha : ((h + 1 : ℕ) : ZMod p) ≠ 0)
    (hb : ((q * h + j + q * (if bit then 1 else 0) : ℕ) : ZMod p) ≠ 0) :
    (((h + 1 : ℕ) : ZMod p)⁻¹ - (q : ZMod p) *
      ((q * h + j + q * (if bit then 1 else 0) : ℕ) : ZMod p)⁻¹) ≠ 0 := by
  have hjp : j < p := lt_trans hjq hqp
  have hj0 : (j : ZMod p) ≠ 0 := by
    intro hz
    have hz' : (j : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hz
    have he := (ZMod.natCast_eq_natCast_iff' j 0 p).mp hz'
    rw [Nat.mod_eq_of_lt hjp, Nat.zero_mod] at he
    omega
  have hne : (j : ZMod p) ≠ (q : ZMod p) := by
    intro hz
    have he := (ZMod.natCast_eq_natCast_iff' j q p).mp hz
    rw [Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt hqp] at he
    omega
  apply reciprocal_step_ne_zero _ _ _ ha hb
  cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero,
    Nat.add_zero, Nat.mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  · convert sub_ne_zero.mpr hne using 1 <;> ring
  · convert hj0 using 1 <;> ring

end CatalanCore.Uniform.Content.UFSimple.WrapPivot
