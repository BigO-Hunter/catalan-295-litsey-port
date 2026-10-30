module

public import CatalanMeasure.GenD.Analytic.GroupedProduct
public import CatalanMeasure.Parametric.PopulationPhysicalValue

/-!
# The per-row comparison `hrow` under the quadrature cap

`signedSecondSheetFixed` (`RealPlaceFixed`) asks, for the marked rows `y ∈ G`,

`log markedSheetWeight P N y ≤ n * populationPhysicalFreeField P N y + c₂ N`.

The free-row field carries a `log |y|` and a `log (1 - y)` term that the marked-row weight
`(2 / (1 + y²))^(n-g-1)` does not have (the factor `|y|^{g-(n-1)}` cancels against the common row
factor).  If `G` keeps `|y| ≥ a` and `1 - y ≥ b` (the quadrature cap), each such term costs a
bounded multiple of `|log a|`, `|log b|`, so `hrow` holds with the explicit constant
`rowCapConst P a b`, which is linear in the parameters:

`rowCapConst P a b = (n₀ + (n₀+b₀+q₀+g₀+h₀)) log 2 + (b₀+q₀+2g₀) |log a| + 2 h₀ |log b|`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open CatalanMeasure.Parametric CatalanMeasure.GenD.Analytic Set Filter

noncomputable section

/-- The explicit constant of `hrow_of_cap`. -/
def rowCapConst (P : Parameters) (a b : ℝ) : ℝ :=
  ((P.n0 : ℝ) + ((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0)) * Real.log 2 +
    ((P.b0 : ℝ) + P.q0 + 2 * P.g0) * |Real.log a| + 2 * (P.h0 : ℝ) * |Real.log b|

/-- Fixed `N`: the row comparison for one row on the cap. -/
theorem log_markedSheetWeight_le_cap (P : Parameters) (N : ℕ) (hn : 0 < P.n N)
    {y a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hya : a ≤ |y|) (hyb : b ≤ 1 - y) :
    Real.log (markedSheetWeight P N y) ≤
      (P.n N : ℝ) * populationPhysicalFreeField P N y +
        (((P.n N : ℝ) + (P.H N : ℝ)) * Real.log 2 +
          (P.A N : ℝ) * |Real.log a| + 2 * (P.h N : ℝ) * |Real.log b|) := by
  have hnr : (P.n N : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hy2 : y ^ 2 < 1 := by
    have h1 := hy.1
    have h2 := hy.2
    nlinarith
  set L : ℝ := Real.log (1 + y ^ 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [sq_nonneg y])
  have hL1 : L ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith)
  have hy0 : 0 < |y| := lt_of_lt_of_le ha hya
  have hlogy : Real.log a ≤ Real.log |y| := Real.log_le_log ha hya
  have hlog1 : Real.log b ≤ Real.log (1 - y) := Real.log_le_log hb hyb
  have hfield : (P.n N : ℝ) * populationPhysicalFreeField P N y =
      (P.A N : ℝ) * Real.log |y| + 2 * (P.h N : ℝ) * Real.log (1 - y) -
        (P.H N : ℝ) * L + 2 * L := by
    unfold populationPhysicalFreeField paramPopulationRowField
    rw [← hL]
    field_simp
    ring
  rw [hfield, log_markedSheetWeight, ← hL]
  set m : ℝ := ((P.n N - P.g N - 1 : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmn : m ≤ (P.n N : ℝ) := by
    rw [hm]; exact_mod_cast (by omega : P.n N - P.g N - 1 ≤ P.n N)
  have hA0 : (0 : ℝ) ≤ (P.A N : ℝ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ (P.h N : ℝ) := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) ≤ (P.H N : ℝ) := Nat.cast_nonneg _
  have h1 : (P.A N : ℝ) * Real.log a ≤ (P.A N : ℝ) * Real.log |y| :=
    mul_le_mul_of_nonneg_left hlogy hA0
  have h2 : (P.h N : ℝ) * Real.log b ≤ (P.h N : ℝ) * Real.log (1 - y) :=
    mul_le_mul_of_nonneg_left hlog1 hh0
  have h3 : (P.A N : ℝ) * (-|Real.log a|) ≤ (P.A N : ℝ) * Real.log a :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hA0
  have h4 : (P.h N : ℝ) * (-|Real.log b|) ≤ (P.h N : ℝ) * Real.log b :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hh0
  have h5 : (P.H N : ℝ) * L ≤ (P.H N : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left hL1 hH0
  have h6 : 0 ≤ m * L := mul_nonneg hm0 hL0
  have h7 : m * Real.log 2 ≤ (P.n N : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hmn (Real.log_nonneg (by norm_num))
  nlinarith

/-- **`hrow` from the quadrature cap.**  If `G` keeps `|y| ≥ a` and `1 - y ≥ b`, the per-row
comparison of `signedSecondSheetFixed` holds eventually in `N` with `c₂ = rowCapConst P a b`
(or any larger constant). -/
theorem hrow_of_cap {P : Parameters} (hP : Admissible P) (G : ℝ → Prop) {a b c2 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hcap : ∀ y, G y → a ≤ |y| ∧ b ≤ 1 - y)
    (hc2 : rowCapConst P a b ≤ c2) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → y ≠ 0 → G y →
      Real.log (markedSheetWeight P N y) ≤
        (P.n N : ℝ) * populationPhysicalFreeField P N y + c2 * N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN y hy _ hG
  obtain ⟨hya, hyb⟩ := hcap y hG
  refine (log_markedSheetWeight_le_cap P N (n_pos hP hN) ha hb hy hya hyb).trans ?_
  have hcost : ((P.n N : ℝ) + (P.H N : ℝ)) * Real.log 2 +
      (P.A N : ℝ) * |Real.log a| + 2 * (P.h N : ℝ) * |Real.log b| =
      rowCapConst P a b * N := by
    unfold rowCapConst
    simp only [Parameters.n, Parameters.H, Parameters.C, Parameters.L, Parameters.A,
      Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    push_cast
    ring
  rw [hcost]
  have : rowCapConst P a b * N ≤ c2 * N :=
    mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg _)
  linarith

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.log_markedSheetWeight_le_cap
#print axioms CatalanMeasure.Signed.hrow_of_cap
