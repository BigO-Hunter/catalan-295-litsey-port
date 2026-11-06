module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace CatalanMeasure.GenD.Signed.AnalyticZero
open Real
noncomputable section

/-! The two shared analytic zero-region scalar bounds (plan row C14, ROUTE-I-CAP-MAJORANTS M11).
The source-geometry inequalities bounding the field by these log expressions are separate
hypotheses and are not proved here. No numerical certificate: `log 10 > 23/10` follows from
`Real.sum_range_le_log_div` at `x = 1/9`, `n = 1` and `Real.log_two_gt_d9`. -/

/-- `log (5/4) ≥ 2/9`, from the one-term series `Real.sum_range_le_log_div`. -/
theorem log_five_fourths_ge : (2 / 9 : ℝ) ≤ Real.log (5 / 4) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 1
  have e : (1 + 1 / 9 : ℝ) / (1 - 1 / 9) = 5 / 4 := by norm_num
  rw [e] at h
  norm_num [Finset.sum_range_one] at h
  linarith

/-- `log 10 > 23/10`. -/
theorem log_ten_gt : (23 / 10 : ℝ) < Real.log 10 := by
  have h2 := Real.log_two_gt_d9
  have h54 := log_five_fourths_ge
  have e : (10 : ℝ) = 2 ^ 3 * (5 / 4) := by norm_num
  have : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  rw [this]
  linarith

/-- Free-row zero-region cap (exact M11 form). -/
theorem zero_free_cap_sharp (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 1000) :
    (11 / 29) * Real.log t + (119 / 29) * Real.log (1 + t) - 2 * Real.log (1 - t)
      ≤ -75647219 / 28971000 := by
  have hl10 := log_ten_gt
  have hlt : Real.log t ≤ -(3 * Real.log 10) := by
    have : Real.log t ≤ Real.log (1 / 1000) := Real.log_le_log h0 h1
    have e : Real.log (1 / 1000 : ℝ) = -(3 * Real.log 10) := by
      rw [one_div, Real.log_inv, show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have hp : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
    linarith
  have hm : -Real.log (1 - t) ≤ 1 / 999 := by
    have h1t : 0 < 1 - t := by linarith
    have := Real.one_sub_inv_le_log_of_pos h1t
    have h2 : (1 - t)⁻¹ ≤ 1000 / 999 := by
      rw [inv_le_comm₀ h1t (by norm_num)]
      norm_num; linarith
    linarith
  linarith

/-- Free-row zero-region cap. -/
theorem zero_free_cap (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 1000) :
    (11 / 29) * Real.log t + (119 / 29) * Real.log (1 + t) - 2 * Real.log (1 - t)
      ≤ -32247 / 12500 := by
  have := zero_free_cap_sharp t h0 h1
  linarith

/-- Near-field zero-region cap (exact M11 form). -/
theorem zero_near_cap_sharp (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1 / 10) :
    (24 / 29) * Real.log y + Real.log (1 + y) - 29557 / 200000 ≤ -11317153 / 5800000 := by
  have hl10 := log_ten_gt
  have hly : Real.log y ≤ -Real.log 10 := by
    have : Real.log y ≤ Real.log (1 / 10) := Real.log_le_log h0 h1
    rw [one_div, Real.log_inv] at this
    exact this
  have hp : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by linarith)
    linarith
  linarith

/-- Near-field zero-region cap at the live cap `-9783/10000`. -/
theorem zero_near_cap (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1 / 10) :
    (24 / 29) * Real.log y + Real.log (1 + y) - 29557 / 200000 ≤ -9783 / 10000 := by
  have := zero_near_cap_sharp y h0 h1
  linarith

/-- The same near-field bound at the original audited cap `-122/125`. -/
theorem zero_near_cap_122 (y : ℝ) (h0 : 0 < y) (h1 : y ≤ 1 / 10) :
    (24 / 29) * Real.log y + Real.log (1 + y) - 29557 / 200000 ≤ -122 / 125 := by
  have := zero_near_cap_sharp y h0 h1
  linarith

/-- Marked-anchor free-row cap `-5127/2000`. -/
theorem zero_free_cap_marked (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 1000) :
    (11 / 29) * Real.log t + (119 / 29) * Real.log (1 + t) - 2 * Real.log (1 - t)
      ≤ -5127 / 2000 := by
  have := zero_free_cap_sharp t h0 h1
  linarith

end
end CatalanMeasure.GenD.Signed.AnalyticZero
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.log_ten_gt
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_free_cap_sharp
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_free_cap
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_near_cap_sharp
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_near_cap
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_near_cap_122
#print axioms CatalanMeasure.GenD.Signed.AnalyticZero.zero_free_cap_marked
