module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
noncomputable section

/-- A convenient small-v bound from arctan(t)<=t; no integration is needed. -/
theorem arccos_one_sub_le_sqrt_div {v V : ℝ} (hv : 0 ≤ v) (hvV : v ≤ V) (hV : V < 1) :
    Real.arccos (1 - v) ≤ Real.sqrt (2 * v) / (1 - V) := by
  have hp : 0 < 1 - v := by linarith
  rw [Real.arccos_eq_arctan hp]
  calc
    _ ≤ Real.sqrt (1 - (1 - v) ^ 2) / (1 - v) := Real.arctan_le_self (by positivity)
    _ ≤ Real.sqrt (2 * v) / (1 - V) :=
      div_le_div₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v]))
        (by linarith) (by linarith)

/-- The frozen Davis tail needs only the coarse derivative bound M<=20000.
The coefficient150 leaves ample room below the approved C1 at N>=10. -/
theorem arccos_tail_le_150 {x v : ℝ} (hxc : (999 / 1000 : ℝ) ≤ x)
    (hx1 : x ≤ 1) (hv : 0 ≤ v)
    (hvs : v ≤ 20000 * (1 - x) ^ 2 / (1 + x ^ 2)) :
    Real.arccos (1 - v) ≤ 150 * (1 - x) := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hprod := (le_div_iff₀ hd).mp hvs
  have hden : (19 / 10 : ℝ) ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 999 / 1000)]
  have hprod' := mul_le_mul_of_nonneg_left hden hv
  have ha : 0 ≤ 1 - x := by linarith
  have haub : 1 - x ≤ (1 / 1000 : ℝ) := by linarith
  have ha2 : (1 - x) ^ 2 ≤ (1 / 1000000 : ℝ) := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr haub)]
  have hvV : v ≤ (1 / 80 : ℝ) := by nlinarith
  have hv2 : 2 * v ≤ (148 * (1 - x)) ^ 2 := by
    nlinarith [sq_nonneg (1 - x)]
  have hroot : Real.sqrt (2 * v) ≤ 148 * (1 - x) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * v)
    nlinarith [Real.sqrt_nonneg (2 * v)]
  calc
    _ ≤ Real.sqrt (2 * v) / (1 - (1 / 80 : ℝ)) :=
      arccos_one_sub_le_sqrt_div hv hvV (by norm_num)
    _ ≤ (148 * (1 - x)) / (1 - (1 / 80 : ℝ)) :=
      div_le_div_of_nonneg_right hroot (by norm_num)
    _ ≤ 150 * (1 - x) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 80)).mpr
      nlinarith

theorem davis_tail_count_coefficient {N K : ℕ} (hN : 10 ≤ N)
    (hK : 130 * K ≤ 66 * N + 130) :
    (K : ℝ) * 150 / Real.pi ≤ (467829 / 1000000 : ℝ) * (72 * N) := by
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hKR : (130 : ℝ) * K ≤ 66 * N + 130 := by exact_mod_cast hK
  have hπ : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hp := mul_le_mul_of_nonneg_left hπ
    (show 0 ≤ (467829 / 1000000 : ℝ) * (72 * N) by positivity)
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.arccos_one_sub_le_sqrt_div
#print axioms CatalanMeasure.GenD.Analytic.arccos_tail_le_150
#print axioms CatalanMeasure.GenD.Analytic.davis_tail_count_coefficient
