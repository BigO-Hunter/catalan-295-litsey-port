module

public import CatalanMeasure.ChebyshevNodes
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Finset
noncomputable section

theorem finset_card_le_real_index_bound {K : ℕ} (s : Finset (Fin K)) {T : ℝ}
    (hT : 0 ≤ T) (hindex : ∀ j ∈ s, (j : ℝ) ≤ T) : (s.card : ℝ) ≤ T + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := s.max'_mem hs
    have hsub : s ⊆ Finset.Iic j := by
      intro k hk
      exact Finset.mem_Iic.mpr (s.le_max' k hk)
    have hc : s.card ≤ j.val + 1 := by
      simpa only [Fin.card_Iic] using Finset.card_le_card hsub
    have hcR : (s.card : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hc
    linarith [hindex j hj]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

theorem chebX_tail_index_bound {K : ℕ} (j : Fin K) {u : ℝ}
    (hu : u ≤ CatalanMeasure.chebX K j) :
    (j : ℝ) ≤ (K : ℝ) * Real.arccos u / Real.pi := by
  have hK : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by have := j.isLt; omega)
  have ha := CatalanMeasure.chebAngle_mem j.isLt
  have ht := Real.arccos_le_arccos hu
  rw [CatalanMeasure.chebX, Real.arccos_cos ha.1.le ha.2.le] at ht
  unfold CatalanMeasure.chebAngle at ht
  have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp ht
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_pos]

theorem chebX_tail_count {K : ℕ} (u : ℝ) :
    ((Finset.univ.filter (fun j : Fin K => u ≤ CatalanMeasure.chebX K j)).card : ℝ) ≤
      (K : ℝ) * Real.arccos u / Real.pi + 1 := by
  classical
  apply finset_card_le_real_index_bound
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg K) (Real.arccos_nonneg u)) Real.pi_pos.le
  · intro j hj
    exact chebX_tail_index_bound j (Finset.mem_filter.mp hj).2

theorem one_sub_chebX_ge_midpoint_gap {K : ℕ} (j : Fin K) :
    1 / (2 * (K : ℝ) ^ 2) ≤ 1 - CatalanMeasure.chebX K j := by
  have hK : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by have := j.isLt; omega)
  have ha := CatalanMeasure.chebAngle_mem j.isLt
  have hsmall : Real.pi / (2 * K) ≤ CatalanMeasure.chebAngle K j := by
    unfold CatalanMeasure.chebAngle
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j.val) Real.pi_pos.le]
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ Real.pi / (2 * K)) ha.1.le).mpr hsmall
  have hcos := Real.cos_le_one_sub_mul_cos_sq (x := CatalanMeasure.chebAngle K j)
    (by rw [abs_of_nonneg ha.1.le]; exact ha.2.le)
  have he : 1 / (2 * (K : ℝ) ^ 2) =
      2 / Real.pi ^ 2 * (Real.pi / (2 * K)) ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  unfold CatalanMeasure.chebX
  have ht := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ (2 : ℝ) / Real.pi ^ 2 by positivity)
  linarith

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.finset_card_le_real_index_bound
#print axioms CatalanMeasure.GenD.Analytic.chebX_tail_index_bound
#print axioms CatalanMeasure.GenD.Analytic.chebX_tail_count
#print axioms CatalanMeasure.GenD.Analytic.one_sub_chebX_ge_midpoint_gap
