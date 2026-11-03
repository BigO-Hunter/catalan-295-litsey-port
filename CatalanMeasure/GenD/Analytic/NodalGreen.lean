module
public import CatalanMeasure.QuadCircle
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial
noncomputable section

/-! Sharp branch-free Chebyshev growth and the one-half Holder estimate
required by the approved Davis keyhole contract. No numerical certificate. -/

theorem one_add_half_sq_le_cosh {x : ℝ} (hx : 0 ≤ x) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => by positivity)
  rw [(Real.hasSum_cosh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem arcosh_one_add_le_sqrt {t : ℝ} (ht : 0 ≤ t) :
    Real.arcosh (1 + t) ≤ Real.sqrt (2 * t) := by
  have ha := Real.arcosh_nonneg (by linarith : 1 ≤ 1 + t)
  have h := one_add_half_sq_le_cosh ha
  rw [Real.cosh_arcosh (by linarith : 1 ≤ 1 + t)] at h
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * t)
  nlinarith [Real.sqrt_nonneg (2 * t)]

theorem arcosh_sub_le_arcosh_one_add {u v : ℝ} (hv : 1 ≤ v) (hvu : v ≤ u) :
    Real.arcosh u - Real.arcosh v ≤ Real.arcosh (1 + (u - v)) := by
  have hu : 1 ≤ u := hv.trans hvu
  have ht : 1 ≤ 1 + (u - v) := by linarith
  have ha := Real.arcosh_nonneg hu
  have hb := Real.arcosh_nonneg hv
  have hc := Real.arcosh_nonneg ht
  have hcosh : Real.cosh (Real.arcosh u) ≤
      Real.cosh (Real.arcosh v + Real.arcosh (1 + (u - v))) := by
    rw [Real.cosh_add, Real.cosh_arcosh hu, Real.cosh_arcosh hv, Real.cosh_arcosh ht]
    have hs := mul_nonneg (Real.sinh_nonneg_iff.mpr hb) (Real.sinh_nonneg_iff.mpr hc)
    have hp := mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr ht)
    nlinarith
  have h := Real.cosh_le_cosh.mp hcosh
  rw [abs_of_nonneg ha, abs_of_nonneg (add_nonneg hb hc)] at h
  linarith

theorem arcosh_abs_sub_le_sqrt {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    |Real.arcosh u - Real.arcosh v| ≤ Real.sqrt (2 * |u - v|) := by
  have key : ∀ a b : ℝ, 1 ≤ b → b ≤ a →
      |Real.arcosh a - Real.arcosh b| ≤ Real.sqrt (2 * |a - b|) := by
    intro a b hb hba
    have hmono := (Real.arcosh_le_arcosh (by linarith : 0 < b) (by linarith : 0 < a)).mpr hba
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (arcosh_sub_le_arcosh_one_add hb hba).trans (arcosh_one_add_le_sqrt (by linarith))
  rcases le_total v u with h | h
  · exact key u v hv h
  · simpa only [abs_sub_comm] using key v u hu h

def ellipseH (v : ℂ) : ℝ := (‖v - 1‖ + ‖v + 1‖) / 2
def ellipseLog (v : ℂ) : ℝ := Real.arcosh (ellipseH v)

theorem ellipseH_ge_one (v : ℂ) : 1 ≤ ellipseH v := by
  have h := norm_sub_le (v + 1) (v - 1)
  rw [show (v + 1) - (v - 1) = (2 : ℂ) by ring] at h
  norm_num only [Complex.norm_ofNat] at h
  unfold ellipseH
  linarith

theorem ellipseH_lipschitz (u v : ℂ) : |ellipseH u - ellipseH v| ≤ ‖u - v‖ := by
  have h1 := abs_norm_sub_norm_le (u - 1) (v - 1)
  have h2 := abs_norm_sub_norm_le (u + 1) (v + 1)
  rw [show (u - 1) - (v - 1) = u - v by ring] at h1
  rw [show (u + 1) - (v + 1) = u - v by ring] at h2
  have h3 := abs_add_le (‖u - 1‖ - ‖v - 1‖) (‖u + 1‖ - ‖v + 1‖)
  have he : ellipseH u - ellipseH v =
      ((‖u - 1‖ - ‖v - 1‖) + (‖u + 1‖ - ‖v + 1‖)) / 2 := by unfold ellipseH; ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem ellipseLog_holder (u v : ℂ) : |ellipseLog u - ellipseLog v| ≤ Real.sqrt (2 * ‖u - v‖) := by
  exact (arcosh_abs_sub_le_sqrt (ellipseH_ge_one u) (ellipseH_ge_one v)).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (ellipseH_lipschitz u v) (by norm_num)))

theorem norm_T_eval_le_exp_ellipseLog (K : ℕ) (v : ℂ) :
    ‖(Chebyshev.T ℂ (K : ℤ)).eval v‖ ≤ Real.exp ((K : ℝ) * ellipseLog v) := by
  have h := CatalanMeasure.norm_T_eval_le K v
  have he : Real.exp (ellipseLog v) = ellipseH v + Real.sqrt (ellipseH v ^ 2 - 1) :=
    Real.exp_arcosh (ellipseH_ge_one v)
  change _ ≤ (ellipseH v + Real.sqrt (ellipseH v ^ 2 - 1)) ^ K at h
  rw [← he, ← Real.exp_nat_mul] at h
  exact h

def nodalGreen (p : ℝ[X]) (m : ℕ) (z : ℂ) : ℝ :=
  ellipseLog ((p.map (algebraMap ℝ ℂ)).eval z) / (m : ℝ)

theorem nodalGreen_nonneg (p : ℝ[X]) (m : ℕ) (z : ℂ) : 0 ≤ nodalGreen p m z := by
  exact div_nonneg (Real.arcosh_nonneg (ellipseH_ge_one _)) (Nat.cast_nonneg _)

theorem nodalGreen_holder (p : ℝ[X]) {m : ℕ} (hm : 0 < m) (z w : ℂ) :
    |nodalGreen p m z - nodalGreen p m w| ≤
      Real.sqrt (2 * ‖(p.map (algebraMap ℝ ℂ)).eval z -
        (p.map (algebraMap ℝ ℂ)).eval w‖) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold nodalGreen
  rw [← sub_div, abs_div, abs_of_pos hmR]
  exact div_le_div_of_nonneg_right (ellipseLog_holder _ _) hmR.le

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.one_add_half_sq_le_cosh
#print axioms CatalanMeasure.GenD.Analytic.arcosh_one_add_le_sqrt
#print axioms CatalanMeasure.GenD.Analytic.arcosh_sub_le_arcosh_one_add
#print axioms CatalanMeasure.GenD.Analytic.arcosh_abs_sub_le_sqrt
#print axioms CatalanMeasure.GenD.Analytic.ellipseH_ge_one
#print axioms CatalanMeasure.GenD.Analytic.ellipseH_lipschitz
#print axioms CatalanMeasure.GenD.Analytic.ellipseLog_holder
#print axioms CatalanMeasure.GenD.Analytic.norm_T_eval_le_exp_ellipseLog
#print axioms CatalanMeasure.GenD.Analytic.nodalGreen_nonneg
#print axioms CatalanMeasure.GenD.Analytic.nodalGreen_holder
