module

public import CatalanMeasure.GenD.Signed.SigmaCap
public import CatalanMeasure.GenD.Signed.Davis.PolynomialNorm
public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section
set_option Elab.async false
set_option profiler true

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionCore
open CatalanMeasure.Signed CatalanMeasure.Refinement CatalanMeasure.GenD.Signed.LogEval
noncomputable section

theorem exp_mul_lower {E F f : ℚ} (k : ℕ)
    (hE0 : 0 ≤ E) (hF0 : 0 ≤ F) (hE : (E : ℝ) ≤ Real.exp 1)
    (hF : (F : ℝ) ≤ Real.exp (f : ℝ)) :
    (E : ℝ) ^ k * (F : ℝ) ≤ Real.exp ((k : ℝ) + f) := by
  rw [Real.exp_add, show (k : ℝ) = (k : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact mul_le_mul (pow_le_pow_left₀ (by exact_mod_cast hE0) hE k) hF
    (by exact_mod_cast hF0) (by positivity)

theorem whole {c R B E F f : ℚ} (k : ℕ)
    (hR : 0 < R) (hB : 0 ≤ B) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hE : (E : ℝ) ≤ Real.exp 1) (hF : (F : ℝ) ≤ Real.exp (f : ℝ))
    (hy : (k : ℚ) + f ≤ -c / R) (hb : R ≤ B * (E ^ k * F)) :
    capInt (c : ℝ) (R : ℝ) (1 / 1000) ≤ (B : ℝ) := by
  have hr : 0 < (R : ℝ) := by exact_mod_cast hR
  have hbr : 0 ≤ (B : ℝ) := by exact_mod_cast hB
  have hle : (k : ℝ) + (f : ℝ) ≤ -((c : ℝ) / (R : ℝ)) := by
    have hy' : ((k : ℝ) + (f : ℝ)) ≤ -(c : ℝ) / (R : ℝ) := by exact_mod_cast hy
    simpa only [neg_div] using hy'
  have he := (exp_mul_lower k hE0 hF0 hE hF).trans (Real.exp_le_exp.mpr hle)
  have hh : (R : ℝ) ≤ (B : ℝ) * ((E : ℝ) ^ k * (F : ℝ)) := by exact_mod_cast hb
  have hu := hh.trans (mul_le_mul_of_nonneg_left he hbr)
  apply (capInt_le_mul_exp hr (by norm_num : 0 < (1 / 1000 : ℝ))).trans
  have inv : Real.exp ((c : ℝ) / (R : ℝ)) = (Real.exp (-((c : ℝ) / (R : ℝ))))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [inv, ← div_eq_mul_inv]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr hu

theorem clipped {c R B L U : ℚ} (hR : 0 < R)
    (hlogL : (L : ℝ) ≤ Real.log (1 / 1000)) (hlogU : Real.log (1 / 1000) ≤ (U : ℝ))
    (hbranch : U ≤ c / R) (hcap : (1/1000 : ℚ) * (c + R - R * L) ≤ B) :
    capInt (c : ℝ) (R : ℝ) (1/1000) ≤ (B : ℝ) := by
  have hr : 0 < (R : ℝ) := by exact_mod_cast hR
  have hbranch' : (U : ℝ) ≤ (c : ℝ) / (R : ℝ) := by exact_mod_cast hbranch
  have ht : (1 / 1000 : ℝ) ≤ Real.exp ((c : ℝ) / (R : ℝ)) := by
    rw [← Real.exp_log (by norm_num : 0 < (1 / 1000 : ℝ))]
    exact Real.exp_le_exp.mpr (hlogU.trans hbranch')
  have hc : (1/1000 : ℝ) * ((c : ℝ) + (R : ℝ) - (R : ℝ) * (L : ℝ)) ≤ (B : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcap
    push_cast at h
    exact h
  have hm := mul_le_mul_of_nonneg_left hlogL hr.le
  rw [capInt, if_pos hr, min_eq_right ht, capPrim]
  linarith only [hm, hc]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionCore

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionCore.whole
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionCore.clipped
