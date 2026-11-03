module

public import CatalanMeasure.GenD.Signed.SigmaCap

@[expose] public section
set_option Elab.async false
set_option profiler true

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionInput
open CatalanMeasure.Signed

theorem monotone {c d r R θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hc : c ≤ d) (hd : d ≤ 0)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : 0 < R) : capInt c r θ ≤ capInt d R θ := by
  rcases hr.eq_or_lt with h0 | hp
  · subst r
    rw [capInt, if_neg (lt_irrefl 0), max_eq_left (hc.trans hd), mul_zero]
    exact capInt_nonneg hR.le hθ
  · let t := min (Real.exp (c / r)) θ
    let T := min (Real.exp (d / R)) θ
    have ht : 0 < t := lt_min (Real.exp_pos _) hθ
    have ht1 : t ≤ 1 := (min_le_right _ _).trans hθ1
    have hdiv : c / r ≤ d / R :=
      (div_le_div_of_nonneg_right hc hp.le).trans
        ((div_le_div_iff₀ hp hR).mpr (mul_le_mul_of_nonpos_left hrR hd))
    have htt : t ≤ T := min_le_min (Real.exp_le_exp.mpr hdiv) le_rfl
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    have hprim : capPrim c r t ≤ capPrim d R t := by
      unfold capPrim
      apply mul_le_mul_of_nonneg_left _ ht.le
      have hm := mul_le_mul_of_nonneg_left hrR (show 0 ≤ 1 - Real.log t by linarith)
      linarith only [hc, hm]
    rw [capInt, if_pos hp, capInt, if_pos hR]
    exact hprim.trans (capPrim_mono hR ht.le htt (min_le_left _ _))

end CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionInput

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionInput.monotone
