module
public import CatalanMeasure.GenD.Signed.LogEval
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
open CatalanMeasure.GenD.Signed.LogEval
noncomputable section

theorem log_interval {n : ℕ} {q v e lo hi : ℚ}
    (h : logQ n q = some (v,e)) (hl : lo ≤ v-e) (hu : v+e ≤ hi) :
    (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ) := by
  have hh := (logQ_spec h).2
  change |Real.log (q:ℝ)-(v:ℝ)| ≤ (e:ℝ) at hh
  have hrL : (lo:ℝ) ≤ (v:ℝ)-(e:ℝ) := by exact_mod_cast hl
  have hrU : (v:ℝ)+(e:ℝ) ≤ (hi:ℝ) := by exact_mod_cast hu
  constructor <;> linarith [(abs_le.mp hh).1,(abs_le.mp hh).2]

def weightedUpper (c lo hi : ℚ) : ℚ := if 0 ≤ c then c*hi else c*lo

theorem weighted_log_upper (c : ℚ) {q lo hi : ℚ}
    (h : (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ)) :
    (c:ℝ)*Real.log (q:ℝ) ≤ ((weightedUpper c lo hi:ℚ):ℝ) := by
  by_cases hc : 0 ≤ c
  · have hr : (0:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have hh := mul_le_mul_of_nonneg_left h.2 hr
    simpa [weightedUpper,hc] using hh
  · have hr : (c:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    have hh := mul_le_mul_of_nonpos_left h.1 hr
    simpa [weightedUpper,hc] using hh

/-- One monotonicity step lifts a cached endpoint log to a whole interval. -/
theorem weighted_site_upper (c site q lo hi : ℚ) (x : ℝ)
    (hq : (0:ℚ) < q) (hx : 0 < |x-(site:ℝ)|)
    (hd : if 0 ≤ c then |x-(site:ℝ)| ≤ (q:ℝ) else (q:ℝ) ≤ |x-(site:ℝ)|)
    (h : (lo:ℝ) ≤ Real.log (q:ℝ) ∧ Real.log (q:ℝ) ≤ (hi:ℝ)) :
    (c:ℝ)*Real.log |x-(site:ℝ)| ≤ ((weightedUpper c lo hi:ℚ):ℝ) := by
  have hb := weighted_log_upper c h
  by_cases hc : 0 ≤ c
  · have hr : (0:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    have he : |x-(site:ℝ)| ≤ (q:ℝ) := by simpa [hc] using hd
    exact (mul_le_mul_of_nonneg_left (Real.log_le_log hx he) hr).trans hb
  · have hr : (c:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    have he : (q:ℝ) ≤ |x-(site:ℝ)| := by simpa [hc] using hd
    have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
    exact (mul_le_mul_of_nonpos_left (Real.log_le_log hqr he) hr).trans hb
end
end CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer.log_interval
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer.weighted_log_upper
#print axioms CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer.weighted_site_upper
