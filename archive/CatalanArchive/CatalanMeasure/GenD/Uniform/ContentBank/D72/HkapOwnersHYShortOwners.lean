module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.HYShortOwners

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

private theorem ge_one_real {N : Nat} (hN : 0 < N) : (1 : ℝ) ≤ N := by
  exact_mod_cast hN

theorem w115_guard : QGuard shortHY10LB72 w115 := by
  have ha : (w115.a : ℝ) = (97/11 : ℝ) := by norm_num [w115, intOdd, intWords]
  have hb : (w115.b : ℝ) = (4409091/500000 : ℝ) := by norm_num [w115, intOdd, intWords]
  have hc0 : (w115.c0 : ℝ) = (177 : ℝ) := by norm_num [w115, intOdd, intWords]
  have hc1 : (w115.c1 : ℝ) = (-20 : ℝ) := by norm_num [w115, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w115_hcert72

theorem w121_guard : QGuard shortHY9LB72 w121 := by
  have ha : (w121.a : ℝ) = (97/10 : ℝ) := by norm_num [w121, intOdd, intWords]
  have hb : (w121.b : ℝ) = (8300000001/850000000 : ℝ) := by norm_num [w121, intOdd, intWords]
  have hc0 : (w121.c0 : ℝ) = (103 : ℝ) := by norm_num [w121, intOdd, intWords]
  have hc1 : (w121.c1 : ℝ) = (-21/2 : ℝ) := by norm_num [w121, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w121_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
