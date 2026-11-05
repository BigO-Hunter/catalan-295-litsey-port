module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner041

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

theorem w030_guard : QGuard Host.Phys041.lb w030 := by
  have ha : (w030.a : ℝ) = (7600000001/2300000000 : ℝ) := by norm_num [w030, intOdd, intWords]
  have hb : (w030.b : ℝ) = (33076923/10000000 : ℝ) := by norm_num [w030, intOdd, intWords]
  have hc0 : (w030.c0 : ℝ) = (-7600000001/100000000 : ℝ) := by norm_num [w030, intOdd, intWords]
  have hc1 : (w030.c1 : ℝ) = (23 : ℝ) := by norm_num [w030, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner041.w030_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
