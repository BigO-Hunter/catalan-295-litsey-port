module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner008

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

theorem w097_guard : QGuard Host.Phys008.lb w097 := by
  have ha : (w097.a : ℝ) = (7200000001/1100000000 : ℝ) := by norm_num [w097, intOdd, intWords]
  have hb : (w097.b : ℝ) = (49499999/7500000 : ℝ) := by norm_num [w097, intOdd, intWords]
  have hc0 : (w097.c0 : ℝ) = (-7200000001/100000000 : ℝ) := by norm_num [w097, intOdd, intWords]
  have hc1 : (w097.c1 : ℝ) = (11 : ℝ) := by norm_num [w097, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner008.w097_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
