module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner010

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

theorem w094_guard : QGuard Host.Phys010.lb w094 := by
  have ha : (w094.a : ℝ) = (28666667/5000000 : ℝ) := by norm_num [w094, intOdd, intWords]
  have hb : (w094.b : ℝ) = (86999999/15000000 : ℝ) := by norm_num [w094, intOdd, intWords]
  have hc0 : (w094.c0 : ℝ) = (599999999/100000000 : ℝ) := by norm_num [w094, intOdd, intWords]
  have hc1 : (w094.c1 : ℝ) = (-1 : ℝ) := by norm_num [w094, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner010.w094_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
