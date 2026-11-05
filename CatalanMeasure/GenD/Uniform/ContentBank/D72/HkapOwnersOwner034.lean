module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner034

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

theorem w031_guard : QGuard Host.Phys034.lb w031 := by
  have ha : (w031.a : ℝ) = (18523077/5600000 : ℝ) := by norm_num [w031, intOdd, intWords]
  have hb : (w031.b : ℝ) = (34542857/10400000 : ℝ) := by norm_num [w031, intOdd, intWords]
  have hc0 : (w031.c0 : ℝ) = (999999999/100000000 : ℝ) := by norm_num [w031, intOdd, intWords]
  have hc1 : (w031.c1 : ℝ) = (-3 : ℝ) := by norm_num [w031, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner034.w031_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
