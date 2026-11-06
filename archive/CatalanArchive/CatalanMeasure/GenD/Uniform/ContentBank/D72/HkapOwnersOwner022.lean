module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner022

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

theorem w084_guard : QGuard Host.Phys022.lb w084 := by
  have ha : (w084.a : ℝ) = (104400001/20400000 : ℝ) := by norm_num [w084, intOdd, intWords]
  have hb : (w084.b : ℝ) = (7199999999/1400000000 : ℝ) := by norm_num [w084, intOdd, intWords]
  have hc0 : (w084.c0 : ℝ) = (7199999999/100000000 : ℝ) := by norm_num [w084, intOdd, intWords]
  have hc1 : (w084.c1 : ℝ) = (-14 : ℝ) := by norm_num [w084, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner022.w084_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
