module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner003

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

theorem w116_guard : QGuard Host.Phys003.lb w116 := by
  have ha : (w116.a : ℝ) = (4409091/500000 : ℝ) := by norm_num [w116, intOdd, intWords]
  have hb : (w116.b : ℝ) = (7999999999/900000000 : ℝ) := by norm_num [w116, intOdd, intWords]
  have hc0 : (w116.c0 : ℝ) = (7999999999/100000000 : ℝ) := by norm_num [w116, intOdd, intWords]
  have hc1 : (w116.c1 : ℝ) = (-9 : ℝ) := by norm_num [w116, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner003.w116_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
