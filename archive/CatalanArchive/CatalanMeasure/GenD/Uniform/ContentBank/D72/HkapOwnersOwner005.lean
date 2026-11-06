module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner005

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

theorem w099_guard : QGuard Host.Phys005.lb w099 := by
  have ha : (w099.a : ℝ) = (18523077/2800000 : ℝ) := by norm_num [w099, intOdd, intWords]
  have hb : (w099.b : ℝ) = (34542857/5200000 : ℝ) := by norm_num [w099, intOdd, intWords]
  have hc0 : (w099.c0 : ℝ) = (1399999999/100000000 : ℝ) := by norm_num [w099, intOdd, intWords]
  have hc1 : (w099.c1 : ℝ) = (-2 : ℝ) := by norm_num [w099, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner005.w099_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
