module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner006

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

theorem w103_guard : QGuard Host.Phys006.lb w103 := by
  have ha : (w103.a : ℝ) = (7400000001/1000000000 : ℝ) := by norm_num [w103, intOdd, intWords]
  have hb : (w103.b : ℝ) = (4476923/600000 : ℝ) := by norm_num [w103, intOdd, intWords]
  have hc0 : (w103.c0 : ℝ) = (-7400000001/100000000 : ℝ) := by norm_num [w103, intOdd, intWords]
  have hc1 : (w103.c1 : ℝ) = (10 : ℝ) := by norm_num [w103, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner006.w103_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
