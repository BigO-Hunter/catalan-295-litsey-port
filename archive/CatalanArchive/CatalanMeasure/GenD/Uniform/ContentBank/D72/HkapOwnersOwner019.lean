module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner019

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

theorem w081_guard : QGuard Host.Phys019.lb w081 := by
  have ha : (w081.a : ℝ) = (279500001/55250000 : ℝ) := by norm_num [w081, intOdd, intWords]
  have hb : (w081.b : ℝ) = (21576923/4250000 : ℝ) := by norm_num [w081, intOdd, intWords]
  have hc0 : (w081.c0 : ℝ) = (-2500000001/100000000 : ℝ) := by norm_num [w081, intOdd, intWords]
  have hc1 : (w081.c1 : ℝ) = (5 : ℝ) := by norm_num [w081, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner019.w081_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
