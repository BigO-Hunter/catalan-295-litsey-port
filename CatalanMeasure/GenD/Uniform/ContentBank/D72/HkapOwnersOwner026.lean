module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner026

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

theorem w093_guard : QGuard Host.Phys026.lb w093 := by
  have ha : (w093.a : ℝ) = (1142857143/200000000 : ℝ) := by norm_num [w093, intOdd, intWords]
  have hb : (w093.b : ℝ) = (487333331/85000000 : ℝ) := by norm_num [w093, intOdd, intWords]
  have hc0 : (w093.c0 : ℝ) = (-8000000001/100000000 : ℝ) := by norm_num [w093, intOdd, intWords]
  have hc1 : (w093.c1 : ℝ) = (14 : ℝ) := by norm_num [w093, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner026.w093_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
