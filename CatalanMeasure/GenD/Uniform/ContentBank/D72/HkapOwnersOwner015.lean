module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner015

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

theorem w088_guard : QGuard Host.Phys015.lb w088 := by
  have ha : (w088.a : ℝ) = (53888889/10000000 : ℝ) := by norm_num [w088, intOdd, intWords]
  have hb : (w088.b : ℝ) = (485999999/90000000 : ℝ) := by norm_num [w088, intOdd, intWords]
  have hc0 : (w088.c0 : ℝ) = (1999999999/100000000 : ℝ) := by norm_num [w088, intOdd, intWords]
  have hc1 : (w088.c1 : ℝ) = (-7/2 : ℝ) := by norm_num [w088, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner015.w088_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
