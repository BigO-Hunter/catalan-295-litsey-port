module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner037

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

theorem w106_guard : QGuard Host.Phys037.lb w106 := by
  have ha : (w106.a : ℝ) = (776923077/100000000 : ℝ) := by norm_num [w106, intOdd, intWords]
  have hb : (w106.b : ℝ) = (31111111/4000000 : ℝ) := by norm_num [w106, intOdd, intWords]
  have hc0 : (w106.c0 : ℝ) = (-10100000001/100000000 : ℝ) := by norm_num [w106, intOdd, intWords]
  have hc1 : (w106.c1 : ℝ) = (13 : ℝ) := by norm_num [w106, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner037.w106_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
