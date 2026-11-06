module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner025

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

theorem w085_guard : QGuard Host.Phys025.lb w085 := by
  have ha : (w085.a : ℝ) = (10100000001/1900000000 : ℝ) := by norm_num [w085, intOdd, intWords]
  have hb : (w085.b : ℝ) = (31999999/6000000 : ℝ) := by norm_num [w085, intOdd, intWords]
  have hc0 : (w085.c0 : ℝ) = (-10100000001/100000000 : ℝ) := by norm_num [w085, intOdd, intWords]
  have hc1 : (w085.c1 : ℝ) = (19 : ℝ) := by norm_num [w085, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner025.w085_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
