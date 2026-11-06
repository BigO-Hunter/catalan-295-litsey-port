module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner030

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

theorem w001_guard : QGuard Host.Phys030.lb w001 := by
  have ha : (w001.a : ℝ) = (4272973/1700000 : ℝ) := by norm_num [w001, intOdd, intWords]
  have hb : (w001.b : ℝ) = (159099999/62900000 : ℝ) := by norm_num [w001, intOdd, intWords]
  have hc0 : (w001.c0 : ℝ) = (-1000000001/100000000 : ℝ) := by norm_num [w001, intOdd, intWords]
  have hc1 : (w001.c1 : ℝ) = (4 : ℝ) := by norm_num [w001, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner030.w001_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
