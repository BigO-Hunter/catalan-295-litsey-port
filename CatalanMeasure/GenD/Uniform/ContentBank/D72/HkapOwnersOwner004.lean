module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner004

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

theorem w104_guard : QGuard Host.Phys004.lb w104 := by
  have ha : (w104.a : ℝ) = (14923077/2000000 : ℝ) := by norm_num [w104, intOdd, intWords]
  have hb : (w104.b : ℝ) = (194999999/26000000 : ℝ) := by norm_num [w104, intOdd, intWords]
  have hc0 : (w104.c0 : ℝ) = (1899999999/100000000 : ℝ) := by norm_num [w104, intOdd, intWords]
  have hc1 : (w104.c1 : ℝ) = (-5/2 : ℝ) := by norm_num [w104, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner004.w104_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
