module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner039

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

theorem w022_guard : QGuard Host.Phys039.lb w022 := by
  have ha : (w022.a : ℝ) = (42857143/15000000 : ℝ) := by norm_num [w022, intOdd, intWords]
  have hb : (w022.b : ℝ) = (3433333333/1200000000 : ℝ) := by norm_num [w022, intOdd, intWords]
  have hc0 : (w022.c0 : ℝ) = (8299999999/100000000 : ℝ) := by norm_num [w022, intOdd, intWords]
  have hc1 : (w022.c1 : ℝ) = (-29 : ℝ) := by norm_num [w022, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner039.w022_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
