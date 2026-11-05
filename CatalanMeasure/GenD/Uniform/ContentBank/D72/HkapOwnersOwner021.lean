module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner021

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

theorem w005_guard : QGuard Host.Phys021.lb w005 := by
  have ha : (w005.a : ℝ) = (2220000011/851000000 : ℝ) := by norm_num [w005, intOdd, intWords]
  have hb : (w005.b : ℝ) = (7599999999/2900000000 : ℝ) := by norm_num [w005, intOdd, intWords]
  have hc0 : (w005.c0 : ℝ) = (7599999999/100000000 : ℝ) := by norm_num [w005, intOdd, intWords]
  have hc1 : (w005.c1 : ℝ) = (-29 : ℝ) := by norm_num [w005, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner021.w005_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
