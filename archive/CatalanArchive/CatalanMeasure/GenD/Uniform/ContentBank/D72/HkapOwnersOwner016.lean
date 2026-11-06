module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner016

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

theorem w105_guard : QGuard Host.Phys016.lb w105 := by
  have ha : (w105.a : ℝ) = (30000001/4000000 : ℝ) := by norm_num [w105, intOdd, intWords]
  have hb : (w105.b : ℝ) = (2633333333/350000000 : ℝ) := by norm_num [w105, intOdd, intWords]
  have hc0 : (w105.c0 : ℝ) = (7899999999/100000000 : ℝ) := by norm_num [w105, intOdd, intWords]
  have hc1 : (w105.c1 : ℝ) = (-21/2 : ℝ) := by norm_num [w105, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner016.w105_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
