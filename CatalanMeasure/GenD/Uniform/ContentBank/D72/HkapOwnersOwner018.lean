module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner018

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

theorem w102_guard : QGuard Host.Phys018.lb w102 := by
  have ha : (w102.a : ℝ) = (26769231/4000000 : ℝ) := by norm_num [w102, intOdd, intWords]
  have hb : (w102.b : ℝ) = (7399999999/1100000000 : ℝ) := by norm_num [w102, intOdd, intWords]
  have hc0 : (w102.c0 : ℝ) = (7399999999/100000000 : ℝ) := by norm_num [w102, intOdd, intWords]
  have hc1 : (w102.c1 : ℝ) = (-11 : ℝ) := by norm_num [w102, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner018.w102_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
