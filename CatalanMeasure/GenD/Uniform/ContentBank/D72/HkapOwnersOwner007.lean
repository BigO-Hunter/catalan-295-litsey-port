module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner007

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

theorem w100_guard : QGuard Host.Phys007.lb w100 := by
  have ha : (w100.a : ℝ) = (39857143/6000000 : ℝ) := by norm_num [w100, intOdd, intWords]
  have hb : (w100.b : ℝ) = (93333333/14000000 : ℝ) := by norm_num [w100, intOdd, intWords]
  have hc0 : (w100.c0 : ℝ) = (1399999999/100000000 : ℝ) := by norm_num [w100, intOdd, intWords]
  have hc1 : (w100.c1 : ℝ) = (-2 : ℝ) := by norm_num [w100, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner007.w100_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
