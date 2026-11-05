module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner014

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

theorem w091_guard : QGuard Host.Phys014.lb w091 := by
  have ha : (w091.a : ℝ) = (92727273/17000000 : ℝ) := by norm_num [w091, intOdd, intWords]
  have hb : (w091.b : ℝ) = (1022999997/187000000 : ℝ) := by norm_num [w091, intOdd, intWords]
  have hc0 : (w091.c0 : ℝ) = (7999999999/100000000 : ℝ) := by norm_num [w091, intOdd, intWords]
  have hc1 : (w091.c1 : ℝ) = (-29/2 : ℝ) := by norm_num [w091, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner014.w091_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
