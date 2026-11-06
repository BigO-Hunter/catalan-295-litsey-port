module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner017

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

theorem w098_guard : QGuard Host.Phys017.lb w098 := by
  have ha : (w098.a : ℝ) = (429000001/65000000 : ℝ) := by norm_num [w098, intOdd, intWords]
  have hb : (w098.b : ℝ) = (33076923/5000000 : ℝ) := by norm_num [w098, intOdd, intWords]
  have hc0 : (w098.c0 : ℝ) = (-7200000001/100000000 : ℝ) := by norm_num [w098, intOdd, intWords]
  have hc1 : (w098.c1 : ℝ) = (11 : ℝ) := by norm_num [w098, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner017.w098_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
