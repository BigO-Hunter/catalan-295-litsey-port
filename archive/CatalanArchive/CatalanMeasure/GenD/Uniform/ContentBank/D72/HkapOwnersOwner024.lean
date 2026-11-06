module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner024

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

theorem w080_guard : QGuard Host.Phys024.lb w080 := by
  have ha : (w080.a : ℝ) = (101/20 : ℝ) := by norm_num [w080, intOdd, intWords]
  have hb : (w080.b : ℝ) = (85999999/17000000 : ℝ) := by norm_num [w080, intOdd, intWords]
  have hc0 : (w080.c0 : ℝ) = (-11100000001/100000000 : ℝ) := by norm_num [w080, intOdd, intWords]
  have hc1 : (w080.c1 : ℝ) = (22 : ℝ) := by norm_num [w080, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner024.w080_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
