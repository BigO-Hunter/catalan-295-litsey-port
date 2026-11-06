module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner001

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

theorem w089_guard : QGuard Host.Phys001.lb w089 := by
  have ha : (w089.a : ℝ) = (432000003/80000000 : ℝ) := by norm_num [w089, intOdd, intWords]
  have hb : (w089.b : ℝ) = (434999997/80000000 : ℝ) := by norm_num [w089, intOdd, intWords]
  have hc0 : (w089.c0 : ℝ) = (1999999999/100000000 : ℝ) := by norm_num [w089, intOdd, intWords]
  have hc1 : (w089.c1 : ℝ) = (-7/2 : ℝ) := by norm_num [w089, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  exact Host.Owner001.w089_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
