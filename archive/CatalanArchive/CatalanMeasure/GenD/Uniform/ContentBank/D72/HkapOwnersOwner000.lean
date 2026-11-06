module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner000

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

theorem w122_guard : QGuard Host.Phys000.lb w122 := by
  have ha : (w122.a : ℝ) = (8300000001/850000000 : ℝ) := by norm_num [w122, intOdd, intWords]
  have hb : (w122.b : ℝ) = (99999997/10000000 : ℝ) := by norm_num [w122, intOdd, intWords]
  have hc0 : (w122.c0 : ℝ) = (1999999999/100000000 : ℝ) := by norm_num [w122, intOdd, intWords]
  have hc1 : (w122.c1 : ℝ) = (-2 : ℝ) := by norm_num [w122, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner000.w122_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
