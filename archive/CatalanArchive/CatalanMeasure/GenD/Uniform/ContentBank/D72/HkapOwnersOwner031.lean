module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner031

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

theorem w095_guard : QGuard Host.Phys031.lb w095 := by
  have ha : (w095.a : ℝ) = (464000001/80000000 : ℝ) := by norm_num [w095, intOdd, intWords]
  have hb : (w095.b : ℝ) = (464999999/80000000 : ℝ) := by norm_num [w095, intOdd, intWords]
  have hc0 : (w095.c0 : ℝ) = (9299999999/100000000 : ℝ) := by norm_num [w095, intOdd, intWords]
  have hc1 : (w095.c1 : ℝ) = (-16 : ℝ) := by norm_num [w095, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner031.w095_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
