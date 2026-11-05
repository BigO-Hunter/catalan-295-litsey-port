module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner035

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

theorem w020_guard : QGuard Host.Phys035.lb w020 := by
  have ha : (w020.a : ℝ) = (679000001/238000000 : ℝ) := by norm_num [w020, intOdd, intWords]
  have hb : (w020.b : ℝ) = (97142857/34000000 : ℝ) := by norm_num [w020, intOdd, intWords]
  have hc0 : (w020.c0 : ℝ) = (2299999999/100000000 : ℝ) := by norm_num [w020, intOdd, intWords]
  have hc1 : (w020.c1 : ℝ) = (-8 : ℝ) := by norm_num [w020, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner035.w020_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
