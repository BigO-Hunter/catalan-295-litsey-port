module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner040

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

theorem w002_guard : QGuard Host.Phys040.lb w002 := by
  have ha : (w002.a : ℝ) = (279500001/110500000 : ℝ) := by norm_num [w002, intOdd, intWords]
  have hb : (w002.b : ℝ) = (2533333333/1000000000 : ℝ) := by norm_num [w002, intOdd, intWords]
  have hc0 : (w002.c0 : ℝ) = (7599999999/100000000 : ℝ) := by norm_num [w002, intOdd, intWords]
  have hc1 : (w002.c1 : ℝ) = (-30 : ℝ) := by norm_num [w002, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner040.w002_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
