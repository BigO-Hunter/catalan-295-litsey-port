module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner032

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

theorem w029_guard : QGuard Host.Phys032.lb w029 := by
  have ha : (w029.a : ℝ) = (96000001/32000000 : ℝ) := by norm_num [w029, intOdd, intWords]
  have hb : (w029.b : ℝ) = (96999999/32000000 : ℝ) := by norm_num [w029, intOdd, intWords]
  have hc0 : (w029.c0 : ℝ) = (-600000001/100000000 : ℝ) := by norm_num [w029, intOdd, intWords]
  have hc1 : (w029.c1 : ℝ) = (2 : ℝ) := by norm_num [w029, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner032.w029_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
