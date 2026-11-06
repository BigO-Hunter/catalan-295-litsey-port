module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner002

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

theorem w086_guard : QGuard Host.Phys002.lb w086 := by
  have ha : (w086.a : ℝ) = (42666667/8000000 : ℝ) := by norm_num [w086, intOdd, intWords]
  have hb : (w086.b : ℝ) = (128999999/24000000 : ℝ) := by norm_num [w086, intOdd, intWords]
  have hc0 : (w086.c0 : ℝ) = (-9300000001/100000000 : ℝ) := by norm_num [w086, intOdd, intWords]
  have hc1 : (w086.c1 : ℝ) = (35/2 : ℝ) := by norm_num [w086, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner002.w086_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
