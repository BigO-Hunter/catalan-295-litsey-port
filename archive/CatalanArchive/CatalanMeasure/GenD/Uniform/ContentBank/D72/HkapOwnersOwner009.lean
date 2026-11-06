module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner009

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

theorem w090_guard : QGuard Host.Phys009.lb w090 := by
  have ha : (w090.a : ℝ) = (957000003/176000000 : ℝ) := by norm_num [w090, intOdd, intWords]
  have hb : (w090.b : ℝ) = (87272727/16000000 : ℝ) := by norm_num [w090, intOdd, intWords]
  have hc0 : (w090.c0 : ℝ) = (1999999999/100000000 : ℝ) := by norm_num [w090, intOdd, intWords]
  have hc1 : (w090.c1 : ℝ) = (-7/2 : ℝ) := by norm_num [w090, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner009.w090_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
