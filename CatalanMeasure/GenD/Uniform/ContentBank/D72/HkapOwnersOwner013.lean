module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner013

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

theorem w082_guard : QGuard Host.Phys013.lb w082 := by
  have ha : (w082.a : ℝ) = (96461539/19000000 : ℝ) := by norm_num [w082, intOdd, intWords]
  have hb : (w082.b : ℝ) = (1260999993/247000000 : ℝ) := by norm_num [w082, intOdd, intWords]
  have hc0 : (w082.c0 : ℝ) = (-2500000001/100000000 : ℝ) := by norm_num [w082, intOdd, intWords]
  have hc1 : (w082.c1 : ℝ) = (5 : ℝ) := by norm_num [w082, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner013.w082_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
