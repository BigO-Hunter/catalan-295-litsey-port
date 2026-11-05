module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner033

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

theorem w004_guard : QGuard Host.Phys033.lb w004 := by
  have ha : (w004.a : ℝ) = (29969697/11500000 : ℝ) := by norm_num [w004, intOdd, intWords]
  have hb : (w004.b : ℝ) = (989999999/379500000 : ℝ) := by norm_num [w004, intOdd, intWords]
  have hc0 : (w004.c0 : ℝ) = (1599999999/100000000 : ℝ) := by norm_num [w004, intOdd, intWords]
  have hc1 : (w004.c1 : ℝ) = (-6 : ℝ) := by norm_num [w004, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner033.w004_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
