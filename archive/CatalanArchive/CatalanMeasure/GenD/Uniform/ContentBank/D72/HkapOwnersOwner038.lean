module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner038

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

theorem w000_guard : QGuard Host.Phys038.lb w000 := by
  have ha : (w000.a : ℝ) = (185000001/74000000 : ℝ) := by norm_num [w000, intOdd, intWords]
  have hb : (w000.b : ℝ) = (5027027/2000000 : ℝ) := by norm_num [w000, intOdd, intWords]
  have hc0 : (w000.c0 : ℝ) = (-1000000001/100000000 : ℝ) := by norm_num [w000, intOdd, intWords]
  have hc1 : (w000.c1 : ℝ) = (4 : ℝ) := by norm_num [w000, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner038.w000_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
