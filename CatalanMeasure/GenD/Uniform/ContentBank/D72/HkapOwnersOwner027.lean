module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner027

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

theorem w003_guard : QGuard Host.Phys027.lb w003 := by
  have ha : (w003.a : ℝ) = (21388889/8250000 : ℝ) := by norm_num [w003, intOdd, intWords]
  have hb : (w003.b : ℝ) = (17590909/6750000 : ℝ) := by norm_num [w003, intOdd, intWords]
  have hc0 : (w003.c0 : ℝ) = (-7000000001/100000000 : ℝ) := by norm_num [w003, intOdd, intWords]
  have hc1 : (w003.c1 : ℝ) = (27 : ℝ) := by norm_num [w003, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner027.w003_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
