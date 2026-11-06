module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner036

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

theorem w019_guard : QGuard Host.Phys036.lb w019 := by
  have ha : (w019.a : ℝ) = (7400000001/2600000000 : ℝ) := by norm_num [w019, intOdd, intWords]
  have hb : (w019.b : ℝ) = (1066999987/374000000 : ℝ) := by norm_num [w019, intOdd, intWords]
  have hc0 : (w019.c0 : ℝ) = (-7400000001/100000000 : ℝ) := by norm_num [w019, intOdd, intWords]
  have hc1 : (w019.c1 : ℝ) = (26 : ℝ) := by norm_num [w019, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner036.w019_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
