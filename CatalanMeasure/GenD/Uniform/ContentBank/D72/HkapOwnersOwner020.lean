module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner020

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

theorem w083_guard : QGuard Host.Phys020.lb w083 := by
  have ha : (w083.a : ℝ) = (412250001/80750000 : ℝ) := by norm_num [w083, intOdd, intWords]
  have hb : (w083.b : ℝ) = (413249999/80750000 : ℝ) := by norm_num [w083, intOdd, intWords]
  have hc0 : (w083.c0 : ℝ) = (7199999999/100000000 : ℝ) := by norm_num [w083, intOdd, intWords]
  have hc1 : (w083.c1 : ℝ) = (-14 : ℝ) := by norm_num [w083, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner020.w083_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
