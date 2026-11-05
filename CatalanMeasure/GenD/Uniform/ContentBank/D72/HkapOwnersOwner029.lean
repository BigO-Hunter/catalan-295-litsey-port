module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner029

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

theorem w096_guard : QGuard Host.Phys029.lb w096 := by
  have ha : (w096.a : ℝ) = (96000001/16000000 : ℝ) := by norm_num [w096, intOdd, intWords]
  have hb : (w096.b : ℝ) = (96999999/16000000 : ℝ) := by norm_num [w096, intOdd, intWords]
  have hc0 : (w096.c0 : ℝ) = (-600000001/100000000 : ℝ) := by norm_num [w096, intOdd, intWords]
  have hc1 : (w096.c1 : ℝ) = (1 : ℝ) := by norm_num [w096, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner029.w096_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
