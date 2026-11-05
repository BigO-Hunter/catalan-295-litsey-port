module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner028

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

theorem w032_guard : QGuard Host.Phys028.lb w032 := by
  have ha : (w032.a : ℝ) = (39857143/12000000 : ℝ) := by norm_num [w032, intOdd, intWords]
  have hb : (w032.b : ℝ) = (93333333/28000000 : ℝ) := by norm_num [w032, intOdd, intWords]
  have hc0 : (w032.c0 : ℝ) = (999999999/100000000 : ℝ) := by norm_num [w032, intOdd, intWords]
  have hc1 : (w032.c1 : ℝ) = (-3 : ℝ) := by norm_num [w032, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner028.w032_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
