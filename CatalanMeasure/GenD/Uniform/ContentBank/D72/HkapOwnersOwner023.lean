module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner023

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

theorem w079_guard : QGuard Host.Phys023.lb w079 := by
  have ha : (w079.a : ℝ) = (85000001/17000000 : ℝ) := by norm_num [w079, intOdd, intWords]
  have hb : (w079.b : ℝ) = (101/20 : ℝ) := by norm_num [w079, intOdd, intWords]
  have hc0 : (w079.c0 : ℝ) = (-1000000001/100000000 : ℝ) := by norm_num [w079, intOdd, intWords]
  have hc1 : (w079.c1 : ℝ) = (2 : ℝ) := by norm_num [w079, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner023.w079_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
