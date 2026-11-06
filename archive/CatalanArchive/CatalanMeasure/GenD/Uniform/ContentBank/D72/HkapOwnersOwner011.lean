module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner011

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

theorem w092_guard : QGuard Host.Phys011.lb w092 := by
  have ha : (w092.a : ℝ) = (186000001/34000000 : ℝ) := by norm_num [w092, intOdd, intWords]
  have hb : (w092.b : ℝ) = (186999999/34000000 : ℝ) := by norm_num [w092, intOdd, intWords]
  have hc0 : (w092.c0 : ℝ) = (7999999999/100000000 : ℝ) := by norm_num [w092, intOdd, intWords]
  have hc1 : (w092.c1 : ℝ) = (-29/2 : ℝ) := by norm_num [w092, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner011.w092_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
