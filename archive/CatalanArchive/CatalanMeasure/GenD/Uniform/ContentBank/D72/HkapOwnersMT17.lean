module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.MT17

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

theorem w087_guard : QGuard mt17LB72 w087 := by
  have ha : (w087.a : ℝ) = (43/8 : ℝ) := by norm_num [w087, intOdd, intWords]
  have hb : (w087.b : ℝ) = (97/18 : ℝ) := by norm_num [w087, intOdd, intWords]
  have hc0 : (w087.c0 : ℝ) = (-77 : ℝ) := by norm_num [w087, intOdd, intWords]
  have hc1 : (w087.c1 : ℝ) = (29/2 : ℝ) := by norm_num [w087, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w087_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
