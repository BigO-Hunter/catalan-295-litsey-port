module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowMixed

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

theorem w073_guard : QGuard FamilyBounds.LowMixed.lb w073 := by
  have ha : (w073.a : ℝ) = (87/19 : ℝ) := by norm_num [w073, intOdd, intWords]
  have hb : (w073.b : ℝ) = (87000000019/19000000000 : ℝ) := by norm_num [w073, intOdd, intWords]
  have hc0 : (w073.c0 : ℝ) = (14 : ℝ) := by norm_num [w073, intOdd, intWords]
  have hc1 : (w073.c1 : ℝ) = (-3 : ℝ) := by norm_num [w073, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowMixed.w073_hcert72

theorem w074_guard : QGuard FamilyBounds.LowMixed.lb w074 := by
  have ha : (w074.a : ℝ) = (87000000019/19000000000 : ℝ) := by norm_num [w074, intOdd, intWords]
  have hb : (w074.b : ℝ) = (60/13 : ℝ) := by norm_num [w074, intOdd, intWords]
  have hc0 : (w074.c0 : ℝ) = (14 : ℝ) := by norm_num [w074, intOdd, intWords]
  have hc1 : (w074.c1 : ℝ) = (-3 : ℝ) := by norm_num [w074, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowMixed.w074_hcert72

theorem w075_guard : QGuard FamilyBounds.LowMixed.lb w075 := by
  have ha : (w075.a : ℝ) = (60/13 : ℝ) := by norm_num [w075, intOdd, intWords]
  have hb : (w075.b : ℝ) = (96999999979/21000000000 : ℝ) := by norm_num [w075, intOdd, intWords]
  have hc0 : (w075.c0 : ℝ) = (74 : ℝ) := by norm_num [w075, intOdd, intWords]
  have hc1 : (w075.c1 : ℝ) = (-16 : ℝ) := by norm_num [w075, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowMixed.w075_hcert72

theorem w076_guard : QGuard FamilyBounds.LowMixed.lb w076 := by
  have ha : (w076.a : ℝ) = (96999999979/21000000000 : ℝ) := by norm_num [w076, intOdd, intWords]
  have hb : (w076.b : ℝ) = (97/21 : ℝ) := by norm_num [w076, intOdd, intWords]
  have hc0 : (w076.c0 : ℝ) = (74 : ℝ) := by norm_num [w076, intOdd, intWords]
  have hc1 : (w076.c1 : ℝ) = (-16 : ℝ) := by norm_num [w076, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowMixed.w076_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
