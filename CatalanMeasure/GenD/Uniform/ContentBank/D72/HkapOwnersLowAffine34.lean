module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffine34

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

theorem w013_guard : QGuard FamilyBounds.LowAffine34.lb w013 := by
  have ha : (w013.a : ℝ) = (36/13 : ℝ) := by norm_num [w013, intOdd, intWords]
  have hb : (w013.b : ℝ) = (36000000013/13000000000 : ℝ) := by norm_num [w013, intOdd, intWords]
  have hc0 : (w013.c0 : ℝ) = (-72 : ℝ) := by norm_num [w013, intOdd, intWords]
  have hc1 : (w013.c1 : ℝ) = (26 : ℝ) := by norm_num [w013, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w013_hcert72

theorem w014_guard : QGuard FamilyBounds.LowAffine34.lb w014 := by
  have ha : (w014.a : ℝ) = (36000000013/13000000000 : ℝ) := by norm_num [w014, intOdd, intWords]
  have hb : (w014.b : ℝ) = (19399999993/7000000000 : ℝ) := by norm_num [w014, intOdd, intWords]
  have hc0 : (w014.c0 : ℝ) = (-72 : ℝ) := by norm_num [w014, intOdd, intWords]
  have hc1 : (w014.c1 : ℝ) = (26 : ℝ) := by norm_num [w014, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w014_hcert72

theorem w015_guard : QGuard FamilyBounds.LowAffine34.lb w015 := by
  have ha : (w015.a : ℝ) = (19399999993/7000000000 : ℝ) := by norm_num [w015, intOdd, intWords]
  have hb : (w015.b : ℝ) = (97/35 : ℝ) := by norm_num [w015, intOdd, intWords]
  have hc0 : (w015.c0 : ℝ) = (-72 : ℝ) := by norm_num [w015, intOdd, intWords]
  have hc1 : (w015.c1 : ℝ) = (26 : ℝ) := by norm_num [w015, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w015_hcert72

theorem w016_guard : QGuard FamilyBounds.LowAffine34.lb w016 := by
  have ha : (w016.a : ℝ) = (97/35 : ℝ) := by norm_num [w016, intOdd, intWords]
  have hb : (w016.b : ℝ) = (19400000007/7000000000 : ℝ) := by norm_num [w016, intOdd, intWords]
  have hc0 : (w016.c0 : ℝ) = (-72 : ℝ) := by norm_num [w016, intOdd, intWords]
  have hc1 : (w016.c1 : ℝ) = (26 : ℝ) := by norm_num [w016, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w016_hcert72

theorem w017_guard : QGuard FamilyBounds.LowAffine34.lb w017 := by
  have ha : (w017.a : ℝ) = (19400000007/7000000000 : ℝ) := by norm_num [w017, intOdd, intWords]
  have hb : (w017.b : ℝ) = (86/31 : ℝ) := by norm_num [w017, intOdd, intWords]
  have hc0 : (w017.c0 : ℝ) = (-72 : ℝ) := by norm_num [w017, intOdd, intWords]
  have hc1 : (w017.c1 : ℝ) = (26 : ℝ) := by norm_num [w017, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w017_hcert72

theorem w018_guard : QGuard FamilyBounds.LowAffine34.lb w018 := by
  have ha : (w018.a : ℝ) = (86/31 : ℝ) := by norm_num [w018, intOdd, intWords]
  have hb : (w018.b : ℝ) = (14/5 : ℝ) := by norm_num [w018, intOdd, intWords]
  have hc0 : (w018.c0 : ℝ) = (14 : ℝ) := by norm_num [w018, intOdd, intWords]
  have hc1 : (w018.c1 : ℝ) = (-5 : ℝ) := by norm_num [w018, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine34.w018_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
