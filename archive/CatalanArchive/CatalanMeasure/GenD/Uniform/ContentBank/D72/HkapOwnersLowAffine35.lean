module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowAffine35

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

theorem w006_guard : QGuard FamilyBounds.LowAffine35.lb w006 := by
  have ha : (w006.a : ℝ) = (83/31 : ℝ) := by norm_num [w006, intOdd, intWords]
  have hb : (w006.b : ℝ) = (24249999991/9000000000 : ℝ) := by norm_num [w006, intOdd, intWords]
  have hc0 : (w006.c0 : ℝ) = (-83 : ℝ) := by norm_num [w006, intOdd, intWords]
  have hc1 : (w006.c1 : ℝ) = (31 : ℝ) := by norm_num [w006, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w006_hcert72

theorem w007_guard : QGuard FamilyBounds.LowAffine35.lb w007 := by
  have ha : (w007.a : ℝ) = (24249999991/9000000000 : ℝ) := by norm_num [w007, intOdd, intWords]
  have hb : (w007.b : ℝ) = (97/36 : ℝ) := by norm_num [w007, intOdd, intWords]
  have hc0 : (w007.c0 : ℝ) = (-83 : ℝ) := by norm_num [w007, intOdd, intWords]
  have hc1 : (w007.c1 : ℝ) = (31 : ℝ) := by norm_num [w007, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w007_hcert72

theorem w008_guard : QGuard FamilyBounds.LowAffine35.lb w008 := by
  have ha : (w008.a : ℝ) = (97/36 : ℝ) := by norm_num [w008, intOdd, intWords]
  have hb : (w008.b : ℝ) = (24250000009/9000000000 : ℝ) := by norm_num [w008, intOdd, intWords]
  have hc0 : (w008.c0 : ℝ) = (14 : ℝ) := by norm_num [w008, intOdd, intWords]
  have hc1 : (w008.c1 : ℝ) = (-5 : ℝ) := by norm_num [w008, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w008_hcert72

theorem w009_guard : QGuard FamilyBounds.LowAffine35.lb w009 := by
  have ha : (w009.a : ℝ) = (24250000009/9000000000 : ℝ) := by norm_num [w009, intOdd, intWords]
  have hb : (w009.b : ℝ) = (2718749999/1000000000 : ℝ) := by norm_num [w009, intOdd, intWords]
  have hc0 : (w009.c0 : ℝ) = (14 : ℝ) := by norm_num [w009, intOdd, intWords]
  have hc1 : (w009.c1 : ℝ) = (-5 : ℝ) := by norm_num [w009, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w009_hcert72

theorem w010_guard : QGuard FamilyBounds.LowAffine35.lb w010 := by
  have ha : (w010.a : ℝ) = (2718749999/1000000000 : ℝ) := by norm_num [w010, intOdd, intWords]
  have hb : (w010.b : ℝ) = (87/32 : ℝ) := by norm_num [w010, intOdd, intWords]
  have hc0 : (w010.c0 : ℝ) = (14 : ℝ) := by norm_num [w010, intOdd, intWords]
  have hc1 : (w010.c1 : ℝ) = (-5 : ℝ) := by norm_num [w010, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w010_hcert72

theorem w011_guard : QGuard FamilyBounds.LowAffine35.lb w011 := by
  have ha : (w011.a : ℝ) = (87/32 : ℝ) := by norm_num [w011, intOdd, intWords]
  have hb : (w011.b : ℝ) = (2718750001/1000000000 : ℝ) := by norm_num [w011, intOdd, intWords]
  have hc0 : (w011.c0 : ℝ) = (101 : ℝ) := by norm_num [w011, intOdd, intWords]
  have hc1 : (w011.c1 : ℝ) = (-37 : ℝ) := by norm_num [w011, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w011_hcert72

theorem w012_guard : QGuard FamilyBounds.LowAffine35.lb w012 := by
  have ha : (w012.a : ℝ) = (2718750001/1000000000 : ℝ) := by norm_num [w012, intOdd, intWords]
  have hb : (w012.b : ℝ) = (101/37 : ℝ) := by norm_num [w012, intOdd, intWords]
  have hc0 : (w012.c0 : ℝ) = (101 : ℝ) := by norm_num [w012, intOdd, intWords]
  have hc1 : (w012.c1 : ℝ) = (-37 : ℝ) := by norm_num [w012, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using FamilyBounds.LowAffine35.w012_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
