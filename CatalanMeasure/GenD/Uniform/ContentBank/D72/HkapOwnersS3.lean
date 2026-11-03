module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.S3

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

theorem w141_guard : QGuard s3LB72 w141 := by
  have ha : (w141.a : ℝ) = (186/7 : ℝ) := by norm_num [w141, intOdd, intWords]
  have hb : (w141.b : ℝ) = (27 : ℝ) := by norm_num [w141, intOdd, intWords]
  have hc0 : (w141.c0 : ℝ) = (-93 : ℝ) := by norm_num [w141, intOdd, intWords]
  have hc1 : (w141.c1 : ℝ) = (7/2 : ℝ) := by norm_num [w141, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact (s3_left_hcert72 hN hlo (by have := ge_one_real hN; linarith)).1

theorem w142_guard : QGuard s3LB72 w142 := by
  have ha : (w142.a : ℝ) = (27 : ℝ) := by norm_num [w142, intOdd, intWords]
  have hb : (w142.b : ℝ) = (28 : ℝ) := by norm_num [w142, intOdd, intWords]
  have hc0 : (w142.c0 : ℝ) = (-66 : ℝ) := by norm_num [w142, intOdd, intWords]
  have hc1 : (w142.c1 : ℝ) = (5/2 : ℝ) := by norm_num [w142, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact (s3_right_hcert72 hN hlo (by have := ge_one_real hN; linarith)).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
