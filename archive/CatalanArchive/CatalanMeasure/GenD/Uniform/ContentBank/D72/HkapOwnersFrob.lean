module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.Frob

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

theorem w147_guard : QGuard frobLB w147 := by
  have ha : (w147.a : ℝ) = (97/3 : ℝ) := by norm_num [w147, intOdd, intWords]
  have hb : (w147.b : ℝ) = (954/29 : ℝ) := by norm_num [w147, intOdd, intWords]
  have hc0 : (w147.c0 : ℝ) = (66 : ℝ) := by norm_num [w147, intOdd, intWords]
  have hc1 : (w147.c1 : ℝ) = (-2 : ℝ) := by norm_num [w147, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one, neg_mul, sub_eq_add_neg] using
    w147_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
