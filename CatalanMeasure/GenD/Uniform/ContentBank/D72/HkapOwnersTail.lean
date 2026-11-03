module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.Tail

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

private theorem ge_one_real {N : Nat} (hN : 0 < N) : (1 : ℝ) ≤ N := by
  exact_mod_cast hN

theorem w137_guard : QGuard (tTailLB P72 p72_admissible) w137 := by
  have ha : (w137.a : ℝ) = (222/11 : ℝ) := by norm_num [w137, intOdd, intWords]
  have hb : (w137.b : ℝ) = (146/7 : ℝ) := by norm_num [w137, intOdd, intWords]
  have hc0 : (w137.c0 : ℝ) = (-20 : ℝ) := by norm_num [w137, intOdd, intWords]
  have hc1 : (w137.c1 : ℝ) = (1 : ℝ) := by norm_num [w137, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w137_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
