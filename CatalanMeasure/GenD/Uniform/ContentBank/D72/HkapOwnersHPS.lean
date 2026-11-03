module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.HPS

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

theorem w110_guard : QGuard hpsLB72 w110 := by
  have ha : (w110.a : ℝ) = (76/9 : ℝ) := by norm_num [w110, intOdd, intWords]
  have hb : (w110.b : ℝ) = (17/2 : ℝ) := by norm_num [w110, intOdd, intWords]
  have hc0 : (w110.c0 : ℝ) = (-76 : ℝ) := by norm_num [w110, intOdd, intWords]
  have hc1 : (w110.c1 : ℝ) = (9 : ℝ) := by norm_num [w110, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w110_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w119_guard : QGuard hpsLB72 w119 := by
  have ha : (w119.a : ℝ) = (202/21 : ℝ) := by norm_num [w119, intOdd, intWords]
  have hb : (w119.b : ℝ) = (29/3 : ℝ) := by norm_num [w119, intOdd, intWords]
  have hc0 : (w119.c0 : ℝ) = (-81 : ℝ) := by norm_num [w119, intOdd, intWords]
  have hc1 : (w119.c1 : ℝ) = (17/2 : ℝ) := by norm_num [w119, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w119_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w123_guard : QGuard hpsLB72 w123 := by
  have ha : (w123.a : ℝ) = (99999997/10000000 : ℝ) := by norm_num [w123, intOdd, intWords]
  have hb : (w123.b : ℝ) = (10 : ℝ) := by norm_num [w123, intOdd, intWords]
  have hc0 : (w123.c0 : ℝ) = (10 : ℝ) := by norm_num [w123, intOdd, intWords]
  have hc1 : (w123.c1 : ℝ) = (-1 : ℝ) := by norm_num [w123, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w123_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w124_guard : QGuard hpsLB72 w124 := by
  have ha : (w124.a : ℝ) = (182/17 : ℝ) := by norm_num [w124, intOdd, intWords]
  have hb : (w124.b : ℝ) = (97/9 : ℝ) := by norm_num [w124, intOdd, intWords]
  have hc0 : (w124.c0 : ℝ) = (-91 : ℝ) := by norm_num [w124, intOdd, intWords]
  have hc1 : (w124.c1 : ℝ) = (17/2 : ℝ) := by norm_num [w124, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w124_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w125_guard : QGuard hpsLB72 w125 := by
  have ha : (w125.a : ℝ) = (97/9 : ℝ) := by norm_num [w125, intOdd, intWords]
  have hb : (w125.b : ℝ) = (87/8 : ℝ) := by norm_num [w125, intOdd, intWords]
  have hc0 : (w125.c0 : ℝ) = (6 : ℝ) := by norm_num [w125, intOdd, intWords]
  have hc1 : (w125.c1 : ℝ) = (-1/2 : ℝ) := by norm_num [w125, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w125_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w126_guard : QGuard hpsLB72 w126 := by
  have ha : (w126.a : ℝ) = (87/8 : ℝ) := by norm_num [w126, intOdd, intWords]
  have hb : (w126.b : ℝ) = (186/17 : ℝ) := by norm_num [w126, intOdd, intWords]
  have hc0 : (w126.c0 : ℝ) = (93 : ℝ) := by norm_num [w126, intOdd, intWords]
  have hc1 : (w126.c1 : ℝ) = (-17/2 : ℝ) := by norm_num [w126, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  have h2 : p ≠ 2 := by
    have h : (2 : ℝ) < p := by have := ge_one_real hN; linarith
    exact (show 2 < p by exact_mod_cast h).ne'
  simpa only [div_one] using w126_hcert72 hN (hp.eq_two_or_odd.resolve_left h2)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
