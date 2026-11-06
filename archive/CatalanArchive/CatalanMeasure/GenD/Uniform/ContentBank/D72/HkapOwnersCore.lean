module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.Core

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

theorem w138_guard : QGuard coreLB72 w138 := by
  have ha : (w138.a : ℝ) = (146/7 : ℝ) := by norm_num [w138, intOdd, intWords]
  have hb : (w138.b : ℝ) = (43/2 : ℝ) := by norm_num [w138, intOdd, intWords]
  have hc0 : (w138.c0 : ℝ) = (-93 : ℝ) := by norm_num [w138, intOdd, intWords]
  have hc1 : (w138.c1 : ℝ) = (9/2 : ℝ) := by norm_num [w138, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w138_hcert72 hN hlo hhi

theorem w139_guard : QGuard coreLB72 w139 := by
  have ha : (w139.a : ℝ) = (43/2 : ℝ) := by norm_num [w139, intOdd, intWords]
  have hb : (w139.b : ℝ) = (87/4 : ℝ) := by norm_num [w139, intOdd, intWords]
  have hc0 : (w139.c0 : ℝ) = (-7 : ℝ) := by norm_num [w139, intOdd, intWords]
  have hc1 : (w139.c1 : ℝ) = (1/2 : ℝ) := by norm_num [w139, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w139_hcert72 hN hlo hhi

theorem w140_guard : QGuard coreLB72 w140 := by
  have ha : (w140.a : ℝ) = (87/4 : ℝ) := by norm_num [w140, intOdd, intWords]
  have hb : (w140.b : ℝ) = (160/7 : ℝ) := by norm_num [w140, intOdd, intWords]
  have hc0 : (w140.c0 : ℝ) = (80 : ℝ) := by norm_num [w140, intOdd, intWords]
  have hc1 : (w140.c1 : ℝ) = (-7/2 : ℝ) := by norm_num [w140, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w140_hcert72 hN hlo hhi

theorem w143_guard : QGuard coreLB72 w143 := by
  have ha : (w143.a : ℝ) = (28 : ℝ) := by norm_num [w143, intOdd, intWords]
  have hb : (w143.b : ℝ) = (86/3 : ℝ) := by norm_num [w143, intOdd, intWords]
  have hc0 : (w143.c0 : ℝ) = (-80 : ℝ) := by norm_num [w143, intOdd, intWords]
  have hc1 : (w143.c1 : ℝ) = (3 : ℝ) := by norm_num [w143, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w143_hcert72 hN hlo hhi

theorem w144_guard : QGuard coreLB72 w144 := by
  have ha : (w144.a : ℝ) = (86/3 : ℝ) := by norm_num [w144, intOdd, intWords]
  have hb : (w144.b : ℝ) = (29 : ℝ) := by norm_num [w144, intOdd, intWords]
  have hc0 : (w144.c0 : ℝ) = (6 : ℝ) := by norm_num [w144, intOdd, intWords]
  have hc1 : (w144.c1 : ℝ) = (0 : ℝ) := by norm_num [w144, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w144_hcert72 hN hlo hhi

theorem w145_guard : QGuard coreLB72 w145 := by
  have ha : (w145.a : ℝ) = (29 : ℝ) := by norm_num [w145, intOdd, intWords]
  have hb : (w145.b : ℝ) = (30 : ℝ) := by norm_num [w145, intOdd, intWords]
  have hc0 : (w145.c0 : ℝ) = (6 : ℝ) := by norm_num [w145, intOdd, intWords]
  have hc1 : (w145.c1 : ℝ) = (0 : ℝ) := by norm_num [w145, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w145_hcert72 hN hlo hhi

theorem w146_guard : QGuard coreLB72 w146 := by
  have ha : (w146.a : ℝ) = (30 : ℝ) := by norm_num [w146, intOdd, intWords]
  have hb : (w146.b : ℝ) = (97/3 : ℝ) := by norm_num [w146, intOdd, intWords]
  have hc0 : (w146.c0 : ℝ) = (66 : ℝ) := by norm_num [w146, intOdd, intWords]
  have hc1 : (w146.c1 : ℝ) = (-2 : ℝ) := by norm_num [w146, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w146_hcert72 hN hlo hhi


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
