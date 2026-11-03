module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.A

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

theorem w127_guard : QGuard aLB72 w127 := by
  have ha : (w127.a : ℝ) = (74/5 : ℝ) := by norm_num [w127, intOdd, intWords]
  have hb : (w127.b : ℝ) = (15 : ℝ) := by norm_num [w127, intOdd, intWords]
  have hc0 : (w127.c0 : ℝ) = (-74 : ℝ) := by norm_num [w127, intOdd, intWords]
  have hc1 : (w127.c1 : ℝ) = (5 : ℝ) := by norm_num [w127, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w127_hcert72 hN hlo hhi

theorem w128_guard : QGuard aLB72 w128 := by
  have ha : (w128.a : ℝ) = (15 : ℝ) := by norm_num [w128, intOdd, intWords]
  have hb : (w128.b : ℝ) = (16 : ℝ) := by norm_num [w128, intOdd, intWords]
  have hc0 : (w128.c0 : ℝ) = (-14 : ℝ) := by norm_num [w128, intOdd, intWords]
  have hc1 : (w128.c1 : ℝ) = (1 : ℝ) := by norm_num [w128, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w128_hcert72 hN hlo hhi

theorem w129_guard : QGuard aLB72 w129 := by
  have ha : (w129.a : ℝ) = (16 : ℝ) := by norm_num [w129, intOdd, intWords]
  have hb : (w129.b : ℝ) = (97/6 : ℝ) := by norm_num [w129, intOdd, intWords]
  have hc0 : (w129.c0 : ℝ) = (-6 : ℝ) := by norm_num [w129, intOdd, intWords]
  have hc1 : (w129.c1 : ℝ) = (1/2 : ℝ) := by norm_num [w129, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w129_hcert72 hN hlo hhi

theorem w130_guard : QGuard aLB72 w130 := by
  have ha : (w130.a : ℝ) = (97/6 : ℝ) := by norm_num [w130, intOdd, intWords]
  have hb : (w130.b : ℝ) = (182/11 : ℝ) := by norm_num [w130, intOdd, intWords]
  have hc0 : (w130.c0 : ℝ) = (91 : ℝ) := by norm_num [w130, intOdd, intWords]
  have hc1 : (w130.c1 : ℝ) = (-11/2 : ℝ) := by norm_num [w130, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  exact w130_hcert72 hN hlo hhi


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
