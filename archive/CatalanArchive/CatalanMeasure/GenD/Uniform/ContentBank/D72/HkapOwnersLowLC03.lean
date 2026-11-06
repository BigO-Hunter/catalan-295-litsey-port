module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC03

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

private theorem ge_one_real {N : Nat} (hN : 0 < N) : (1 : ℝ) ≤ N := by
  exact_mod_cast hN

theorem w026_guard : QGuard (cCellLBP Low.LC03.cell P72 p72_admissible) w026 := by
  have ha : (w026.a : ℝ) = (80/27 : ℝ) := by norm_num [w026, intOdd, intWords]
  have hb : (w026.b : ℝ) = (86/29 : ℝ) := by norm_num [w026, intOdd, intWords]
  have hc0 : (w026.c0 : ℝ) = (-80 : ℝ) := by norm_num [w026, intOdd, intWords]
  have hc1 : (w026.c1 : ℝ) = (27 : ℝ) := by norm_num [w026, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC03.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC03.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC03.cell.coprime_of_gt (by decide) hp hcap
  exact (w026_hcert72 hpos hlo hhi hcop).1

theorem w027_guard : QGuard (cCellLBP Low.LC03.cell P72 p72_admissible) w027 := by
  have ha : (w027.a : ℝ) = (86/29 : ℝ) := by norm_num [w027, intOdd, intWords]
  have hb : (w027.b : ℝ) = (2999999999/1000000000 : ℝ) := by norm_num [w027, intOdd, intWords]
  have hc0 : (w027.c0 : ℝ) = (6 : ℝ) := by norm_num [w027, intOdd, intWords]
  have hc1 : (w027.c1 : ℝ) = (-2 : ℝ) := by norm_num [w027, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC03.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC03.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC03.cell.coprime_of_gt (by decide) hp hcap
  exact (w027_hcert72 hpos hlo hhi hcop).1

theorem w028_guard : QGuard (cCellLBP Low.LC03.cell P72 p72_admissible) w028 := by
  have ha : (w028.a : ℝ) = (2999999999/1000000000 : ℝ) := by norm_num [w028, intOdd, intWords]
  have hb : (w028.b : ℝ) = (3 : ℝ) := by norm_num [w028, intOdd, intWords]
  have hc0 : (w028.c0 : ℝ) = (6 : ℝ) := by norm_num [w028, intOdd, intWords]
  have hc1 : (w028.c1 : ℝ) = (-2 : ℝ) := by norm_num [w028, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC03.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC03.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC03.cell.coprime_of_gt (by decide) hp hcap
  exact (w028_hcert72 hpos hlo hhi hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
