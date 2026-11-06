module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC02

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

theorem w021_guard : QGuard (cCellLBP Low.LC02.cell P72 p72_admissible) w021 := by
  have ha : (w021.a : ℝ) = (20/7 : ℝ) := by norm_num [w021, intOdd, intWords]
  have hb : (w021.b : ℝ) = (42857143/15000000 : ℝ) := by norm_num [w021, intOdd, intWords]
  have hc0 : (w021.c0 : ℝ) = (-20 : ℝ) := by norm_num [w021, intOdd, intWords]
  have hc1 : (w021.c1 : ℝ) = (7 : ℝ) := by norm_num [w021, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC02.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC02.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC02.cell.coprime_of_gt (by decide) hp hcap
  exact (w021_hcert72 hpos hlo hhi hcop).1

theorem w023_guard : QGuard (cCellLBP Low.LC02.cell P72 p72_admissible) w023 := by
  have ha : (w023.a : ℝ) = (3433333333/1200000000 : ℝ) := by norm_num [w023, intOdd, intWords]
  have hb : (w023.b : ℝ) = (43/15 : ℝ) := by norm_num [w023, intOdd, intWords]
  have hc0 : (w023.c0 : ℝ) = (-20 : ℝ) := by norm_num [w023, intOdd, intWords]
  have hc1 : (w023.c1 : ℝ) = (7 : ℝ) := by norm_num [w023, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC02.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC02.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC02.cell.coprime_of_gt (by decide) hp hcap
  exact (w023_hcert72 hpos hlo hhi hcop).1

theorem w024_guard : QGuard (cCellLBP Low.LC02.cell P72 p72_admissible) w024 := by
  have ha : (w024.a : ℝ) = (43/15 : ℝ) := by norm_num [w024, intOdd, intWords]
  have hb : (w024.b : ℝ) = (65999999977/23000000000 : ℝ) := by norm_num [w024, intOdd, intWords]
  have hc0 : (w024.c0 : ℝ) = (66 : ℝ) := by norm_num [w024, intOdd, intWords]
  have hc1 : (w024.c1 : ℝ) = (-23 : ℝ) := by norm_num [w024, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC02.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC02.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC02.cell.coprime_of_gt (by decide) hp hcap
  exact (w024_hcert72 hpos hlo hhi hcop).1

theorem w025_guard : QGuard (cCellLBP Low.LC02.cell P72 p72_admissible) w025 := by
  have ha : (w025.a : ℝ) = (65999999977/23000000000 : ℝ) := by norm_num [w025, intOdd, intWords]
  have hb : (w025.b : ℝ) = (66/23 : ℝ) := by norm_num [w025, intOdd, intWords]
  have hc0 : (w025.c0 : ℝ) = (66 : ℝ) := by norm_num [w025, intOdd, intWords]
  have hc1 : (w025.c1 : ℝ) = (-23 : ℝ) := by norm_num [w025, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC02.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC02.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC02.cell.coprime_of_gt (by decide) hp hcap
  exact (w025_hcert72 hpos hlo hhi hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
