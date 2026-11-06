module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC06

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

theorem w069_guard : QGuard (cCellLB Low.LC06.cell P72 p72_admissible) w069 := by
  have ha : (w069.a : ℝ) = (9/2 : ℝ) := by norm_num [w069, intOdd, intWords]
  have hb : (w069.b : ℝ) = (4500000001/1000000000 : ℝ) := by norm_num [w069, intOdd, intWords]
  have hc0 : (w069.c0 : ℝ) = (-72 : ℝ) := by norm_num [w069, intOdd, intWords]
  have hc1 : (w069.c1 : ℝ) = (16 : ℝ) := by norm_num [w069, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC06.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC06.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC06.cell.coprime_of_gt (by decide) hp hcap
  exact (w069_hcert72 hpos hlo hhi hcop).1

theorem w070_guard : QGuard (cCellLB Low.LC06.cell P72 p72_admissible) w070 := by
  have ha : (w070.a : ℝ) = (4500000001/1000000000 : ℝ) := by norm_num [w070, intOdd, intWords]
  have hb : (w070.b : ℝ) = (86/19 : ℝ) := by norm_num [w070, intOdd, intWords]
  have hc0 : (w070.c0 : ℝ) = (-72 : ℝ) := by norm_num [w070, intOdd, intWords]
  have hc1 : (w070.c1 : ℝ) = (16 : ℝ) := by norm_num [w070, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC06.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC06.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC06.cell.coprime_of_gt (by decide) hp hcap
  exact (w070_hcert72 hpos hlo hhi hcop).1

theorem w071_guard : QGuard (cCellLB Low.LC06.cell P72 p72_admissible) w071 := by
  have ha : (w071.a : ℝ) = (86/19 : ℝ) := by norm_num [w071, intOdd, intWords]
  have hb : (w071.b : ℝ) = (86999999981/19000000000 : ℝ) := by norm_num [w071, intOdd, intWords]
  have hc0 : (w071.c0 : ℝ) = (14 : ℝ) := by norm_num [w071, intOdd, intWords]
  have hc1 : (w071.c1 : ℝ) = (-3 : ℝ) := by norm_num [w071, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC06.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC06.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC06.cell.coprime_of_gt (by decide) hp hcap
  exact (w071_hcert72 hpos hlo hhi hcop).1

theorem w072_guard : QGuard (cCellLB Low.LC06.cell P72 p72_admissible) w072 := by
  have ha : (w072.a : ℝ) = (86999999981/19000000000 : ℝ) := by norm_num [w072, intOdd, intWords]
  have hb : (w072.b : ℝ) = (87/19 : ℝ) := by norm_num [w072, intOdd, intWords]
  have hc0 : (w072.c0 : ℝ) = (14 : ℝ) := by norm_num [w072, intOdd, intWords]
  have hc1 : (w072.c1 : ℝ) = (-3 : ℝ) := by norm_num [w072, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC06.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC06.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC06.cell.coprime_of_gt (by decide) hp hcap
  exact (w072_hcert72 hpos hlo hhi hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
