module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC04

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

theorem w056_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w056 := by
  have ha : (w056.a : ℝ) = (4 : ℝ) := by norm_num [w056, intOdd, intWords]
  have hb : (w056.b : ℝ) = (4000000001/1000000000 : ℝ) := by norm_num [w056, intOdd, intWords]
  have hc0 : (w056.c0 : ℝ) = (-12 : ℝ) := by norm_num [w056, intOdd, intWords]
  have hc1 : (w056.c1 : ℝ) = (3 : ℝ) := by norm_num [w056, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w056_hcert72 hpos hlo hhi hcop).1

theorem w057_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w057 := by
  have ha : (w057.a : ℝ) = (4000000001/1000000000 : ℝ) := by norm_num [w057, intOdd, intWords]
  have hb : (w057.b : ℝ) = (12124999997/3000000000 : ℝ) := by norm_num [w057, intOdd, intWords]
  have hc0 : (w057.c0 : ℝ) = (-12 : ℝ) := by norm_num [w057, intOdd, intWords]
  have hc1 : (w057.c1 : ℝ) = (3 : ℝ) := by norm_num [w057, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w057_hcert72 hpos hlo hhi hcop).1

theorem w058_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w058 := by
  have ha : (w058.a : ℝ) = (12124999997/3000000000 : ℝ) := by norm_num [w058, intOdd, intWords]
  have hb : (w058.b : ℝ) = (97/24 : ℝ) := by norm_num [w058, intOdd, intWords]
  have hc0 : (w058.c0 : ℝ) = (-12 : ℝ) := by norm_num [w058, intOdd, intWords]
  have hc1 : (w058.c1 : ℝ) = (3 : ℝ) := by norm_num [w058, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w058_hcert72 hpos hlo hhi hcop).1

theorem w059_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w059 := by
  have ha : (w059.a : ℝ) = (97/24 : ℝ) := by norm_num [w059, intOdd, intWords]
  have hb : (w059.b : ℝ) = (12125000003/3000000000 : ℝ) := by norm_num [w059, intOdd, intWords]
  have hc0 : (w059.c0 : ℝ) = (-12 : ℝ) := by norm_num [w059, intOdd, intWords]
  have hc1 : (w059.c1 : ℝ) = (3 : ℝ) := by norm_num [w059, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w059_hcert72 hpos hlo hhi hcop).1

theorem w060_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w060 := by
  have ha : (w060.a : ℝ) = (12125000003/3000000000 : ℝ) := by norm_num [w060, intOdd, intWords]
  have hb : (w060.b : ℝ) = (86/21 : ℝ) := by norm_num [w060, intOdd, intWords]
  have hc0 : (w060.c0 : ℝ) = (-12 : ℝ) := by norm_num [w060, intOdd, intWords]
  have hc1 : (w060.c1 : ℝ) = (3 : ℝ) := by norm_num [w060, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w060_hcert72 hpos hlo hhi hcop).1

theorem w061_guard : QGuard (cCellLB Low.LC04.cell P72 p72_admissible) w061 := by
  have ha : (w061.a : ℝ) = (86/21 : ℝ) := by norm_num [w061, intOdd, intWords]
  have hb : (w061.b : ℝ) = (37/9 : ℝ) := by norm_num [w061, intOdd, intWords]
  have hc0 : (w061.c0 : ℝ) = (74 : ℝ) := by norm_num [w061, intOdd, intWords]
  have hc1 : (w061.c1 : ℝ) = (-18 : ℝ) := by norm_num [w061, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC04.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC04.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC04.cell.coprime_of_gt (by decide) hp hcap
  exact (w061_hcert72 hpos hlo hhi hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
