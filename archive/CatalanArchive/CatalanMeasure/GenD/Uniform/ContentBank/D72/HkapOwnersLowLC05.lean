module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC05

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

theorem w062_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w062 := by
  have ha : (w062.a : ℝ) = (72/17 : ℝ) := by norm_num [w062, intOdd, intWords]
  have hb : (w062.b : ℝ) = (72000000017/17000000000 : ℝ) := by norm_num [w062, intOdd, intWords]
  have hc0 : (w062.c0 : ℝ) = (-72 : ℝ) := by norm_num [w062, intOdd, intWords]
  have hc1 : (w062.c1 : ℝ) = (17 : ℝ) := by norm_num [w062, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w062_hcert72 hpos hlo hhi hcop).1

theorem w063_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w063 := by
  have ha : (w063.a : ℝ) = (72000000017/17000000000 : ℝ) := by norm_num [w063, intOdd, intWords]
  have hb : (w063.b : ℝ) = (30/7 : ℝ) := by norm_num [w063, intOdd, intWords]
  have hc0 : (w063.c0 : ℝ) = (-72 : ℝ) := by norm_num [w063, intOdd, intWords]
  have hc1 : (w063.c1 : ℝ) = (17 : ℝ) := by norm_num [w063, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w063_hcert72 hpos hlo hhi hcop).1

theorem w064_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w064 := by
  have ha : (w064.a : ℝ) = (30/7 : ℝ) := by norm_num [w064, intOdd, intWords]
  have hb : (w064.b : ℝ) = (43/10 : ℝ) := by norm_num [w064, intOdd, intWords]
  have hc0 : (w064.c0 : ℝ) = (-12 : ℝ) := by norm_num [w064, intOdd, intWords]
  have hc1 : (w064.c1 : ℝ) = (3 : ℝ) := by norm_num [w064, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w064_hcert72 hpos hlo hhi hcop).1

theorem w065_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w065 := by
  have ha : (w065.a : ℝ) = (43/10 : ℝ) := by norm_num [w065, intOdd, intWords]
  have hb : (w065.b : ℝ) = (4349999999/1000000000 : ℝ) := by norm_num [w065, intOdd, intWords]
  have hc0 : (w065.c0 : ℝ) = (74 : ℝ) := by norm_num [w065, intOdd, intWords]
  have hc1 : (w065.c1 : ℝ) = (-17 : ℝ) := by norm_num [w065, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w065_hcert72 hpos hlo hhi hcop).1

theorem w066_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w066 := by
  have ha : (w066.a : ℝ) = (4349999999/1000000000 : ℝ) := by norm_num [w066, intOdd, intWords]
  have hb : (w066.b : ℝ) = (87/20 : ℝ) := by norm_num [w066, intOdd, intWords]
  have hc0 : (w066.c0 : ℝ) = (74 : ℝ) := by norm_num [w066, intOdd, intWords]
  have hc1 : (w066.c1 : ℝ) = (-17 : ℝ) := by norm_num [w066, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w066_hcert72 hpos hlo hhi hcop).1

theorem w067_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w067 := by
  have ha : (w067.a : ℝ) = (87/20 : ℝ) := by norm_num [w067, intOdd, intWords]
  have hb : (w067.b : ℝ) = (4350000001/1000000000 : ℝ) := by norm_num [w067, intOdd, intWords]
  have hc0 : (w067.c0 : ℝ) = (74 : ℝ) := by norm_num [w067, intOdd, intWords]
  have hc1 : (w067.c1 : ℝ) = (-17 : ℝ) := by norm_num [w067, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w067_hcert72 hpos hlo hhi hcop).1

theorem w068_guard : QGuard (cCellLB Low.LC05.cell P72 p72_admissible) w068 := by
  have ha : (w068.a : ℝ) = (4350000001/1000000000 : ℝ) := by norm_num [w068, intOdd, intWords]
  have hb : (w068.b : ℝ) = (74/17 : ℝ) := by norm_num [w068, intOdd, intWords]
  have hc0 : (w068.c0 : ℝ) = (74 : ℝ) := by norm_num [w068, intOdd, intWords]
  have hc1 : (w068.c1 : ℝ) = (-17 : ℝ) := by norm_num [w068, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC05.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC05.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC05.cell.coprime_of_gt (by decide) hp hcap
  exact (w068_hcert72 hpos hlo hhi hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
