module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowLC07

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

theorem w077_guard : QGuard (cCellLB Low.LC07.cell P72 p72_admissible) w077 := by
  have ha : (w077.a : ℝ) = (97/21 : ℝ) := by norm_num [w077, intOdd, intWords]
  have hb : (w077.b : ℝ) = (97000000021/21000000000 : ℝ) := by norm_num [w077, intOdd, intWords]
  have hc0 : (w077.c0 : ℝ) = (74 : ℝ) := by norm_num [w077, intOdd, intWords]
  have hc1 : (w077.c1 : ℝ) = (-16 : ℝ) := by norm_num [w077, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC07.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC07.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC07.cell.coprime_of_gt (by decide) hp hcap
  simpa only [div_one] using (w077_hcert72 hpos
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi) hcop).1

theorem w078_guard : QGuard (cCellLB Low.LC07.cell P72 p72_admissible) w078 := by
  have ha : (w078.a : ℝ) = (97000000021/21000000000 : ℝ) := by norm_num [w078, intOdd, intWords]
  have hb : (w078.b : ℝ) = (37/8 : ℝ) := by norm_num [w078, intOdd, intWords]
  have hc0 : (w078.c0 : ℝ) = (74 : ℝ) := by norm_num [w078, intOdd, intWords]
  have hc1 : (w078.c1 : ℝ) = (-16 : ℝ) := by norm_num [w078, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 Low.LC07.cell.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : Low.LC07.cell.modulus < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hcop := Low.LC07.cell.coprime_of_gt (by decide) hp hcap
  simpa only [div_one] using (w078_hcert72 hpos
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi) hcop).1


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
