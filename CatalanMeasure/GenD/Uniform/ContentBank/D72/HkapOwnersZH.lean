module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.ZH
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.ZUnits

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

private theorem ge_one_real {N : Nat} (hN : 0 < N) : (1 : ℝ) ≤ N := by
  exact_mod_cast hN

theorem w134_guard : QGuard (zHLBcap P72 p72_admissible) w134 := by
  have ha : (w134.a : ℝ) = (132/7 : ℝ) := by norm_num [w134, intOdd, intWords]
  have hb : (w134.b : ℝ) = (97/5 : ℝ) := by norm_num [w134, intOdd, intWords]
  have hc0 : (w134.c0 : ℝ) = (-66 : ℝ) := by norm_num [w134, intOdd, intWords]
  have hc1 : (w134.c1 : ℝ) = (7/2 : ℝ) := by norm_num [w134, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcH6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcH6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  simpa only [div_one] using w134_hcert72 hpos (no_zH6_unit72 hcap) hp (by omega)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w135_guard : QGuard (zHLBnc P72 p72_admissible) w135 := by
  have ha : (w135.a : ℝ) = (97/5 : ℝ) := by norm_num [w135, intOdd, intWords]
  have hb : (w135.b : ℝ) = (20 : ℝ) := by norm_num [w135, intOdd, intWords]
  have hc0 : (w135.c0 : ℝ) = (31 : ℝ) := by norm_num [w135, intOdd, intWords]
  have hc1 : (w135.c1 : ℝ) = (-3/2 : ℝ) := by norm_num [w135, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcH6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcH6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  simpa only [div_one] using w135_hcert72 hpos (no_zH_unit72 hcap)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w136_guard : QGuard (zHLBnc P72 p72_admissible) w136 := by
  have ha : (w136.a : ℝ) = (20 : ℝ) := by norm_num [w136, intOdd, intWords]
  have hb : (w136.b : ℝ) = (222/11 : ℝ) := by norm_num [w136, intOdd, intWords]
  have hc0 : (w136.c0 : ℝ) = (91 : ℝ) := by norm_num [w136, intOdd, intWords]
  have hc1 : (w136.c1 : ℝ) = (-9/2 : ℝ) := by norm_num [w136, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcH6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcH6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  simpa only [div_one] using w136_hcert72 hpos (no_zH_unit72 hcap)
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
