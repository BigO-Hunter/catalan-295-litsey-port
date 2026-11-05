module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.ZL

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

theorem w131_guard : QGuard (zLLB P72 p72_admissible) w131 := by
  have ha : (w131.a : ℝ) = (186/11 : ℝ) := by norm_num [w131, intOdd, intWords]
  have hb : (w131.b : ℝ) = (86/5 : ℝ) := by norm_num [w131, intOdd, intWords]
  have hc0 : (w131.c0 : ℝ) = (-93 : ℝ) := by norm_num [w131, intOdd, intWords]
  have hc1 : (w131.c1 : ℝ) = (11/2 : ℝ) := by norm_num [w131, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcL6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcL6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hu : ¬p ∣ ZcL6 := not_dvd_ZcL6 hcap
  simpa only [div_one] using w131_hcert72 hpos hu (hp.eq_two_or_odd.resolve_left (by omega))
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w132_guard : QGuard (zLLB P72 p72_admissible) w132 := by
  have ha : (w132.a : ℝ) = (86/5 : ℝ) := by norm_num [w132, intOdd, intWords]
  have hb : (w132.b : ℝ) = (87/5 : ℝ) := by norm_num [w132, intOdd, intWords]
  have hc0 : (w132.c0 : ℝ) = (-7 : ℝ) := by norm_num [w132, intOdd, intWords]
  have hc1 : (w132.c1 : ℝ) = (1/2 : ℝ) := by norm_num [w132, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcL6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcL6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hu : ¬p ∣ ZcL6 := not_dvd_ZcL6 hcap
  simpa only [div_one] using w132_hcert72 hpos hu (hp.eq_two_or_odd.resolve_left (by omega))
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w133_guard : QGuard (zLLB P72 p72_admissible) w133 := by
  have ha : (w133.a : ℝ) = (87/5 : ℝ) := by norm_num [w133, intOdd, intWords]
  have hb : (w133.b : ℝ) = (160/9 : ℝ) := by norm_num [w133, intOdd, intWords]
  have hc0 : (w133.c0 : ℝ) = (80 : ℝ) := by norm_num [w133, intOdd, intWords]
  have hc1 : (w133.c1 : ℝ) = (-9/2 : ℝ) := by norm_num [w133, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_ge_atTop (max 100 ZcL6)] with N hN
  intro p hp hlo hhi
  have hN0 : 100 ≤ N := (le_max_left _ _).trans hN
  have hpos : 0 < N := by omega
  have hnr : (N : ℝ) < p := by have := ge_one_real hpos; linarith
  have hn : N < p := by exact_mod_cast hnr
  have hcap : ZcL6 < p := ((le_max_right _ _).trans hN).trans_lt hn
  have hu : ¬p ∣ ZcL6 := not_dvd_ZcL6 hcap
  simpa only [div_one] using w133_hcert72 hpos hu (hp.eq_two_or_odd.resolve_left (by omega))
    (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
