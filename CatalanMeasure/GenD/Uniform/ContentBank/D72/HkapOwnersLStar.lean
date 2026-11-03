module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LStar

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

theorem w033_guard : QGuard lstarLB72 w033 := by
  have ha : (w033.a : ℝ) = (74/21 : ℝ) := by norm_num [w033, intOdd, intWords]
  have hb : (w033.b : ℝ) = (60/17 : ℝ) := by norm_num [w033, intOdd, intWords]
  have hc0 : (w033.c0 : ℝ) = (-74 : ℝ) := by norm_num [w033, intOdd, intWords]
  have hc1 : (w033.c1 : ℝ) = (21 : ℝ) := by norm_num [w033, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w033_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w034_guard : QGuard lstarLB72 w034 := by
  have ha : (w034.a : ℝ) = (60/17 : ℝ) := by norm_num [w034, intOdd, intWords]
  have hb : (w034.b : ℝ) = (43/12 : ℝ) := by norm_num [w034, intOdd, intWords]
  have hc0 : (w034.c0 : ℝ) = (-14 : ℝ) := by norm_num [w034, intOdd, intWords]
  have hc1 : (w034.c1 : ℝ) = (4 : ℝ) := by norm_num [w034, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w034_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w035_guard : QGuard lstarLB72 w035 := by
  have ha : (w035.a : ℝ) = (43/12 : ℝ) := by norm_num [w035, intOdd, intWords]
  have hb : (w035.b : ℝ) = (96999999973/27000000000 : ℝ) := by norm_num [w035, intOdd, intWords]
  have hc0 : (w035.c0 : ℝ) = (72 : ℝ) := by norm_num [w035, intOdd, intWords]
  have hc1 : (w035.c1 : ℝ) = (-20 : ℝ) := by norm_num [w035, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w035_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w036_guard : QGuard lstarLB72 w036 := by
  have ha : (w036.a : ℝ) = (96999999973/27000000000 : ℝ) := by norm_num [w036, intOdd, intWords]
  have hb : (w036.b : ℝ) = (97/27 : ℝ) := by norm_num [w036, intOdd, intWords]
  have hc0 : (w036.c0 : ℝ) = (72 : ℝ) := by norm_num [w036, intOdd, intWords]
  have hc1 : (w036.c1 : ℝ) = (-20 : ℝ) := by norm_num [w036, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w036_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w037_guard : QGuard lstarLB72 w037 := by
  have ha : (w037.a : ℝ) = (97/27 : ℝ) := by norm_num [w037, intOdd, intWords]
  have hb : (w037.b : ℝ) = (97000000027/27000000000 : ℝ) := by norm_num [w037, intOdd, intWords]
  have hc0 : (w037.c0 : ℝ) = (72 : ℝ) := by norm_num [w037, intOdd, intWords]
  have hc1 : (w037.c1 : ℝ) = (-20 : ℝ) := by norm_num [w037, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w037_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w038_guard : QGuard lstarLB72 w038 := by
  have ha : (w038.a : ℝ) = (97000000027/27000000000 : ℝ) := by norm_num [w038, intOdd, intWords]
  have hb : (w038.b : ℝ) = (3599999999/1000000000 : ℝ) := by norm_num [w038, intOdd, intWords]
  have hc0 : (w038.c0 : ℝ) = (72 : ℝ) := by norm_num [w038, intOdd, intWords]
  have hc1 : (w038.c1 : ℝ) = (-20 : ℝ) := by norm_num [w038, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w038_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w039_guard : QGuard lstarLB72 w039 := by
  have ha : (w039.a : ℝ) = (3599999999/1000000000 : ℝ) := by norm_num [w039, intOdd, intWords]
  have hb : (w039.b : ℝ) = (18/5 : ℝ) := by norm_num [w039, intOdd, intWords]
  have hc0 : (w039.c0 : ℝ) = (72 : ℝ) := by norm_num [w039, intOdd, intWords]
  have hc1 : (w039.c1 : ℝ) = (-20 : ℝ) := by norm_num [w039, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w039_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w040_guard : QGuard lstarLB72 w040 := by
  have ha : (w040.a : ℝ) = (37/10 : ℝ) := by norm_num [w040, intOdd, intWords]
  have hb : (w040.b : ℝ) = (48499999987/13000000000 : ℝ) := by norm_num [w040, intOdd, intWords]
  have hc0 : (w040.c0 : ℝ) = (-74 : ℝ) := by norm_num [w040, intOdd, intWords]
  have hc1 : (w040.c1 : ℝ) = (20 : ℝ) := by norm_num [w040, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w040_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w041_guard : QGuard lstarLB72 w041 := by
  have ha : (w041.a : ℝ) = (48499999987/13000000000 : ℝ) := by norm_num [w041, intOdd, intWords]
  have hb : (w041.b : ℝ) = (97/26 : ℝ) := by norm_num [w041, intOdd, intWords]
  have hc0 : (w041.c0 : ℝ) = (-74 : ℝ) := by norm_num [w041, intOdd, intWords]
  have hc1 : (w041.c1 : ℝ) = (20 : ℝ) := by norm_num [w041, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w041_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w042_guard : QGuard lstarLB72 w042 := by
  have ha : (w042.a : ℝ) = (97/26 : ℝ) := by norm_num [w042, intOdd, intWords]
  have hb : (w042.b : ℝ) = (48500000013/13000000000 : ℝ) := by norm_num [w042, intOdd, intWords]
  have hc0 : (w042.c0 : ℝ) = (-74 : ℝ) := by norm_num [w042, intOdd, intWords]
  have hc1 : (w042.c1 : ℝ) = (20 : ℝ) := by norm_num [w042, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w042_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w043_guard : QGuard lstarLB72 w043 := by
  have ha : (w043.a : ℝ) = (48500000013/13000000000 : ℝ) := by norm_num [w043, intOdd, intWords]
  have hb : (w043.b : ℝ) = (86/23 : ℝ) := by norm_num [w043, intOdd, intWords]
  have hc0 : (w043.c0 : ℝ) = (-74 : ℝ) := by norm_num [w043, intOdd, intWords]
  have hc1 : (w043.c1 : ℝ) = (20 : ℝ) := by norm_num [w043, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w043_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w044_guard : QGuard lstarLB72 w044 := by
  have ha : (w044.a : ℝ) = (86/23 : ℝ) := by norm_num [w044, intOdd, intWords]
  have hb : (w044.b : ℝ) = (15/4 : ℝ) := by norm_num [w044, intOdd, intWords]
  have hc0 : (w044.c0 : ℝ) = (12 : ℝ) := by norm_num [w044, intOdd, intWords]
  have hc1 : (w044.c1 : ℝ) = (-3 : ℝ) := by norm_num [w044, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w044_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w045_guard : QGuard lstarLB72 w045 := by
  have ha : (w045.a : ℝ) = (15/4 : ℝ) := by norm_num [w045, intOdd, intWords]
  have hb : (w045.b : ℝ) = (86999999977/23000000000 : ℝ) := by norm_num [w045, intOdd, intWords]
  have hc0 : (w045.c0 : ℝ) = (72 : ℝ) := by norm_num [w045, intOdd, intWords]
  have hc1 : (w045.c1 : ℝ) = (-19 : ℝ) := by norm_num [w045, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w045_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w046_guard : QGuard lstarLB72 w046 := by
  have ha : (w046.a : ℝ) = (86999999977/23000000000 : ℝ) := by norm_num [w046, intOdd, intWords]
  have hb : (w046.b : ℝ) = (87/23 : ℝ) := by norm_num [w046, intOdd, intWords]
  have hc0 : (w046.c0 : ℝ) = (72 : ℝ) := by norm_num [w046, intOdd, intWords]
  have hc1 : (w046.c1 : ℝ) = (-19 : ℝ) := by norm_num [w046, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w046_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w047_guard : QGuard lstarLB72 w047 := by
  have ha : (w047.a : ℝ) = (87/23 : ℝ) := by norm_num [w047, intOdd, intWords]
  have hb : (w047.b : ℝ) = (87000000023/23000000000 : ℝ) := by norm_num [w047, intOdd, intWords]
  have hc0 : (w047.c0 : ℝ) = (72 : ℝ) := by norm_num [w047, intOdd, intWords]
  have hc1 : (w047.c1 : ℝ) = (-19 : ℝ) := by norm_num [w047, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w047_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w048_guard : QGuard lstarLB72 w048 := by
  have ha : (w048.a : ℝ) = (87000000023/23000000000 : ℝ) := by norm_num [w048, intOdd, intWords]
  have hb : (w048.b : ℝ) = (71999999981/19000000000 : ℝ) := by norm_num [w048, intOdd, intWords]
  have hc0 : (w048.c0 : ℝ) = (72 : ℝ) := by norm_num [w048, intOdd, intWords]
  have hc1 : (w048.c1 : ℝ) = (-19 : ℝ) := by norm_num [w048, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w048_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w049_guard : QGuard lstarLB72 w049 := by
  have ha : (w049.a : ℝ) = (71999999981/19000000000 : ℝ) := by norm_num [w049, intOdd, intWords]
  have hb : (w049.b : ℝ) = (72/19 : ℝ) := by norm_num [w049, intOdd, intWords]
  have hc0 : (w049.c0 : ℝ) = (72 : ℝ) := by norm_num [w049, intOdd, intWords]
  have hc1 : (w049.c1 : ℝ) = (-19 : ℝ) := by norm_num [w049, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w049_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w050_guard : QGuard lstarLB72 w050 := by
  have ha : (w050.a : ℝ) = (74/19 : ℝ) := by norm_num [w050, intOdd, intWords]
  have hb : (w050.b : ℝ) = (43/11 : ℝ) := by norm_num [w050, intOdd, intWords]
  have hc0 : (w050.c0 : ℝ) = (-74 : ℝ) := by norm_num [w050, intOdd, intWords]
  have hc1 : (w050.c1 : ℝ) = (19 : ℝ) := by norm_num [w050, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w050_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w051_guard : QGuard lstarLB72 w051 := by
  have ha : (w051.a : ℝ) = (43/11 : ℝ) := by norm_num [w051, intOdd, intWords]
  have hb : (w051.b : ℝ) = (43499999989/11000000000 : ℝ) := by norm_num [w051, intOdd, intWords]
  have hc0 : (w051.c0 : ℝ) = (12 : ℝ) := by norm_num [w051, intOdd, intWords]
  have hc1 : (w051.c1 : ℝ) = (-3 : ℝ) := by norm_num [w051, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w051_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w052_guard : QGuard lstarLB72 w052 := by
  have ha : (w052.a : ℝ) = (43499999989/11000000000 : ℝ) := by norm_num [w052, intOdd, intWords]
  have hb : (w052.b : ℝ) = (87/22 : ℝ) := by norm_num [w052, intOdd, intWords]
  have hc0 : (w052.c0 : ℝ) = (12 : ℝ) := by norm_num [w052, intOdd, intWords]
  have hc1 : (w052.c1 : ℝ) = (-3 : ℝ) := by norm_num [w052, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w052_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w053_guard : QGuard lstarLB72 w053 := by
  have ha : (w053.a : ℝ) = (87/22 : ℝ) := by norm_num [w053, intOdd, intWords]
  have hb : (w053.b : ℝ) = (43500000011/11000000000 : ℝ) := by norm_num [w053, intOdd, intWords]
  have hc0 : (w053.c0 : ℝ) = (12 : ℝ) := by norm_num [w053, intOdd, intWords]
  have hc1 : (w053.c1 : ℝ) = (-3 : ℝ) := by norm_num [w053, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w053_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w054_guard : QGuard lstarLB72 w054 := by
  have ha : (w054.a : ℝ) = (43500000011/11000000000 : ℝ) := by norm_num [w054, intOdd, intWords]
  have hb : (w054.b : ℝ) = (3999999999/1000000000 : ℝ) := by norm_num [w054, intOdd, intWords]
  have hc0 : (w054.c0 : ℝ) = (12 : ℝ) := by norm_num [w054, intOdd, intWords]
  have hc1 : (w054.c1 : ℝ) = (-3 : ℝ) := by norm_num [w054, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w054_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)

theorem w055_guard : QGuard lstarLB72 w055 := by
  have ha : (w055.a : ℝ) = (3999999999/1000000000 : ℝ) := by norm_num [w055, intOdd, intWords]
  have hb : (w055.b : ℝ) = (4 : ℝ) := by norm_num [w055, intOdd, intWords]
  have hc0 : (w055.c0 : ℝ) = (12 : ℝ) := by norm_num [w055, intOdd, intWords]
  have hc1 : (w055.c1 : ℝ) = (-3 : ℝ) := by norm_num [w055, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  filter_upwards [eventually_gt_atTop (0 : Nat)] with N hN
  intro p hp hlo hhi
  simpa only [div_one] using
    w055_hcert72 hN (by simpa only [div_one] using hlo) (by simpa only [div_one] using hhi)


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
