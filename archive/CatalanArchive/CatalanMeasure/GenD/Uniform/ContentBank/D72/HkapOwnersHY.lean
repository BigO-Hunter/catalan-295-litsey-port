module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.HY

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

theorem w107_guard : QGuard hyLB72 w107 := by
  have ha : (w107.a : ℝ) = (70/9 : ℝ) := by norm_num [w107, intOdd, intWords]
  have hb : (w107.b : ℝ) = (86/11 : ℝ) := by norm_num [w107, intOdd, intWords]
  have hc0 : (w107.c0 : ℝ) = (-105 : ℝ) := by norm_num [w107, intOdd, intWords]
  have hc1 : (w107.c1 : ℝ) = (27/2 : ℝ) := by norm_num [w107, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w107_hcert72

theorem w108_guard : QGuard hyLB72 w108 := by
  have ha : (w108.a : ℝ) = (86/11 : ℝ) := by norm_num [w108, intOdd, intWords]
  have hb : (w108.b : ℝ) = (87/11 : ℝ) := by norm_num [w108, intOdd, intWords]
  have hc0 : (w108.c0 : ℝ) = (-19 : ℝ) := by norm_num [w108, intOdd, intWords]
  have hc1 : (w108.c1 : ℝ) = (5/2 : ℝ) := by norm_num [w108, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w108_hcert72

theorem w109_guard : QGuard hyLB72 w109 := by
  have ha : (w109.a : ℝ) = (87/11 : ℝ) := by norm_num [w109, intOdd, intWords]
  have hb : (w109.b : ℝ) = (8 : ℝ) := by norm_num [w109, intOdd, intWords]
  have hc0 : (w109.c0 : ℝ) = (68 : ℝ) := by norm_num [w109, intOdd, intWords]
  have hc1 : (w109.c1 : ℝ) = (-17/2 : ℝ) := by norm_num [w109, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w109_hcert72

theorem w111_guard : QGuard hyLB72 w111 := by
  have ha : (w111.a : ℝ) = (17/2 : ℝ) := by norm_num [w111, intOdd, intWords]
  have hb : (w111.b : ℝ) = (43/5 : ℝ) := by norm_num [w111, intOdd, intWords]
  have hc0 : (w111.c0 : ℝ) = (-93 : ℝ) := by norm_num [w111, intOdd, intWords]
  have hc1 : (w111.c1 : ℝ) = (11 : ℝ) := by norm_num [w111, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w111_hcert72

theorem w112_guard : QGuard hyLB72 w112 := by
  have ha : (w112.a : ℝ) = (43/5 : ℝ) := by norm_num [w112, intOdd, intWords]
  have hb : (w112.b : ℝ) = (87/10 : ℝ) := by norm_num [w112, intOdd, intWords]
  have hc0 : (w112.c0 : ℝ) = (-7 : ℝ) := by norm_num [w112, intOdd, intWords]
  have hc1 : (w112.c1 : ℝ) = (1 : ℝ) := by norm_num [w112, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w112_hcert72

theorem w113_guard : QGuard hyLB72 w113 := by
  have ha : (w113.a : ℝ) = (87/10 : ℝ) := by norm_num [w113, intOdd, intWords]
  have hb : (w113.b : ℝ) = (35/4 : ℝ) := by norm_num [w113, intOdd, intWords]
  have hc0 : (w113.c0 : ℝ) = (80 : ℝ) := by norm_num [w113, intOdd, intWords]
  have hc1 : (w113.c1 : ℝ) = (-9 : ℝ) := by norm_num [w113, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w113_hcert72

theorem w114_guard : QGuard hyLB72 w114 := by
  have ha : (w114.a : ℝ) = (35/4 : ℝ) := by norm_num [w114, intOdd, intWords]
  have hb : (w114.b : ℝ) = (97/11 : ℝ) := by norm_num [w114, intOdd, intWords]
  have hc0 : (w114.c0 : ℝ) = (80 : ℝ) := by norm_num [w114, intOdd, intWords]
  have hc1 : (w114.c1 : ℝ) = (-9 : ℝ) := by norm_num [w114, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w114_hcert72

theorem w117_guard : QGuard hyLB72 w117 := by
  have ha : (w117.a : ℝ) = (66/7 : ℝ) := by norm_num [w117, intOdd, intWords]
  have hb : (w117.b : ℝ) = (86/9 : ℝ) := by norm_num [w117, intOdd, intWords]
  have hc0 : (w117.c0 : ℝ) = (-66 : ℝ) := by norm_num [w117, intOdd, intWords]
  have hc1 : (w117.c1 : ℝ) = (7 : ℝ) := by norm_num [w117, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w117_hcert72

theorem w118_guard : QGuard hyLB72 w118 := by
  have ha : (w118.a : ℝ) = (86/9 : ℝ) := by norm_num [w118, intOdd, intWords]
  have hb : (w118.b : ℝ) = (202/21 : ℝ) := by norm_num [w118, intOdd, intWords]
  have hc0 : (w118.c0 : ℝ) = (20 : ℝ) := by norm_num [w118, intOdd, intWords]
  have hc1 : (w118.c1 : ℝ) = (-2 : ℝ) := by norm_num [w118, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using w118_hcert72

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
