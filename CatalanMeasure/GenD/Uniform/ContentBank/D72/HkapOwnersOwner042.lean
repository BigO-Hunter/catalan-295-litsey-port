module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.HkapCore
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Host.Owner042

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

theorem w120_guard : QGuard Host.Phys042.lb w120 := by
  have ha : (w120.a : ℝ) = (96666667/10000000 : ℝ) := by norm_num [w120, intOdd, intWords]
  have hb : (w120.b : ℝ) = (290999999/30000000 : ℝ) := by norm_num [w120, intOdd, intWords]
  have hc0 : (w120.c0 : ℝ) = (599999999/100000000 : ℝ) := by norm_num [w120, intOdd, intWords]
  have hc1 : (w120.c1 : ℝ) = (-1/2 : ℝ) := by norm_num [w120, intOdd, intWords]
  unfold QGuard
  rw [ha, hb, hc0, hc1]
  simpa only [div_one] using Host.Owner042.w120_hcert72


end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
