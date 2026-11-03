module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_3
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_0
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked00 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 20971520000 23291528349470761893966643200 617693877547504934893653276000 3996002 1998000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row00 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (154578047434310544267681 : ℝ)/1208925819614629174706176000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (1 : ℝ)/1998000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked00 hx
  have he : 0 ≤ (4830867575180058182125879296000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (1 : ℝ)/1998000 + x/2) - (154578047434310544267681 : ℝ)/1208925819614629174706176000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked01 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 524288000000 582288208736769047349166080000 15206259413412552898279022496000 3552002 1776000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row01 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (4281041501523804306947923 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (1 : ℝ)/1776000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked01 hx
  have he : 0 ≤ (107352612781779070713908428800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (1 : ℝ)/1776000 + x/2) - (4281041501523804306947923 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked02 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 10485760000 11645764174735380946983321600 915102071225772416271030528000 9472006 4736000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row02 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (96611282857450635163749 : ℝ)/604462909807314587353088000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (3 : ℝ)/4736000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked02 hx
  have he : 0 ≤ (5725472681694883771408449536000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (3 : ℝ)/4736000 + x/2) - (96611282857450635163749 : ℝ)/604462909807314587353088000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_0
