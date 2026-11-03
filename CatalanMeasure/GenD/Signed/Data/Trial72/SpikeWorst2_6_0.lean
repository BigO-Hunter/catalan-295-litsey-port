module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_0
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked00 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 608174080000 431299663605281586801373347840 17913122448877643111915945004000 3996002 1998000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row00 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (154578047434310544267681 : ℝ)/1208925819614629174706176000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (1 : ℝ)/1998000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked00 hx
  have he : 0 ≤ (140095159680221687281650499584000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (1 : ℝ)/1998000 + x/2) - (154578047434310544267681 : ℝ)/1208925819614629174706176000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked01 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 15204352000000 10782491590132039670034333696000 440981522988964034050091652384000 3552002 1776000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row01 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (4281041501523804306947923 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (1 : ℝ)/1776000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked01 hx
  have he : 0 ≤ (3113225770671593050703344435200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (1 : ℝ)/1776000 + x/2) - (4281041501523804306947923 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked02 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 304087040000 215649831802640793400686673920 26537960065547400071859885312000 9472006 4736000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row02 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (96611282857450635163749 : ℝ)/604462909807314587353088000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (3 : ℝ)/4736000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked02 hx
  have he : 0 ≤ (166038707769151629370845036544000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (3 : ℝ)/4736000 + x/2) - (96611282857450635163749 : ℝ)/604462909807314587353088000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_0
