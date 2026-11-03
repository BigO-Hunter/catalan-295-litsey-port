module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_1
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked03 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 15204352000000 10782491590132039670034333696000 11934649323735765227912947828736000 75776054 37888000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row03 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (5431002320694645028137809 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (27 : ℝ)/37888000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked03 hx
  have he : 0 ≤ (66415483107660651748338014617600000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (27 : ℝ)/37888000 + x/2) - (5431002320694645028137809 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked04 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 15204352000000 10782491590132039670034333696000 108911792690354283056680303706112000 606208486 303104000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row04 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (6195198773833533582685191 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (243 : ℝ)/303104000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked04 hx
  have he : 0 ≤ (531323864861285213986704116940800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (243 : ℝ)/303104000 + x/2) - (6195198773833533582685191 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked05 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 380108800000 269562289753300991750858342400 24319663923771228780190056185856000 4849668374 2424832000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row05 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (172921072639196765826351 : ℝ)/755578637259143234191360000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (2187 : ℝ)/2424832000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked05 hx
  have he : 0 ≤ (106264772972257042797340823388160000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (2187 : ℝ)/2424832000 + x/2) - (172921072639196765826351 : ℝ)/755578637259143234191360000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_1
