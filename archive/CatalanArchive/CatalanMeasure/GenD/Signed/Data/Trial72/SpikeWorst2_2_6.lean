module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_6
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked18 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 26214400000 29114410436838452367458304000 4295792054607577129554641833873360753262592000 2666142097524466743046 1333065489701666816000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row18 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (1611245691901060781528781 : ℝ)/1511157274518286468382720000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (5559060566555523 : ℝ)/1333065489701666816000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked18 hx
  have he : 0 ≤ (4028943224343911407406355351992135623639040000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (5559060566555523 : ℝ)/1333065489701666816000 + x/2) - (1611245691901060781528781 : ℝ)/1511157274518286468382720000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked19 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 262144000000 291144104368384523674583040000 386941480777252120769069954972530536666365952000 21329147898316867055414 10664523917613334528000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row19 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (18141526230635883336138267 : ℝ)/15111572745182864683827200000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (50031545098999707 : ℝ)/10664523917613334528000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked19 hx
  have he : 0 ≤ (322315457947512912592508428159370849891123200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (50031545098999707 : ℝ)/10664523917613334528000 + x/2) - (18141526230635883336138267 : ℝ)/15111572745182864683827200000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked20 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 131072000000 145572052184192261837291520000 1736822253196767954326910708592102294606053376000 170633283249625134442726 85316191340906676224000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row20 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (10178737622362727916059887 : ℝ)/7555786372591432341913600000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (450283905890997363 : ℝ)/85316191340906676224000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked20 hx
  have he : 0 ≤ (1289261831790051650370033712637483399564492800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (450283905890997363 : ℝ)/85316191340906676224000 + x/2) - (10178737622362727916059887 : ℝ)/7555786372591432341913600000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_6
