module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_6
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked18 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 760217600000 539124579506601983501716684800 124577969583619736757084613182327461844615168000 2666142097524466743046 1333065489701666816000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row18 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (1611245691901060781528781 : ℝ)/1511157274518286468382720000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (5559060566555523 : ℝ)/1333065489701666816000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked18 hx
  have he : 0 ≤ (116839353505973430814784305207771933085532160000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (5559060566555523 : ℝ)/1333065489701666816000 + x/2) - (1611245691901060781528781 : ℝ)/1511157274518286468382720000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked19 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 7602176000000 5391245795066019835017166848000 11221302942540311502303028694203385563324612608000 21329147898316867055414 10664523917613334528000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row19 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (18141526230635883336138267 : ℝ)/15111572745182864683827200000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (50031545098999707 : ℝ)/10664523917613334528000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked19 hx
  have he : 0 ≤ (9347148280477874465182744416621754646842572800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (50031545098999707 : ℝ)/10664523917613334528000 + x/2) - (18141526230635883336138267 : ℝ)/15111572745182864683827200000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked20 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 3801088000000 2695622897533009917508583424000 50367845342706270675480410549170966543575547904000 170633283249625134442726 85316191340906676224000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row20 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (10178737622362727916059887 : ℝ)/7555786372591432341913600000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (450283905890997363 : ℝ)/85316191340906676224000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked20 hx
  have he : 0 ≤ (37388593121911497860730977666487018587370291200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (450283905890997363 : ℝ)/85316191340906676224000 + x/2) - (10178737622362727916059887 : ℝ)/7555786372591432341913600000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_6
