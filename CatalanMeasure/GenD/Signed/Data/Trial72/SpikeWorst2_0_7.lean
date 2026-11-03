module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_0
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_7
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked21 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 26214400000 29114410436838452367458304000 3129179906359535960789884138071751285805154304000 1365067166564812857536534 682529530727253409792000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row21 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (2292340305792565014152081 : ℝ)/1511157274518286468382720000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (4052555153018976267 : ℝ)/682529530727253409792000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked21 hx
  have he : 0 ≤ (2062818930864082640592053940219973439303188480000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (4052555153018976267 : ℝ)/682529530727253409792000 + x/2) - (2292340305792565014152081 : ℝ)/1511157274518286468382720000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked22 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 52428800000 58228820873676904734916608000 56530015341313904986653566965563522088452489216000 10920545437628808898244806 5460236245818027278336000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row22 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (5176517351663127552622353 : ℝ)/3022314549036572936765440000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (36472996377170786403 : ℝ)/5460236245818027278336000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked22 hx
  have he : 0 ≤ (33005102893825322249472863043519575028851015680000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (36472996377170786403 : ℝ)/5460236245818027278336000 + x/2) - (5176517351663127552622353 : ℝ)/3022314549036572936765440000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked23 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 10485760000 11645764174735380946983321600 101748857718813062757319664287555671507509182464000 87364436447023225527531254 43681889966544218226688000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row23 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (1164657227477360741988339 : ℝ)/604462909807314587353088000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (328256967394537077627 : ℝ)/43681889966544218226688000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked23 hx
  have he : 0 ≤ (52808164630120515599156580869631320046161625088000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (328256967394537077627 : ℝ)/43681889966544218226688000 + x/2) - (1164657227477360741988339 : ℝ)/604462909807314587353088000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_7
