module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_3
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_7
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked21 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 760217600000 539124579506601983501716684800 90746217284426542862906640004080787288349474816000 1365067166564812857536534 682529530727253409792000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row21 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (2292340305792565014152081 : ℝ)/1511157274518286468382720000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (4052555153018976267 : ℝ)/682529530727253409792000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked21 hx
  have he : 0 ≤ (59821748995058396577169564266379229739792465920000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (4052555153018976267 : ℝ)/682529530727253409792000 + x/2) - (2292340305792565014152081 : ℝ)/1511157274518286468382720000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked22 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 1520435200000 1078249159013203967003433369600 1639370444898103244612953442001342140565122187264000 10920545437628808898244806 5460236245818027278336000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row22 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (5176517351663127552622353 : ℝ)/3022314549036572936765440000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (36472996377170786403 : ℝ)/5460236245818027278336000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked22 hx
  have he : 0 ≤ (957147983920934345234713028262067675836679454720000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (36472996377170786403 : ℝ)/5460236245818027278336000 + x/2) - (5176517351663127552622353 : ℝ)/3022314549036572936765440000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked23 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 304087040000 215649831802640793400686673920 2950716873845578819962270264339114473717766291456000 87364436447023225527531254 43681889966544218226688000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row23 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (1164657227477360741988339 : ℝ)/604462909807314587353088000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (328256967394537077627 : ℝ)/43681889966544218226688000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked23 hx
  have he : 0 ≤ (1531436774273494952375540845219308281338687127552000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (328256967394537077627 : ℝ)/43681889966544218226688000 + x/2) - (1164657227477360741988339 : ℝ)/604462909807314587353088000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_7
