module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_0
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_4
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked12 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 3801088000000 2695622897533009917508583424000 1168184861539077834732467993032370683904000 10170503477634406 5085241278464000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row12 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (3960700623527057079978217 : ℝ)/7555786372591432341913600000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (10460353203 : ℝ)/5085241278464000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked12 hx
  have he : 0 ≤ (2228533811683148018165289024501265203200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (10460353203 : ℝ)/5085241278464000 + x/2) - (3960700623527057079978217 : ℝ)/7555786372591432341913600000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked13 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 15204352000000 10782491590132039670034333696000 42263765045850977714044198548312135041024000 81364048741781654 40681930227712000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row13 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (17911775576037904804816919 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (94143178827 : ℝ)/40681930227712000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked13 hx
  have he : 0 ≤ (71313081973860736581289248784040486502400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (94143178827 : ℝ)/40681930227712000 + x/2) - (17911775576037904804816919 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked14 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 7602176000000 5391245795066019835017166848000 190401321242960758878656120314018278670336000 650912578220610886 325455441821696000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row14 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (10086730713014800878150827 : ℝ)/15111572745182864683827200000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (847288609443 : ℝ)/325455441821696000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked14 hx
  have he : 0 ≤ (285252327895442946325156995136161946009600000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (847288609443 : ℝ)/325455441821696000 + x/2) - (10086730713014800878150827 : ℝ)/15111572745182864683827200000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_4
