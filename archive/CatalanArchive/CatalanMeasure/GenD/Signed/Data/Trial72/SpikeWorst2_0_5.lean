module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_0
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_5
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked15 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 524288000000 582288208736769047349166080000 117911865997443773692913247903555411509248000 5207302320342105974 2603643534573568000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row15 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (22643626984973522494473443 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (7625597484987 : ℝ)/2603643534573568000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked15 hx
  have he : 0 ≤ (157380594700934039351810755937192797798400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (7625597484987 : ℝ)/2603643534573568000 + x/2) - (22643626984973522494473443 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked16 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 6553600000 7278602609209613091864576000 13194871212279488726532418105256735408128000 41658433813931817766 20829148276588544000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row16 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (316740536796461404228081 : ℝ)/377789318629571617095680000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (68630377364883 : ℝ)/20829148276588544000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked16 hx
  have he : 0 ≤ (15738059470093403935181075593719279779840000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (68630377364883 : ℝ)/20829148276588544000 + x/2) - (316740536796461404228081 : ℝ)/377789318629571617095680000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked17 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 524288000000 582288208736769047349166080000 9580070535474626520072593500410366822187008000 333267607772209271894 166633186212708352000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row17 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (28745986178424278063127777 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (617673396283947 : ℝ)/166633186212708352000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked17 hx
  have he : 0 ≤ (10072358060859778518515888379980339059097600000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (617673396283947 : ℝ)/166633186212708352000 + x/2) - (28745986178424278063127777 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_5
