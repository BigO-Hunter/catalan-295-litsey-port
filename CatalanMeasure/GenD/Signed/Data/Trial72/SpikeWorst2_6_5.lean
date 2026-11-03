module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_5
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked15 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 15204352000000 10782491590132039670034333696000 3419444113925869437094484189203106933768192000 5207302320342105974 2603643534573568000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row15 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (22643626984973522494473443 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (7625597484987 : ℝ)/2603643534573568000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked15 hx
  have he : 0 ≤ (4564037246327087141202511922178591136153600000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (7625597484987 : ℝ)/2603643534573568000 + x/2) - (22643626984973522494473443 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked16 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 190054400000 134781144876650495875429171200 382651265156105173069440125052445326835712000 41658433813931817766 20829148276588544000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row16 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (316740536796461404228081 : ℝ)/377789318629571617095680000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (68630377364883 : ℝ)/20829148276588544000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked16 hx
  have he : 0 ≤ (456403724632708714120251192217859113615360000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (68630377364883 : ℝ)/20829148276588544000 + x/2) - (316740536796461404228081 : ℝ)/377789318629571617095680000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked17 :
    (shareN SpikeCell2_6.NP 120 3 (8) (12) 15204352000000 10782491590132039670034333696000 277822045528764169082105211511900637843423232000 333267607772209271894 166633186212708352000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row17 {x : ℝ} (hx : x ∈ Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (28745986178424278063127777 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (617673396283947 : ℝ)/166633186212708352000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) checked17 hx
  have he : 0 ≤ (292098383764933577036960763019429832713830400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (617673396283947 : ℝ)/166633186212708352000 + x/2) - (28745986178424278063127777 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_6_5
