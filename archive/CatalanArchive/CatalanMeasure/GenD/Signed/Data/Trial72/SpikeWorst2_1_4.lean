module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_1
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_1_4
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked12 :
    (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 131072000000 145572052184192261837291520000 40282236604795787404567861828702437376000 10170503477634406 5085241278464000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row12 {x : ℝ} (hx : x ∈ Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (3960700623527057079978217 : ℝ)/7555786372591432341913600000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (10460353203 : ℝ)/5085241278464000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) checked12 hx
  have he : 0 ≤ (76845993506315448902251345672457420800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (10460353203 : ℝ)/5085241278464000 + x/2) - (3960700623527057079978217 : ℝ)/7555786372591432341913600000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked13 :
    (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 524288000000 582288208736769047349166080000 1457371208477619921173937880976280518656000 81364048741781654 40681930227712000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row13 {x : ℝ} (hx : x ∈ Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (17911775576037904804816919 : ℝ)/30223145490365729367654400000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (94143178827 : ℝ)/40681930227712000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) checked13 hx
  have he : 0 ≤ (2459071792202094364872043061518637465600000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (94143178827 : ℝ)/40681930227712000 + x/2) - (17911775576037904804816919 : ℝ)/30223145490365729367654400000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked14 :
    (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 262144000000 291144104368384523674583040000 6565562801481405478574348976345457885184000 650912578220610886 325455441821696000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row14 {x : ℝ} (hx : x ∈ Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (10086730713014800878150827 : ℝ)/15111572745182864683827200000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (847288609443 : ℝ)/325455441821696000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) checked14 hx
  have he : 0 ≤ (9836287168808377459488172246074549862400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (847288609443 : ℝ)/325455441821696000 + x/2) - (10086730713014800878150827 : ℝ)/15111572745182864683827200000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_1_4
