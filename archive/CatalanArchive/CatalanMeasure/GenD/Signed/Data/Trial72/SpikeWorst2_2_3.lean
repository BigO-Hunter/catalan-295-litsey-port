module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_3
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked09 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 26214400000 29114410436838452367458304000 11013287093692857796287461280710656000 19864252441814 9932111872000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row09 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (554428264382565031396349 : ℝ)/1511157274518286468382720000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (14348907 : ℝ)/9932111872000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked09 hx
  have he : 0 ≤ (30017966213404472227441931903303680000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (14348907 : ℝ)/9932111872000 + x/2) - (554428264382565031396349 : ℝ)/1511157274518286468382720000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked10 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 262144000000 291144104368384523674583040000 995989259105927538426012845696090112000 158914048232326 79456894976000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row10 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (6267481628918211922414581 : ℝ)/15111572745182864683827200000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (129140163 : ℝ)/79456894976000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked10 hx
  have he : 0 ≤ (2401437297072357778195354552264294400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (129140163 : ℝ)/79456894976000 + x/2) - (6267481628918211922414581 : ℝ)/15111572745182864683827200000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked11 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 65536000000 72786026092096130918645760000 2243232902187361182863039258335117312000 1271312644138934 635655159808000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row11 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (1764504596222369175617507 : ℝ)/3777893186295716170956800000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (1162261467 : ℝ)/635655159808000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked11 hx
  have he : 0 ≤ (4802874594144715556390709104528588800000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (1162261467 : ℝ)/635655159808000 + x/2) - (1764504596222369175617507 : ℝ)/3777893186295716170956800000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_3
