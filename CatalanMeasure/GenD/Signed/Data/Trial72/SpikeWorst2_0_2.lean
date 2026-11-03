module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_0
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_2
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked06 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 118784000000 84238215547906559922143232000 68786399045445635909078895034368000 38797351366 19398656000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row06 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (61136833259751066498591 : ℝ)/236118324143482260684800000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (19683 : ℝ)/19398656000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked06 hx
  have he : 0 ≤ (265661932430642606993352058470400000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (19683 : ℝ)/19398656000 + x/2) - (61136833259751066498591 : ℝ)/236118324143482260684800000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked07 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 1900544000000 1347811448766504958754291712000 9922423475182072781007121157193728000 310378850294 155189248000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row07 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (1102371904099206753457817 : ℝ)/3777893186295716170956800000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (177147 : ℝ)/155189248000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked07 hx
  have he : 0 ≤ (34004727351122253695149063484211200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (177147 : ℝ)/155189248000 + x/2) - (1102371904099206753457817 : ℝ)/3777893186295716170956800000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked08 :
    (shareN SpikeCell2_0.NP 120 3 (-16) (-15) 237568000000 168476431095813119844286464000 11143397396199703842279430457131008000 2483031156646 1241513984000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row08 {x : ℝ} (hx : x ∈ Icc (((-16 : ℤ) : ℝ)/2^3) (((-15 : ℤ) : ℝ)/2^3)) :
    (154752619615912435248639 : ℝ)/472236648286964521369600000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (1594323 : ℝ)/1241513984000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_0.NP) (m := 120)
    (by decide +kernel) SpikeCell2_0.mob_exact (by decide +kernel) checked08 hx
  have he : 0 ≤ (34004727351122253695149063484211200000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (1594323 : ℝ)/1241513984000 + x/2) - (154752619615912435248639 : ℝ)/472236648286964521369600000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_0_2
