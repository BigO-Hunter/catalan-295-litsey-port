module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_8
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked24 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 3040870400000 2156498318026407934006866739200 264683927419857020753116278542963229037891820716032000 698916148090120593294405286 349455119732353745813504000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row24 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (13058947293411277440351651 : ℝ)/6044629098073145873530880000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (2954312706550833698643 : ℝ)/349455119732353745813504000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked24 hx
  have he : 0 ≤ (122514941941879596190043267617544662507094970204160000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (2954312706550833698643 : ℝ)/349455119732353745813504000 + x/2) - (13058947293411277440351651 : ℝ)/6044629098073145873530880000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked25 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 60817408000 43129966360528158680137334784 47831987456205991520837214558709144420882529124352000 5591335093346377848022639574 2795640957858829966508032000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row25 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (294991184966659519639567 : ℝ)/120892581961462917470617600 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (26588814358957503287787 : ℝ)/2795640957858829966508032000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked25 hx
  have he : 0 ≤ (19602390710700735390406922818807146001135195232665600000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (26588814358957503287787 : ℝ)/2795640957858829966508032000 + x/2) - (294991184966659519639567 : ℝ)/120892581961462917470617600) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked26 :
    (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 76021760000 53912457950660198350171668480 515060904674514921306806711896933072447768891490304000 44730733924399740699187692166 22365127662870639732064256000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row26 {x : ℝ} (hx : x ∈ Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (397062809534745431443623 : ℝ)/151115727451828646838272000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) *
      (1 + (239299329230617529590083 : ℝ)/22365127662870639732064256000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) checked26 hx
  have he : 0 ≤ (196023907107007353904069228188071460011351952326656000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (1255247228561439513 : ℝ)/102034679057612800) * (1 + (239299329230617529590083 : ℝ)/22365127662870639732064256000 + x/2) - (397062809534745431443623 : ℝ)/151115727451828646838272000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_2_8
