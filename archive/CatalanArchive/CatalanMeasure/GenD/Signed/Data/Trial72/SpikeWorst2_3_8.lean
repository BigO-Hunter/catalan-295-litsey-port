module
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_3
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_8
open Set CatalanMeasure.Signed.Consts
noncomputable section

private theorem checked24 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 104857600000 116457641747353809469833216000 9127031979995069681141940639412525139237648990208000 698916148090120593294405286 349455119732353745813504000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row24 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (13058947293411277440351651 : ℝ)/6044629098073145873530880000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (2954312706550833698643 : ℝ)/349455119732353745813504000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked24 hx
  have he : 0 ≤ (4224653170409641247932526469570505603692930007040000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (2954312706550833698643 : ℝ)/349455119732353745813504000 + x/2) - (13058947293411277440351651 : ℝ)/6044629098073145873530880000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked25 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 2097152000 2329152834947076189396664320 1649378877800206604166800502024453255892501004288000 5591335093346377848022639574 2795640957858829966508032000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row25 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (294991184966659519639567 : ℝ)/120892581961462917470617600 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (26588814358957503287787 : ℝ)/2795640957858829966508032000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked25 hx
  have he : 0 ≤ (675944507265542599669204235131280896590868801126400000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (26588814358957503287787 : ℝ)/2795640957858829966508032000 + x/2) - (294991184966659519639567 : ℝ)/120892581961462917470617600) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

private theorem checked26 :
    (shareN SpikeCell2_3.NP 120 3 (-12) (-8) 2621440000 2911441043683845236745830400 17760720850845342114027817651618381808543754878976000 44730733924399740699187692166 22365127662870639732064256000).all
      (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s, measured normalized share-check class.
  decide +kernel

theorem row26 {x : ℝ} (hx : x ∈ Icc (((-12 : ℤ) : ℝ)/2^3) (((-8 : ℤ) : ℝ)/2^3)) :
    (397062809534745431443623 : ℝ)/151115727451828646838272000 ≤ ((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) *
      (1 + (239299329230617529590083 : ℝ)/22365127662870639732064256000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_3.NP) (m := 120)
    (by decide +kernel) SpikeCell2_3.mob_exact (by decide +kernel) checked26 hx
  have he : 0 ≤ (6759445072655425996692042351312808965908688011264000000 : ℝ) *
      (((5 : ℝ)/288230376151711744 * zv SpikeNormalized2.V x - (13557453843224073 : ℝ)/703687441776640) * (1 + (239299329230617529590083 : ℝ)/22365127662870639732064256000 + x/2) - (397062809534745431443623 : ℝ)/151115727451828646838272000) := by
    convert h using 1 <;> push_cast <;> ring
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right he (by norm_num))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeWorst2_3_8
