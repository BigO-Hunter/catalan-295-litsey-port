module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_4
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_8
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho24_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 191489798169491061069578240000 0 19609041906645676881488716787299511239072059199873911797286124388352000 698916148090120593294405286 349455119732353745813504000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho25_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 3829795963389821221391564800 0 3543620708858077364464634493759521374972368158161035935924849999872000 5591335093346377848022639574 2795640957858829966508032000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho26_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 4787244954237276526739456000 0 38158157024081130454416154392881029009922039469666747195255731257344000 44730733924399740699187692166 22365127662870639732064256000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho24_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (13058947293411277440351651 : ℝ)/191489798169491061069578240000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (2954312706550833698643 : ℝ)/349455119732353745813504000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho24_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (349455119732353745813504000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho25_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (294991184966659519639567 : ℝ)/3829795963389821221391564800 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (26588814358957503287787 : ℝ)/2795640957858829966508032000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho25_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (2795640957858829966508032000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho26_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (397062809534745431443623 : ℝ)/4787244954237276526739456000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (239299329230617529590083 : ℝ)/22365127662870639732064256000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho26_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (22365127662870639732064256000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_8

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_8.rho24_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_8.rho25_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_8.rho26_cell
