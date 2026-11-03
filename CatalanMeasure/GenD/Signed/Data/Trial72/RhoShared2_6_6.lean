module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_6
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho18_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 47872449542372765267394560000 0 9229327409574938014283348887094488900804263837185273493454848000 2666142097524466743046 1333065489701666816000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho19_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 478724495423727652673945600000 0 831327394120160425409553574446328166131073109805246098532466688000 21329147898316867055414 10664523917613334528000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho20_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 239362247711863826336972800000 0 3731489099849586446543404472264364552121484604126021074177490944000 170633283249625134442726 85316191340906676224000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho18_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (1611245691901060781528781 : ℝ)/47872449542372765267394560000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (5559060566555523 : ℝ)/1333065489701666816000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho18_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (1333065489701666816000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho19_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (18141526230635883336138267 : ℝ)/478724495423727652673945600000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (50031545098999707 : ℝ)/10664523917613334528000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho19_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (10664523917613334528000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho20_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (10178737622362727916059887 : ℝ)/239362247711863826336972800000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (450283905890997363 : ℝ)/85316191340906676224000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho20_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (85316191340906676224000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_6

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_6.rho18_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_6.rho19_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_6.rho20_cell
