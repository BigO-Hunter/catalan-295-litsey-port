module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_4
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_3
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho09_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 47872449542372765267394560000 0 23661581182523683983608752073230211969123346771083264000 19864252441814 9932111872000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho10_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 478724495423727652673945600000 0 2139840767862376059090122754177621547974432963824713728000 158914048232326 79456894976000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho11_checked : (shareN SpikeCell2_4.NP 120 3 (-8) (0) 119681123855931913168486400000 0 4819490945333811545399045542129311430414800480295190528000 1271312644138934 635655159808000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho09_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (554428264382565031396349 : ℝ)/47872449542372765267394560000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (14348907 : ℝ)/9932111872000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho09_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (9932111872000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho10_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (6267481628918211922414581 : ℝ)/478724495423727652673945600000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (129140163 : ℝ)/79456894976000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho10_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (79456894976000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho11_cell {x : ℝ} (hx : x ∈ Set.Icc (((-8 : ℤ) : ℝ)/2^3) (((0 : ℤ) : ℝ)/2^3)) :
    (1764504596222369175617507 : ℝ)/119681123855931913168486400000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (1162261467 : ℝ)/635655159808000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_4.NP) (m := 120)
    (by decide +kernel) SpikeCell2_4.mob_exact (by decide +kernel) rho11_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (635655159808000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_3

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_3.rho09_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_3.rho10_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_4_3.rho11_cell
