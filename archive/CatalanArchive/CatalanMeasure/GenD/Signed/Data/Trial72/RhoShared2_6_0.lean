module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_0
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho00_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 2252821154935188953759744000 0 78064067762765617838201265090672036719788032000 3996002 1998000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho01_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 957448990847455305347891200000 0 32670004743545681314292465140545903704688820224000 3552002 1776000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho02_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 19148979816949106106957824000 0 1966058068258693845689846240471198801363730432000 9472006 4736000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho00_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (9092826319665326133393 : ℝ)/2252821154935188953759744000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (1 : ℝ)/1998000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho00_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (1998000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho01_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (4281041501523804306947923 : ℝ)/957448990847455305347891200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (1 : ℝ)/1776000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho01_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (1776000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho02_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (96611282857450635163749 : ℝ)/19148979816949106106957824000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (3 : ℝ)/4736000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho02_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (4736000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_0

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_0.rho00_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_0.rho01_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_0.rho02_cell
