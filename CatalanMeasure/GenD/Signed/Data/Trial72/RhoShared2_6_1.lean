module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_6
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_1
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho03_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 56320528873379723843993600000 0 52010322387503568688703708546220363813788581888000 75776054 37888000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho04_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 957448990847455305347891200000 0 8068702651541670637551134221335336422048878559232000 606208486 303104000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho05_checked : (shareN SpikeCell2_6.NP 120 3 (8) (12) 23936224771186382633697280000 0 1801716158912459692897335602284004166098711740416000 4849668374 2424832000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho03_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (319470724746743825184577 : ℝ)/56320528873379723843993600000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (27 : ℝ)/37888000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho03_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (37888000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho04_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (6195198773833533582685191 : ℝ)/957448990847455305347891200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (243 : ℝ)/303104000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho04_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (303104000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho05_cell {x : ℝ} (hx : x ∈ Set.Icc (((8 : ℤ) : ℝ)/2^3) (((12 : ℤ) : ℝ)/2^3)) :
    (172921072639196765826351 : ℝ)/23936224771186382633697280000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (2187 : ℝ)/2424832000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_6.NP) (m := 120)
    (by decide +kernel) SpikeCell2_6.mob_exact (by decide +kernel) rho05_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (2424832000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_1

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_1.rho03_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_1.rho04_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_6_1.rho05_cell
