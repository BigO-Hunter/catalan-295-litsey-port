module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_7
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho21_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 47872449542372765267394560000 0 6722910586018444275708726569148309855992822453240449371761278976000 1365067166564812857536534 682529530727253409792000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho22_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 95744899084745530534789120000 0 121452345323298207484574195627077400003464595496500992364620283904000 10920545437628808898244806 5460236245818027278336000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho23_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 19148979816949106106957824000 0 218603114280159625384831570404669511039428240294408019577212502016000 87364436447023225527531254 43681889966544218226688000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho21_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (2292340305792565014152081 : ℝ)/47872449542372765267394560000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (4052555153018976267 : ℝ)/682529530727253409792000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho21_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (682529530727253409792000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho22_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (5176517351663127552622353 : ℝ)/95744899084745530534789120000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (36472996377170786403 : ℝ)/5460236245818027278336000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho22_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (5460236245818027278336000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho23_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (1164657227477360741988339 : ℝ)/19148979816949106106957824000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (328256967394537077627 : ℝ)/43681889966544218226688000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho23_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (43681889966544218226688000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_7

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_7.rho21_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_7.rho22_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_7.rho23_cell
