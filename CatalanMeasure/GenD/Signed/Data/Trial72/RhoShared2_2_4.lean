module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_4
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho12_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 239362247711863826336972800000 0 86544680396450605793608350873005249136869387893099986944000 10170503477634406 5085241278464000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho13_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 957448990847455305347891200000 0 3131100358058780431450098897145764629226634127182621835264000 81364048741781654 40681930227712000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho14_checked : (shareN SpikeCell2_2.NP 120 3 (-14) (-12) 478724495423727652673945600000 0 14105833791001181227631641883100882922475566002818510749696000 650912578220610886 325455441821696000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho12_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (3960700623527057079978217 : ℝ)/239362247711863826336972800000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (10460353203 : ℝ)/5085241278464000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho12_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (5085241278464000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho13_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (17911775576037904804816919 : ℝ)/957448990847455305347891200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (94143178827 : ℝ)/40681930227712000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho13_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (40681930227712000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho14_cell {x : ℝ} (hx : x ∈ Set.Icc (((-14 : ℤ) : ℝ)/2^3) (((-12 : ℤ) : ℝ)/2^3)) :
    (10086730713014800878150827 : ℝ)/478724495423727652673945600000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (847288609443 : ℝ)/325455441821696000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_2.NP) (m := 120)
    (by decide +kernel) SpikeCell2_2.mob_exact (by decide +kernel) rho14_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (325455441821696000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_4

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_4.rho12_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_4.rho13_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_2_4.rho14_cell
