module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_1_2
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho06_checked : (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 7480070240995744573030400000 0 5096022998592561409034910300977757278651755266048000 38797351366 19398656000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho07_checked : (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 7040066109172465480499200000 0 43241190403742351863035271272670069452706964045824000 310378850294 155189248000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho08_checked : (shareN SpikeCell2_1.NP 120 3 (-15) (-14) 14960140481991489146060800000 0 825555781397602284421698374236743218991925284569088000 2483031156646 1241513984000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho06_cell {x : ℝ} (hx : x ∈ Set.Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (61136833259751066498591 : ℝ)/7480070240995744573030400000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (19683 : ℝ)/19398656000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) rho06_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (19398656000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho07_cell {x : ℝ} (hx : x ∈ Set.Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (64845406123482750203401 : ℝ)/7040066109172465480499200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (177147 : ℝ)/155189248000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) rho07_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (155189248000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho08_cell {x : ℝ} (hx : x ∈ Set.Icc (((-15 : ℤ) : ℝ)/2^3) (((-14 : ℤ) : ℝ)/2^3)) :
    (154752619615912435248639 : ℝ)/14960140481991489146060800000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (1594323 : ℝ)/1241513984000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_1.NP) (m := 120)
    (by decide +kernel) SpikeCell2_1.mob_exact (by decide +kernel) rho08_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (1241513984000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_1_2

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_1_2.rho06_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_1_2.rho07_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_1_2.rho08_cell
