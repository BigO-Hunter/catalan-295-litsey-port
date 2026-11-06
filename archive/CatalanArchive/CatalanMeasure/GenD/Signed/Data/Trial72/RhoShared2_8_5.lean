module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_8
public import CatalanMeasure.GenD.Signed.Data.Trial72.RhoSharedScale

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_8_5
open CatalanMeasure.Signed.Consts
noncomputable section

theorem rho15_checked : (shareN SpikeCell2_8.NP 120 3 (14) (16) 957448990847455305347891200000 0 253328653466152685069076767807562054716599534906624402522112000 5207302320342105974 2603643534573568000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho16_checked : (shareN SpikeCell2_8.NP 120 3 (14) (16) 11968112385593191316848640000 0 28348622325581125800555203069818683071017758925626206584832000 41658433813931817766 20829148276588544000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho17_checked : (shareN SpikeCell2_8.NP 120 3 (14) (16) 957448990847455305347891200000 0 20582376068199655719455729194301356228286797200708399689367552000 333267607772209271894 166633186212708352000).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 1.38 s measured from the C28 normalized rho class.
  decide +kernel

theorem rho15_cell {x : ℝ} (hx : x ∈ Set.Icc (((14 : ℤ) : ℝ)/2^3) (((16 : ℤ) : ℝ)/2^3)) :
    (22643626984973522494473443 : ℝ)/957448990847455305347891200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (7625597484987 : ℝ)/2603643534573568000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_8.NP) (m := 120)
    (by decide +kernel) SpikeCell2_8.mob_exact (by decide +kernel) rho15_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (2603643534573568000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho16_cell {x : ℝ} (hx : x ∈ Set.Icc (((14 : ℤ) : ℝ)/2^3) (((16 : ℤ) : ℝ)/2^3)) :
    (316740536796461404228081 : ℝ)/11968112385593191316848640000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (68630377364883 : ℝ)/20829148276588544000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_8.NP) (m := 120)
    (by decide +kernel) SpikeCell2_8.mob_exact (by decide +kernel) rho16_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (20829148276588544000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

theorem rho17_cell {x : ℝ} (hx : x ∈ Set.Icc (((14 : ℤ) : ℝ)/2^3) (((16 : ℤ) : ℝ)/2^3)) :
    (28745986178424278063127777 : ℝ)/957448990847455305347891200000 ≤ (zv SpikeNormalized2.V x / 2148457674918354944) * (1 + (617673396283947 : ℝ)/166633186212708352000 + x/2) := by
  have h := share_cell_Icc (Pn := SpikeNormalized2.V) (MP := SpikeCell2_8.NP) (m := 120)
    (by decide +kernel) SpikeCell2_8.mob_exact (by decide +kernel) rho17_checked hx
  apply RhoSharedScale.sound (by norm_num : 0 < (166633186212708352000 : ℝ)) (by norm_num) (by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_8_5

#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_8_5.rho15_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_8_5.rho16_cell
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoShared2_8_5.rho17_cell
