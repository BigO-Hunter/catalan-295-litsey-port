module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_7
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell1_7

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom1_7
open CatalanMeasure.Signed.Consts
noncomputable section

theorem checked : mobDomOK 5 1 SpikeCell2_7.NP SpikeCell1_7.NP = true := by
  -- kcost: .159 s measured dominance class; 121 weighted transformed coefficients.
  decide +kernel

theorem transfer {x : ℝ} (hx : x ∈ Set.Icc (((12 : ℤ) : ℝ)/2^3) (((14 : ℤ) : ℝ)/2^3)) :
    (1311314498851535 : ℝ)/35184372088832 * (zv SpikeNormalized2.V x / 2148457674918354944) ≤
      (684782692610523 : ℝ)/17592186044416 * (zv SpikeNormalized1.V x / 11219479635730808832) := by
  have h := mob_dom_Icc (p := SpikeNormalized2.V) (q := SpikeNormalized1.V) (m := 120)
    (by decide +kernel) (by decide +kernel) SpikeCell2_7.mob_exact SpikeCell1_7.mob_exact (by decide +kernel) checked hx
  apply le_of_mul_le_mul_left _ (show 0 < (288230376151711744 : ℝ) by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom1_7
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom1_7.checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom1_7.transfer
