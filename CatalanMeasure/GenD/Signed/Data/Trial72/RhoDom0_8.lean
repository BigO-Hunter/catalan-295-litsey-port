module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell2_8
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeCell0_8

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom0_8
open CatalanMeasure.Signed.Consts
noncomputable section

theorem checked : mobDomOK 5 1 SpikeCell2_8.NP SpikeCell0_8.NP = true := by
  -- kcost: .159 s measured dominance class; 121 weighted transformed coefficients.
  decide +kernel

theorem transfer {x : ℝ} (hx : x ∈ Set.Icc (((14 : ℤ) : ℝ)/2^3) (((16 : ℤ) : ℝ)/2^3)) :
    (1311314498851535 : ℝ)/35184372088832 * (zv SpikeNormalized2.V x / 2148457674918354944) ≤
      (5498093038080309 : ℝ)/140737488355328 * (zv SpikeNormalized0.V x / 11260094541988472832) := by
  have h := mob_dom_Icc (p := SpikeNormalized2.V) (q := SpikeNormalized0.V) (m := 120)
    (by decide +kernel) (by decide +kernel) SpikeCell2_8.mob_exact SpikeCell0_8.mob_exact (by decide +kernel) checked hx
  apply le_of_mul_le_mul_left _ (show 0 < (288230376151711744 : ℝ) by norm_num)
  convert h using 1 <;> push_cast <;> ring

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom0_8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom0_8.checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RhoDom0_8.transfer
