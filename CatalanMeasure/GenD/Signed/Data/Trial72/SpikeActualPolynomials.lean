module

public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeChebIntegerPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeChebInteger1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeChebInteger2
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeNormalized0
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeNormalized1
public import CatalanMeasure.GenD.Signed.Data.Trial72.SpikeNormalized2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikeActualPolynomials
open CatalanMeasure.Signed.Consts OAI.InternalCatalan
noncomputable section

theorem coeff0 : SpikeChebIntegerPilot.pn = SpikeNormalized0.Pn := by decide +kernel
theorem denom0 : SpikeChebIntegerPilot.denominator = SpikeNormalized0.denominator := rfl
theorem actual0 (x : ℝ) : chebPs (bSeq SpikeChebIntegerPilot.bs) x = zv SpikeNormalized0.Pn x / (SpikeNormalized0.denominator : ℝ) := by
  rw [ SpikeChebIntegerPilot.actual_polynomial, coeff0, denom0]

theorem coeff1 : SpikeChebInteger1.pn = SpikeNormalized1.Pn := by decide +kernel
theorem denom1 : SpikeChebInteger1.denominator = SpikeNormalized1.denominator := rfl
theorem actual1 (x : ℝ) : chebPs (bSeq SpikeChebInteger1.bs) x = zv SpikeNormalized1.Pn x / (SpikeNormalized1.denominator : ℝ) := by
  rw [ SpikeChebInteger1.actual_polynomial, coeff1, denom1]

theorem coeff2 : SpikeChebInteger2.pn = SpikeNormalized2.Pn := by decide +kernel
theorem denom2 : SpikeChebInteger2.denominator = SpikeNormalized2.denominator := rfl
theorem actual2 (x : ℝ) : chebPs (bSeq SpikeChebInteger2.bs) x = zv SpikeNormalized2.Pn x / (SpikeNormalized2.denominator : ℝ) := by
  rw [ SpikeChebInteger2.actual_polynomial, coeff2, denom2]

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikeActualPolynomials
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeActualPolynomials.actual0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeActualPolynomials.actual1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikeActualPolynomials.actual2
