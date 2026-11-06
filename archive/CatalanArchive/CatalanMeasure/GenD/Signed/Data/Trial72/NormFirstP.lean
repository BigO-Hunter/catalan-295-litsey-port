module
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NormFirstP
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Raw firstP finite-square/disk certificates. The full norm still needs
the remaining log/cross chunks; no complete norm bound is claimed here. -/
-- kcost: 0.0640s estimated: 640 rational operations over160 finite coefficients.
theorem squareFirstP : nSq NormData.firstPInt 0 ≤ (1620030563216890883 / 1152921504606846976 : ℚ) := by decide +kernel
-- kcost: 0.0300s estimated: 300 rational operations over75 tails.
theorem diskFirstP : CatalanMeasure.GenD.Signed.Data.Trial.tailOKB ReferenceData.firstPData.tail = true := ReferenceData.firstP_tail
end
end CatalanMeasure.GenD.Signed.Data.Trial72.NormFirstP
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormFirstP.squareFirstP
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormFirstP.diskFirstP
