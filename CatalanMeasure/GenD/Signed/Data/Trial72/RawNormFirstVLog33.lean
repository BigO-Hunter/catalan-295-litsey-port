module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog33
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row66 : logUpperWOK
    (((firstVTail.drop (1 * 66)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 66 0) = true := by
  -- kcost: 1.3202 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row67 : logUpperWOK
    (((firstVTail.drop (1 * 67)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 67 0) = true := by
  -- kcost: 1.3244 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog33
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog33.row66
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog33.row67
