module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog16
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row32 : logUpperWOK
    (((firstVTail.drop (1 * 32)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 32 0) = true := by
  -- kcost: 1.1106 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row33 : logUpperWOK
    (((firstVTail.drop (1 * 33)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 33 0) = true := by
  -- kcost: 1.0886 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog16.row32
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog16.row33
