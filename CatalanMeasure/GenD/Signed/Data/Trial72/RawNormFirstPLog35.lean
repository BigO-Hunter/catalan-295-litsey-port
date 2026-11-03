module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog35
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row70 : logUpperWOK
    (((firstPTail.drop (1 * 70)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 70 0) = true := by
  -- kcost: 1.2938 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row71 : logUpperWOK
    (((firstPTail.drop (1 * 71)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 71 0) = true := by
  -- kcost: 1.2914 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog35
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog35.row70
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog35.row71
