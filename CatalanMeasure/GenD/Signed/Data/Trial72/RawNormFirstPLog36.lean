module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog36
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row72 : logUpperWOK
    (((firstPTail.drop (1 * 72)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 72 0) = true := by
  -- kcost: 1.2878 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row73 : logUpperWOK
    (((firstPTail.drop (1 * 73)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 73 0) = true := by
  -- kcost: 1.2758 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog36
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog36.row72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog36.row73
