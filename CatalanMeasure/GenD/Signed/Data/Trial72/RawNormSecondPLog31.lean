module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog31
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row62 : logUpperWOK
    (((secondPTail.drop (1 * 62)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 62 0) = true := by
  -- kcost: 1.3367 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row63 : logUpperWOK
    (((secondPTail.drop (1 * 63)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 63 0) = true := by
  -- kcost: 1.3265 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog31
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog31.row62
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog31.row63
