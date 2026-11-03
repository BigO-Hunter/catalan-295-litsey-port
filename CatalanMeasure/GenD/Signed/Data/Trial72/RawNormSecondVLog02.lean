module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog02
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row4 : logUpperWOK
    (((secondVTail.drop (1 * 4)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondVTail))
    (secondVLogUBs.getD 4 0) = true := by
  -- kcost: 1.1938 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row5 : logUpperWOK
    (((secondVTail.drop (1 * 5)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondVTail))
    (secondVLogUBs.getD 5 0) = true := by
  -- kcost: 1.1860 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog02
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog02.row4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog02.row5
