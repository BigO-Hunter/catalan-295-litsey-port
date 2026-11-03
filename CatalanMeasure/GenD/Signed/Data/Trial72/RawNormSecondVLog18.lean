module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog18
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row36 : logUpperWOK
    (((secondVTail.drop (1 * 36)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondVTail))
    (secondVLogUBs.getD 36 0) = true := by
  -- kcost: 1.3754 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row37 : logUpperWOK
    (((secondVTail.drop (1 * 37)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondVTail))
    (secondVLogUBs.getD 37 0) = true := by
  -- kcost: 1.3820 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog18
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog18.row36
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVLog18.row37
