module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog24
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row48 : logUpperWOK
    (((secondPTail.drop (1 * 48)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 48 0) = true := by
  -- kcost: 1.3370 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row49 : logUpperWOK
    (((secondPTail.drop (1 * 49)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 49 0) = true := by
  -- kcost: 1.3364 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog24
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog24.row48
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog24.row49
