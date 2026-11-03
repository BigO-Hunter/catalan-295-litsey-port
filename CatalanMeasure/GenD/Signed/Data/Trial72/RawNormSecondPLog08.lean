module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog08
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row16 : logUpperWOK
    (((secondPTail.drop (1 * 16)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 16 0) = true := by
  -- kcost: 1.1064 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row17 : logUpperWOK
    (((secondPTail.drop (1 * 17)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms secondPTail))
    (secondPLogUBs.getD 17 0) = true := by
  -- kcost: 1.1118 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog08
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog08.row16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPLog08.row17
