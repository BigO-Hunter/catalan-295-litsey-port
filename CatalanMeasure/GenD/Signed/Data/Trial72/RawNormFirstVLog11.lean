module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog11
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row22 : logUpperWOK
    (((firstVTail.drop (1 * 22)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 22 0) = true := by
  -- kcost: 1.1388 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row23 : logUpperWOK
    (((firstVTail.drop (1 * 23)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 23 0) = true := by
  -- kcost: 1.1172 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog11.row22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog11.row23
