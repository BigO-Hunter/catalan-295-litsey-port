module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog25
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row50 : logUpperWOK
    (((firstVTail.drop (1 * 50)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 50 0) = true := by
  -- kcost: 1.3745 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row51 : logUpperWOK
    (((firstVTail.drop (1 * 51)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstVTail))
    (firstVLogUBs.getD 51 0) = true := by
  -- kcost: 1.3721 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog25
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog25.row50
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVLog25.row51
