module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog15
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row30 : logUpperWOK
    (((firstPTail.drop (1 * 30)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 30 0) = true := by
  -- kcost: 1.0892 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row31 : logUpperWOK
    (((firstPTail.drop (1 * 31)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms firstPTail))
    (firstPLogUBs.getD 31 0) = true := by
  -- kcost: 1.0808 s estimated;150 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog15
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog15.row30
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPLog15.row31
