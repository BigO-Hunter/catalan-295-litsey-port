module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log07
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row14 : logUpperWOK
    (((A0Tail.drop (1 * 14)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A0Tail))
    (A0LogUBs.getD 14 0) = true := by
  -- kcost: 0.2338 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row15 : logUpperWOK
    (((A0Tail.drop (1 * 15)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A0Tail))
    (A0LogUBs.getD 15 0) = true := by
  -- kcost: 0.2344 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log07
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log07.row14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log07.row15
