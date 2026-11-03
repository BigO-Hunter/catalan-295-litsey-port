module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log00
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row0 : logUpperWOK
    (((A0Tail.drop (1 * 0)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A0Tail))
    (A0LogUBs.getD 0 0) = true := by
  -- kcost: 0.2320 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row1 : logUpperWOK
    (((A0Tail.drop (1 * 1)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A0Tail))
    (A0LogUBs.getD 1 0) = true := by
  -- kcost: 0.2338 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log00.row0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log00.row1
