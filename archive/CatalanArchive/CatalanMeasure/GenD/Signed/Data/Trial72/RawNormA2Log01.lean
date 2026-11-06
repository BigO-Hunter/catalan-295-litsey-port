module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log01
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row2 : logUpperWOK
    (((A2Tail.drop (1 * 2)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 2 0) = true := by
  -- kcost: 0.2320 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row3 : logUpperWOK
    (((A2Tail.drop (1 * 3)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 3 0) = true := by
  -- kcost: 0.2326 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log01.row2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log01.row3
