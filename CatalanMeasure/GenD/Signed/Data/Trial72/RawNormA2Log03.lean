module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log03
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row6 : logUpperWOK
    (((A2Tail.drop (1 * 6)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 6 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row7 : logUpperWOK
    (((A2Tail.drop (1 * 7)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 7 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log03
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log03.row6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log03.row7
