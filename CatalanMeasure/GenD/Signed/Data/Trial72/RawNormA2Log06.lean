module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log06
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row12 : logUpperWOK
    (((A2Tail.drop (1 * 12)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 12 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row13 : logUpperWOK
    (((A2Tail.drop (1 * 13)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
    (A2LogUBs.getD 13 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log06
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log06.row12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log06.row13
