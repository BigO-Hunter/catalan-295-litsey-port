module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Cert.WLogSpec

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log04
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem row8 : logUpperWOK
    (((A1Tail.drop (1 * 8)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A1Tail))
    (A1LogUBs.getD 8 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel
theorem row9 : logUpperWOK
    (((A1Tail.drop (1 * 9)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A1Tail))
    (A1LogUBs.getD 9 0) = true := by
  -- kcost: 0.2332 s estimated;40 actual input terms; adaptive cutoff/series, per-term2^-128 rounding.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log04
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log04.row8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log04.row9
