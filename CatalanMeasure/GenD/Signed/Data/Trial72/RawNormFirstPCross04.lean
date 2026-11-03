module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross04
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross17 : (((firstPTail.drop (4 * 17)).take 4).map (nCross NormData.firstPInt)).sum ≤
    firstPCrossUBs.getD 17 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross18 : (((firstPTail.drop (4 * 18)).take 4).map (nCross NormData.firstPInt)).sum ≤
    firstPCrossUBs.getD 18 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;480 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross04
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross04.cross17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstPCross04.cross18
