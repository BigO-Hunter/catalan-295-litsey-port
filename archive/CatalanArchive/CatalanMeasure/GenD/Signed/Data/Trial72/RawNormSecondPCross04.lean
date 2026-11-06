module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross16 : (((secondPTail.drop (4 * 16)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 16 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross17 : (((secondPTail.drop (4 * 17)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 17 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross18 : (((secondPTail.drop (4 * 18)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 18 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;480 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04.cross16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04.cross17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross04.cross18
