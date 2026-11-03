module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross0 : (((secondPTail.drop (4 * 0)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 0 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross1 : (((secondPTail.drop (4 * 1)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 1 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross2 : (((secondPTail.drop (4 * 2)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 2 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross3 : (((secondPTail.drop (4 * 3)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 3 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00.cross0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00.cross1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00.cross2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross00.cross3
