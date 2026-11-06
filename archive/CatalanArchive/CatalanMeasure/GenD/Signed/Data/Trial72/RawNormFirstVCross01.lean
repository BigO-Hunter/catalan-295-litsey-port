module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross4 : (((firstVTail.drop (4 * 4)).take 4).map (nCross NormData.firstVInt)).sum ≤
    firstVCrossUBs.getD 4 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross5 : (((firstVTail.drop (4 * 5)).take 4).map (nCross NormData.firstVInt)).sum ≤
    firstVCrossUBs.getD 5 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross6 : (((firstVTail.drop (4 * 6)).take 4).map (nCross NormData.firstVInt)).sum ≤
    firstVCrossUBs.getD 6 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross7 : (((firstVTail.drop (4 * 7)).take 4).map (nCross NormData.firstVInt)).sum ≤
    firstVCrossUBs.getD 7 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01.cross4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01.cross5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01.cross6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormFirstVCross01.cross7
