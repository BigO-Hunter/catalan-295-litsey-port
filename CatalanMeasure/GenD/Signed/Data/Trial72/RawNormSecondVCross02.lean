module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross8 : (((secondVTail.drop (4 * 8)).take 4).map (nCross NormData.secondVInt)).sum ≤
    secondVCrossUBs.getD 8 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross9 : (((secondVTail.drop (4 * 9)).take 4).map (nCross NormData.secondVInt)).sum ≤
    secondVCrossUBs.getD 9 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross10 : (((secondVTail.drop (4 * 10)).take 4).map (nCross NormData.secondVInt)).sum ≤
    secondVCrossUBs.getD 10 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross11 : (((secondVTail.drop (4 * 11)).take 4).map (nCross NormData.secondVInt)).sum ≤
    secondVCrossUBs.getD 11 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02.cross8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02.cross9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02.cross10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondVCross02.cross11
