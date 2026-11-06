module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross8 : (((secondPTail.drop (4 * 8)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 8 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross9 : (((secondPTail.drop (4 * 9)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 9 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross10 : (((secondPTail.drop (4 * 10)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 10 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross11 : (((secondPTail.drop (4 * 11)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 11 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02.cross8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02.cross9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02.cross10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross02.cross11
