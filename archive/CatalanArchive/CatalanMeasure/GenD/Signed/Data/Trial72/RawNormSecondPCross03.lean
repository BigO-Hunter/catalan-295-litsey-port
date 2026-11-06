module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem cross12 : (((secondPTail.drop (4 * 12)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 12 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross13 : (((secondPTail.drop (4 * 13)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 13 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross14 : (((secondPTail.drop (4 * 14)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 14 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel
theorem cross15 : (((secondPTail.drop (4 * 15)).take 4).map (nCross NormData.secondPInt)).sum ≤
    secondPCrossUBs.getD 15 0 := by
  -- kcost: 1.81 s measured same-class maxheight firstP four-tail pilot;640 coefficient visits.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03.cross12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03.cross13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03.cross14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSecondPCross03.cross15
