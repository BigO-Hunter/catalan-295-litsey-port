module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormBounds
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormFirstP

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem firstP_sq : nSq NormData.firstPInt 0 ≤ firstPSqUB := by
  exact NormFirstP.squareFirstP
theorem firstV_sq : nSq NormData.firstVInt 0 ≤ firstVSqUB := by
  -- kcost: 0.160 s measured same-class160 coefficient square.
  decide +kernel
theorem secondP_sq : nSq NormData.secondPInt 0 ≤ secondPSqUB := by
  -- kcost: 0.160 s measured same-class160 coefficient square.
  decide +kernel
theorem secondV_sq : nSq NormData.secondVInt 0 ≤ secondVSqUB := by
  -- kcost: 0.160 s measured same-class160 coefficient square.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares.firstP_sq
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares.firstV_sq
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares.secondP_sq
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormSquares.secondV_sq
