module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormA0Data
theorem cross0 : qCross f ((tails.drop 0).take 4) ≤ caps.getD 0 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross1 : qCross f ((tails.drop 4).take 4) ≤ caps.getD 1 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross2 : qCross f ((tails.drop 8).take 4) ≤ caps.getD 2 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross3 : qCross f ((tails.drop 12).take 4) ≤ caps.getD 3 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel


end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00.cross0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00.cross1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00.cross2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Cross00.cross3
