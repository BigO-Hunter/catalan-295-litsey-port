module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormP0Data
theorem cross4 : qCross f ((tails.drop 16).take 4) ≤ caps.getD 4 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross5 : qCross f ((tails.drop 20).take 4) ≤ caps.getD 5 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross6 : qCross f ((tails.drop 24).take 4) ≤ caps.getD 6 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross7 : qCross f ((tails.drop 28).take 4) ≤ caps.getD 7 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel


end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01.cross4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01.cross5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01.cross6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP0Cross01.cross7
