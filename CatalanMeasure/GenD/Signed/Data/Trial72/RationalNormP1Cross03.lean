module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormP1Data
theorem cross12 : qCross f ((tails.drop 48).take 4) ≤ caps.getD 12 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross13 : qCross f ((tails.drop 52).take 4) ≤ caps.getD 13 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross14 : qCross f ((tails.drop 56).take 4) ≤ caps.getD 14 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross15 : qCross f ((tails.drop 60).take 4) ≤ caps.getD 15 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel


end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03.cross12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03.cross13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03.cross14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross03.cross15
