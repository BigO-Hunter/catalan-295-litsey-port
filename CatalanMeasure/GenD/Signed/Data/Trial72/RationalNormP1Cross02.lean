module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormP1Data
theorem cross8 : qCross f ((tails.drop 32).take 4) ≤ caps.getD 8 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross9 : qCross f ((tails.drop 36).take 4) ≤ caps.getD 9 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross10 : qCross f ((tails.drop 40).take 4) ≤ caps.getD 10 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel

theorem cross11 : qCross f ((tails.drop 44).take 4) ≤ caps.getD 11 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel


end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02.cross8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02.cross9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02.cross10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormP1Cross02.cross11
