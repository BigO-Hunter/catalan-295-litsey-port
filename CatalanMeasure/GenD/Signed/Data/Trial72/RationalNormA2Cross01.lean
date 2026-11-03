module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Cross01
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open RationalNormA2Data
theorem cross4 : qCross f ((tails.drop 16).take 4) ≤ caps.getD 4 0 := by
  -- kcost: 1.2468 s; conservative 3× operation model under TL.
  decide +kernel


end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Cross01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Cross01.cross4
