module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheData
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCachePilot

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_2
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def form : LF := (pairLF p1_0 p1_2 true).smul (-1)
theorem cache_checked : form.normalize = cache11_0_2 := by
  exact EnergyCachePilot.cache_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_2.cache_checked
