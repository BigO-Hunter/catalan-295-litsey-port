module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheData

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_2
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def form : LF := (pairLF p0_0 p1_2 true).smul (-1)
theorem cache_checked : form.normalize = cache01_0_2 := by
  -- kcost: 20.4 s measured C32 largest exact normalized-LF case; one directed pair.
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_2.cache_checked
