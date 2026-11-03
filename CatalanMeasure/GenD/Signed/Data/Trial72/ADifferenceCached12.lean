module

public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable1
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.ADifferenceCached12
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def lower : ℚ := (qlist (raw_ints% [54557312152897, 576460752303423488])).headD 0
def interval : Iv := cachedLoop ivS sqDiv 0 (dl T1.aF T2.aF) (diffTable ATailTable1.table ATailTable2.table) zero
theorem checked : lower.num * ((ivS * ivS : ℕ) : ℤ) ≤ interval.lo * lower.den := by
  -- kcost: 5.472 s TL bound (3× the 1000 cached difference operation model).
  decide +kernel

end
end CatalanMeasure.GenD.Signed.Data.Trial72.ADifferenceCached12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.ADifferenceCached12.checked
