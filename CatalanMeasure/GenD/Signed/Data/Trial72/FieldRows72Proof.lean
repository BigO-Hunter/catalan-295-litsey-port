module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRows72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSC72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSM72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsNear72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCoverBind2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


/-- The endpoint rows at the frozen D72 caps. -/
theorem fieldRows : FieldRows where
  hSnA := FieldRowsSN72.hSnA
  hSpA := FieldRowsSP72.hSpA
  hSyA := FieldRowsSC72.hSyA
  hnegA := FieldRowsSM72.hnegA
  hposA := FieldRowsSPm72.hposA
  hposTopA := FieldRowsSPm72.hposTopA
  hnearA := FieldRowsNear72.hnearA FieldNearCoverBind0.cover FieldNearCoverBind1.cover FieldNearCoverBind2.cover
  hnearTopA := FieldRowsNear72.hnearTopA FieldNearCoverBind0.cover FieldNearCoverBind1.cover FieldNearCoverBind2.cover
  hSnB := FieldRowsSN72.hSnB
  hSpB := FieldRowsSP72.hSpB
  hSyB := FieldRowsSC72.hSyB
  hnegB := FieldRowsSM72.hnegB
  hposB := FieldRowsSPm72.hposB
  hposTopB := FieldRowsSPm72.hposTopB
  hnearB := FieldRowsNear72.hnearB FieldNearCoverBind0.cover FieldNearCoverBind1.cover FieldNearCoverBind2.cover
  hnearTopB := FieldRowsNear72.hnearTopB FieldNearCoverBind0.cover FieldNearCoverBind1.cover FieldNearCoverBind2.cover
#print axioms fieldRows

end CatalanMeasure.GenD.Signed.Data.Trial72.Rows72
