module
public import CatalanMeasure.GenD.Signed.Davis.ScalarInstance72
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkExcess
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.LinkExcess72
open CatalanMeasure.Signed CatalanMeasure.Signed.Consts Davis.ScalarInstance72

theorem excess_bound (α : ℝ) :
    excess baseTarget72 cost72 target72 (72*cost72) (13/100000) (dc72.n0 : ℝ) α ≤ 13/5000 := by
  rw [dc72_n0, excess_const α (by norm_num) rfl]
  norm_num [target72, gain72]

end CatalanMeasure.GenD.Signed.Data.Trial72.LinkExcess72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.LinkExcess72.excess_bound
