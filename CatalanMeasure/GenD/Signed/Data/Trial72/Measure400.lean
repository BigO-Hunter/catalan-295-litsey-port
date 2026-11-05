module
public import CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyTheorem72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRows72Proof
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0SpikeEnv
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1SpikeEnv
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2SpikeEnv
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FullContent
@[expose] public section
set_option Elab.async false

/-! The D72 measure: mu(G) <= 400, from the content certificate, the field rows
and the three spike environments. -/

namespace CatalanMeasure.GenD.Signed.Data.Trial72.Measure400
open Filter
noncomputable section

theorem catalan_irrationalityMeasure_400 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(400 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  AssemblyTheorem72.of_covers
    (CatalanMeasure.GenD.Uniform.ContentBank.D72.lb72
      CatalanMeasure.GenD.Uniform.ContentBank.D72.fams72)
    CatalanMeasure.GenD.Uniform.ContentBank.D72.hcontent
    Rows72.fieldRows
    CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly.spikeEnv
    CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly.spikeEnv
    CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly.spikeEnv

end
end CatalanMeasure.GenD.Signed.Data.Trial72.Measure400
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.Measure400.catalan_irrationalityMeasure_400
