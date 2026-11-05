module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN2Bridge

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN2
open Set Filter CatalanMeasure.Signed
abbrev S := FieldRowSN2Bridge.S
theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T2.D N).fNeg y ≤ (S : ℝ) + ε :=
  FieldRowSN2Bridge.eventualOf CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover.named
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN2
