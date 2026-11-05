module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1Bridge

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1
open Set Filter CatalanMeasure.Signed
abbrev S := FieldRowSN1Bridge.S
theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T1.D N).fNeg y ≤ (S : ℝ) + ε :=
  FieldRowSN1Bridge.eventualOf CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover.named
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1
