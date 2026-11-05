module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0Bridge

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0
open Set Filter CatalanMeasure.Signed
abbrev S := FieldRowSN0Bridge.S
theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T0.D N).fNeg y ≤ (S : ℝ) + ε :=
  FieldRowSN0Bridge.eventualOf CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover.named
#print axioms eventual
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0
