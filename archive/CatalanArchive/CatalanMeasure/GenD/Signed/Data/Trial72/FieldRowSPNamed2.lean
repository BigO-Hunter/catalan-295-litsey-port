module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2NamedCover
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPNamed2
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem eventual : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (0 : ℝ) 1, (T2.D N).fPosS y ≤ (FieldRowSP2.S : ℝ) + ε :=
  FieldRowSP2.eventualOf CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover.before CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover.after
#print axioms eventual

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPNamed2
