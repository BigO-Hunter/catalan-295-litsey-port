module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0CoverBridge
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0NamedCover
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200NamedCover
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed0
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem covers : FieldRowSPm0CoverBridge.Covers where
  before := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover.named0B0
  after := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover.named1B0
  lower := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover.named0B0

theorem top : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T0.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) + ε := FieldRowSPm0CoverBridge.top covers
#print axioms top

theorem offSmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-256471011 : ℚ) / 536870912) : ℚ) : ℝ)+ε := FieldRowSPm0CoverBridge.offSmall covers
#print axioms offSmall

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed0
