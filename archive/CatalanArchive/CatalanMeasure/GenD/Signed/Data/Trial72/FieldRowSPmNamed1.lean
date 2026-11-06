module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm1CoverBridge
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1NamedCover
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200NamedCover
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116NamedCover
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed1
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem covers : FieldRowSPm1CoverBridge.Covers where
  before := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover.named0B0
  after := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover.named1B0
  lower := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT11200Cover.named0B0
  upper := by simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover.named0B0

theorem top : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T1.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-518573281 : ℚ) / 536870912) : ℚ) : ℝ) + ε := FieldRowSPm1CoverBridge.top covers
#print axioms top

theorem offSmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ)+ε := FieldRowSPm1CoverBridge.offSmall covers
#print axioms offSmall

theorem offWide : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-487700071 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε := FieldRowSPm1CoverBridge.offWide covers
#print axioms offWide

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed1
