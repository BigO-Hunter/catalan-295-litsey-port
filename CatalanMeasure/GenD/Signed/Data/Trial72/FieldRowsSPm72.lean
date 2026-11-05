module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72Bridge
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPmNamed2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem endpoints : FieldRowsSPm72Bridge.Endpoints where
  t0top := FieldRowSPmNamed0.top
  t0offSmall := FieldRowSPmNamed0.offSmall
  t1top := FieldRowSPmNamed1.top
  t1offSmall := FieldRowSPmNamed1.offSmall
  t1offWide := FieldRowSPmNamed1.offWide
  t2top := FieldRowSPmNamed2.top
  t2offWide := FieldRowSPmNamed2.offWide

theorem hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPA α + ε := FieldRowsSPm72Bridge.hposA endpoints
#print axioms hposA

theorem hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPA α + ε := FieldRowsSPm72Bridge.hposTopA endpoints
#print axioms hposTopA

theorem hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPB α + ε := FieldRowsSPm72Bridge.hposB endpoints
#print axioms hposB

theorem hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPB α + ε := FieldRowsSPm72Bridge.hposTopB endpoints
#print axioms hposTopB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72
