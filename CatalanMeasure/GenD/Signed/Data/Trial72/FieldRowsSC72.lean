module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSC2

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSC72
open Set Filter CatalanMeasure.Signed
open Inputs72 RowsCaps72

set_option Elab.async false
set_option profiler true

theorem hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fCol x ≤ SyA i + ε := by
  intro i ε hε
  fin_cases i
  · exact FieldRowSC0.eventual ε hε
  · exact FieldRowSC1.eventual ε hε

theorem hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fCol x ≤ SyB i + ε := by
  intro i ε hε
  fin_cases i
  · exact FieldRowSC1.eventual ε hε
  · exact FieldRowSC2.eventual ε hε

#print axioms hSyA
#print axioms hSyB
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSC72
