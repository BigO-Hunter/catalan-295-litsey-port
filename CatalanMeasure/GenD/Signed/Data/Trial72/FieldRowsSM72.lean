module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSM2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSM72
open Set Filter CatalanMeasure.Signed CatalanMeasure.GenD.Analytic
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option profiler true

theorem hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DA i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNA + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [FieldRowSM0.eventual ε hε] with N hN α hα x hx hcut
    exact hN x hx hcut
  · filter_upwards [FieldRowSM1.eventual ε hε] with N hN α hα x hx hcut
    exact hN x hx hcut
#print axioms hnegA

theorem hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
      x ≤ -geometry72.gsN → (I.DB i N).fNegM (groupedMarkedField dc72.toParameters N) x ≤ (capE i).lamNB + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [FieldRowSM1.eventual ε hε] with N hN α hα x hx hcut
    exact hN x hx hcut
  · filter_upwards [FieldRowSM2.eventual ε hε] with N hN α hα x hx hcut
    exact hN x hx hcut
#print axioms hnegB
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSM72
