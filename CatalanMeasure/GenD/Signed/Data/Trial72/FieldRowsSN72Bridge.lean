module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72Bridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

structure Endpoints : Prop where
  t0 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T0.D N).fNeg y ≤ ((-1919817152395/1099511627776 : ℚ) : ℝ) + ε
  t1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T1.D N).fNeg y ≤ ((-1917131856951/1099511627776 : ℚ) : ℝ) + ε
  t2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (-1 : ℝ) 0, (T2.D N).fNeg y ≤ ((-1885879722183/1099511627776 : ℚ) : ℝ) + ε

theorem hSnA (r : Endpoints) : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DA i N).fNeg x ≤ SnA i + ε := by
  intro i ε hε
  fin_cases i
  · exact r.t0 ε hε
  · exact r.t1 ε hε
#print axioms hSnA

theorem hSnB (r : Endpoints) : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DB i N).fNeg x ≤ SnB i + ε := by
  intro i ε hε
  fin_cases i
  · exact r.t1 ε hε
  · exact r.t2 ε hε
#print axioms hSnB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72Bridge
