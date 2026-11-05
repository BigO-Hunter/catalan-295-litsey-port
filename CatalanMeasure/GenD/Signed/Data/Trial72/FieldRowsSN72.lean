module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72Bridge
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSN2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem endpoints : FieldRowsSN72Bridge.Endpoints where
  t0 := FieldRowSN0.eventual
  t1 := FieldRowSN1.eventual
  t2 := FieldRowSN2.eventual

theorem hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DA i N).fNeg x ≤ SnA i + ε := FieldRowsSN72Bridge.hSnA endpoints
#print axioms hSnA

theorem hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (-1 : ℝ) 0, (I.DB i N).fNeg x ≤ SnB i + ε := FieldRowsSN72Bridge.hSnB endpoints
#print axioms hSnB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSN72
