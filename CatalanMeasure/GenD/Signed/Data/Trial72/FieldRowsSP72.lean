module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72Bridge
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPNamed0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPNamed1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPNamed2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

private theorem endpoints : FieldRowsSP72Bridge.Endpoints where
  t0 := FieldRowSPNamed0.eventual
  t1 := FieldRowSPNamed1.eventual
  t2 := FieldRowSPNamed2.eventual

theorem hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fPosS x ≤ SpA i + ε := FieldRowsSP72Bridge.hSpA endpoints
#print axioms hSpA

theorem hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fPosS x ≤ SpB i + ε := FieldRowsSP72Bridge.hSpB endpoints
#print axioms hSpB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72
