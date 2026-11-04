module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSP2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72Bridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

structure Endpoints : Prop where
  t0 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (0 : ℝ) 1, (T0.D N).fPosS y ≤ (FieldRowSP0.S : ℝ) + ε
  t1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (0 : ℝ) 1, (T1.D N).fPosS y ≤ (FieldRowSP1.S : ℝ) + ε
  t2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ y ∈ Ioo (0 : ℝ) 1, (T2.D N).fPosS y ≤ (FieldRowSP2.S : ℝ) + ε

theorem hSpA (r : Endpoints) : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DA i N).fPosS x ≤ SpA i + ε := by
  intro i ε hε
  fin_cases i
  · exact r.t0 ε hε
  · exact r.t1 ε hε
#print axioms hSpA

theorem hSpB (r : Endpoints) : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x ∈ Ioo (0 : ℝ) 1, (I.DB i N).fPosS x ≤ SpB i + ε := by
  intro i ε hε
  fin_cases i
  · exact r.t1 ε hε
  · exact r.t2 ε hε
#print axioms hSpB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSP72Bridge
