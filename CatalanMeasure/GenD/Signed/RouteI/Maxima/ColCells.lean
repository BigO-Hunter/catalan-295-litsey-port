module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColData
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 1 cell declaration(s); Mobius transform at base 2(mass+1), descending decode (X: 5-10 s per cell at degree 395)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCells
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.ColInst
theorem y_cell0 : cellCheck csY ⟨0, 1, 1⟩ 127=true := by decide +kernel -- kcost: 1.5 s (standalone 6 Nov)
theorem y_hcells : ∀ i : Fin cellsY.length,cellCheck csY (cellsY.get i) (vsY.getD i 0)=true := by
  intro i
  obtain ⟨i,hi⟩ := i
  have h : i<1 := by simpa [cellsY] using hi
  interval_cases i
  · exact y_cell0
#print axioms y_cell0
#print axioms y_hcells
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCells
