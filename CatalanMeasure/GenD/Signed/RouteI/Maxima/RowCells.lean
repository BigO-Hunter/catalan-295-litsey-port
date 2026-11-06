module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Mathlib.Tactic.IntervalCases
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: 18 cell declarations; Mobius transform at base 2(mass+1), descending decode (prior probe: 5.9 s worst cell)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCells
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem x_cell0 : cellCheck csX ⟨-1024, -1023, 1024⟩ 10=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell1 : cellCheck csX ⟨-1023, -1022, 1024⟩ 1=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell2 : cellCheck csX ⟨-511, -510, 512⟩ 2=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell3 : cellCheck csX ⟨-255, -254, 256⟩ 2=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell4 : cellCheck csX ⟨-127, -126, 128⟩ 3=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell5 : cellCheck csX ⟨-63, -62, 64⟩ 4=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell6 : cellCheck csX ⟨-31, -30, 32⟩ 6=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell7 : cellCheck csX ⟨-15, -14, 16⟩ 7=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell8 : cellCheck csX ⟨-7, -6, 8⟩ 12=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell9 : cellCheck csX ⟨-3, -2, 4⟩ 17=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell10 : cellCheck csX ⟨-2, -1, 4⟩ 16=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell11 : cellCheck csX ⟨-2, -1, 8⟩ 17=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell12 : cellCheck csX ⟨-1, 0, 8⟩ 8=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell13 : cellCheck csX ⟨0, 1, 8⟩ 8=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell14 : cellCheck csX ⟨1, 2, 8⟩ 18=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell15 : cellCheck csX ⟨1, 2, 4⟩ 16=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell16 : cellCheck csX ⟨2, 3, 4⟩ 18=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_cell17 : cellCheck csX ⟨3, 4, 4⟩ 33=true := by decide +kernel -- kcost: 5-10 s each (120 s total, standalone 5 Nov)
theorem x_hcells : ∀ i : Fin cellsX.length,cellCheck csX (cellsX.get i) (vsX.getD i 0)=true := by
  intro i
  obtain ⟨i,hi⟩ := i
  have h : i<18 := by simpa [cellsX] using hi
  interval_cases i
  · exact x_cell0
  · exact x_cell1
  · exact x_cell2
  · exact x_cell3
  · exact x_cell4
  · exact x_cell5
  · exact x_cell6
  · exact x_cell7
  · exact x_cell8
  · exact x_cell9
  · exact x_cell10
  · exact x_cell11
  · exact x_cell12
  · exact x_cell13
  · exact x_cell14
  · exact x_cell15
  · exact x_cell16
  · exact x_cell17
#print axioms x_cell0
#print axioms x_cell1
#print axioms x_cell2
#print axioms x_cell3
#print axioms x_cell4
#print axioms x_cell5
#print axioms x_cell6
#print axioms x_cell7
#print axioms x_cell8
#print axioms x_cell9
#print axioms x_cell10
#print axioms x_cell11
#print axioms x_cell12
#print axioms x_cell13
#print axioms x_cell14
#print axioms x_cell15
#print axioms x_cell16
#print axioms x_cell17
#print axioms x_hcells
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCells
