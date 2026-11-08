module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.DataP

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The bindings of the row, sign P

kcost: three merges of cells against segments and three chains of atom conditions; priced at each declaration.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.RowCert

open CatalanMeasure.GenD.Signed.RouteI.FreeRowCap0
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.Davis.CircleCheb
open Set

theorem sOP : sumW OPE = 0 := by
  decide +kernel -- kcost: 597 rational additions
theorem sQP : sumW QPE = 0 := by
  decide +kernel -- kcost: 277 rational additions
theorem sCP : sumW CPE = 0 := by
  decide +kernel -- kcost: 1507 rational additions
theorem cnOP : cancelB 40000 (cellEv 1 (sumP row0) gasPosT) (mergeA 40000 OPE (segEv GsP)) = true := by
  decide +kernel -- kcost: merge of 1194 events, rational additions
theorem cnQP : cancelB 40000 (cellEv 1 (sumP row0) gasNegT) (mirror QPE) = true := by
  decide +kernel -- kcost: merge of 554 events, rational additions
theorem cnCP : cancelB 40000 (cellEv 1 (sumP col0) col0) CPE = true := by
  decide +kernel -- kcost: merge of 3014 events, rational additions
theorem kOP : keyB (GoP ++ GsP) = true := by
  decide +kernel -- kcost: 597 comparisons
theorem kQP : keyB GqP = true := by
  decide +kernel -- kcost: 277 comparisons
theorem pSP : (GsP.all fun g => decide (0 ≤ g.2.2)) = true := by
  decide +kernel -- kcost: 2 comparisons
theorem chkRP : reflB (GoP ++ GsP) qRP = true := by
  decide +kernel -- kcost: 597 rational checks
theorem chkOP : oppB GqP qOP = true := by
  decide +kernel -- kcost: 277 rational checks
theorem chkCP : colB GcP (qC0P :: qCTP) = true := by
  decide +kernel -- kcost: 1507 node checks at about 25 ms measured on the unit

end CatalanMeasure.GenD.Signed.RouteI.RowCert
