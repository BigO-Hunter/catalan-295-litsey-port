module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.RowCert.DataN

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option autoImplicit false

/-!
# The bindings of the row, sign N

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

theorem sON : sumW ONE = 0 := by
  decide +kernel -- kcost: 1626 rational additions
theorem sQN : sumW QNE = 0 := by
  decide +kernel -- kcost: 427 rational additions
theorem sCN : sumW CNE = 0 := by
  decide +kernel -- kcost: 628 rational additions
theorem cnON : cancelB 40000 (cellEv 1 (sumP row0) gasNegT) (mirror (mergeA 40000 ONE (segEv GsN))) = true := by
  decide +kernel -- kcost: merge of 3252 events, rational additions
theorem cnQN : cancelB 40000 (cellEv 1 (sumP row0) gasPosT) QNE = true := by
  decide +kernel -- kcost: merge of 854 events, rational additions
theorem cnCN : cancelB 40000 (cellEv 1 (sumP col0) col0) (mirror CNE) = true := by
  decide +kernel -- kcost: merge of 1256 events, rational additions
theorem kON : keyB (GoN ++ GsN) = true := by
  decide +kernel -- kcost: 1626 comparisons
theorem kQN : keyB GqN = true := by
  decide +kernel -- kcost: 427 comparisons
theorem pSN : (GsN.all fun g => decide (0 ≤ g.2.2)) = true := by
  decide +kernel -- kcost: 1 comparisons
theorem chkRN : reflB (GoN ++ GsN) qRN = true := by
  decide +kernel -- kcost: 1626 rational checks
theorem chkON : oppB GqN qON = true := by
  decide +kernel -- kcost: 427 rational checks
theorem chkCN : colB GcN (qC0N :: qCTN) = true := by
  decide +kernel -- kcost: 628 node checks at about 25 ms measured on the unit

end CatalanMeasure.GenD.Signed.RouteI.RowCert
