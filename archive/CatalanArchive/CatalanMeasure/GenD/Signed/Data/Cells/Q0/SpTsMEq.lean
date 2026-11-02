module

public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpTsM
public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.SpFq

@[expose] public section

/-! The merged SP Laurent list equals `mergeL q0spTs` (Core merge lemma `lfieldTower_mergeL`). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q0spTsM_eq : q0spTsM = mergeL q0spTs := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
