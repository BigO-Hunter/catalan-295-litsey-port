module

public import CatalanMeasure.GenD.Signed.Data.Cells.Q1.NearFq
public import CatalanMeasure.GenD.Signed.Data.Trial.T1Fields

@[expose] public section

/-! Shared-path identification of the NEAR top data with the trial-1 literals. -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

theorem q1nearTs_eq : q1nearTs = CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial.T1.trial.qFn)) := by decide +kernel
theorem q1nearFq_plogs : q1nearFq.plogs = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.plogs.take 2 := by decide +kernel
theorem q1nearFq_poles : q1nearFq.poles = CatalanMeasure.GenD.Signed.Data.Trial.T1.nearFq.poles := by decide +kernel

end CatalanMeasure.GenD.Signed.Data.Cells
