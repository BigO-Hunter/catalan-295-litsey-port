module

public import CatalanMeasure.GenD.Signed.Data.Cells.Q0.FrFq

@[expose] public section

/-! FR, alpha = 0.0: the box cell `V` at the end x = -1 (`boxOK`: polynomial range, unimodal pole ranges). -/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

def q0frV0Lo : ℚ := qmk (-1) 1 0 0
def q0frV0Hi : ℚ := qmk (-17592186044415) 1 0 44
theorem q0frV0 : boxOK q0frFq 56 q0frV0Lo q0frV0Hi [] q0frT = true := by decide +kernel
theorem q0frV0Bound : ∀ x ∈ Icc ((q0frV0Lo : ℚ) : ℝ) ((q0frV0Hi : ℚ) : ℝ), fieldTower q0frFq (poleF q0frFq.poles) 0 x ≤ (q0frT : ℝ) :=
  boxOK_sound _ _ _ _ _ _ q0frV0

end CatalanMeasure.GenD.Signed.Data.Cells
