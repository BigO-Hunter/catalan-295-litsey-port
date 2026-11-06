module
public import Submission.CatalanMeasure.CellCert.RawInts
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeP

open CatalanMeasure.Signed.Consts

def cutsX : List ℤ := raw_ints% [-14, -12]

theorem cx0 : zNonnegCheck [1000] 4 (-(2 : ℤ) ^ 4) (-14) = true := by decide +kernel
theorem cx1 : zNonnegCheck [1000] 4 (-14) (-12) = true := by decide +kernel
theorem cx2 : zNonnegCheck [1000] 4 (-12) (2 ^ 4) = true := by decide +kernel

theorem cx : covM1P1 [1000] 4 cutsX = true := by
  have h : cutsX = ([-14, -12] : List ℤ) := rfl
  rw [h]
  simp only [covM1P1, zNonnegCov, cx0, cx1, cx2, Bool.and_true]
