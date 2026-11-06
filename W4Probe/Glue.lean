module
public import Submission.CatalanMeasure.GenD.Signed.Data.Consts.SpikeP

/-! Glue-pattern validator: the same shape `split_cov.py` emits, on a 4-cell toy,
so the boolean glue is proven to close *without* re-running a cell computation. -/

open CatalanMeasure.Signed.Consts

def toycs : List ℤ := [-1, 0, 1]

theorem toy_cell0 : zNonnegCheck [2, 1, 1] 1 (-(2 : ℤ) ^ 1) (-1) = true := by decide +kernel
theorem toy_cell1 : zNonnegCheck [2, 1, 1] 1 (-1) (0) = true := by decide +kernel
theorem toy_cell2 : zNonnegCheck [2, 1, 1] 1 (0) (1) = true := by decide +kernel
theorem toy_cell3 : zNonnegCheck [2, 1, 1] 1 (1) (2 ^ 1) = true := by decide +kernel

theorem toy : covM1P1 [2, 1, 1] 1 toycs = true := by
  simp only [covM1P1, zNonnegCov, toycs, toy_cell0, toy_cell1, toy_cell2, toy_cell3,
    Bool.true_and, Bool.and_true]

example : zNonnegCov [2, 1, 1] 1 (-(2 : ℤ) ^ 1) toycs (2 ^ 1) = true := toy
