module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.D72
open CatalanMeasure.GenD.Signed.TaylorCell

/-- Remove only affine factors whose absolute value is identically one. -/
def zeroLogFactor : Option (ℚ × ℚ) → Bool
  | none => false
  | some (a, b) => decide (a = 0 ∧ (b = 1 ∨ b = -1))

theorem zeroLogFactor_sound (f : Option (ℚ × ℚ)) (h : zeroLogFactor f = true)
    (x : ℝ) : lfTower f 0 x = 0 := by
  rcases f with _ | ⟨a,b⟩
  · simp [zeroLogFactor] at h
  · simp only [zeroLogFactor, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl | rfl⟩ <;> norm_num [lfTower, linLogTower]

def pruneZeroLogs (ts : List LTerm) : List LTerm :=
  ts.filter (fun t => !zeroLogFactor t.2)

theorem pruneZeroLogs_sound (ts : List LTerm) (x : ℝ) :
    lfieldTower (pruneZeroLogs ts) 0 x = lfieldTower ts 0 x := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases h : zeroLogFactor t.2 with
    | false =>
      have he : pruneZeroLogs (t :: ts) = t :: pruneZeroLogs ts := by
        simp [pruneZeroLogs, List.filter_cons, h]
      rw [he, lf_cons, lf_cons, ih]
    | true =>
      have he : pruneZeroLogs (t :: ts) = pruneZeroLogs ts := by
        simp [pruneZeroLogs, List.filter_cons, h]
      rw [he, ih, lf_cons, zeroLogFactor_sound t.2 h, mul_zero, zero_add]

#print axioms zeroLogFactor_sound
#print axioms pruneZeroLogs_sound

end CatalanMeasure.GenD.Signed.Data.Cells.D72
