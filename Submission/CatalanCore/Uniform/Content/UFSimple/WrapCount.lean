module

public import Submission.CatalanCore.Uniform.Content.UFSimple.Count

@[expose] public section

/-! # Deletion accounting for a depth-three wrapped source

A source supported on unedited candidate residues loses one kernel coordinate
per edited candidate class. Only multiply edited candidate classes and edited
credited balanced classes can add a retained source factor. Their loss is paid
by the reduction in raw matrix size.
-/

namespace CatalanCore.Uniform.Content.UFSimple.WrapCount

/-- The nontrivial part of the depth-three gain. -/
def gain (sigma retained : ℕ) : ℕ := sigma + (sigma - retained)

/-- Removing `t` supported coordinates and adding `u` retained factors loses
at most `2*t+u`, including all truncated-subtraction boundary cases. -/
theorem gain_loss (sigma retained t u : ℕ) :
    gain sigma retained ≤ gain (sigma - t) (retained + u) + 2 * t + u := by
  unfold gain
  omega

/-- One deletion per singly edited class, two per multiply edited class,
and one per edited credited balanced class cover the entire gain loss. -/
theorem gain_loss_deletions (sigma retained t1 t2 e k sigma' retained' : ℕ)
    (hbudget : t1 + 2 * t2 + e ≤ k)
    (hsigma : sigma - (t1 + t2) ≤ sigma')
    (hretained : retained' ≤ retained + t2 + e) :
    gain sigma retained ≤ gain sigma' retained' + 2 * k := by
  have h := gain_loss sigma retained (t1 + t2) (t2 + e)
  unfold gain at *
  omega

/-- The raw size drops by twice the deletion count, so the complete
candidate price has debit zero. This lemma needs only the source loss
inequality; the source construction supplies `hgain`. -/
theorem price_debit_zero (n k saving saving' : ℕ)
    (hgain : saving ≤ saving' + 2 * k) :
    2 * (n - k) - saving' ≤ 2 * n - saving := by
  omega

/-- Candidate-level zero debit from the explicit edited-class ledger. -/
theorem candidate_debit_zero (n k d sigma retained t1 t2 e sigma' retained' : ℕ)
    (hbudget : t1 + 2 * t2 + e ≤ k)
    (hsigma : sigma - (t1 + t2) ≤ sigma')
    (hretained : retained' ≤ retained + t2 + e) :
    2 * (n - k) - (d + gain sigma' retained') ≤
      2 * n - (d + gain sigma retained) := by
  apply price_debit_zero
  have := gain_loss_deletions sigma retained t1 t2 e k sigma' retained'
    hbudget hsigma hretained
  omega


end CatalanCore.Uniform.Content.UFSimple.WrapCount
