module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Bound
public import CatalanCore.Uniform.Bank.Chi3.KContent.Bound
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Bound
public import CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound
public import CatalanCore.Uniform.Bank.HalvesContent.Bound
public import CatalanCore.Uniform.Bank.Irrational

public section

/-!
Proofs of the statements in `ChallengeHybrid.lean`, from the `Level3Bound` theorems of the trigamma-difference
banks (`CatalanCore.Uniform.Bank.*Content.Level3Bound`, `HalvesContent.Bound` and `Chi3.KContent.Bound`).
Each constant is irrational (`CatalanCore.Uniform.Bank.Irrational`), so the bound for reduced fractions
extends to all fractions (`MeasureLBAt.all_of_irrational`); for `G ± 5π²/48` the target is rewritten first.
-/

namespace TrigammaDifferences

open CatalanCore

theorem lambda_minus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((78219 / 2500 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
    have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
      (CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_irrational false)
      (CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_measure false)
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget false = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget, sub_eq_add_neg]
    rw [e] at h
    exact h

theorem lambda_plus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((78219 / 2500 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
    have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
      (CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_irrational true)
      (CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_measure true)
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget true = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget]
    rw [e] at h
    exact h

theorem chi3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((137046 / 10000 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.Chi3.KContent.chi3_irrational
    CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measure_L2_k
  exact h

theorem chi3_plus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((47499 / 5000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_irrational
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_measure
  exact h

theorem chi3_minus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((47499 / 5000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_minus_irrational
    CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_minus_measure
  exact h

theorem fifths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths1_irrational
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths1_measure
  exact h

theorem fifths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths2_irrational
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths2_measure
  exact h

theorem fifths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths3_irrational
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths3_measure
  exact h

theorem fifths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths4_irrational
    CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths4_measure
  exact h

theorem sevenths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨0, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨0, by decide⟩)
  exact h

theorem sevenths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨1, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨1, by decide⟩)
  exact h

theorem sevenths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨2, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨2, by decide⟩)
  exact h

theorem sevenths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨3, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨3, by decide⟩)
  exact h

theorem sevenths5_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨4, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨4, by decide⟩)
  exact h

theorem sevenths6_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_irrational ⟨5, by decide⟩)
    (CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure ⟨5, by decide⟩)
  exact h

theorem pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((65253 / 10000 : ℚ) : ℝ) + e)) <
        |Real.pi ^ 2 - (p : ℝ) / q| := by
  have h := CatalanCore.Measure.MeasureLBAt.all_of_irrational (by norm_num)
    CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_irrational
    CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_measure
  exact h

#print axioms lambda_minus_measure
#print axioms lambda_plus_measure
#print axioms chi3_measure
#print axioms chi3_plus_pi2_measure
#print axioms chi3_minus_pi2_measure
#print axioms fifths1_measure
#print axioms fifths2_measure
#print axioms fifths3_measure
#print axioms fifths4_measure
#print axioms sevenths1_measure
#print axioms sevenths2_measure
#print axioms sevenths3_measure
#print axioms sevenths4_measure
#print axioms sevenths5_measure
#print axioms sevenths6_measure
#print axioms pi2_measure

end TrigammaDifferences
