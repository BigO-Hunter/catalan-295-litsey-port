module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
Irrationality measures for differences of trigamma values, with every constant written as a series.
`G - 5π²/48` and `G + 5π²/48` have exponent 31.2876; `L(2, χ₋₃)` has exponent 13.7046;
`L(2, χ₋₃) + π²/9` and `L(2, χ₋₃) - π²/9` have exponent 9.4998;
the four numbers `ψ'(a/5) - π²/6` (a = 1, ..., 4) have exponent 23.8272;
the six numbers `ψ'(a/7) - π²/6` (a = 1, ..., 6) have exponent 2207.8697;
`π²` has exponent 6.5253.
For every positive error in the exponent, the bound holds for all fractions p/q with q sufficiently large.
-/

namespace TrigammaDifferences

theorem lambda_minus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((78219 / 2500 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  sorry

theorem lambda_plus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((78219 / 2500 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
  sorry

theorem chi3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((137046 / 10000 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (p : ℝ) / q| := by
  sorry

theorem chi3_plus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((47499 / 5000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  sorry

theorem chi3_minus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((47499 / 5000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  sorry

theorem fifths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem fifths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem fifths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem fifths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((14892 / 625 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths5_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem sevenths6_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((22078697 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| := by
  sorry

theorem pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q →
      (q : ℝ) ^ (-(((65253 / 10000 : ℚ) : ℝ) + e)) <
        |Real.pi ^ 2 - (p : ℝ) / q| := by
  sorry

end TrigammaDifferences
