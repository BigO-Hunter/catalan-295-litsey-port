module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowBounds
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Low.LC02
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

#time theorem w021_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (20 / 7 : ℝ) * N < p) (hr : (p : ℝ) ≤ (42857143 / 15000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC02.cell.modulus) :
    (N : ℝ) * ((-20 : ℝ) + (7 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC02.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-20 : ℝ) + (7 : ℝ) * ((p : ℝ) / N)) = (-20 : ℝ) * N + (7 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC02.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC02.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w023_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (3433333333 / 1200000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (43 / 15 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC02.cell.modulus) :
    (N : ℝ) * ((-20 : ℝ) + (7 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC02.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-20 : ℝ) + (7 : ℝ) * ((p : ℝ) / N)) = (-20 : ℝ) * N + (7 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC02.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC02.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w024_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (43 / 15 : ℝ) * N < p) (hr : (p : ℝ) ≤ (65999999977 / 23000000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC02.cell.modulus) :
    (N : ℝ) * ((66 : ℝ) + (-23 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC02.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((66 : ℝ) + (-23 : ℝ) * ((p : ℝ) / N)) = (66 : ℝ) * N + (-23 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC02.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC02.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w025_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (65999999977 / 23000000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (66 / 23 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC02.cell.modulus) :
    (N : ℝ) * ((66 : ℝ) + (-23 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC02.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((66 : ℝ) + (-23 : ℝ) * ((p : ℝ) / N)) = (66 : ℝ) * N + (-23 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC02.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC02.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
