module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowBounds
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Low.LC03
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

#time theorem w026_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (80 / 27 : ℝ) * N < p) (hr : (p : ℝ) ≤ (86 / 29 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC03.cell.modulus) :
    (N : ℝ) * ((-80 : ℝ) + (27 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC03.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-80 : ℝ) + (27 : ℝ) * ((p : ℝ) / N)) = (-80 : ℝ) * N + (27 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC03.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC03.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w027_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (86 / 29 : ℝ) * N < p) (hr : (p : ℝ) ≤ (2999999999 / 1000000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC03.cell.modulus) :
    (N : ℝ) * ((6 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC03.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((6 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) = (6 : ℝ) * N + (-2 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC03.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC03.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w028_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (2999999999 / 1000000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (3 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC03.cell.modulus) :
    (N : ℝ) * ((6 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLBP Low.LC03.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : p ≤ 4 * N := by
    exact_mod_cast (show p ≤ (4 : ℝ) * N by linarith)
  have hc : lowCost72 N p = 4 * N - p := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((6 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) = (6 : ℝ) * N + (-2 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowCp_kap72 Low.LC03.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC03.cell, hc]
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
