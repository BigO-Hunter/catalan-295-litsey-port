module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.LowBounds
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Low.LC05
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

#time theorem w062_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (72 / 17 : ℝ) * N < p) (hr : (p : ℝ) ≤ (72000000017 / 17000000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((-72 : ℝ) + (17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-72 : ℝ) + (17 : ℝ) * ((p : ℝ) / N)) = (-72 : ℝ) * N + (17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w063_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (72000000017 / 17000000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (30 / 7 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((-72 : ℝ) + (17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-72 : ℝ) + (17 : ℝ) * ((p : ℝ) / N)) = (-72 : ℝ) * N + (17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w064_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (30 / 7 : ℝ) * N < p) (hr : (p : ℝ) ≤ (43 / 10 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((-12 : ℝ) + (3 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((-12 : ℝ) + (3 : ℝ) * ((p : ℝ) / N)) = (-12 : ℝ) * N + (3 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w065_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (43 / 10 : ℝ) * N < p) (hr : (p : ℝ) ≤ (4349999999 / 1000000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) = (74 : ℝ) * N + (-17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w066_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (4349999999 / 1000000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (87 / 20 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) = (74 : ℝ) * N + (-17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w067_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (87 / 20 : ℝ) * N < p) (hr : (p : ℝ) ≤ (4350000001 / 1000000000 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) = (74 : ℝ) * N + (-17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
    push_cast [Nat.cast_sub hp]
    try simp only [Int.cast_min, Int.cast_max]
    rw [le_sub_iff_add_le]
    rw [le_sub_iff_add_le]
    simp only [add_max, max_le_iff, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), le_min_iff, max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    repeat' apply And.intro
    all_goals linarith
  · exact g14472 (p := p) hN (by linarith)

#time theorem w068_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (4350000001 / 1000000000 : ℝ) * N < p) (hr : (p : ℝ) ≤ (74 / 17 : ℝ) * N)
    (hcop : Nat.Coprime p Low.LC05.cell.modulus) :
    (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((cCellLB Low.LC05.cell P72 p72_admissible).kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 4 * N ≤ p := by
    exact_mod_cast (show (4 : ℝ) * N ≤ p by linarith)
  have hc : lowCost72 N p = p - 4 * N := by unfold lowCost72; omega
  have hn : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have he : (N : ℝ) * ((74 : ℝ) + (-17 : ℝ) * ((p : ℝ) / N)) = (74 : ℝ) * N + (-17 : ℝ) * p := by
    field_simp <;> ring
  constructor
  · rw [he]; apply lowC_kap72 Low.LC05.cell hN hp hcop
    simp only [lowHi2_72, lowLo72, Low.LC05.cell, hc]
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
