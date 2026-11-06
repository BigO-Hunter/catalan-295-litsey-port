module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWin
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

#time theorem w131_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcL6) (hodd : p % 2 = 1)
    (hlo : (186 / 11 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (86 / 5 : ℝ) * N) :
    (N : ℝ) * ((-93 : ℝ) + (11 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zLLB P72 p72_admissible).kap N p : ℝ) := by
  have hl : 186 * N < 11 * p := by
    exact_mod_cast (show (186 : ℝ) * N < 11 * p by linarith)
  have hh : 5 * p ≤ 86 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 86 * N by linarith)
  have ha : zLApp5 P72 N p := by
    unfold zLApp5
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zLLB P72 p72_admissible).kap N p
  have hg := zLLB_kap_ge p72_admissible hodd ha
  rw [p72_H, p72_L] at hg
  simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hg
  have hc : (11 : ℤ) * p ≤ (2 : ℤ) * v + (4 : ℤ) * 1 + (186 : ℤ) * N := by
    change _ ≤ _ at hg
    unfold v
    simp only [P72, Signed.dc72_toParameters]
    omega
  have hcR : (11 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (186 : ℝ) * N := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-93 : ℝ) + (11 / 2 : ℝ) * ((p : ℝ) / N)) = (-93 : ℝ) * N + (11 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

#time theorem w132_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcL6) (hodd : p % 2 = 1)
    (hlo : (86 / 5 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87 / 5 : ℝ) * N) :
    (N : ℝ) * ((-7 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zLLB P72 p72_admissible).kap N p : ℝ) := by
  have hl : 86 * N < 5 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 5 * p by linarith)
  have hh : 5 * p ≤ 87 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 87 * N by linarith)
  have ha : zLApp5 P72 N p := by
    unfold zLApp5
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zLLB P72 p72_admissible).kap N p
  have hg := zLLB_kap_ge p72_admissible hodd ha
  rw [p72_H, p72_L] at hg
  simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hg
  have hc : (1 : ℤ) * p ≤ (2 : ℤ) * v + (4 : ℤ) * 1 + (14 : ℤ) * N := by
    change _ ≤ _ at hg
    unfold v
    simp only [P72, Signed.dc72_toParameters]
    omega
  have hcR : (1 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (14 : ℝ) * N := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-7 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) = (-7 : ℝ) * N + (1 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

#time theorem w133_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcL6) (hodd : p % 2 = 1)
    (hlo : (87 / 5 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (160 / 9 : ℝ) * N) :
    (N : ℝ) * ((80 : ℝ) + (-9 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zLLB P72 p72_admissible).kap N p : ℝ) := by
  have hl : 87 * N < 5 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 5 * p by linarith)
  have hh : 9 * p ≤ 160 * N := by
    exact_mod_cast (show (9 : ℝ) * p ≤ 160 * N by linarith)
  have ha : zLApp5 P72 N p := by
    unfold zLApp5
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zLLB P72 p72_admissible).kap N p
  have hg := zLLB_kap_ge p72_admissible hodd ha
  rw [p72_H, p72_L] at hg
  simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hg
  have hc : (160 : ℤ) * N ≤ (2 : ℤ) * v + (4 : ℤ) * 1 + (9 : ℤ) * p := by
    change _ ≤ _ at hg
    unfold v
    simp only [P72, Signed.dc72_toParameters]
    omega
  have hcR : (160 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (9 : ℝ) * p := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((80 : ℝ) + (-9 / 2 : ℝ) * ((p : ℝ) / N)) = (80 : ℝ) * N + (-9 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
