module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.FrobInst.CBank
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.Parametric CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.FrobInst CatalanMeasure.GenD.Uniform.W
noncomputable section
def frobApp (N p : ℕ) : Prop := 97 * N < 3 * p ∧ 2 * p + 2 ≤ 66 * N

def frobVal (N p : ℕ) : ℕ := 66 * N - 2 * p - 1

theorem seen_card {N p : ℕ} (h1 : 97 * N < 3 * p) (h2 : 2 * p + 2 ≤ 66 * N) :
    (seenSet P72 N p 0 (0 + (66 * N - 2 * p - 2 + 1))).card ≤ 2 := by
  have hp0 : 0 < p := by omega
  have hp0' : (0 : ℤ) < p := by exact_mod_cast hp0
  have hsub : seenSet P72 N p 0 (0 + (66 * N - 2 * p - 2 + 1)) ⊆
      ({(0, 2), (1, 2)} : Finset (ℕ × ℤ)) := by
    intro y hy
    unfold seenSet at hy
    obtain ⟨⟨j, e⟩, hmem, rfl⟩ := Finset.mem_image.mp hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hmem
    obtain ⟨⟨⟨hj1, hj2⟩, ⟨he1, he2⟩⟩, a, ha⟩ := hmem
    have hjd := Nat.div_add_mod j p
    have hell : j % p < p := Nat.mod_lt _ hp0
    rw [p72_L] at hj2
    rw [p72_H] at ha
    change 11 * N ≤ j at hj1
    change e < 4 * N + (0 + (66 * N - 2 * p - 2 + 1)) at he2
    push_cast at ha
    have hJ : (P72.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = p * a := by
      rw [p72_H]
      push_cast
      exact ha
    have hdiv : ((P72.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p = a := by
      rw [hJ]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hp0')
    simp only
    rw [hdiv]
    have hH : (P72.H N : ℤ) = 97 * N := by rw [p72_H]; push_cast; ring
    rw [hH] at hJ
    have ha1 : 1 < a := by
      by_contra hc
      have : (p : ℤ) * a ≤ p := by nlinarith
      omega
    have ha3 : a < 3 := by
      by_contra hc
      have : 3 * (p : ℤ) ≤ p * a := by nlinarith
      omega
    have ha2 : a = 2 := by omega
    subst ha2
    have hj : j / p < 2 := by
      by_contra hc
      have : 2 * p ≤ p * (j / p) := by nlinarith
      omega
    have h0 := Nat.zero_le (j / p)
    have : j / p = 0 ∨ j / p = 1 := by omega
    rcases this with h | h <;> simp [h]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem frob_win {N p : ℕ} (hA : frobApp N p) :
    0 + (66 * N - 2 * p - 2 + 1) ≤ (p - 1) / 2 ∧
      FrobGood P72 N p 3 0 (66 * N - 2 * p - 2 + 1) 0 := by
  obtain ⟨h1, h2⟩ := hA
  refine ⟨by omega, ?_⟩
  intro k hk
  refine ⟨?_, ?_⟩ <;> (interval_cases k <;> (simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.g]; push_cast; omega))

def frobLB : NullityLB P72 :=
  frobInstLB P72 p72_admissible frobApp frobVal (fun _ _ => 3) (fun _ _ => 0)
    (fun N p => 66 * N - 2 * p - 2) (fun _ _ => 0)
    (fun N p hN hp hp2 hH hA => frob_win hA)
    (fun N p hA => by
      obtain ⟨h1, h2⟩ := hA
      have hc := seen_card h1 h2
      unfold frobVal
      generalize (seenSet P72 N p 0 (0 + (66 * N - 2 * p - 2 + 1))).card = c at hc ⊢
      have h3 : 1 ≤ 3 - c := by omega
      calc 66 * N - 2 * p - 1 = (66 * N - 2 * p - 2 + 1) * 1 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ h3)

theorem frob_cell {N p : ℕ} (h1 : 97 * N < 3 * p) (h2 : 2 * p ≤ 66 * N) :
    (66 : ℤ) * N + (-2) * p ≤ 1 * ((frobLB.kap N p : ℕ) : ℤ) + 2 := by
  by_cases hA : frobApp N p
  · have hk : frobLB.kap N p = frobVal N p := by
      simp [frobLB, frobInstLB, frobProductLB, NullityLB.ofWindow, hA]
    rw [hk]
    unfold frobVal
    omega
  · have hk : frobLB.kap N p = 0 := by
      simp [frobLB, frobInstLB, frobProductLB, NullityLB.ofWindow, hA]
    rw [hk]
    have : ¬ (97 * N < 3 * p ∧ 2 * p + 2 ≤ 66 * N) := hA
    omega

#time theorem w147_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (97 / 3 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (954 / 29 : ℝ) * N) :
    (N : ℝ) * (66 - 2 * ((p : ℝ) / N)) - 2 ≤ (frobLB.kap N p : ℝ) := by
  have hl : 97 * N < 3 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 3 * p by linarith)
  have hh : 2 * p ≤ 66 * N := by
    exact_mod_cast (show 2 * (p : ℝ) ≤ 66 * N by linarith)
  have hc : (66 : ℝ) * N - 2 * p ≤ (frobLB.kap N p : ℝ) + 2 := by
    exact_mod_cast (show (66 : ℤ) * N - 2 * p ≤ (frobLB.kap N p : ℤ) + 2 by
      simpa using frob_cell hl hh)
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * (66 - 2 * ((p : ℝ) / N)) = 66 * N - 2 * p := by
    field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
