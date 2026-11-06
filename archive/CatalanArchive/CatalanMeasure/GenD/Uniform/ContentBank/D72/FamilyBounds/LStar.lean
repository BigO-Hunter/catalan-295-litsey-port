module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.LStar.Cells
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 2000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section

def lstarLB72 : NullityLB P72 := lstarLB P72 p72_admissible

#time theorem w033_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (74 / 21 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (60 / 17 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (21 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 74 * N < 21 * p := by
    exact_mod_cast (show (74 : ℝ) * N < 21 * p by linarith)
  have hh : 17 * p ≤ 60 * N := by
    exact_mod_cast (show (17 : ℝ) * p ≤ 60 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((97 : ℤ) * N + (-27) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 21 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 21 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (21 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (21 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w034_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (60 / 17 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (43 / 12 : ℝ) * N) :
    (N : ℝ) * ((-14 / 1 : ℝ) + (4 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 60 * N < 17 * p := by
    exact_mod_cast (show (60 : ℝ) * N < 17 * p by linarith)
  have hh : 12 * p ≤ 43 * N := by
    exact_mod_cast (show (12 : ℝ) * p ≤ 43 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((97 : ℤ) * N + (-27) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 4 * p ≤ lstarLB72.kap N p + 2 + 14 * N := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 4 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 14 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-14 / 1 : ℝ) + (4 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-14 / 1 : ℝ) * N + (4 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w035_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (43 / 12 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (96999999973 / 27000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 43 * N < 12 * p := by
    exact_mod_cast (show (43 : ℝ) * N < 12 * p by linarith)
  have hh : 27000000000 * p ≤ 96999999973 * N := by
    exact_mod_cast (show (27000000000 : ℝ) * p ≤ 96999999973 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-3) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 20 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 20 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w036_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (96999999973 / 27000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 27 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 96999999973 * N < 27000000000 * p := by
    exact_mod_cast (show (96999999973 : ℝ) * N < 27000000000 * p by linarith)
  have hh : 27 * p ≤ 97 * N := by
    exact_mod_cast (show (27 : ℝ) * p ≤ 97 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-3) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 20 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 20 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w037_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (97 / 27 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97000000027 / 27000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 97 * N < 27 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 27 * p by linarith)
  have hh : 27000000000 * p ≤ 97000000027 * N := by
    exact_mod_cast (show (27000000000 : ℝ) * p ≤ 97000000027 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-3) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 20 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 20 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w038_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (97000000027 / 27000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (3599999999 / 1000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 97000000027 * N < 27000000000 * p := by
    exact_mod_cast (show (97000000027 : ℝ) * N < 27000000000 * p by linarith)
  have hh : 1000000000 * p ≤ 3599999999 * N := by
    exact_mod_cast (show (1000000000 : ℝ) * p ≤ 3599999999 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-3) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 20 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 20 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w039_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (3599999999 / 1000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (18 / 5 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 3599999999 * N < 1000000000 * p := by
    exact_mod_cast (show (3599999999 : ℝ) * N < 1000000000 * p by linarith)
  have hh : 5 * p ≤ 18 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 18 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-3) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-24) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 26 24 3 (18) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 20 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 20 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w040_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (37 / 10 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (48499999987 / 13000000000 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 37 * N < 10 * p := by
    exact_mod_cast (show (37 : ℝ) * N < 10 * p by linarith)
  have hh : 13000000000 * p ≤ 48499999987 * N := by
    exact_mod_cast (show (13000000000 : ℝ) * p ≤ 48499999987 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((97 : ℤ) * N + (-26) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 20 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 20 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w041_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (48499999987 / 13000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 26 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 48499999987 * N < 13000000000 * p := by
    exact_mod_cast (show (48499999987 : ℝ) * N < 13000000000 * p by linarith)
  have hh : 26 * p ≤ 97 * N := by
    exact_mod_cast (show (26 : ℝ) * p ≤ 97 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((97 : ℤ) * N + (-26) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 20 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 20 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w042_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (97 / 26 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (48500000013 / 13000000000 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 97 * N < 26 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 26 * p by linarith)
  have hh : 13000000000 * p ≤ 48500000013 * N := by
    exact_mod_cast (show (13000000000 : ℝ) * p ≤ 48500000013 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((0 : ℤ) * N + (0) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  let lo1 : Nat := ((97 : ℤ) * N + (-25) * p).toNat
  let hi1 : Nat := ((0 : ℤ) * N + (1) * p).toNat
  have hlen1 : lo1 ≤ hi1 := by dsimp [lo1, hi1]; omega
  have htop1 : hi1 ≤ p := by dsimp [hi1]; omega
  have hg1 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo1 ≤ ℓ) (hβ : ℓ < hi1) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo1, hi1] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hdis : hi0 ≤ lo1 := by dsimp [hi0, lo1]; omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0) + (if lo1 ≤ ℓ ∧ ℓ < hi1 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · have h1 : ¬ (lo1 ≤ ℓ ∧ ℓ < hi1) := by omega
        simpa [h0, h1] using hg0 ℓ hℓ h0.1 h0.2
      · by_cases h1 : lo1 ≤ ℓ ∧ ℓ < hi1
        · simpa [h0, h1] using hg1 ℓ hℓ h1.1 h1.2
        · simp only [if_neg h0, if_neg h1, Nat.zero_add]
          have := lrank_le_jCard P72 N p ℓ
          have := jCard_pos (P := P72) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p lo0 hi0 hlen0 htop0,
    sum_interval p lo1 hi1 hlen1 htop1] at hkap
  change (hi0 - lo0) + (hi1 - lo1) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 20 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0, lo1, hi1] at hkap hlen0
    dsimp only [lo1, hi1] at hlen1
    omega
  have hboundR : 20 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w043_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (48500000013 / 13000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (86 / 23 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 48500000013 * N < 13000000000 * p := by
    exact_mod_cast (show (48500000013 : ℝ) * N < 13000000000 * p by linarith)
  have hh : 23 * p ≤ 86 * N := by
    exact_mod_cast (show (23 : ℝ) * p ≤ 86 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((0 : ℤ) * N + (0) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  let lo1 : Nat := ((97 : ℤ) * N + (-25) * p).toNat
  let hi1 : Nat := ((0 : ℤ) * N + (1) * p).toNat
  have hlen1 : lo1 ≤ hi1 := by dsimp [lo1, hi1]; omega
  have htop1 : hi1 ≤ p := by dsimp [hi1]; omega
  have hg1 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo1 ≤ ℓ) (hβ : ℓ < hi1) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo1, hi1] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hdis : hi0 ≤ lo1 := by dsimp [hi0, lo1]; omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0) + (if lo1 ≤ ℓ ∧ ℓ < hi1 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · have h1 : ¬ (lo1 ≤ ℓ ∧ ℓ < hi1) := by omega
        simpa [h0, h1] using hg0 ℓ hℓ h0.1 h0.2
      · by_cases h1 : lo1 ≤ ℓ ∧ ℓ < hi1
        · simpa [h0, h1] using hg1 ℓ hℓ h1.1 h1.2
        · simp only [if_neg h0, if_neg h1, Nat.zero_add]
          have := lrank_le_jCard P72 N p ℓ
          have := jCard_pos (P := P72) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p lo0 hi0 hlen0 htop0,
    sum_interval p lo1 hi1 hlen1 htop1] at hkap
  change (hi0 - lo0) + (hi1 - lo1) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 20 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0, lo1, hi1] at hkap hlen0
    dsimp only [lo1, hi1] at hlen1
    omega
  have hboundR : 20 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w044_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (86 / 23 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (15 / 4 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 86 * N < 23 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 23 * p by linarith)
  have hh : 4 * p ≤ 15 * N := by
    exact_mod_cast (show (4 : ℝ) * p ≤ 15 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((0 : ℤ) * N + (0) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-7) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  let lo1 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi1 : Nat := ((0 : ℤ) * N + (1) * p).toNat
  have hlen1 : lo1 ≤ hi1 := by dsimp [lo1, hi1]; omega
  have htop1 : hi1 ≤ p := by dsimp [hi1]; omega
  have hg1 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo1 ≤ ℓ) (hβ : ℓ < hi1) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo1, hi1] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hdis : hi0 ≤ lo1 := by dsimp [hi0, lo1]; omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0) + (if lo1 ≤ ℓ ∧ ℓ < hi1 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · have h1 : ¬ (lo1 ≤ ℓ ∧ ℓ < hi1) := by omega
        simpa [h0, h1] using hg0 ℓ hℓ h0.1 h0.2
      · by_cases h1 : lo1 ≤ ℓ ∧ ℓ < hi1
        · simpa [h0, h1] using hg1 ℓ hℓ h1.1 h1.2
        · simp only [if_neg h0, if_neg h1, Nat.zero_add]
          have := lrank_le_jCard P72 N p ℓ
          have := jCard_pos (P := P72) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p lo0 hi0 hlen0 htop0,
    sum_interval p lo1 hi1 hlen1 htop1] at hkap
  change (hi0 - lo0) + (hi1 - lo1) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0, lo1, hi1] at hkap hlen0
    dsimp only [lo1, hi1] at hlen1
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w045_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (15 / 4 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (86999999977 / 23000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 15 * N < 4 * p := by
    exact_mod_cast (show (15 : ℝ) * N < 4 * p by linarith)
  have hh : 23000000000 * p ≤ 86999999977 * N := by
    exact_mod_cast (show (23000000000 : ℝ) * p ≤ 86999999977 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((0 : ℤ) * N + (0) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-23) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  let lo1 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi1 : Nat := ((0 : ℤ) * N + (1) * p).toNat
  have hlen1 : lo1 ≤ hi1 := by dsimp [lo1, hi1]; omega
  have htop1 : hi1 ≤ p := by dsimp [hi1]; omega
  have hg1 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo1 ≤ ℓ) (hβ : ℓ < hi1) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo1, hi1] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hdis : hi0 ≤ lo1 := by dsimp [hi0, lo1]; omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0) + (if lo1 ≤ ℓ ∧ ℓ < hi1 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · have h1 : ¬ (lo1 ≤ ℓ ∧ ℓ < hi1) := by omega
        simpa [h0, h1] using hg0 ℓ hℓ h0.1 h0.2
      · by_cases h1 : lo1 ≤ ℓ ∧ ℓ < hi1
        · simpa [h0, h1] using hg1 ℓ hℓ h1.1 h1.2
        · simp only [if_neg h0, if_neg h1, Nat.zero_add]
          have := lrank_le_jCard P72 N p ℓ
          have := jCard_pos (P := P72) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p lo0 hi0 hlen0 htop0,
    sum_interval p lo1 hi1 hlen1 htop1] at hkap
  change (hi0 - lo0) + (hi1 - lo1) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 19 * p := by
    dsimp only [lo0, hi0, lo1, hi1] at hkap hlen0
    dsimp only [lo1, hi1] at hlen1
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 19 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w046_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (86999999977 / 23000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87 / 23 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 86999999977 * N < 23000000000 * p := by
    exact_mod_cast (show (86999999977 : ℝ) * N < 23000000000 * p by linarith)
  have hh : 23 * p ≤ 87 * N := by
    exact_mod_cast (show (23 : ℝ) * p ≤ 87 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((0 : ℤ) * N + (0) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-23) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 25 23 3 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  let lo1 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi1 : Nat := ((0 : ℤ) * N + (1) * p).toNat
  have hlen1 : lo1 ≤ hi1 := by dsimp [lo1, hi1]; omega
  have htop1 : hi1 ≤ p := by dsimp [hi1]; omega
  have hg1 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo1 ≤ ℓ) (hβ : ℓ < hi1) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo1, hi1] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hdis : hi0 ≤ lo1 := by dsimp [hi0, lo1]; omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0) + (if lo1 ≤ ℓ ∧ ℓ < hi1 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · have h1 : ¬ (lo1 ≤ ℓ ∧ ℓ < hi1) := by omega
        simpa [h0, h1] using hg0 ℓ hℓ h0.1 h0.2
      · by_cases h1 : lo1 ≤ ℓ ∧ ℓ < hi1
        · simpa [h0, h1] using hg1 ℓ hℓ h1.1 h1.2
        · simp only [if_neg h0, if_neg h1, Nat.zero_add]
          have := lrank_le_jCard P72 N p ℓ
          have := jCard_pos (P := P72) (N := N) hp hLb hℓ
          omega)
  rw [Finset.sum_add_distrib, sum_interval p lo0 hi0 hlen0 htop0,
    sum_interval p lo1 hi1 hlen1 htop1] at hkap
  change (hi0 - lo0) + (hi1 - lo1) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 19 * p := by
    dsimp only [lo0, hi0, lo1, hi1] at hkap hlen0
    dsimp only [lo1, hi1] at hlen1
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 19 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w047_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (87 / 23 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87000000023 / 23000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 87 * N < 23 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 23 * p by linarith)
  have hh : 23000000000 * p ≤ 87000000023 * N := by
    exact_mod_cast (show (23000000000 : ℝ) * p ≤ 87000000023 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-22) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 19 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 19 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w048_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (87000000023 / 23000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (71999999981 / 19000000000 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 87000000023 * N < 23000000000 * p := by
    exact_mod_cast (show (87000000023 : ℝ) * N < 23000000000 * p by linarith)
  have hh : 19000000000 * p ≤ 71999999981 * N := by
    exact_mod_cast (show (19000000000 : ℝ) * p ≤ 71999999981 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-22) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 19 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 19 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w049_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (71999999981 / 19000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (72 / 19 : ℝ) * N) :
    (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 71999999981 * N < 19000000000 * p := by
    exact_mod_cast (show (71999999981 : ℝ) * N < 19000000000 * p by linarith)
  have hh : 19 * p ≤ 72 * N := by
    exact_mod_cast (show (19 : ℝ) * p ≤ 72 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((87 : ℤ) * N + (-22) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 24 22 2 (17) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 72 * N ≤ lstarLB72.kap N p + 2 + 19 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 72 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 19 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((72 / 1 : ℝ) + (-19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (72 / 1 : ℝ) * N + (-19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w050_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (74 / 19 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (43 / 11 : ℝ) * N) :
    (N : ℝ) * ((-74 / 1 : ℝ) + (19 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 74 * N < 19 * p := by
    exact_mod_cast (show (74 : ℝ) * N < 19 * p by linarith)
  have hh : 11 * p ≤ 43 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 43 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((97 : ℤ) * N + (-24) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 19 * p ≤ lstarLB72.kap N p + 2 + 74 * N := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 19 * p ≤ (lstarLB72.kap N p : ℝ) + 2 + 74 * N := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-74 / 1 : ℝ) + (19 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-74 / 1 : ℝ) * N + (19 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w051_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (43 / 11 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (43499999989 / 11000000000 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 43 * N < 11 * p := by
    exact_mod_cast (show (43 : ℝ) * N < 11 * p by linarith)
  have hh : 11000000000 * p ≤ 43499999989 * N := by
    exact_mod_cast (show (11000000000 : ℝ) * p ≤ 43499999989 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w052_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (43499999989 / 11000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87 / 22 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 43499999989 * N < 11000000000 * p := by
    exact_mod_cast (show (43499999989 : ℝ) * N < 11000000000 * p by linarith)
  have hh : 22 * p ≤ 87 * N := by
    exact_mod_cast (show (22 : ℝ) * p ≤ 87 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w053_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (87 / 22 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (43500000011 / 11000000000 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 87 * N < 22 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 22 * p by linarith)
  have hh : 11000000000 * p ≤ 43500000011 * N := by
    exact_mod_cast (show (11000000000 : ℝ) * p ≤ 43500000011 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w054_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (43500000011 / 11000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (3999999999 / 1000000000 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 43500000011 * N < 11000000000 * p := by
    exact_mod_cast (show (43500000011 : ℝ) * N < 11000000000 * p by linarith)
  have hh : 1000000000 * p ≤ 3999999999 * N := by
    exact_mod_cast (show (1000000000 : ℝ) * p ≤ 3999999999 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

#time theorem w055_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (3999999999 / 1000000000 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (4 / 1 : ℝ) * N) :
    (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (lstarLB72.kap N p : ℝ) := by
  have hl : 3999999999 * N < 1000000000 * p := by
    exact_mod_cast (show (3999999999 : ℝ) * N < 1000000000 * p by linarith)
  have hh : 1 * p ≤ 4 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 4 * N by linarith)
  have hp : 0 < p := by omega
  have hLb : p ≤ P72.L N - P72.b N := by
    rw [p72_L]
    change p ≤ 87 * N - 11 * N
    omega
  have hpq : p ≤ P72.q N := by change p ≤ 4 * N; omega
  let lo0 : Nat := ((11 : ℤ) * N + (-2) * p).toNat
  let hi0 : Nat := ((27 : ℤ) * N + (-6) * p).toNat
  have hlen0 : lo0 ≤ hi0 := by dsimp [lo0, hi0]; omega
  have htop0 : hi0 ≤ p := by dsimp [hi0]; omega
  have hg0 (ℓ : Nat) (hℓ : ℓ < p) (hα : lo0 ≤ ℓ) (hβ : ℓ < hi0) :
      1 + lrank P72 N p ℓ + 1 ≤ (jSet P72 N p ℓ).card := by
    dsimp [lo0, hi0] at hα hβ
    apply gap_ge P72 N p ℓ hp hℓ 23 21 2 (16) (-1) 1
    all_goals try simp only [p72_H, p72_L, P72, Signed.dc72_toParameters,
      Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    all_goals omega
  have hkap := lstarKap_ge (P := P72) (N := N) hp hLb hpq
    (fun ℓ => (if lo0 ≤ ℓ ∧ ℓ < hi0 then 1 else 0)) (fun ℓ hℓ => by
      by_cases h0 : lo0 ≤ ℓ ∧ ℓ < hi0
      · simpa [h0] using hg0 ℓ hℓ h0.1 h0.2
      · simp only [if_neg h0, Nat.zero_add]
        have := lrank_le_jCard P72 N p ℓ
        have := jCard_pos (P := P72) (N := N) hp hLb hℓ
        omega)
  rw [sum_interval p lo0 hi0 hlen0 htop0] at hkap
  change (hi0 - lo0) + p ≤ lstarLB72.kap N p + 4 * N at hkap
  have hbound : 12 * N ≤ lstarLB72.kap N p + 2 + 3 * p := by
    dsimp only [lo0, hi0] at hkap hlen0
    skip
    omega
  have hboundR : 12 * N ≤ (lstarLB72.kap N p : ℝ) + 2 + 3 * p := by exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((12 / 1 : ℝ) + (-3 / 1 : ℝ) * ((p : ℝ) / N)) =
      (12 / 1 : ℝ) * N + (-3 / 1 : ℝ) * p := by field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
