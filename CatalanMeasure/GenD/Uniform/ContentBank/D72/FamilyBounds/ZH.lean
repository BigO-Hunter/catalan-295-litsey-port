module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLBcap
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.ZoneZ CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

theorem zcap_strict72 {N p : Nat} (hp : p.Prime) (h97 : 97 < p) (hN : 0 < N)
    (hNp : N < p) (h : 5 * p ≤ 97 * N) : 5 * p + 1 ≤ 97 * N := by
  by_contra hn
  have he : 5 * p = 97 * N := by omega
  have hd : p ∣ 97 * N := by rw [← he]; exact ⟨5, by omega⟩
  rcases hp.dvd_mul.mp hd with hd | hd
  · have := Nat.le_of_dvd (by decide : 0 < 97) hd; omega
  · have := Nat.le_of_dvd hN hd; omega

#time theorem w134_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcH6) (hp : p.Prime) (h97 : 97 < p)
    (hlo : (132 / 7 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 5 : ℝ) * N) :
    (N : ℝ) * ((-66 : ℝ) + (7 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zHLBcap P72 p72_admissible).kap N p : ℝ) := by
  have hl : 132 * N < 7 * p := by
    exact_mod_cast (show (132 : ℝ) * N < 7 * p by linarith)
  have hh : 5 * p ≤ 97 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 97 * N by linarith)
  have h5 := zcap_strict72 hp h97 hN (by omega : N < p) (by omega : 5*p ≤ 97*N)
  have ha : zHAppCap P72 N p := by
    unfold zHAppCap
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zHLBcap P72 p72_admissible).kap N p
  have hv : v = zHvalCap P72 N p := by
    classical
    change (if zHAppCap P72 N p then zHvalCap P72 N p else 0) = _
    exact if_pos ha
  have hc : (7) * p ≤ (2) * v + (4) * 1 + (132) * N := by
    rw [hv]
    unfold zHvalCap
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hcR : (7 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (132 : ℝ) * N := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-66 : ℝ) + (7 / 2 : ℝ) * ((p : ℝ) / N)) = (-66 : ℝ) * N + (7 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

#time theorem w135_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcH')
    (hlo : (97 / 5 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (20 : ℝ) * N) :
    (N : ℝ) * ((31 : ℝ) + (-3 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zHLBnc P72 p72_admissible).kap N p : ℝ) := by
  have hl : 97 * N < 5 * p := by
    exact_mod_cast (show (97 : ℝ) * N < 5 * p by linarith)
  have hh : 1 * p ≤ 20 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 20 * N by linarith)
  have ha : zHApp P72 N p := by
    unfold zHApp
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zHLBnc P72 p72_admissible).kap N p
  have hv : v = zHval P72 N p := by
    classical
    change (if zHApp P72 N p then zHval P72 N p else 0) = _
    exact if_pos ha
  have hc : (62) * N ≤ (2) * v + (4) * 1 + (3) * p := by
    rw [hv]
    unfold zHval
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hcR : (62 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (3 : ℝ) * p := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((31 : ℝ) + (-3 / 2 : ℝ) * ((p : ℝ) / N)) = (31 : ℝ) * N + (-3 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

#time theorem w136_hcert72 {N p : Nat} (hN : 0 < N) (hunit : ¬ p ∣ ZcH')
    (hlo : (20 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (222 / 11 : ℝ) * N) :
    (N : ℝ) * ((91 : ℝ) + (-9 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤
      ((zHLBnc P72 p72_admissible).kap N p : ℝ) := by
  have hl : 20 * N < 1 * p := by
    exact_mod_cast (show (20 : ℝ) * N < 1 * p by linarith)
  have hh : 11 * p ≤ 222 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 222 * N by linarith)
  have ha : zHApp P72 N p := by
    unfold zHApp
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    refine ⟨hunit, ?_⟩
    repeat' apply And.intro
    all_goals omega
  let v := (zHLBnc P72 p72_admissible).kap N p
  have hv : v = zHval P72 N p := by
    classical
    change (if zHApp P72 N p then zHval P72 N p else 0) = _
    exact if_pos ha
  have hc : (182) * N ≤ (2) * v + (4) * 1 + (9) * p := by
    rw [hv]
    unfold zHval
    rw [p72_H]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hcR : (182 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (9 : ℝ) * p := by exact_mod_cast hc
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((91 : ℝ) + (-9 / 2 : ℝ) * ((p : ℝ) / N)) = (91 : ℝ) * N + (-9 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  change _ ≤ (v : ℝ)
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
