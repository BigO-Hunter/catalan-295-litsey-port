module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Interface
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

def coreLB72 : NullityLB P72 :=
  NullityLB.ofFam P72 p72_admissible (famKap P72) (fun _ _ _ _ _ _ => le_rfl)

#time theorem w138_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (146 / 7 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (43 / 2 : ℝ) * N) :
    (N : ℝ) * ((-93 : ℝ) + (9 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 146 * N < 7 * p := by
    exact_mod_cast (show (146 : ℝ) * N < 7 * p by linarith)
  have hh : 2 * p ≤ 43 * N := by
    exact_mod_cast (show (2 : ℝ) * p ≤ 43 * N by linarith)
  have ha : SApp P72 N p := by
    unfold SApp
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := sVal P72 N p
  have hc : (9) * p ≤ (2) * v + (4) * 1 + (186) * N := by
    unfold v sVal sM0 sM1 sE
    rw [p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hcR : (9 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (186 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-93 : ℝ) + (9 / 2 : ℝ) * ((p : ℝ) / N)) = (-93 : ℝ) * N + (9 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w139_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (43 / 2 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (87 / 4 : ℝ) * N) :
    (N : ℝ) * ((-7 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 43 * N < 2 * p := by
    exact_mod_cast (show (43 : ℝ) * N < 2 * p by linarith)
  have hh : 4 * p ≤ 87 * N := by
    exact_mod_cast (show (4 : ℝ) * p ≤ 87 * N by linarith)
  have ha : SApp P72 N p := by
    unfold SApp
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := sVal P72 N p
  have hc : (1) * p ≤ (2) * v + (4) * 1 + (14) * N := by
    unfold v sVal sM0 sM1 sE
    rw [p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hcR : (1 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (14 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-7 : ℝ) + (1 / 2 : ℝ) * ((p : ℝ) / N)) = (-7 : ℝ) * N + (1 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w140_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (87 / 4 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (160 / 7 : ℝ) * N) :
    (N : ℝ) * ((80 : ℝ) + (-7 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 87 * N < 4 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 4 * p by linarith)
  have hh : 7 * p ≤ 160 * N := by
    exact_mod_cast (show (7 : ℝ) * p ≤ 160 * N by linarith)
  have ha : SApp P72 N p := by
    unfold SApp
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := sVal P72 N p
  have hc : (160) * N ≤ (2) * v + (4) * 1 + (7) * p := by
    unfold v sVal sM0 sM1 sE
    rw [p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hcR : (160 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (7 : ℝ) * p := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((80 : ℝ) + (-7 / 2 : ℝ) * ((p : ℝ) / N)) = (80 : ℝ) * N + (-7 / 2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w143_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (28 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (86 / 3 : ℝ) * N) :
    (N : ℝ) * ((-80 : ℝ) + (3 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 28 * N < 1 * p := by
    exact_mod_cast (show (28 : ℝ) * N < 1 * p by linarith)
  have hh : 3 * p ≤ 86 * N := by
    exact_mod_cast (show (3 : ℝ) * p ≤ 86 * N by linarith)
  have ha : TApp P72 N p := by
    unfold TApp tentD Parameters.C
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := tVal P72 N p
  have hc : (6) * p ≤ (2) * v + (4) * 1 + (160) * N := by
    unfold v tVal tentD Parameters.C
    rw [p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hcR : (6 : ℝ) * p ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (160 : ℝ) * N := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((-80 : ℝ) + (3 : ℝ) * ((p : ℝ) / N)) = (-80 : ℝ) * N + (3 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w144_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (86 / 3 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (29 : ℝ) * N) :
    (N : ℝ) * ((6 : ℝ) + (0 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 86 * N < 3 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 3 * p by linarith)
  have hh : 1 * p ≤ 29 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 29 * N by linarith)
  have ha : TApp P72 N p := by
    unfold TApp tentD Parameters.C
    rw [p72_H, p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  let v := tVal P72 N p
  have hc : (12) * N ≤ (2) * v + (4) * 1 := by
    unfold v tVal tentD Parameters.C
    rw [p72_L]
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hcR : (12 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((6 : ℝ) + (0 : ℝ) * ((p : ℝ) / N)) = (6 : ℝ) * N + (0 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w145_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (29 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (30 : ℝ) * N) :
    (N : ℝ) * ((6 : ℝ) + (0 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 29 * N < 1 * p := by
    exact_mod_cast (show (29 : ℝ) * N < 1 * p by linarith)
  have hh : 1 * p ≤ 30 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 30 * N by linarith)
  have ha : UApp P72 N p := by
    constructor <;> simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] <;> omega
  let v := uVal P72 N p
  have hc : (12) * N ≤ (2) * v + (4) * 1 := by
    unfold v uVal uStar
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hcR : (12 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((6 : ℝ) + (0 : ℝ) * ((p : ℝ) / N)) = (6 : ℝ) * N + (0 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

#time theorem w146_hcert72 {N p : Nat} (hN : 0 < N)
    (hlo : (30 : ℝ) * N < p) (hhi : (p : ℝ) ≤ (97 / 3 : ℝ) * N) :
    (N : ℝ) * ((66 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (coreLB72.kap N p : ℝ) := by
  have hl : 30 * N < 1 * p := by
    exact_mod_cast (show (30 : ℝ) * N < 1 * p by linarith)
  have hh : 3 * p ≤ 97 * N := by
    exact_mod_cast (show (3 : ℝ) * p ≤ 97 * N by linarith)
  have ha : UApp P72 N p := by
    constructor <;> simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] <;> omega
  let v := uVal P72 N p
  have hc : (132) * N ≤ (2) * v + (4) * 1 + (4) * p := by
    unfold v uVal uStar
    simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    omega
  have hv : v ≤ coreLB72.kap N p := by
    classical
    change v ≤ famKap P72 N p
    unfold famKap
    rw [if_pos ha]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hcR : (132 : ℝ) * N ≤ (2 : ℝ) * v + (4 : ℝ) * 1 + (4 : ℝ) * p := by exact_mod_cast hc
  have hvR : (v : ℝ) ≤ coreLB72.kap N p := by exact_mod_cast hv
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N : ℝ) * ((66 : ℝ) + (-2 : ℝ) * ((p : ℝ) / N)) = (66 : ℝ) * N + (-2 : ℝ) * p := by
    field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
