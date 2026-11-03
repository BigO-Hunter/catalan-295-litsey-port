module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
@[expose] public section
set_option Elab.async false
/-! Finite c=2 guards for the two retained indexed-S windows at D72. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

def s3LB72 : NullityLB P72 := NullityLB.ofSIndex P72 p72_admissible 3 (by decide)

theorem s3_app72 {N p : Nat} (h : 186 * N < 7 * p) : SApp P72 N p := by
  simp only [SApp, P72, Signed.dc72_toParameters, Parameters.q, Parameters.h,
    Parameters.n, Parameters.g]
  omega

theorem s3_kap72 {N p : Nat} (h : SApp P72 N p) :
    s3LB72.kap N p = sM1_k P72 N p 3 - sM0_k P72 N p 3 - sE P72 N p := by
  classical
  change (if SApp P72 N p then sM1_k P72 N p 3 - sM0_k P72 N p 3 - sE P72 N p else 0) = _
  exact if_pos h

set_option maxHeartbeats 1000000 in
#time theorem s3_left_count72 {N p : Nat} (hl : 186 * N < 7 * p) (hr : p ≤ 27 * N) :
    7 * p ≤ 2 * s3LB72.kap N p + 186 * N + 1 := by
  rw [s3_kap72 (s3_app72 hl)]
  simp only [sM0_k, sM1_k, sE]
  rw [p72_L]
  simp only [P72, Signed.dc72_toParameters, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
  omega

set_option maxHeartbeats 1000000 in
#time theorem s3_right_count72 {N p : Nat} (hN : 0 < N) (hl : 27 * N < p) (hr : 3 * p ≤ 86 * N) :
    5 * p + 1 ≤ 2 * s3LB72.kap N p + 132 * N := by
  have ha : 186 * N < 7 * p := by omega
  rw [s3_kap72 (s3_app72 ha)]
  simp only [sM0_k, sM1_k, sE]
  rw [p72_L]
  simp only [P72, Signed.dc72_toParameters, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
  omega

/- Actual left window inequality including the safe-pool conjunct. -/
#time theorem s3_left_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (186 / 7 : ℝ) * N < p) (hr : (p : ℝ) ≤ 27 * N) :
    (N : ℝ) * (-93 + (7 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (s3LB72.kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hl' : 186 * N < 7 * p := by
    exact_mod_cast (show (186 : ℝ) * N < 7 * p by linarith)
  have hr' : p ≤ 27 * N := by exact_mod_cast hr
  have h := s3_left_count72 hl' hr'
  have hc : (7 : ℝ) * p ≤ 2 * (s3LB72.kap N p : ℝ) + 186 * N + 1 := by exact_mod_cast h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he : (N : ℝ) * (-93 + (7 / 2 : ℝ) * ((p : ℝ) / N)) = -93 * (N : ℝ) + (7 / 2 : ℝ) * p := by
    field_simp <;> ring
  have hN0 : (0 : ℝ) ≤ N := by positivity
  constructor
  · rw [he]; linarith
  · exact g14472 hN (by linarith)

/- Actual right window inequality including the safe-pool conjunct. -/
#time theorem s3_right_hcert72 {N p : Nat} (hN : 0 < N)
    (hl : (27 : ℝ) * N < p) (hr : (p : ℝ) ≤ (86 / 3 : ℝ) * N) :
    (N : ℝ) * (-66 + (5 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (s3LB72.kap N p : ℝ) ∧
      (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hl' : 27 * N < p := by exact_mod_cast hl
  have hr' : 3 * p ≤ 86 * N := by
    exact_mod_cast (show (3 : ℝ) * p ≤ 86 * N by linarith)
  have h := s3_right_count72 hN hl' hr'
  have hc : (5 : ℝ) * p + 1 ≤ 2 * (s3LB72.kap N p : ℝ) + 132 * N := by exact_mod_cast h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he : (N : ℝ) * (-66 + (5 / 2 : ℝ) * ((p : ℝ) / N)) = -66 * (N : ℝ) + (5 / 2 : ℝ) * p := by
    field_simp <;> ring
  have hN0 : (0 : ℝ) ≤ N := by positivity
  constructor
  · rw [he]; linarith
  · exact g14472 hN (by linarith)

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
