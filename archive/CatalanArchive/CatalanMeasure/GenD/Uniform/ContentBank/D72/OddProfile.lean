module
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Uniform.Arithmetic.SafeOdd
@[expose] public section
set_option Elab.async false
/-! Exact D72 odd loss and the safe pool on the full content band. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.Arithmetic
open MeasureTheory intervalIntegral
noncomputable section

abbrev P72 : Parameters := Signed.dc72.toParameters

theorem p72_admissible : Admissible P72 := Signed.dc72.admissible

theorem p72_H (N : Nat) : P72.H N = 97 * N := by
  simp only [P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L,
    Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
  omega

theorem p72_L (N : Nat) : P72.L N = 87 * N := by
  simp only [P72, Signed.dc72_toParameters, Parameters.L, Parameters.n, Parameters.b, Parameters.q]
  omega

theorem p72_A (N : Nat) : P72.A N = 27 * N := by
  simp only [P72, Signed.dc72_toParameters, Parameters.A, Parameters.b, Parameters.q, Parameters.g]
  omega

theorem p72_normalizer_cut : P72.H 1 < 98 := by rw [p72_H]; decide

def lossNat72 (N p : Nat) : Nat :=
  if p ≤ 37 * N then 144 * N else
  if p ≤ 43 * N then 218 * N - 2 * p else
  if 2 * p ≤ 97 * N then 132 * N else
  if 2 * p ≤ 101 * N then 229 * N - 2 * p else
  if p ≤ 60 * N then 330 * N - 4 * p else
  if p ≤ 86 * N then 270 * N - 3 * p else
  if p ≤ 87 * N then 184 * N - 2 * p else 97 * N - p

theorem lower_eq72 {N p : Nat} (h : 2 * p ≤ 97 * N) : lowerPrimeLoss P72 N p = lossNat72 N p := by
  rw [OddProfile.lowerPrimeLoss_eq]
  rw [p72_H, p72_L, p72_A]
  simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b, Parameters.q]
  unfold lossNat72
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
theorem upper_eq72 {N p : Nat} (h : 97 * N ≤ 2 * p) (hp : p ≤ 97 * N) :
    upperPrimeLoss P72 N p = lossNat72 N p := by
  rw [OddProfile.upperPrimeLoss_eq]
  simp only [OddProfile.upperR, OddProfile.upperPd, OddProfile.upperE]
  rw [p72_H, p72_L, p72_A]
  simp only [P72, Signed.dc72_toParameters, Parameters.n, Parameters.b]
  unfold lossNat72
  split_ifs <;> omega

def f72 : PL.Prof := ⟨144, 0, [(-2, 37), (2, 43), (-2, 97/2), (-2, 101/2), (1, 60), (1, 86), (1, 87)]⟩

def kappa072 : ℝ := 144

local macro "seg72_ker" : tactic =>
  `(tactic| (intro wt hwt
             simp only [f72, List.mem_cons, List.not_mem_nil, or_false] at hwt
             rcases hwt with h | h | h | h | h | h | h <;> (subst h; norm_num)))

local macro "seg72_facts" : tactic =>
  `(tactic| norm_num [f72, PL.hingeSlope, PL.hingeIntercept])

theorem lossNat72_cast {N p : Nat} (hN : 0 < N) (hp : p ≤ 97 * N) :
    (lossNat72 N p : ℝ) = N * f72.eval ((p : ℝ) / N) := by
  unfold lossNat72
  split_ifs
  · exact OddProfile.loss_eq_segment f72 hN 144 0 (by omega) (u1 := 0) (w1 := 1) (u2 := 37) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 218 (-2) (by omega) (u1 := 37) (w1 := 1) (u2 := 43) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 132 0 (by omega) (u1 := 43) (w1 := 1) (u2 := 97) (w2 := 2)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 229 (-2) (by omega) (u1 := 97) (w1 := 2) (u2 := 101) (w2 := 2)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 330 (-4) (by omega) (u1 := 101) (w1 := 2) (u2 := 60) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 270 (-3) (by omega) (u1 := 60) (w1 := 1) (u2 := 86) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 184 (-2) (by omega) (u1 := 86) (w1 := 1) (u2 := 87) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)
  · exact OddProfile.loss_eq_segment f72 hN 97 (-1) (by omega) (u1 := 87) (w1 := 1) (u2 := 97) (w2 := 1)
      (by norm_num) (by norm_num) (by omega) (by omega) (by seg72_ker) (by seg72_facts) (by seg72_facts)

theorem upper_side72 {N p : Nat} (hN : 0 < N) (h : P72.H N ≤ 2 * p) :
    OddProfile.UpperSide P72 N p := by
  rw [p72_H] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p72_A]; omega
  · rw [p72_L, p72_H]; omega
  · simp only [P72, Signed.dc72_toParameters, Parameters.b]; omega
  · rw [p72_H, p72_L]; omega

theorem hloss72 (N p : Nat) (hN : 0 < N) (hp : p ≤ P72.H N) :
    (safeOddLoss P72 N p : ℝ) ≤ N * f72.eval ((p : ℝ) / N) := by
  have hsafe := safeOddLoss_le_old P72 N p hp (upper_side72 hN)
  have hp' : p ≤ 97 * N := by simpa only [p72_H] using hp
  have he : OddProfile.oddLossNat P72 N p = lossNat72 N p := by
    unfold OddProfile.oddLossNat
    rw [p72_H]
    split_ifs with h
    · exact lower_eq72 h
    · exact upper_eq72 (by omega) hp'
  rw [he] at hsafe
  rw [← lossNat72_cast hN hp']
  exact_mod_cast hsafe

theorem hf072 (x : ℝ) (hx : x ≤ 1) : f72.eval x = kappa072 := by
  simp only [PL.Prof.eval, f72, PL.hinges_cons, PL.hinges_nil, kappa072]
  rw [PL.ramp_of_le (by linarith : x ≤ 37), PL.ramp_of_le (by linarith : x ≤ 43),
    PL.ramp_of_le (by linarith : x ≤ 97 / 2), PL.ramp_of_le (by linarith : x ≤ 101 / 2),
    PL.ramp_of_le (by linarith : x ≤ 60), PL.ramp_of_le (by linarith : x ≤ 86),
    PL.ramp_of_le (by linarith : x ≤ 87)]
  ring

theorem odd_area72 : kappa072 + (∫ x in (1 : ℝ)..97, f72.eval x) = 19129 / 2 := by
  rw [PL.Prof.integral_eval f72 (by norm_num)]
  norm_num [PL.Prof.area, f72, PL.hingeInt_cons, PL.hingeInt_nil, PL.ramp, kappa072]

/-- All accepted windows lie below this bound, so the actual safe odd pool is
exactly `144 N` there. No asymptotic loss or rounding is used. -/
theorem safe_pool72 {N p : Nat} (hN : 0 < N) (hp : 29 * p ≤ 954 * N) :
    safeOddLoss P72 N p = 144 * N := by
  have hnot : ¬UpperAvailable P72 N p := by
    intro hu
    have h := hu.2.1
    rw [p72_H] at h
    omega
  rw [safeOddLoss_eq_lower P72 N p hnot, lower_eq72 (by omega)]
  exact if_pos (by omega : p ≤ 37 * N)

theorem g14472 {N p : Nat} (hN : 0 < N) (hp : (p : ℝ) ≤ (954 / 29 : ℝ) * N) :
    (144 : ℝ) * N - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  have hr : (29 : ℝ) * p ≤ 954 * N := by linarith
  have hn : 29 * p ≤ 954 * N := by exact_mod_cast hr
  rw [safe_pool72 hN hn]
  push_cast
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72
