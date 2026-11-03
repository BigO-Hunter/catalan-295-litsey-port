module
public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.PolySplit
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.RootScale
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

def scFast (a : Nat) : Nat → List ℚ → List ℚ
  | _, [] => []
  | i, x :: xs => x/2^(a*i) :: scFast a (i+1) xs

theorem scFast_eq (a : Nat) (p : List ℚ) (i : Nat) :
    scFast a i p = (scQ a p).map (fun v => v/2^(a*i)) := by
  induction p generalizing i with
  | nil => rfl
  | cons x xs ih =>
      simp only [scFast, scQ, List.map_cons, ih, List.map_map]
      congr 1
      apply List.map_congr_left
      intro v hv
      simp only [Nat.mul_add, Nat.mul_one, pow_add, div_div, Function.comp_apply]
      ring

theorem scFast_zero (a : Nat) (p : List ℚ) : scFast a 0 p = scQ a p := by
  simpa using scFast_eq a p 0

theorem sclPow_getD (r : ℚ) (l : List ℚ) (i k : Nat) :
    (sclPow r i l).getD k 0 = l.getD k 0*r^(i+k) := by
  induction l generalizing i k with
  | nil => simp [sclPow]
  | cons x xs ih =>
      cases k with
      | zero => simp [sclPow]
      | succ k => simpa only [sclPow,List.getD_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) k

theorem list_eq_of_getD (a b : List ℚ) (hlen : a.length = b.length)
    (h : ∀ k, a.getD k 0 = b.getD k 0) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
      cases b with
      | nil => simp at hlen
      | cons y ys =>
          have hh : x = y := by simpa using h 0
          rw [hh]
          congr 1
          apply ih ys (by simpa using hlen)
          intro k
          simpa using h (k+1)

theorem unitShift_scale (a : Nat) (c r : ℚ) (M : Nat) (p : List ℚ) :
    sclPow (2^a*r) 0 (shiftLK (2^a*c) M (scQ a p)) = sclPow r 0 (shiftLK c M p) := by
  apply list_eq_of_getD
  · simp only [cellRound_sclPow_length,shiftLK_eq',shiftL_length]
  · intro k
    by_cases hk : k ≤ M
    · rw [sclPow_getD,sclPow_getD,shiftLK_eq',shiftLK_eq',shiftL_scale a c M p k hk]
      simp only [Nat.zero_add,mul_pow,← pow_mul]
      have htwo : (2 : ℚ)^(a*k) ≠ 0 := by positivity
      field_simp
    · have h1 : (shiftLK (2^a*c) M (scQ a p)).length ≤ k := by simp only [shiftLK_eq',shiftL_length]; omega
      have h2 : (shiftLK c M p).length ≤ k := by simp only [shiftLK_eq',shiftL_length]; omega
      rw [sclPow_getD,sclPow_getD,List.getD_eq_default _ _ h1,List.getD_eq_default _ _ h2]
      simp only [zero_mul]

theorem scQ_length (a : Nat) (p : List ℚ) : (scQ a p).length = p.length := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [scQ,ih]

theorem polyRoundApx_scale (a P : Nat) (lo hi : ℚ) (p : List ℚ) :
    polyRoundApx P (2^a*lo) (2^a*hi) (scQ a p) = polyRoundApx P lo hi p := by
  have hc : (2^a*lo+2^a*hi)/2 = (2:ℚ)^a*((lo+hi)/2) := by ring
  have hr : (2^a*hi-2^a*lo)/2 = (2:ℚ)^a*((hi-lo)/2) := by ring
  simp only [polyRoundApx,cellRound,scQ_length,hc,hr]
  rw [unitShift_scale]
  simp only [shiftLK_eq',shiftL_length]

#print axioms scFast_eq
#print axioms scFast_zero
#print axioms sclPow_getD
#print axioms list_eq_of_getD
#print axioms unitShift_scale
#print axioms scQ_length
#print axioms polyRoundApx_scale
end CatalanMeasure.GenD.Signed.Data.Cells.RootScale
