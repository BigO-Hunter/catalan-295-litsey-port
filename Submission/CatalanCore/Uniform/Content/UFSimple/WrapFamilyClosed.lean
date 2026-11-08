module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapFamily

@[expose] public section

/-! # Automatic closed wrapped candidates for the original determinant -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapFamilyClosed

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}

namespace Hyp
variable (H : WrapClosed.Hyp Fr q o r s l p N T)
include H

theorem block_gle (K : Finset (Fin r)) (B L lo hi : ℕ) (hBL : B=L*p) (hhi : hi<p) (hlo : lo≤hi)
    (hS : p∣B+lo ∨ p∣q*(B+lo)-o) (hE : p∣B+hi+1 ∨ p∣q*(B+hi+1)-o)
    (hNo : ∀ k,B+lo<k → k≤B+hi → ¬ttSing p q o (k:ℤ)) :
    GLE p (closedBound (s+1-l) (r+2*l-1) p (max (r+2*l-1) (B+lo))
      (min (B+hi) (r+2*l-1+p-1)) (B+lo))
      (FullN Fr (fun a:WrapKeep.Keep K => (a.1:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let a := r+2*l-1
  let t0 := max a (B+lo)
  let tv := min (B+hi) (a+p-1)
  by_cases hok : t0<r+p ∧ t0≤tv
  · exact WrapFamily.window_gle (H.blockWindow B L lo hi hBL hhi hlo hok.1 hok.2 hS hE hNo) K
  · have hsub : min (tv+1) (a+2*(s+1-l))-t0=0 := by
      have := H.hl; have := H.hls; have := H.hp
      dsimp only [a] at *
      omega
    have he : closedBound (s+1-l) a p t0 tv (B+lo)=2*(r+s+l)-(s+1-l) := by
      unfold closedBound
      rw [hsub]
      simp only [Nat.zero_sub,Nat.zero_add,add_zero]
      have := H.hl; have := H.hls
      dsimp only [a]
      congr 1
      omega
    rw [show closedBound (s+1-l) (r+2*l-1) p (max (r+2*l-1) (B+lo))
      (min (B+hi) (r+2*l-1+p-1)) (B+lo)=2*(r+s+l)-(s+1-l) from he]
    exact (WrapMember.baseline H K).mono (by omega)

theorem candidate_gle (K : Finset (Fin r)) (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o)
    (j : ℕ) (z : Bool) : GLE p (WrapExpr.candidate r p (s+l) rho 0 j z)
      (FullN Fr (fun a:WrapKeep.Keep K => (a.1:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let B := p*(r/p)+j*p
  have hB : p∣B := by refine ⟨r/p+j,?_⟩; dsimp only [B]; ring
  have hBL : B=(r/p+j)*p := by dsimp only [B]; ring
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  cases z
  · have hE : p∣q*(B+(rho-1)+1)-o := by
      have he : B+(rho-1)+1=B+rho := by omega
      rw [he]
      exact pole_dvd hB hrho hrho1 T.o_lt
    have hh := block_gle H K B (r/p+j) 0 (rho-1) hBL (by omega) (by omega)
      (Or.inl (by simpa only [add_zero] using hB)) (Or.inr hE)
      (noSing_blk T H.hqp hB (by omega) hrho hrho1 hrhop (Or.inr (by omega)))
    simpa only [WrapExpr.candidate,H.dim_eq,H.virtual_eq,Nat.zero_add,B,
      Bool.false_eq_true,eq_self_iff_true,if_true,if_false] using hh
  · have hE : p∣B+(p-1)+1 := by
      have he : B+(p-1)+1=B+p := by omega
      rw [he]
      exact Nat.dvd_add hB (dvd_refl p)
    have hh := block_gle H K B (r/p+j) rho (p-1) hBL (by omega) (by omega)
      (Or.inr (pole_dvd hB hrho hrho1 T.o_lt)) (Or.inl hE)
      (noSing_blk T H.hqp hB (by omega) hrho hrho1 hrhop (Or.inl le_rfl))
    simpa only [WrapExpr.candidate,H.dim_eq,H.virtual_eq,Nat.zero_add,B,
      Bool.false_eq_true,eq_self_iff_true,if_true,if_false] using hh

/-- The best of all six wrapped candidates is a proved original-determinant price. -/
theorem price_gle (K : Finset (Fin r)) (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p (WrapExpr.price r p (s+l) rho 0)
      (FullN Fr (fun a:WrapKeep.Keep K => (a.1:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hh := candidate_gle H K rho hrho1 hrhop hrho
  unfold WrapExpr.price
  exact WrapClosed.gle_min (WrapClosed.gle_min (WrapClosed.gle_min (hh 0 false) (hh 0 true)) (WrapClosed.gle_min (hh 1 false) (hh 1 true)))
    (WrapClosed.gle_min (hh 2 false) (hh 2 true))

/-- The existing expression language evaluates to the proved full wrapped price. -/
theorem expr_gle (K : Finset (Fin r)) (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p ((WrapExpr.tWrap 0).evalN r p (s+l) rho)
      (FullN Fr (fun a:WrapKeep.Keep K => (a.1:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  rw [WrapExpr.evalN_tWrap]
  exact price_gle H K rho hrho1 hrhop hrho

end Hyp

theorem wrapped_member_gle (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r m : ℕ) (hm : m<p) (hmp : p≤2*m)
    (hsize : r+2*m≤N) (K : Finset (Fin r)) (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p ((WrapExpr.tWrap 0).evalN r p m rho)
      (FullN Fr (fun a:WrapKeep.Keep K => (a.1:ℕ)) (WrapActual.xs r (m:=m)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hp2 : p≠2 := by have := T.o_pos; have := T.o_lt; omega
  have hpOdd : p%2=1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  obtain ⟨s,l,hl,hls,hp,rfl⟩ : ∃ s l,1≤l ∧ l≤s ∧ p=2*s+1 ∧ m=s+l := by
    have hh := WrapGeometry.wrap_parameters hpOdd hm hmp
    exact ⟨p/2,m-p/2,hh⟩
  have H : WrapClosed.Hyp Fr q o r s l p N T :=
    { hl := hl, hls := hls, hp := hp, hqp := hqp, hN := hN, hsize := hsize,
      hsq := hsq, hnorm := hnorm, hnorm0 := hnorm0 }
  exact Hyp.expr_gle H K rho hrho1 hrhop hrho

end CatalanCore.Uniform.Content.UFSimple.WrapFamilyClosed
