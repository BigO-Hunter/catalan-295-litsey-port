module

public import CatalanCore.Uniform.Content.UFSimple.WrapWindow

@[expose] public section

/-! # Automatic closed wrapped candidates for the original determinant -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapClosed

/-- Single-level hypotheses for the actual wrapped alternating matrix. -/
structure Hyp (Fr : Frame) (q o r s l p N : ℕ) (T : TwoTermData Fr q o) [Fact p.Prime] where
  hl : 1≤l
  hls : l≤s
  hp : p=2*s+1
  hqp : q<p
  hN : N<p*p
  hsize : r+2*(s+l)≤N
  hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o
  hnorm : Fr.norm∈S p
  hnorm0 : red p Fr.norm≠0

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}

/-- Simultaneous denominator prices give their minimum. -/
theorem gle_min {a b : ℕ} {f : ℚ[X]} (ha : GLE p a f) (hb : GLE p b f) : GLE p (min a b) f := by
  rcases min_choice a b with h|h
  · rwa [h]
  · rwa [h]

namespace Hyp

variable (H : Hyp Fr q o r s l p N T)
include H

theorem hp2 : p≠2 := by have := H.hl; have := H.hls; have := H.hp; omega

theorem ho : (o:ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff o p).1 hz
  have hle := Nat.le_of_dvd T.o_pos hd
  have := T.o_lt; have := H.hqp; omega

theorem hq0 : (q:ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff q p).1 hz
  have hpos : 0<q := by have := T.o_pos; have := T.o_lt; omega
  have hle := Nat.le_of_dvd hpos hd
  have := H.hqp; omega

noncomputable def D : PoleData Fr p N := twoTermPoleData T H.hN.le H.hsq H.hnorm H.hnorm0

theorem common_bound (a : Fin r) : (a:ℕ)<N := by
  have := a.2; have := H.hl; have := H.hls; have := H.hsize; omega

theorem xs_bound (i : Fin (s+l)) : WrapActual.xs r i<N := by
  change r+2*(i:ℕ)<N
  have := i.2; have := H.hsize; omega

theorem ys_bound (i : Fin (s+l)) : WrapActual.ys r i<N := by
  change r+2*(i:ℕ)+1<N
  have := i.2; have := H.hsize; omega

noncomputable def hint : ∀ i j,(p:ℚ)^2*Fr.Mn
    (rowNode (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) i)
    (colNode (fun a:Fin r => (a:ℕ)) (WrapActual.ys r (m:=s+l)) j)∈LocRing p :=
  hint_of_poleData H.D H.hN H.common_bound H.xs_bound H.ys_bound

noncomputable def matrix := WrapActual.reordered (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hint

/-- The primitive mixed core already supplies the baseline first Schur layer. -/
noncomputable def baseData := TwoLevelData.trivial (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
  (WrapSchur.dividedSchur H.matrix)

noncomputable def baseWitness := WrapActual.witness_of_data T H.hqp H.hN H.hsq H.hnorm H.hnorm0
  (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.baseData

theorem base_price : H.baseWitness.price=2*(r+s+l)-(s+1-l) := by
  simpa only [baseWitness,Fintype.card_fin,Nat.sub_self,Nat.zero_add,add_zero] using
    (WrapActual.witness_of_data_price T H.hqp H.hN H.hsq H.hnorm H.hnorm0 (fun a:Fin r => (a:ℕ))
      r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.baseData)

theorem base_gle : GLE p (2*(r+s+l)-(s+1-l))
    (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let M := FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])
  have hs := WrapSource.gle_minor_reindex (M.map (scaleU p))
    (WrapGeometry.rowFullEquiv (Fin r) s l H.hl H.hls)
    (WrapGeometry.colFullEquiv (Fin r) s l H.hl H.hls) H.baseWitness id id (le_rfl)
  have hg := gle_submatrix_of_scaleU M id id hs
  have hf : GLE p H.baseWitness.price M.det := by
    simpa only [Nat.sub_self,add_zero,Matrix.submatrix_id_id] using hg
  rwa [H.base_price] at hf

/-- A regular block-bit interval supplies every arithmetic field of the
actual wrapped window, including both outside separation obligations. -/
noncomputable def blockWindow (B L lo hi : ℕ) (hBL : B=L*p) (hhi : hi<p) (hlo : lo≤hi)
    (hok1 : max (r+2*l-1) (B+lo)<r+p)
    (hok2 : max (r+2*l-1) (B+lo)≤min (B+hi) (r+2*l-1+p-1))
    (hS : p∣B+lo ∨ p∣q*(B+lo)-o) (hE : p∣B+hi+1 ∨ p∣q*(B+hi+1)-o)
    (hNo : ∀ k,B+lo<k → k≤B+hi → ¬ttSing p q o (k:ℤ)) :
    WrapWindow.Window Fr q o r s l p N T := by
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  have hdivB : ∀ x,B≤x → x<B+p → x/p=L := by
    intro x hx1 hx2
    apply Nat.div_eq_of_lt_le
    · rw [← hBL]; exact hx1
    · rw [Nat.add_mul,one_mul,← hBL]; exact hx2
  refine {
    hl := H.hl, hls := H.hls, hp := H.hp, hqp := H.hqp, hN := H.hN, hsize := H.hsize,
    hsq := H.hsq, hnorm := H.hnorm, hnorm0 := H.hnorm0, hp2 := H.hp2, ho := H.ho, hq0 := H.hq0,
    w0 := B+lo, t0 := max (r+2*l-1) (B+lo), tv := min (B+hi) (r+2*l-1+p-1),
    hmax := rfl, ht0p := hok1, htv := hok2,
    htvp := by have := H.hl; omega,
    hwin := by omega,
    hdiv := ?_, hw := ?_, hsepL := ?_, hsepR := ?_ }
  · rw [hdivB (min (B+hi) (r+2*l-1+p-1)) (by omega) (by omega),
      hdivB (B+lo) (by omega) (by omega)]
  · intro k hk1 hk2
    exact hNo k hk1 (by omega)
  · intro v hv0 hv1
    exact ⟨B+lo,by omega,by omega,hS⟩
  · intro v hv1 hv2
    have hcap : v≤r+2*l-1+p-1 := by have := H.hl; have := H.hls; have := H.hp; omega
    exact ⟨B+hi+1,by omega,by omega,hE⟩

/-- Every block-bit candidate is sound. Empty or out-of-range candidates
reduce exactly to the primitive mixed-core baseline. -/
theorem block_gle (B L lo hi : ℕ) (hBL : B=L*p) (hhi : hi<p) (hlo : lo≤hi)
    (hS : p∣B+lo ∨ p∣q*(B+lo)-o) (hE : p∣B+hi+1 ∨ p∣q*(B+hi+1)-o)
    (hNo : ∀ k,B+lo<k → k≤B+hi → ¬ttSing p q o (k:ℤ)) :
    GLE p (closedBound (s+1-l) (r+2*l-1) p (max (r+2*l-1) (B+lo))
      (min (B+hi) (r+2*l-1+p-1)) (B+lo))
      (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let a := r+2*l-1
  let t0 := max a (B+lo)
  let tv := min (B+hi) (a+p-1)
  by_cases hok : t0<r+p ∧ t0≤tv
  · exact (H.blockWindow B L lo hi hBL hhi hlo hok.1 hok.2 hS hE hNo).full_gle
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
    exact H.base_gle

theorem dim_eq : WrapExpr.dim (s+l) p=s+1-l := by
  have hm : s+l<p := by have := H.hp; have := H.hls; omega
  have he : p-(s+l)=s+1-l := by have := H.hp; have := H.hl; have := H.hls; omega
  unfold WrapExpr.dim
  rw [Nat.mod_eq_of_lt hm,he,min_eq_right (by have := H.hl; have := H.hls; omega)]

theorem virtual_eq : WrapExpr.virtual r (s+l) p=r+2*l-1 := by
  unfold WrapExpr.virtual
  rw [H.dim_eq]
  have := H.hl; have := H.hls; omega

/-- Every unconditional expression candidate prices the original wrapped determinant. -/
theorem candidate_gle (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o)
    (j : ℕ) (z : Bool) : GLE p (WrapExpr.candidate r p (s+l) rho 0 j z)
      (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let B := p*(r/p)+j*p
  have hB : p∣B := by refine ⟨r/p+j,?_⟩; dsimp only [B]; ring
  have hBL : B=(r/p+j)*p := by dsimp only [B]; ring
  have hp0 : 0<p := (Fact.out : p.Prime).pos
  cases z
  · have hE : p∣q*(B+(rho-1)+1)-o := by
      have he : B+(rho-1)+1=B+rho := by omega
      rw [he]
      exact pole_dvd hB hrho hrho1 T.o_lt
    have hh := H.block_gle B (r/p+j) 0 (rho-1) hBL (by omega) (by omega)
      (Or.inl (by simpa only [add_zero] using hB)) (Or.inr hE)
      (noSing_blk T H.hqp hB (by omega) hrho hrho1 hrhop (Or.inr (by omega)))
    simpa only [WrapExpr.candidate,H.dim_eq,H.virtual_eq,Nat.zero_add,B,
      Bool.false_eq_true,eq_self_iff_true,if_true,if_false] using hh
  · have hE : p∣B+(p-1)+1 := by
      have he : B+(p-1)+1=B+p := by omega
      rw [he]
      exact Nat.dvd_add hB (dvd_refl p)
    have hh := H.block_gle B (r/p+j) rho (p-1) hBL (by omega) (by omega)
      (Or.inr (pole_dvd hB hrho hrho1 T.o_lt)) (Or.inl hE)
      (noSing_blk T H.hqp hB (by omega) hrho hrho1 hrhop (Or.inl le_rfl))
    simpa only [WrapExpr.candidate,H.dim_eq,H.virtual_eq,Nat.zero_add,B,
      Bool.false_eq_true,eq_self_iff_true,if_true,if_false] using hh

/-- The best of all six wrapped candidates is a proved original-determinant price. -/
theorem price_gle (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p (WrapExpr.price r p (s+l) rho 0)
      (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hh := H.candidate_gle rho hrho1 hrhop hrho
  unfold WrapExpr.price
  exact gle_min (gle_min (gle_min (hh 0 false) (hh 0 true)) (gle_min (hh 1 false) (hh 1 true)))
    (gle_min (hh 2 false) (hh 2 true))

/-- The existing expression language evaluates to the proved full wrapped price. -/
theorem expr_gle (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p ((WrapExpr.tWrap 0).evalN r p (s+l) rho)
      (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  rw [WrapExpr.evalN_tWrap]
  exact H.price_gle rho hrho1 hrhop hrho

end Hyp

/-- Uniform full-determinant wrapped theorem in the original m,p parameters.
This theorem alone does not assert common-deletion zero debit or prefix descent. -/
theorem wrapped_full_gle (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (r m : ℕ) (hm : m<p) (hmp : p≤2*m)
    (hsize : r+2*m≤N) (rho : ℕ) (hrho1 : 1≤rho) (hrhop : rho<p) (hrho : p∣q*rho-o) :
    GLE p ((WrapExpr.tWrap 0).evalN r p m rho)
      (FullN Fr (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=m)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hp2 : p≠2 := by have := T.o_pos; have := T.o_lt; omega
  have hpOdd : p%2=1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  obtain ⟨s,l,hl,hls,hp,rfl⟩ : ∃ s l,1≤l ∧ l≤s ∧ p=2*s+1 ∧ m=s+l := by
    have hh := WrapGeometry.wrap_parameters hpOdd hm hmp
    exact ⟨p/2,m-p/2,hh⟩
  have H : Hyp Fr q o r s l p N T :=
    { hl := hl, hls := hls, hp := hp, hqp := hqp, hN := hN, hsize := hsize,
      hsq := hsq, hnorm := hnorm, hnorm0 := hnorm0 }
  exact H.expr_gle rho hrho1 hrhop hrho

end CatalanCore.Uniform.Content.UFSimple.WrapClosed
