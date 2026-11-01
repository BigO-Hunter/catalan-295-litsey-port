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


theorem dim_eq : WrapExpr.dim (s+l) p=s+1-l := by
  have hm : s+l<p := by have := H.hp; have := H.hls; omega
  have he : p-(s+l)=s+1-l := by have := H.hp; have := H.hl; have := H.hls; omega
  unfold WrapExpr.dim
  rw [Nat.mod_eq_of_lt hm,he,min_eq_right (by have := H.hl; have := H.hls; omega)]

theorem virtual_eq : WrapExpr.virtual r (s+l) p=r+2*l-1 := by
  unfold WrapExpr.virtual
  rw [H.dim_eq]
  have := H.hl; have := H.hls; omega


end Hyp


end CatalanCore.Uniform.Content.UFSimple.WrapClosed
