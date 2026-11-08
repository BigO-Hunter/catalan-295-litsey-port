module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapHarmonic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapHarmonicPivot

variable (p : ℕ) [Fact p.Prime]

theorem cast_injective {ι : Type*} (x : ι → ℕ) (hx : Function.Injective x)
    (hsmall : ∀ i,x i<p) : Function.Injective (fun i => (x i:ZMod p)) := by
  intro i j he
  apply hx
  have hm := (ZMod.natCast_eq_natCast_iff' (x i) (x j) p).mp he
  simpa only [Nat.mod_eq_of_lt (hsmall i),Nat.mod_eq_of_lt (hsmall j)] using hm

theorem pole_ne (b x : ℕ) (hxb : x+b<p) (k : Fin b) :
    (x:ZMod p)≠WrapHarmonic.poles b k := by
  unfold WrapHarmonic.poles
  intro he
  push_cast at he
  have hz : ((x+(k:ℕ)+1:ℕ):ZMod p)=0 := by
    push_cast
    linear_combination he
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hpos : 0<x+(k:ℕ)+1 := by omega
  have hbound := Nat.le_of_dvd hpos hd
  have := k.2
  omega

theorem poles_injective (b : ℕ) (hb : b<p) :
    Function.Injective (WrapHarmonic.poles (K:=ZMod p) b) := by
  intro i j he
  apply Fin.ext
  have hcast : (((i:ℕ)+1:ℕ):ZMod p)=(((j:ℕ)+1:ℕ):ZMod p) := neg_injective he
  have hm := (ZMod.natCast_eq_natCast_iff' ((i:ℕ)+1) ((j:ℕ)+1) p).mp hcast
  have hi : (i:ℕ)+1<p := by have := i.2; omega
  have hj : (j:ℕ)+1<p := by have := j.2; omega
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hm
  omega

/-- The balanced block of the actual harmonic test is nonsingular at
all distinct, disjoint original quotient nodes below the checker bound. -/
theorem det_ne (b : ℕ) (epsilon : Bool) (x y : Fin b → ℕ) (hb : b<p)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxb : ∀ i,x i+b<p) (hyb : ∀ i,y i+b<p) (hxy : ∀ i j,y j≠x i) :
    (WrapHarmonic.matrix (K:=ZMod p) b epsilon x y).det≠0 := by
  have hxsmall : ∀ i,x i<p := by intro i; have := hxb i; omega
  have hysmall : ∀ i,y i<p := by intro i; have := hyb i; omega
  have hdis : ∀ i j,(y j:ZMod p)≠(x i:ZMod p) := by
    intro i j he
    apply hxy i j
    have hm := (ZMod.natCast_eq_natCast_iff' (y j) (x i) p).mp he
    simpa only [Nat.mod_eq_of_lt (hysmall j),Nat.mod_eq_of_lt (hxsmall i)] using hm
  rw [WrapHarmonic.matrix_neg,Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (WrapTelescoping.loewner_det_ne _ _ _ (poles_injective p b hb)
      (cast_injective p x hx hxsmall) (cast_injective p y hy hysmall)
      (fun i k => pole_ne p b (x i) (hxb i) k)
      (fun i k => pole_ne p b (y i) (hyb i) k) hdis)

theorem cast_ne (a b : ℕ) (ha : a<p) (hb : b<p) (hab : a≠b) :
    (a:ZMod p)≠(b:ZMod p) := by
  intro he
  apply hab
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp he
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hm

/-- The same actual harmonic test has a nonzero row reference at each
unused original quotient node. Row and column balanced nodes may differ. -/
theorem reference_ne (b : ℕ) (epsilon : Bool) (x y : Fin b → ℕ) (t : ℕ) (hb : b<p)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxb : ∀ i,x i+b<p) (hyb : ∀ i,y i+b<p) (htb : t+b<p)
    (hxy : ∀ i j,y j≠x i) (hxt : ∀ i,x i≠t) (hyt : ∀ i,y i≠t) :
    1-(fun j => WrapHarmonic.entry (K:=ZMod p) b epsilon t (y j)) ⬝ᵥ
      ((WrapHarmonic.matrix b epsilon x y)⁻¹ *ᵥ 1)≠0 := by
  have hxsmall : ∀ i,x i<p := by intro i; have := hxb i; omega
  have hysmall : ∀ i,y i<p := by intro i; have := hyb i; omega
  have htsmall : t<p := by omega
  have hdis := fun i j => cast_ne p (y j) (x i) (hysmall j) (hxsmall i) (hxy i j)
  have hpoles := poles_injective p b hb
  have hxf := cast_injective p x hx hxsmall
  have hyf := cast_injective p y hy hysmall
  have hxp := fun i k => pole_ne p b (x i) (hxb i) k
  have hyp := fun i k => pole_ne p b (y i) (hyb i) k
  have hQ := WrapTelescoping.loewner_det_ne _ _ _ hpoles hxf hyf hxp hyp hdis
  have hs : (fun j => WrapHarmonic.entry (K:=ZMod p) b epsilon t (y j))=
      -(fun j => WrapTelescoping.entry (WrapHarmonic.poles b) (t:ZMod p) (y j:ZMod p)) := by
    funext j
    exact WrapHarmonic.entry_eq b t (y j) epsilon
  rw [hs,WrapHarmonic.matrix_neg,WrapHarmonic.neg_reference _ _ (isUnit_iff_ne_zero.mpr hQ)]
  exact WrapTelescoping.row_reference_ne _ _ _ hpoles hxf hyf hxp hyp hdis (t:ZMod p)
    (fun k => pole_ne p b t htb k)
    (fun i => cast_ne p (x i) t (hxsmall i) htsmall (hxt i))
    (fun j => cast_ne p (y j) t (hysmall j) htsmall (hyt j))

end CatalanCore.Uniform.Content.UFSimple.WrapHarmonicPivot
