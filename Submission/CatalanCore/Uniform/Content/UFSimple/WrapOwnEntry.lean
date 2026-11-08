module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapLoadTest
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapTestEntryRelation
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapHarmonicPivot

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnEntry

variable (p : ℕ) [Fact p.Prime]

/-- The actual independently indexed row/column test entry is precisely
the harmonic Cauchy entry, with the original frame normalization. -/
theorem residue (q o k j0 gamma m N b x y : ℕ) (u : GaussLoc p)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p) (hroot : q*k=j0*p+o)
    (hsize : 2*m≤N) (hN : q*N<p*p)
    (hxN : gamma+x*p<N) (hyN : gamma+y*p<N)
    (hb : b≤m/p+1) (hb0 : 1≤b)
    (hxsmall : x<p) (hysmall : y<p) (hxy : x≠y) :
    res p (WrapEntryTest.value p q o
      (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)) u
      (gamma+x*p) (gamma+y*p))=
        res p u*WrapHarmonic.entry (K:=RatFunc (ZMod p)) b (decide (k≤gamma)) x y := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N hq0) hN
  have hcol : ((gamma+x*p:ℕ):ZMod p)=((gamma+y*p:ℕ):ZMod p) := by simp
  have hd := WrapTestEntryRelation.divided_commutator p
    (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)) q o N u hsingle
    (gamma+x*p) (gamma+y*p) hxN hyN hcol
  have hqx : (gamma+x*p)/p=x := by
    rw [Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hg,zero_add]
  have hqy : (gamma+y*p)/p=y := by
    rw [Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hg,zero_add]
  rw [hqx,hqy] at hd
  have hres := congrArg (res p) hd
  simp only [map_mul,map_sub,map_natCast,WrapTestEntryRelation.load] at hres
  rw [WrapLoadTest.own_load p q o k j0 gamma y m N b hq0 hqp hq2 hoq hk0 hk hg hroot
      hsize hN hyN hb hb0,
    WrapLoadTest.own_load p q o k j0 gamma x m N b hq0 hqp hq2 hoq hk0 hk hg hroot
      hsize hN hxN hb hb0] at hres
  have hden : (y:RatFunc (ZMod p))-(x:RatFunc (ZMod p))≠0 := by
    apply sub_ne_zero.mpr
    intro he
    apply WrapHarmonicPivot.cast_ne p y x hysmall hxsmall (Ne.symm hxy)
    apply (RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
    simpa only [map_natCast] using he
  apply mul_left_cancel₀ hden
  unfold WrapHarmonic.entry
  rw [WrapHarmonic.load_test,WrapHarmonic.load_test]
  simp only [Bool.decide_iff]
  convert hres using 1 <;> field_simp [hden] <;> ring

end CatalanCore.Uniform.Content.UFSimple.WrapOwnEntry
