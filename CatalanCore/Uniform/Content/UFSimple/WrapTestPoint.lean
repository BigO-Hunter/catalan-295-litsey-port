module

public import CatalanCore.Uniform.Content.UFSimple.WrapPoleTest
public import CatalanCore.Uniform.Content.UFSimple.WrapPoleResidue
public import CatalanCore.Uniform.Content.UFSimple.WrapPoleLoad
public import CatalanCore.Uniform.Content.UFSimple.WrapTestBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapTestPoint

variable (p : ℕ) [Fact p.Prime]

noncomputable def point (q j0 b epsilon : ℕ) : GaussLoc p :=
  ((b:GaussLoc p)+1-(epsilon:GaussLoc p))-
    (j0:GaussLoc p)*Ring.inverse (q:GaussLoc p)

theorem point_residue (q j0 b epsilon : ℕ) (hq : res p (q:GaussLoc p)≠0) :
    res p (point p q j0 b epsilon)=
      ((b:RatFunc (ZMod p))+1-(epsilon:RatFunc (ZMod p)))-
        (j0:RatFunc (ZMod p))/(q:RatFunc (ZMod p)) := by
  unfold point
  rw [map_sub,map_sub,map_add,map_one,map_mul,
    res_inverse _ (isUnit_of_res_ne _ hq)]
  simp only [WrapSimplePole.res_nat,map_natCast,div_eq_mul_inv]

/-- Actual fractional poles, indexed in their original progression,
have unit elementary denominators at the selected own-fibre test. -/
theorem pole_unit (q o k j0 m N a b j epsilon h : ℕ)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hroot : q*k=j0*p+o)
    (hsize : 2*m≤N) (hN : q*N<p*p) (haN : a<N)
    (hb : b≤m/p+1) (hb0 : 1≤b) (hj : j≤a/p)
    (he : epsilon≤1) (hh : h<j+epsilon)
    (hz : res p ((q*(k+h*p)-o:ℕ):GaussLoc p)=0) :
    IsUnit (WrapPole.quotient p ((q*(k+h*p)-o:ℕ):GaussLoc p) hz+
      (q:GaussLoc p)*point p q j0 b epsilon) := by
  have hp := (Fact.out : p.Prime).pos
  have hq := WrapSimplePole.q_res_ne p q hq0 hqp
  have hqf : (q:RatFunc (ZMod p))≠0 := by
    simpa only [WrapSimplePole.res_nat,map_natCast] using hq
  have hd := WrapTestBounds.denominator_ne p q m N a b j epsilon h
    hq2 hsize hN haN hb hb0 hj he hh
  have hdf : ((h+b+1-epsilon:ℕ):RatFunc (ZMod p))≠0 := by
    intro hzero
    apply hd
    apply (RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
    simpa only [map_natCast,map_zero] using hzero
  apply isUnit_of_res_ne
  rw [map_add,map_mul,WrapPoleResidue.quotient_nat,
    WrapPoleLoad.fractional_quotient p q o k j0 h hp hroot,
    point_residue p q j0 b epsilon hq]
  simp only [WrapSimplePole.res_nat,map_natCast,Nat.cast_add,Nat.cast_mul,map_add,map_mul]
  rw [WrapTestBounds.test_identity q j0 h b epsilon hqf]
  have hsub : epsilon≤h+b+1 := by omega
  have heq : (h:RatFunc (ZMod p))+(b:RatFunc (ZMod p))+1-(epsilon:RatFunc (ZMod p))=
      ((h+b+1-epsilon:ℕ):RatFunc (ZMod p)) := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  rw [heq]
  exact mul_ne_zero hqf hdf

end CatalanCore.Uniform.Content.UFSimple.WrapTestPoint
