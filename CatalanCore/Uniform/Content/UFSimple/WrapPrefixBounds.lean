module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Small quotient nodes for actual prefix Cauchy tests -/

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixBounds


/-- Actual row/column quotient nodes plus every Cauchy-test pole index
stay strictly below p. This prevents introducing a new bad prime. -/
theorem quotient_add_count (p q m N a b : ℕ) (hp : 1<p) (hq : 2≤q)
    (hsize : 2*m≤N) (hN : q*N<p*p) (ha : a<N) (hb : b≤m/p+1) :
    a/p+b<p := by
  have hpa : a/p*p≤a := Nat.div_mul_le_self a p
  have hpm : m/p*p≤m := Nat.div_mul_le_self m p
  have hsmall := Nat.mul_le_mul_right N hq
  have ha2 : 2*(a/p)<p := by
    have h2a : 2*a<p*p := by nlinarith
    have hh : (2*(a/p))*p<p*p := by nlinarith
    exact (Nat.mul_lt_mul_right (by omega : 0<p)).mp hh
  have hm4 : 4*(m/p)<p := by
    have h4m : 4*m<p*p := by nlinarith
    have hh : (4*(m/p))*p<p*p := by nlinarith
    exact (Nat.mul_lt_mul_right (by omega : 0<p)).mp hh
  omega


end CatalanCore.Uniform.Content.UFSimple.WrapPrefixBounds
