module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Small quotient nodes for actual prefix Cauchy tests -/

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixBounds

/-- A nonempty prefix strip forces the prime beyond twice the frame
modulus, using the same qN < p squared bound supplied by the checker. -/
theorem prime_large (p q m N : ℕ) (hp : 0<p) (hm : p≤m)
    (hsize : 2*m≤N) (hN : q*N<p*p) : 2*q<p := by
  have h1 := Nat.mul_le_mul_left q hsize
  have h2 := Nat.mul_le_mul_left (2*q) hm
  have hh : (2*q)*p<p*p := by nlinarith
  exact (Nat.mul_lt_mul_right hp).mp hh

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

/-- All denominators of the integer Cauchy specialization are nonzero
in the actual prime field. -/
theorem cauchy_denominator_ne (p q m N a b : ℕ) [Fact p.Prime]
    (hq : 2≤q) (hsize : 2*m≤N) (hN : q*N<p*p) (ha : a<N)
    (hb : b≤m/p+1) (k : Fin b) :
    ((a/p:ℕ):ZMod p)-(-(((k:ℕ)+1:ℕ):ZMod p))≠0 := by
  have hp := (Fact.out : p.Prime).one_lt
  have hsum := quotient_add_count p q m N a b hp hq hsize hN ha hb
  have hk := k.2
  have hlt : a/p+((k:ℕ)+1)<p := by omega
  have hpos : 0<a/p+((k:ℕ)+1) := by positivity
  rw [sub_neg_eq_add,← Nat.cast_add]
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hh := Nat.le_of_dvd hpos hd
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixBounds
