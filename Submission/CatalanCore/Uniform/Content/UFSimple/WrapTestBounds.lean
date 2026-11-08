module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPrefixBounds

@[expose] public section

/-! # Elementary denominators at an own-fibre Cauchy test -/

namespace CatalanCore.Uniform.Content.UFSimple.WrapTestBounds

/-- Every fractional pole before an own-fibre endpoint survives its
Cauchy test. The test uses at least one pole, even for an empty pivot. -/
theorem denominator_bounds (p q m N a b j epsilon h : ℕ)
    (hp : 1<p) (hq : 2≤q) (hsize : 2*m≤N) (hN : q*N<p*p)
    (ha : a<N) (hb : b≤m/p+1) (hb0 : 1≤b)
    (hj : j≤a/p) (he : epsilon≤1) (hh : h<j+epsilon) :
    0<h+b+1-epsilon ∧ h+b+1-epsilon<p := by
  have hs := WrapPrefixBounds.quotient_add_count p q m N a b hp hq hsize hN ha hb
  omega

theorem denominator_ne (p q m N a b j epsilon h : ℕ) [Fact p.Prime]
    (hq : 2≤q) (hsize : 2*m≤N) (hN : q*N<p*p)
    (ha : a<N) (hb : b≤m/p+1) (hb0 : 1≤b)
    (hj : j≤a/p) (he : epsilon≤1) (hh : h<j+epsilon) :
    ((h+b+1-epsilon:ℕ):ZMod p)≠0 := by
  have hd := denominator_bounds p q m N a b j epsilon h
    (Fact.out : p.Prime).one_lt hq hsize hN ha hb hb0 hj he hh
  intro hz
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have := Nat.le_of_dvd hd.1 hdiv
  omega

/-- The fractional root cancels at the test, leaving an integer
Cauchy denominator times q. -/
theorem test_identity {K : Type*} [Field K] (q j0 h b epsilon : ℕ)
    (hq : (q:K)≠0) :
    ((j0:K)+(q:K)*(h:K))+(q:K)*
      (((b:K)+1-(epsilon:K))-(j0:K)/(q:K))=
        (q:K)*((h:K)+(b:K)+1-(epsilon:K)) := by
  field_simp [hq]
  <;> ring

end CatalanCore.Uniform.Content.UFSimple.WrapTestBounds
