module

public import CatalanCore.Uniform.Content.UFSimple.WrapSimplePole

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Integral deformed original two-term matrix entries -/

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapDeformedEntry

variable (p : ℕ) [Fact p.Prime]

/-- Direct integral entry formula: the node difference uses its ORIGINAL
normalized reciprocal, while only the fractional pole is deformed. -/
noncomputable def entry (q o : ℕ) (normInv : GaussLoc p) (a b : ℕ) : WrapDeform.Extension p :=
  if a=b then -(WrapDeform.embed p (Polynomial.C normInv)*
    ∑ t∈Icc 1 a,WrapIncrement.dsq p q o t)
  else WrapDeform.embed p (Polynomial.C normInv)*
    WrapDeform.embed p (Polynomial.C (WrapPole.originalNormalized p ((max a b-min a b:ℕ):GaussLoc p)))*
      ∑ t∈Ioc (min a b) (max a b),WrapIncrement.delta p q o t

noncomputable def original (q o : ℕ) (normInv : GaussLoc p) (a b : ℕ) : GaussLoc p :=
  if a=b then -(normInv*∑ t∈Icc 1 a,WrapIncrement.originalDsq p q o t)
  else normInv*WrapPole.originalNormalized p ((max a b-min a b:ℕ):GaussLoc p)*
    ∑ t∈Ioc (min a b) (max a b),WrapIncrement.originalDelta p q o t

/-- Every original entry has an original-unit clearing denominator under
the actual arithmetic hypotheses, with no generic pivot specialization. -/
theorem specializes (q o N : ℕ) (hq0 : 0<q) (hqp : q<p) (hoq : o<q)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (normInv : GaussLoc p) (a b : ℕ) (ha : a<N) (hb : b<N) :
    WrapPole.Specializes p (entry p q o normInv a b) (original p q o normInv a b) := by
  classical
  by_cases hab : a=b
  · rw [entry,original,if_pos hab,if_pos hab]
    apply WrapSpecialization.Rel.neg
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.constant _
    · apply WrapIncrement.sum_specializes
      intro t ht
      have ht1 := (Finset.mem_Icc.mp ht).1
      have htN : t<N := lt_of_le_of_lt (Finset.mem_Icc.mp ht).2 ha
      have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
      exact WrapSimplePole.dsq_specializes p q o t hq0 hqp hle (hsq t ht1 htN)
  · rw [entry,original,if_neg hab,if_neg hab]
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.mul (WrapSpecialization.Rel.constant _) (WrapSpecialization.Rel.constant _)
    · apply WrapIncrement.sum_specializes
      intro t ht
      have ht1 : 1≤t := by have := (Finset.mem_Ioc.mp ht).1; omega
      have htN : t<N := lt_of_le_of_lt (Finset.mem_Ioc.mp ht).2 (max_lt ha hb)
      have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
      exact WrapSimplePole.delta_specializes p q o t hq0 hqp hle (hsq t ht1 htN)

end CatalanCore.Uniform.Content.UFSimple.WrapDeformedEntry
