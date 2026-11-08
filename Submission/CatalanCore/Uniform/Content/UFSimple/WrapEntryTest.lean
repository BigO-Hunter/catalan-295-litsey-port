module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapDeformedEntry
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapIncrementTest

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapEntryTest

variable (p : ℕ) [Fact p.Prime]

noncomputable def value (q o : ℕ) (point : GaussLoc p) (normInv : GaussLoc p) (a b : ℕ) : GaussLoc p :=
  if a=b then -(normInv*∑ t∈Icc 1 a,WrapIncrementTest.testDsq p q o t point)
  else normInv*WrapPole.originalNormalized p ((max a b-min a b:ℕ):GaussLoc p)*
    ∑ t∈Ioc (min a b) (max a b),WrapIncrementTest.testDelta p q o t point

/-- Every original entry has an original-unit clearing denominator under
the actual arithmetic hypotheses, with no generic pivot specialization. -/
theorem at_point (q o N : ℕ) (point : GaussLoc p)
    (hq : res p (q:GaussLoc p)≠0)
    (hpole : ∀ t,1≤t → t<N → ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point))
    (normInv : GaussLoc p) (a b : ℕ) (ha : a<N) (hb : b<N) :
    WrapPoleTest.At p point (WrapDeformedEntry.entry p q o normInv a b) (value p q o point normInv a b) := by
  classical
  by_cases hab : a=b
  · rw [WrapDeformedEntry.entry,value,if_pos hab,if_pos hab]
    apply WrapEvaluation.Rel.neg
    apply WrapEvaluation.Rel.mul
    · exact WrapEvaluation.Rel.constant _
    · apply WrapIncrementTest.sum_at
      intro t ht
      have ht1 := (Finset.mem_Icc.mp ht).1
      have htN : t<N := lt_of_le_of_lt (Finset.mem_Icc.mp ht).2 ha
      exact WrapIncrementTest.dsq_at p q o t point hq (hpole t ht1 htN)
  · rw [WrapDeformedEntry.entry,value,if_neg hab,if_neg hab]
    apply WrapEvaluation.Rel.mul
    · exact WrapEvaluation.Rel.mul (WrapEvaluation.Rel.constant _) (WrapEvaluation.Rel.constant _)
    · apply WrapIncrementTest.sum_at
      intro t ht
      have ht1 : 1≤t := by have := (Finset.mem_Ioc.mp ht).1; omega
      have htN : t<N := lt_of_le_of_lt (Finset.mem_Ioc.mp ht).2 (max_lt ha hb)
      exact WrapIncrementTest.delta_at p q o t point hq (hpole t ht1 htN)

end CatalanCore.Uniform.Content.UFSimple.WrapEntryTest
