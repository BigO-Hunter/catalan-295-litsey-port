module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapIncrement
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPoleTest

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapIncrementTest

variable (p : ℕ) [Fact p.Prime]

open WrapIncrement

noncomputable def testDelta (q o t : ℕ) (point : GaussLoc p) : GaussLoc p :=
  WrapPole.originalNormalized p (t:GaussLoc p)-
    (q:GaussLoc p)*WrapPoleTest.value p (argument p q o t) (q:GaussLoc p) point

noncomputable def testDsq (q o t : ℕ) (point : GaussLoc p) : GaussLoc p :=
  WrapPole.originalNormalized p (t:GaussLoc p)^2-
    (q:GaussLoc p)^2*WrapPoleTest.value p (argument p q o t) (q:GaussLoc p) point^2

theorem delta_at (q o t : ℕ) (point : GaussLoc p) (hq : res p (q:GaussLoc p)≠0)
    (hpole : ∀ ha : res p (argument p q o t)=0,
      IsUnit (WrapPole.quotient p (argument p q o t) ha+(q:GaussLoc p)*point))
 :
    WrapPoleTest.At p point (WrapIncrement.delta p q o t) (testDelta p q o t point) := by
  unfold WrapIncrement.delta testDelta
  simp only [sub_eq_add_neg]
  apply WrapEvaluation.Rel.add
  · exact WrapEvaluation.Rel.constant _
  · apply WrapEvaluation.Rel.neg
    apply WrapEvaluation.Rel.mul
    · exact WrapEvaluation.Rel.constant _
    · exact WrapPoleTest.normalized_at p _ _ point hq hpole

theorem dsq_at (q o t : ℕ) (point : GaussLoc p) (hq : res p (q:GaussLoc p)≠0)
    (hpole : ∀ ha : res p (argument p q o t)=0,
      IsUnit (WrapPole.quotient p (argument p q o t) ha+(q:GaussLoc p)*point))
 :
    WrapPoleTest.At p point (WrapIncrement.dsq p q o t) (testDsq p q o t point) := by
  unfold WrapIncrement.dsq testDsq
  simp only [sub_eq_add_neg]
  apply WrapEvaluation.Rel.add
  · exact WrapEvaluation.Rel.constant _
  · apply WrapEvaluation.Rel.neg
    apply WrapEvaluation.Rel.mul
    · exact WrapEvaluation.Rel.constant _
    · rw [pow_two,pow_two]
      exact WrapEvaluation.Rel.mul
        (WrapPoleTest.normalized_at p _ _ point hq hpole)
        (WrapPoleTest.normalized_at p _ _ point hq hpole)

/-- Finite cumulative loads retain original-unit clearing denominators. -/
theorem sum_at (point : GaussLoc p) {ι : Type*} (s : Finset ι)
    (f : ι → WrapDeform.Extension p) (f0 : ι → GaussLoc p)
    (h : ∀ i∈s,WrapPoleTest.At p point (f i) (f0 i)) :
    WrapPoleTest.At p point (∑ i∈s,f i) (∑ i∈s,f0 i) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact ⟨0,1,by simp,by simp,by simp⟩
  | @insert i s hi ih =>
    intro h
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact WrapEvaluation.Rel.add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end CatalanCore.Uniform.Content.UFSimple.WrapIncrementTest
