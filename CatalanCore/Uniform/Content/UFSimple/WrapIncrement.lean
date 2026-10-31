module

public import CatalanCore.Uniform.Content.UFSimple.WrapPole

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Integral deformed two-term increments and original specialization -/

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapIncrement

variable (p : ℕ) [Fact p.Prime]

noncomputable def argument (q o t : ℕ) : GaussLoc p := (q:GaussLoc p)*(t:GaussLoc p)-(o:GaussLoc p)
noncomputable def delta (q o t : ℕ) : WrapDeform.Extension p :=
  WrapDeform.embed p (Polynomial.C (WrapPole.originalNormalized p (t:GaussLoc p)))-
    WrapDeform.embed p (Polynomial.C (q:GaussLoc p))*
      WrapPole.normalizedInverse p (argument p q o t) (q:GaussLoc p)
noncomputable def dsq (q o t : ℕ) : WrapDeform.Extension p :=
  WrapDeform.embed p (Polynomial.C (WrapPole.originalNormalized p (t:GaussLoc p)^2))-
    WrapDeform.embed p (Polynomial.C ((q:GaussLoc p)^2))*
      WrapPole.normalizedInverse p (argument p q o t) (q:GaussLoc p)^2
noncomputable def originalDelta (q o t : ℕ) : GaussLoc p :=
  WrapPole.originalNormalized p (t:GaussLoc p)-
    (q:GaussLoc p)*WrapPole.originalNormalized p (argument p q o t)
noncomputable def originalDsq (q o t : ℕ) : GaussLoc p :=
  WrapPole.originalNormalized p (t:GaussLoc p)^2-
    (q:GaussLoc p)^2*WrapPole.originalNormalized p (argument p q o t)^2

/-- The original normalized reciprocal is pi/a whenever the original
pole is simple; the identity is proved without introducing a field inverse. -/
theorem original_mul_normalized (a : GaussLoc p)
    (hpole : ∀ ha : res p a=0,IsUnit (WrapPole.quotient p a ha))
    (hnonpole : res p a≠0 → IsUnit a) : a*WrapPole.originalNormalized p a=piL p := by
  classical
  by_cases ha : res p a=0
  · rw [WrapPole.originalNormalized,dif_pos ha]
    calc
      _=(piL p*WrapPole.quotient p a ha)*Ring.inverse (WrapPole.quotient p a ha) :=
        congrArg (fun z => z*Ring.inverse (WrapPole.quotient p a ha)) (WrapPole.quotient_spec p a ha)
      _=_ := by rw [mul_assoc,Ring.mul_inverse_cancel _ (hpole ha),mul_one]
  · rw [WrapPole.originalNormalized,dif_neg ha]
    calc
      _=piL p*(a*Ring.inverse a) := by ring
      _=_ := by rw [Ring.mul_inverse_cancel _ (hnonpole ha),mul_one]

theorem delta_specializes (q o t : ℕ) (hq : res p (q:GaussLoc p)≠0)
    (hpole : ∀ ha : res p (argument p q o t)=0,
      IsUnit (WrapPole.quotient p (argument p q o t) ha))
    (hnonpole : res p (argument p q o t)≠0 → IsUnit (argument p q o t)) :
    WrapPole.Specializes p (delta p q o t) (originalDelta p q o t) := by
  unfold delta originalDelta
  simp only [sub_eq_add_neg]
  apply WrapSpecialization.Rel.add
  · exact WrapSpecialization.Rel.constant _
  · apply WrapSpecialization.Rel.neg
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.constant _
    · exact WrapPole.normalized_specializes p _ _ hq hpole hnonpole

theorem dsq_specializes (q o t : ℕ) (hq : res p (q:GaussLoc p)≠0)
    (hpole : ∀ ha : res p (argument p q o t)=0,
      IsUnit (WrapPole.quotient p (argument p q o t) ha))
    (hnonpole : res p (argument p q o t)≠0 → IsUnit (argument p q o t)) :
    WrapPole.Specializes p (dsq p q o t) (originalDsq p q o t) := by
  unfold dsq originalDsq
  simp only [sub_eq_add_neg]
  apply WrapSpecialization.Rel.add
  · exact WrapSpecialization.Rel.constant _
  · apply WrapSpecialization.Rel.neg
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.constant _
    · rw [pow_two,pow_two]
      exact WrapSpecialization.Rel.mul
        (WrapPole.normalized_specializes p _ _ hq hpole hnonpole)
        (WrapPole.normalized_specializes p _ _ hq hpole hnonpole)

/-- Finite cumulative loads retain original-unit clearing denominators. -/
theorem sum_specializes {ι : Type*} (s : Finset ι)
    (f : ι → WrapDeform.Extension p) (f0 : ι → GaussLoc p)
    (h : ∀ i∈s,WrapPole.Specializes p (f i) (f0 i)) :
    WrapPole.Specializes p (∑ i∈s,f i) (∑ i∈s,f0 i) := by
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
    exact WrapSpecialization.Rel.add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end CatalanCore.Uniform.Content.UFSimple.WrapIncrement
