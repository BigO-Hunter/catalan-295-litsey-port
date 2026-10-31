module

public import CatalanCore.Uniform.Content.UFSimple.WrapPole
public import CatalanCore.Uniform.Content.UFSimple.WrapEvaluation
public import CatalanCore.Uniform.Content.UFMoments.NodeLoc

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Elementary deformed pole factors at a prefix test point -/

open Polynomial CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPoleTest

variable (p : ℕ) [Fact p.Prime]

noncomputable def At :=
  WrapEvaluation.Rel (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)

open Classical in
noncomputable def value (a b point : GaussLoc p) : GaussLoc p :=
  if ha : res p a=0 then Ring.inverse (WrapPole.quotient p a ha+b*point)
  else piL p*Ring.inverse (a+piL p*b*point)

theorem nonpole_unit (a b point : GaussLoc p) (ha : res p a≠0) :
    IsUnit (a+piL p*b*point) := by
  apply isUnit_of_res_ne
  simpa only [map_add,map_mul,res_piL,zero_mul,add_zero] using ha

/-- The only test-point unit required is an elementary pole denominator. -/
theorem normalized_at (a b point : GaussLoc p) (hb : res p b≠0)
    (hpole : ∀ ha : res p a=0,IsUnit (WrapPole.quotient p a ha+b*point)) :
    At p point (WrapPole.normalizedInverse p a b) (value p a b point) := by
  classical
  unfold At WrapEvaluation.Rel
  by_cases ha : res p a=0
  · rw [WrapPole.normalizedInverse,dif_pos ha,value,dif_pos ha]
    refine ⟨1,Polynomial.C (WrapPole.quotient p a ha)+Polynomial.C b*Polynomial.X,?_,?_,?_⟩
    · simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X] using hpole ha
    · rw [map_one]
      change WrapPole.affine p (WrapPole.quotient p a ha) b*
        Ring.inverse (WrapPole.affine p (WrapPole.quotient p a ha) b)=1
      exact Ring.mul_inverse_cancel _ (WrapPole.affine_unit p _ b hb)
    · simp only [Polynomial.eval_one,Polynomial.eval_add,Polynomial.eval_C,
        Polynomial.eval_mul,Polynomial.eval_X]
      exact (Ring.mul_inverse_cancel _ (hpole ha)).symm
  · rw [WrapPole.normalizedInverse,dif_neg ha,value,dif_neg ha]
    refine ⟨Polynomial.C (piL p),
      Polynomial.C a+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X,?_,?_,?_⟩
    · simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X] using nonpole_unit p a b point ha
    · change WrapPole.denominator p a b*
        (WrapDeform.uniformizer p*Ring.inverse (WrapPole.denominator p a b))=
        WrapDeform.uniformizer p
      calc
        _=WrapDeform.uniformizer p*(WrapPole.denominator p a b*
          Ring.inverse (WrapPole.denominator p a b)) := by ring
        _=_ := by rw [Ring.mul_inverse_cancel _ (WrapPole.denominator_unit p a b ha),mul_one]
    · simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
      calc
        piL p=piL p*((a+piL p*b*point)*Ring.inverse (a+piL p*b*point)) := by
          rw [Ring.mul_inverse_cancel _ (nonpole_unit p a b point ha),mul_one]
        _=(a+piL p*b*point)*(piL p*Ring.inverse (a+piL p*b*point)) := by ring

end CatalanCore.Uniform.Content.UFSimple.WrapPoleTest
