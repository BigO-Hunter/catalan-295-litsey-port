module

public import CatalanCore.Uniform.Content.UFSimple.WrapDeform
public import CatalanCore.Uniform.Content.UFSimple.WrapSpecialization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Integral normalized reciprocals of the actual deformed pole factors -/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPole

variable (p : ℕ) [Fact p.Prime]

noncomputable def affine (a b : GaussLoc p) : WrapDeform.Extension p :=
  WrapDeform.embed p (Polynomial.C a+Polynomial.C b*Polynomial.X)

theorem affine_unit (a b : GaussLoc p) (hb : res p b≠0) : IsUnit (affine p a b) := by
  apply WrapParameter.unit_of_poly_ne (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
  change (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p))))
    ((Polynomial.C a+Polynomial.C b*Polynomial.X).map (res p))≠0
  rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,Polynomial.map_X]
  intro h
  apply hb
  have hinj : Function.Injective
      (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))) := IsFractionRing.injective _ _
  have hh : (Polynomial.C (res p a)+Polynomial.C (res p b)*Polynomial.X:(RatFunc (ZMod p))[X])=0 := by
    apply hinj
    rw [map_zero]
    exact h
  simpa using congrArg (fun f : (RatFunc (ZMod p))[X] => f.coeff 1) hh

noncomputable def denominator (a b : GaussLoc p) : WrapDeform.Extension p :=
  WrapDeform.embed p (Polynomial.C a+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X)

theorem denominator_unit (a b : GaussLoc p) (ha : res p a≠0) : IsUnit (denominator p a b) := by
  apply WrapParameter.unit_of_poly_ne (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
  change (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p))))
    ((Polynomial.C a+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X).map (res p))≠0
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,res_piL,
    Polynomial.C_0,zero_mul,add_zero]
  intro h
  apply ha
  have hinj : Function.Injective
      (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))) := IsFractionRing.injective _ _
  have hh : (Polynomial.C (res p a):(RatFunc (ZMod p))[X])=0 := by
    apply hinj
    rw [map_zero]
    exact h
  simpa using congrArg (fun f : (RatFunc (ZMod p))[X] => f.coeff 0) hh

noncomputable def quotient (a : GaussLoc p) (ha : res p a=0) : GaussLoc p :=
  Classical.choose ((res_eq_zero_iff p a).mp ha)

theorem quotient_spec (a : GaussLoc p) (ha : res p a=0) : a=piL p*quotient p a ha :=
  Classical.choose_spec ((res_eq_zero_iff p a).mp ha)

theorem denominator_factor (a b : GaussLoc p) (ha : res p a=0) :
    denominator p a b=WrapDeform.uniformizer p*affine p (quotient p a ha) b := by
  have hf : Polynomial.C a+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X=
      Polynomial.C (piL p)*(Polynomial.C (quotient p a ha)+Polynomial.C b*Polynomial.X) := by
    calc
      _=Polynomial.C (piL p*quotient p a ha)+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X :=
        congrArg (fun z : GaussLoc p => Polynomial.C z+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X)
          (quotient_spec p a ha)
      _=_ := by rw [map_mul]; ring
  change WrapDeform.embed p _=WrapDeform.embed p (Polynomial.C (piL p))*WrapDeform.embed p _
  rw [← (WrapDeform.embed p).map_mul,hf]

open Classical in
/-- pi divided by the deformed denominator, expressed integrally. -/
noncomputable def normalizedInverse (a b : GaussLoc p) : WrapDeform.Extension p :=
  if ha : res p a=0 then Ring.inverse (affine p (quotient p a ha) b)
  else WrapDeform.uniformizer p*Ring.inverse (denominator p a b)

/-- The normalized reciprocal identity uses only the original residue
case and a nonzero slope, with no specialization of an inverse pivot. -/
theorem denominator_mul_normalized (a b : GaussLoc p) (hb : res p b≠0) :
    denominator p a b*normalizedInverse p a b=WrapDeform.uniformizer p := by
  classical
  by_cases ha : res p a=0
  · rw [normalizedInverse,dif_pos ha,denominator_factor p a b ha,mul_assoc,
      Ring.mul_inverse_cancel _ (affine_unit p _ b hb),mul_one]
  · rw [normalizedInverse,dif_neg ha]
    calc
      _=WrapDeform.uniformizer p*(denominator p a b*Ring.inverse (denominator p a b)) := by ring
      _=_ := by rw [Ring.mul_inverse_cancel _ (denominator_unit p a b ha),mul_one]

/-- Squaring yields the integral normalization for the derivative load. -/
theorem denominator_sq_mul_normalized_sq (a b : GaussLoc p) (hb : res p b≠0) :
    denominator p a b^2*normalizedInverse p a b^2=WrapDeform.uniformizer p^2 := by
  rw [← mul_pow,denominator_mul_normalized p a b hb]

theorem normalized_nonpole_residue (a b : GaussLoc p) (ha : res p a≠0) :
    WrapDeform.residue p (normalizedInverse p a b)=0 := by
  classical
  rw [normalizedInverse,dif_neg ha,map_mul]
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  rw [hp,zero_mul]

open Classical in
noncomputable def originalNormalized (a : GaussLoc p) : GaussLoc p :=
  if ha : res p a=0 then Ring.inverse (quotient p a ha)
  else piL p*Ring.inverse a

noncomputable def Specializes :=
  WrapSpecialization.Rel (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)

/-- Elementary normalized pole reciprocals have original unit clearing
denominators whenever the original pole is simple. -/
theorem normalized_specializes (a b : GaussLoc p) (hb : res p b≠0)
    (hpole : ∀ ha : res p a=0,IsUnit (quotient p a ha))
    (hnonpole : res p a≠0 → IsUnit a) :
    Specializes p (normalizedInverse p a b) (originalNormalized p a) := by
  classical
  unfold Specializes WrapSpecialization.Rel
  by_cases ha : res p a=0
  · rw [normalizedInverse,dif_pos ha,originalNormalized,dif_pos ha]
    refine ⟨1,Polynomial.C (quotient p a ha)+Polynomial.C b*Polynomial.X,?_,?_,?_⟩
    · simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X,mul_zero,add_zero] using hpole ha
    · rw [map_one]
      change affine p (quotient p a ha) b*Ring.inverse (affine p (quotient p a ha) b)=1
      exact Ring.mul_inverse_cancel _ (affine_unit p _ b hb)
    · simp only [Polynomial.eval_one,Polynomial.eval_add,Polynomial.eval_C,
        Polynomial.eval_mul,Polynomial.eval_X,mul_zero,add_zero]
      exact (Ring.mul_inverse_cancel _ (hpole ha)).symm
  · rw [normalizedInverse,dif_neg ha,originalNormalized,dif_neg ha]
    refine ⟨Polynomial.C (piL p),
      Polynomial.C a+Polynomial.C (piL p)*Polynomial.C b*Polynomial.X,?_,?_,?_⟩
    · simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X,mul_zero,add_zero] using hnonpole ha
    · change denominator p a b*(WrapDeform.uniformizer p*Ring.inverse (denominator p a b))=
        WrapDeform.uniformizer p
      calc
        _=WrapDeform.uniformizer p*(denominator p a b*Ring.inverse (denominator p a b)) := by ring
        _=_ := by rw [Ring.mul_inverse_cancel _ (denominator_unit p a b ha),mul_one]
    · simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
        Polynomial.eval_X,mul_zero,add_zero]
      calc
        piL p=piL p*(a*Ring.inverse a) := by rw [Ring.mul_inverse_cancel _ (hnonpole ha),mul_one]
        _=a*(piL p*Ring.inverse a) := by ring

end CatalanCore.Uniform.Content.UFSimple.WrapPole
