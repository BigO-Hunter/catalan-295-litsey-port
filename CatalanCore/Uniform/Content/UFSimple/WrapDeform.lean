module

public import CatalanCore.Uniform.Content.UFSimple.WrapParameter
public import CatalanCore.Uniform.Content.UFMoments.Local

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual original Gauss ring with one generic pole parameter -/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapDeform

variable (p : ℕ) [Fact p.Prime]

abbrev Extension := WrapParameter.Extension (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)

noncomputable def embed : (GaussLoc p)[X] →+* Extension p := algebraMap _ _
noncomputable def residue := WrapParameter.residue (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
noncomputable def uniformizer := WrapParameter.uniformizer (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p) (piL p)

/-- The original uniformizer remains prime before adjoining the parameter. -/
theorem pi_prime : Prime (piL p) := by
  have hpi : piL p≠0 := by
    intro h
    have hh := algebraMap_injective p (h.trans (map_zero _).symm)
    exact (Polynomial.prime_C_iff.2 (prime_p p)).ne_zero hh
  refine ⟨hpi,?_,?_⟩
  · intro hu
    have hh := hu.map (res p)
    rw [res_piL] at hh
    exact not_isUnit_zero hh
  · intro a b hab
    have hh : res p a*res p b=0 := by
      rw [← map_mul,res_eq_zero_iff]
      exact hab
    rcases mul_eq_zero.mp hh with ha|hb
    · exact Or.inl ((res_eq_zero_iff p a).mp ha)
    · exact Or.inr ((res_eq_zero_iff p b).mp hb)

-- Proof aliases retain the exact localization instances of the generic statements.
noncomputable def residue_map :=
  WrapParameter.residue_map (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)

noncomputable def residue_zero_iff :=
  WrapParameter.residue_zero_iff (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p) (piL p) (res_eq_zero_iff p)

/-- A shifted pole quotient is a unit as a generic polynomial, including
when the quotient at the original parameter value would vanish. -/
noncomputable def linear (a : GaussLoc p) : Extension p := embed p (Polynomial.X+Polynomial.C a)

theorem linear_unit (a : GaussLoc p) : IsUnit (linear p a) := by
  apply WrapParameter.unit_of_poly_ne (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
  change (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p))))
    ((Polynomial.X+Polynomial.C a).map (res p))≠0
  rw [Polynomial.map_add,Polynomial.map_X,Polynomial.map_C]
  intro h
  have hinj : Function.Injective
      (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))) := IsFractionRing.injective _ _
  have hh : (Polynomial.X+Polynomial.C (res p a):(RatFunc (ZMod p))[X])=0 := by
    apply hinj
    rw [map_zero]
    exact h
  have hc := congrArg (fun z : (RatFunc (ZMod p))[X] => z.coeff 1) hh
  simpa using hc

theorem linear_residue (a : GaussLoc p) :
    residue p (linear p a)=
      algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))
        (Polynomial.X+Polynomial.C (res p a)) := by
  unfold linear residue embed
  erw [WrapParameter.residue_map]
  change (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p))))
    ((Polynomial.X+Polynomial.C a).map (res p))=_
  rw [Polynomial.map_add,Polynomial.map_X,Polynomial.map_C]

/-- An original nonpole denominator remains a unit after adding pi times
the parameter. This uses only the original nonzero residue. -/
theorem nonpole_unit (a : GaussLoc p) (ha : res p a≠0) :
    IsUnit (embed p (Polynomial.C a+Polynomial.C (piL p)*Polynomial.X)) := by
  apply WrapParameter.unit_of_poly_ne (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
  change (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p))))
    ((Polynomial.C a+Polynomial.C (piL p)*Polynomial.X).map (res p))≠0
  rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,Polynomial.map_X,res_piL]
  simp only [Polynomial.C_0,zero_mul,add_zero]
  intro h
  apply ha
  have hinj : Function.Injective
      (algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))) := IsFractionRing.injective _ _
  have hh : (Polynomial.C (res p a):(RatFunc (ZMod p))[X])=0 := by
    apply hinj
    rw [map_zero]
    exact h
  simpa using congrArg (fun z : (RatFunc (ZMod p))[X] => z.coeff 0) hh

noncomputable def inverseLinear (a : GaussLoc p) : Extension p := Ring.inverse (linear p a)

theorem linear_inverse (a : GaussLoc p) : linear p a*inverseLinear p a=1 :=
  Ring.mul_inverse_cancel _ (linear_unit p a)

theorem inverseLinear_residue (a : GaussLoc p) :
    residue p (inverseLinear p a)=(residue p (linear p a))⁻¹ := by
  have hu : residue p (linear p a)≠0 := ((linear_unit p a).map (residue p)).ne_zero
  have hm := congrArg (residue p) (linear_inverse p a)
  rw [map_mul,map_one] at hm
  apply mul_left_cancel₀ hu
  rw [hm,mul_inv_cancel₀ hu]

/-- Final descent at the original pole parameter, with the original
clearing denominator as the only specialization unit hypothesis. -/
noncomputable def specialize_zero :=
  WrapParameter.specialize_zero (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p) (piL p)
    (res_eq_zero_iff p) (pi_prime p)

end CatalanCore.Uniform.Content.UFSimple.WrapDeform
