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


noncomputable def residue_zero_iff :=
  WrapParameter.residue_zero_iff (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p) (piL p) (res_eq_zero_iff p)


end CatalanCore.Uniform.Content.UFSimple.WrapDeform
