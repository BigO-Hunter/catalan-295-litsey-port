module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapParameter

@[expose] public section

open Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapUnits

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- A generic parameter-ring element is a unit as soon as its actual
residue is nonzero. -/
theorem of_residue_ne (phi : R →+* K) (x : WrapParameter.Extension phi)
    (hx : WrapParameter.residue phi x≠0) : IsUnit x := by
  obtain ⟨⟨a,s⟩,rfl⟩ := IsLocalization.mk'_surjective (WrapParameter.primeIdeal phi).primeCompl x
  dsimp only at hx ⊢
  have ha : WrapParameter.polyResidue phi a≠0 := by
    intro hz
    apply hx
    exact (IsLocalization.lift_mk'_spec
      (M:=(WrapParameter.primeIdeal phi).primeCompl) (S:=WrapParameter.Extension phi)
      _ _ _ _).2 (by rw [hz,mul_zero])
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  refine (WrapParameter.unit_of_poly_ne phi ha).mul (IsUnit.of_mul_eq_one
    (algebraMap R[X] (WrapParameter.Extension phi) s) ?_)
  rw [IsLocalization.mk'_spec,map_one]

end CatalanCore.Uniform.Content.UFSimple.WrapUnits
