module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapParameter

@[expose] public section

/-! # Residue lifts in the generic pole-parameter ring -/

open Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapParameterLift

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- The original prime remains prime in the generic parameter ring. -/
theorem uniformizer_prime (phi : R →+* K) (pi : R)
    (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi) :
    Prime (WrapParameter.uniformizer phi pi) := by
  have hinj : Function.Injective (algebraMap R[X] (WrapParameter.Extension phi)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors (WrapParameter.primeIdeal phi))
  have hne : WrapParameter.uniformizer phi pi≠0 := by
    intro hz
    apply (Polynomial.C_ne_zero.mpr hpi.ne_zero)
    apply hinj
    change algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C pi)=0 at hz
    simpa only [map_zero] using hz
  have hz : WrapParameter.residue phi (WrapParameter.uniformizer phi pi)=0 :=
    (WrapParameter.residue_zero_iff phi pi hker _).mpr (dvd_refl _)
  refine ⟨hne,?_,?_⟩
  · intro hu
    have hh := hu.map (WrapParameter.residue phi)
    rw [hz] at hh
    exact not_isUnit_zero hh
  · intro a b hab
    have hh := (WrapParameter.residue_zero_iff phi pi hker (a*b)).mpr hab
    rw [map_mul] at hh
    rcases mul_eq_zero.mp hh with ha|hb
    · exact Or.inl ((WrapParameter.residue_zero_iff phi pi hker a).mp ha)
    · exact Or.inr ((WrapParameter.residue_zero_iff phi pi hker b).mp hb)

/-- A surjective original coefficient residue gives a surjective generic
residue. These lifts support the existing Smith rank machinery. -/
theorem residue_surjective (phi : R →+* K) (hphi : Function.Surjective phi) :
    Function.Surjective (WrapParameter.residue phi) := by
  intro z
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective (A:=K[X]) z
  obtain ⟨a',ha⟩ := Polynomial.map_surjective phi hphi a
  obtain ⟨b',hb'⟩ := Polynomial.map_surjective phi hphi b
  have hne : algebraMap K[X] (RatFunc K) b≠0 := by
    intro hz
    apply nonZeroDivisors.ne_zero hb
    apply IsFractionRing.injective K[X] (RatFunc K)
    simpa only [map_zero] using hz
  have hbpoly : WrapParameter.polyResidue phi b'≠0 := by
    change algebraMap K[X] (RatFunc K) (b'.map phi)≠0
    rw [hb']
    exact hne
  let eb := algebraMap R[X] (WrapParameter.Extension phi) b'
  let ea := algebraMap R[X] (WrapParameter.Extension phi) a'
  have hu : IsUnit eb := WrapParameter.unit_of_poly_ne phi hbpoly
  have hresb : WrapParameter.residue phi eb=algebraMap K[X] (RatFunc K) b := by
    rw [WrapParameter.residue_map]
    change algebraMap K[X] (RatFunc K) (b'.map phi)=_
    rw [hb']
  have hresa : WrapParameter.residue phi ea=algebraMap K[X] (RatFunc K) a := by
    rw [WrapParameter.residue_map]
    change algebraMap K[X] (RatFunc K) (a'.map phi)=_
    rw [ha]
  have hunit : WrapParameter.residue phi eb≠0 := by rw [hresb]; exact hne
  have hinv : WrapParameter.residue phi (Ring.inverse eb)=(WrapParameter.residue phi eb)⁻¹ := by
    apply mul_left_cancel₀ hunit
    rw [← map_mul,Ring.mul_inverse_cancel _ hu,map_one,mul_inv_cancel₀ hunit]
  refine ⟨ea*Ring.inverse eb,?_⟩
  rw [map_mul,hinv,hresa,hresb,← div_eq_mul_inv]

/-- The quotient-lift hypothesis expected by the Smith determinant
lemmas follows with clearing denominator one in the parameter ring. -/
theorem quotient_lift (phi : R →+* K) (hphi : Function.Surjective phi) (z : RatFunc K) :
    ∃ r d : WrapParameter.Extension phi,WrapParameter.residue phi d≠0 ∧
      WrapParameter.residue phi r=WrapParameter.residue phi d*z := by
  obtain ⟨r,hr⟩ := residue_surjective phi hphi z
  refine ⟨r,1,by simp,?_⟩
  simpa only [map_one,one_mul] using hr

end CatalanCore.Uniform.Content.UFSimple.WrapParameterLift
