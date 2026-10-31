module

public import CatalanCore.Uniform.Content.UFSimple.WrapDescent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

/-! # One generic pole parameter over the original Gauss ring

Localize away from coefficientwise residue zero. The original spectral
variable remains in the coefficient ring. Only cleared scalar determinants
are descended and specialized; generic inverse pivots are never specialized.
-/

open Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapParameter

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

noncomputable def polyResidue (phi : R →+* K) : R[X] →+* RatFunc K :=
  (algebraMap K[X] (RatFunc K)).comp (Polynomial.mapRingHom phi)

noncomputable def primeIdeal (phi : R →+* K) : Ideal R[X] := RingHom.ker (polyResidue phi)

instance primeIdeal_isPrime (phi : R →+* K) : (primeIdeal phi).IsPrime :=
  RingHom.ker_isPrime (polyResidue phi)

abbrev Extension (phi : R →+* K) := Localization.AtPrime (primeIdeal phi)

lemma mem_compl (phi : R →+* K) (f : R[X]) :
    f∈(primeIdeal phi).primeCompl ↔ polyResidue phi f≠0 := by
  change f∉primeIdeal phi ↔ _
  rw [primeIdeal,RingHom.mem_ker]

noncomputable def residue (phi : R →+* K) : Extension phi →+* RatFunc K :=
  IsLocalization.lift (M := (primeIdeal phi).primeCompl) (S := Extension phi) (g := polyResidue phi)
    (fun s => isUnit_iff_ne_zero.mpr ((mem_compl phi s).mp s.2))

lemma residue_map (phi : R →+* K) (f : R[X]) :
    residue phi (algebraMap R[X] (Extension phi) f)=polyResidue phi f :=
  IsLocalization.lift_eq _ _

lemma poly_zero_iff (phi : R →+* K) (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (f : R[X]) :
    polyResidue phi f=0 ↔ Polynomial.C pi∣f := by
  constructor
  · intro h
    have hinj : Function.Injective (algebraMap K[X] (RatFunc K)) := IsFractionRing.injective _ _
    change (algebraMap K[X] (RatFunc K)) (f.map phi)=0 at h
    have hm : f.map phi=0 := by
      apply hinj
      rw [map_zero]
      exact h
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply (hker _).mp
    have hh := congrArg (fun z : K[X] => z.coeff i) hm
    simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using hh
  · rintro ⟨g,rfl⟩
    have hp : phi pi=0 := (hker pi).mpr (dvd_refl pi)
    change (algebraMap K[X] (RatFunc K)) ((Polynomial.C pi*g).map phi)=0
    simp only [Polynomial.map_mul,Polynomial.map_C,hp,Polynomial.C_0,zero_mul,map_zero]

noncomputable def uniformizer (phi : R →+* K) (pi : R) : Extension phi :=
  algebraMap R[X] (Extension phi) (Polynomial.C pi)

/-- The parameter extension has precisely the same uniformizer. -/
theorem residue_zero_iff (phi : R →+* K) (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a)
    (x : Extension phi) : residue phi x=0 ↔ uniformizer phi pi∣x := by
  constructor
  · intro h
    obtain ⟨⟨a,s⟩,rfl⟩ := IsLocalization.mk'_surjective (primeIdeal phi).primeCompl x
    have hh : polyResidue phi a=polyResidue phi s*0 :=
      (IsLocalization.lift_mk'_spec (M := (primeIdeal phi).primeCompl) (S := Extension phi) _ _ _ _).1 h
    rw [mul_zero,poly_zero_iff phi pi hker] at hh
    obtain ⟨b,rfl⟩ := hh
    exact ⟨IsLocalization.mk' (Extension phi) b s,
      (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm⟩
  · rintro ⟨y,rfl⟩
    have hp : residue phi (uniformizer phi pi)=0 := by
      rw [uniformizer,residue_map,poly_zero_iff phi pi hker]
    rw [map_mul,hp,zero_mul]

/-- Generic pivot denominators are inverted only when their polynomial
residue is nonzero; they need not survive specialization. -/
theorem unit_of_poly_ne (phi : R →+* K) {f : R[X]} (hf : polyResidue phi f≠0) :
    IsUnit (algebraMap R[X] (Extension phi) f) :=
  IsLocalization.map_units (Extension phi) (⟨f,(mem_compl phi f).mpr hf⟩ : (primeIdeal phi).primeCompl)

/-- Descend divisibility of the original cleared scalar polynomial. -/
theorem descend (phi : R →+* K) (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (f : R[X]) (k : ℕ) (x : Extension phi)
    (h : algebraMap R[X] (Extension phi) f=uniformizer phi pi^k*x) :
    Polynomial.C pi^k∣f := by
  apply WrapDescent.dvd_of_local (primeIdeal phi).primeCompl (Polynomial.C pi)
    (Polynomial.prime_C_iff.mpr hpi) _ f k x h
  intro s hs hd
  exact (mem_compl phi s).mp hs ((poly_zero_iff phi pi hker s).mpr hd)

/-- Specialize only after descent. The ORIGINAL clearing denominator is
the sole unit required at the original parameter value. -/
theorem specialize_zero (phi : R →+* K) (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (D f : R[X]) (k : ℕ) (x : Extension phi)
    (h : algebraMap R[X] (Extension phi) (D*f)=uniformizer phi pi^k*x)
    (hD : IsUnit (D.eval 0)) : pi^k∣f.eval 0 := by
  have hd := descend phi pi hker hpi (D*f) k x h
  have hh := WrapAlgebra.specialize_cleared (Polynomial.evalRingHom (0:R))
    (Polynomial.C pi^k) D f hd hD
  simpa only [Polynomial.coe_evalRingHom,Polynomial.eval_pow,Polynomial.eval_C] using hh

end CatalanCore.Uniform.Content.UFSimple.WrapParameter
