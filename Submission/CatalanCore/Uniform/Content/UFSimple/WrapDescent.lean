module

public import Mathlib.RingTheory.Localization.Basic
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapAlgebra

@[expose] public section

/-! # Descent and specialization of deformed member determinants

Generic pivot matrices are never specialized. First descend the scalar
prime-power divisibility from the Gauss localization, then specialize the
original cleared determinant using its unit denominator.
-/

namespace CatalanCore.Uniform.Content.UFSimple.WrapDescent

variable {R A B : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- A prime-power divisibility in a localization away from that prime
already holds in the original domain. -/
theorem dvd_of_local (S : Submonoid R) [IsLocalization S A]
    (pi : R) (hpi : Prime pi) (hS : ∀ s ∈ S, ¬ pi ∣ s)
    (g : R) (k : ℕ) (x : A)
    (h : algebraMap R A g = algebraMap R A pi ^ k * x) : pi ^ k ∣ g := by
  have hnonzero : S ≤ nonZeroDivisors R := by
    intro s hs
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro hz
    apply hS s hs
    rw [hz]
    exact dvd_zero pi
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hnonzero
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  rw [← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.eq_mk'_iff_mul_eq, ← map_mul] at h
  have h2 := hinj h
  exact hpi.pow_dvd_of_dvd_mul_right k (hS s s.2) ⟨b, h2⟩


end CatalanCore.Uniform.Content.UFSimple.WrapDescent
