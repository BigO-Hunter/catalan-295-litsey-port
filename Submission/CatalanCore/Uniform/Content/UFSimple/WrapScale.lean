module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapHarmonic

@[expose] public section

open Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapScale

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Simultaneous actual frame normalization of the core and its border
leaves the reference normalization unchanged. -/
theorem reference (u : K) (hu : u≠0) (Q : Matrix ι ι K)
    (hQ : IsUnit Q.det) (sigma : ι → K) :
    1-(u • sigma) ⬝ᵥ ((u • Q)⁻¹ *ᵥ 1)=1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1) := by
  have hi : (u • Q)⁻¹=u⁻¹ • Q⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.nonsing_inv_mul Q hQ,
      smul_smul,inv_mul_cancel₀ hu,one_smul]
  rw [hi,Matrix.smul_mulVec,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ hu,one_mul]

theorem det_ne (u : K) (hu : u≠0) (Q : Matrix ι ι K) (hQ : Q.det≠0) :
    (u • Q).det≠0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hu) hQ

end CatalanCore.Uniform.Content.UFSimple.WrapScale
