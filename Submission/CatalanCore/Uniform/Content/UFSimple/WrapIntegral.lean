module

public import Submission.CatalanCore.Uniform.Content.UFMember.JBlock
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapCount
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-! # Integral Smith content for deformed mixed prefix cores -/

open Matrix Finset
open CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFSimple.WrapIntegral

variable {R K ι κ : Type*} [CommRing R] [IsDomain R] [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reuse the existing two-level Smith minor theorem in the parameter
ring. No frame-specific witness or new Smith-form implementation is needed. -/
theorem two_level_content (phi : R →+* K) (pi : R) (hpi : Prime pi)
    (hker : ∀ x,phi x=0 ↔ pi∣x)
    (hlift : ∀ z : K,∃ r d : R,phi d≠0 ∧ phi r=phi d*z)
    (W : Matrix κ κ R) (a b : ℕ) (T : TwoLevelData phi pi W a b) :
    pi^(a+(a-b))∣W.det := by
  have hh := two_level_dvd_det_submatrix phi hpi hker hlift W T.L₂ T.P₂
    T.hL₂ T.hP₂ T.s T.hrow T.hcol T.N₂ T.hN₂ b T.hb
    (id:κ→κ) (id:κ→κ) Function.injective_id Function.injective_id
  simpa only [Nat.add_sub_cancel,Matrix.submatrix_id_id,T.hcard] using hh

/-- Eliminating an invertible actual mixed core and a divided border
Schur block gives the full scalar content needed before specialization. -/
theorem block_content (phi : R →+* K) (pi : R) (hpi : Prime pi)
    (hker : ∀ x,phi x=0 ↔ pi∣x)
    (hlift : ∀ z : K,∃ r d : R,phi d≠0 ∧ phi r=phi d*z)
    (Q : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D W : Matrix κ κ R)
    (hQ : IsUnit Q.det) (hSch : D-C*Q⁻¹*B=pi • W)
    (a b : ℕ) (T : TwoLevelData phi pi W a b) :
    pi^(Fintype.card κ+(a+(a-b)))∣(Matrix.fromBlocks Q B C D).det := by
  letI : Invertible Q := Matrix.invertibleOfIsUnitDet Q hQ
  have he : (Matrix.fromBlocks Q B C D).det=Q.det*(pi^Fintype.card κ*W.det) := by
    rw [Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,hSch,Matrix.det_smul]
  obtain ⟨x,hx⟩ := two_level_content phi pi hpi hker hlift W a b T
  refine ⟨Q.det*x,?_⟩
  rw [he,hx,pow_add]
  ring


end CatalanCore.Uniform.Content.UFSimple.WrapIntegral
