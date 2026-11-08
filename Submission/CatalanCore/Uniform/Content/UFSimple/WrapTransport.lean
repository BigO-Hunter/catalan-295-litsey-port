module

public import Submission.CatalanCore.Uniform.Content.UFMoments.Own

@[expose] public section

/-! # Bilinear transport in actual mixed coordinates

Independent row and column relabellings swap their roles in the inverse.
Transposition swaps the two loads; symmetry of the core is unnecessary.
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapTransport

variable {R ι τ : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

/-- Bilinear inverse response under independent row and column equivalences. -/
theorem response_reindex (Q : Matrix ι ι R) (er ec : τ ≃ ι) (uR uC : ι → R) :
    (uC ∘ ec) ⬝ᵥ (Q.submatrix er ec)⁻¹ *ᵥ (uR ∘ er) =
      uC ⬝ᵥ Q⁻¹ *ᵥ uR := by
  rw [Matrix.inv_submatrix_equiv]
  simp only [dotProduct, mulVec, Matrix.submatrix_apply, Function.comp_def]
  have hr : ∀ i : τ, (∑ j : τ, Q⁻¹ (ec i) (er j) * uR (er j)) =
      ∑ j : ι, Q⁻¹ (ec i) j * uR j := fun i => Equiv.sum_comp er (fun j : ι => Q⁻¹ (ec i) j * uR j)
  simp_rw [hr]
  exact Equiv.sum_comp ec (fun i : ι => uC i * ∑ j : ι, Q⁻¹ i j * uR j)

/-- Transposition exchanges row and column loads in a mixed response. -/
theorem response_transpose (Q : Matrix ι ι R) (uR uC : ι → R) :
    uC ⬝ᵥ Q⁻¹ *ᵥ uR = uR ⬝ᵥ Qᵀ⁻¹ *ᵥ uC := by
  rw [← Matrix.transpose_nonsing_inv]
  simp only [dotProduct, mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end CatalanCore.Uniform.Content.UFSimple.WrapTransport
