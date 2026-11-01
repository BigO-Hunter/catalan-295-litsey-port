module

public import CatalanCore.Uniform.Content.UFSimple.WrapConstantMatrix

@[expose] public section

open Matrix Polynomial

namespace CatalanCore.Uniform.Content.UFSimple.WrapArrowCore

variable {R ι κ : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Cleared reference arrow over the integral original or parameter ring. -/
def arrow (Q : Matrix ι ι R) (sigma : ι → R) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks Q (Matrix.of fun _ _ => 1) (Matrix.of fun _ j => sigma j) (1:Matrix Unit Unit R)

theorem det_arrow (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (sigma : ι → R) :
    (arrow Q sigma).det=Q.det*(1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1)) := by
  letI : Invertible Q := Matrix.invertibleOfIsUnitDet Q hQ
  unfold arrow
  rw [Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,Matrix.det_unique (n:=Unit)]
  simp only [Matrix.sub_apply,Matrix.one_apply_eq,Matrix.mul_apply,Matrix.of_apply,
    Matrix.mulVec,dotProduct,Pi.one_apply,mul_one,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Regroup the original common nodes before appending the cleared
balanced reference. This is an exact simultaneous row/column permutation. -/
theorem regroup (A : Matrix ι ι R) (B : Matrix ι κ R) (E : Matrix κ ι R)
    (D : Matrix κ κ R) (sigmaC : ι → R) (sigmaB : κ → R) :
    Matrix.reindex (Equiv.sumAssoc ι κ Unit) (Equiv.sumAssoc ι κ Unit)
      (arrow (Matrix.fromBlocks A B E D) (Sum.elim sigmaC sigmaB))=
        Matrix.fromBlocks A
          (Matrix.of fun i j => Sum.elim (fun j => B i j) (fun _ : Unit => 1) j)
          (Matrix.of fun i j => Sum.elim (fun i => E i j) (fun _ : Unit => sigmaC j) i)
          (arrow D sigmaB) := by
  apply Matrix.ext; intro i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · rcases j with j|j <;> rfl
  · rcases i with i|i <;> rfl
  · rcases i with i|i <;> rcases j with j|j <;> rfl

variable {K : Type*} [Field K]

/-- The actual mixed spectral reference numerator is nonzero from the
balanced reference and constant prime-field residues alone. -/
theorem spectral_ne (A : Matrix ι ι (RatFunc K)) (B : Matrix ι κ (RatFunc K))
    (E : Matrix κ ι (RatFunc K)) (D : Matrix κ κ (RatFunc K))
    (sigmaC : ι → RatFunc K) (sigmaB : κ → RatFunc K)
    (hA : ∀ i j,∃ a:K,A i j=RatFunc.C a)
    (hB : ∀ i j,∃ a:K,B i j=RatFunc.C a)
    (hE : ∀ i j,∃ a:K,E i j=RatFunc.C a)
    (hDc : ∀ i j,∃ a:K,D i j=RatFunc.C a)
    (hSC : ∀ i,∃ a:K,sigmaC i=RatFunc.C a)
    (hSB : ∀ i,∃ a:K,sigmaB i=RatFunc.C a)
    (hD : D.det≠0) (href : 1-sigmaB ⬝ᵥ (D⁻¹ *ᵥ 1)≠0) :
    (arrow (Matrix.fromBlocks ((RatFunc.X:RatFunc K) • (1:Matrix ι ι (RatFunc K))+A) B E D)
      (Sum.elim sigmaC sigmaB)).det≠0 := by
  rw [← Matrix.det_reindex_self (Equiv.sumAssoc ι κ Unit),regroup]
  apply WrapConstantMatrix.spectral_det_ne
  · exact hA
  · intro i j
    rcases j with j|j
    · exact hB i j
    · exact ⟨1,(map_one RatFunc.C).symm⟩
  · intro i j
    rcases i with i|i
    · exact hE i j
    · exact hSC j
  · intro i j
    rcases i with i|i <;> rcases j with j|j
    · exact hDc i j
    · exact ⟨1,(map_one RatFunc.C).symm⟩
    · exact hSB j
    · exact ⟨1,by simp [arrow]⟩
  · rw [det_arrow D (isUnit_iff_ne_zero.mpr hD) sigmaB]
    exact mul_ne_zero hD href

end CatalanCore.Uniform.Content.UFSimple.WrapArrowCore
