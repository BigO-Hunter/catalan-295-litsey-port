module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapDeletion

@[expose] public section

/-! # Single common deletion for an actual mixed prefix core -/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapMixedDeletion

section Load
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Independent row and column coordinates in the cleared load relation. -/
theorem load_relation (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (tR tC LR LC sigma : ι → R) (Lt d : R)
    (hdisp : ∀ i j,(tC j-tR i)*Q i j=LC j-LR i)
    (hsigma : ∀ i,tR i*sigma i=LR i-Lt)
    (hdir : Lt-d=∑ j,(LC j-d)*(Q⁻¹ *ᵥ sigma) j) :
    (1-∑ j,(Q⁻¹ *ᵥ sigma) j) • (Q⁻¹ *ᵥ fun i => LR i-d)=
      fun i => tC i*(Q⁻¹ *ᵥ sigma) i := by
  let g := Q⁻¹ *ᵥ sigma
  let B := 1-∑ j,g j
  have hQg : Q *ᵥ g=sigma := by
    rw [show g=Q⁻¹ *ᵥ sigma from rfl,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  have hd : Lt-d=∑ j,LC j*g j-d*∑ j,g j := by
    calc
      _=∑ j,(LC j-d)*g j := hdir
      _=_ := by simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
  have hterm (i j : ι) : Q i j*(tC j*g j)=tR i*(Q i j*g j)+(LC j-LR i)*g j := by
    linear_combination (g j)*hdisp i j
  have hvec : Q *ᵥ (fun i => tC i*g i)=B • (fun i => LR i-d) := by
    funext i
    change (∑ j,Q i j*(tC j*g j))=B*(LR i-d)
    simp_rw [hterm]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    rw [show (∑ j,Q i j*g j)=sigma i from congrFun hQg i,hsigma i]
    simp only [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
    dsimp only [B]
    linear_combination -hd
  have hh := congrArg (fun v => Q⁻¹ *ᵥ v) hvec
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q hQ,Matrix.one_mulVec,Matrix.mulVec_smul] at hh
  exact hh.symm
end Load

section Deletion
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem residual_pairing (Q : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K)
    (R u : ι ⊕ Unit → K) (hR : ∀ i,R (Sum.inl i)=0) :
    u ⬝ᵥ (Q⁻¹ *ᵥ R)=(Qᵀ⁻¹ *ᵥ u) (Sum.inr ())*R (Sum.inr ()) := by
  rw [WrapTransport.response_transpose Q R u]
  simp only [dotProduct,Fintype.sum_sum_type,hR,zero_mul,Finset.sum_const_zero,zero_add,Fintype.sum_unique]
  exact mul_comm _ _

/-- A single common deletion preserves the mixed source moment when
its row own direction persists. The row and column loads remain independent. -/
theorem single_deletion_moment (Q : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K)
    (hQ : IsUnit Q.det) (hminor : IsUnit Q.toBlocks₁₁.det)
    (tR tC LR LC sigmaR : ι ⊕ Unit → K) (Lt d : K)
    (hdisp : ∀ i j,(tC j-tR i)*Q i j=LC j-LR i)
    (hsigma : ∀ i,tC i*sigmaR i=LC i-Lt)
    (hfull : sigmaR ⬝ᵥ (Q⁻¹ *ᵥ fun i => LR i-d)=Lt-d)
    (hdeleted : (fun i => sigmaR (Sum.inl i)) ⬝ᵥ
      (Q.toBlocks₁₁⁻¹ *ᵥ fun i => LR (Sum.inl i)-d)=Lt-d)
    (hB : 1-∑ j,(Qᵀ⁻¹ *ᵥ sigmaR) j≠0) :
    (fun i => LC i-d) ⬝ᵥ (Q⁻¹ *ᵥ fun i => LR i-d)=
      (fun i => LC (Sum.inl i)-d) ⬝ᵥ
        (Q.toBlocks₁₁⁻¹ *ᵥ fun i => LR (Sum.inl i)-d) := by
  let YR := fun i => LR i-d
  let YC := fun i => LC i-d
  let z := Q⁻¹ *ᵥ YR
  let g := Qᵀ⁻¹ *ᵥ sigmaR
  let B := 1-∑ j,g j
  let w := Sum.elim (Q.toBlocks₁₁⁻¹ *ᵥ fun i => YR (Sum.inl i)) (fun _ : Unit => 0)
  let R := YR-Q *ᵥ w
  have hsolve : Q.toBlocks₁₁ *ᵥ (Q.toBlocks₁₁⁻¹ *ᵥ fun i => YR (Sum.inl i))=
      fun i => YR (Sum.inl i) := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hminor,Matrix.one_mulVec]
  have hR : ∀ i,R (Sum.inl i)=0 := by
    intro i
    dsimp only [R,Pi.sub_apply]
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,
      mul_zero,Finset.sum_const_zero,add_zero]
    change YR (Sum.inl i)-(Q.toBlocks₁₁ *ᵥ (Q.toBlocks₁₁⁻¹ *ᵥ fun i => YR (Sum.inl i))) i=0
    rw [hsolve,sub_self]
  have hres : Q⁻¹ *ᵥ R=z-w := by
    dsimp only [R,z]
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q hQ,Matrix.one_mulVec]
  have hwSigma : sigmaR ⬝ᵥ w=(fun i => sigmaR (Sum.inl i)) ⬝ᵥ
      (Q.toBlocks₁₁⁻¹ *ᵥ fun i => YR (Sum.inl i)) := by
    simp only [dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero]
  have hzero : sigmaR ⬝ᵥ (Q⁻¹ *ᵥ R)=0 := by
    rw [hres,dotProduct_sub,hfull,hwSigma,hdeleted,sub_self]
  have hprod : g (Sum.inr ())*R (Sum.inr ())=0 :=
    (residual_pairing Q R sigmaR hR).symm.trans hzero
  have hdispT : ∀ i j,(tR j-tC i)*Qᵀ i j=LR j-LC i := by
    intro i j
    dsimp only [Matrix.transpose_apply]
    linear_combination -hdisp j i
  have hdir : Lt-d=∑ i,(LR i-d)*g i := by
    rw [← hfull,WrapTransport.response_transpose Q YR sigmaR]
    rfl
  have hQT : IsUnit Qᵀ.det := by rw [Matrix.det_transpose]; exact hQ
  have hload := load_relation Qᵀ hQT tC tR LC LR sigmaR Lt d hdispT hsigma hdir
  have hlast : B*(Qᵀ⁻¹ *ᵥ YC) (Sum.inr ())=tR (Sum.inr ())*g (Sum.inr ()) :=
    congrFun hload (Sum.inr ())
  have hmoment : YC ⬝ᵥ (Q⁻¹ *ᵥ R)=0 := by
    rw [residual_pairing Q R YC hR]
    rcases mul_eq_zero.mp hprod with hg|hr
    · have hz : (Qᵀ⁻¹ *ᵥ YC) (Sum.inr ())=0 := by
        have hh : B*(Qᵀ⁻¹ *ᵥ YC) (Sum.inr ())=0 := by rw [hlast,hg,mul_zero]
        exact (mul_eq_zero.mp hh).resolve_left hB
      rw [hz,zero_mul]
    · rw [hr,mul_zero]
  rw [hres,dotProduct_sub] at hmoment
  calc
    _=YC ⬝ᵥ w := sub_eq_zero.mp hmoment
    _=_ := by
      simp only [YC,YR,dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,mul_zero,
        Finset.sum_const_zero,add_zero]
end Deletion

end CatalanCore.Uniform.Content.UFSimple.WrapMixedDeletion
