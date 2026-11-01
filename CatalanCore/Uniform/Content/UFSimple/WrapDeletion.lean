module

public import Mathlib.Tactic.LinearCombination
public import CatalanCore.Uniform.Content.UFSimple.WrapAlgebra
public import CatalanCore.Uniform.Content.UFSimple.WrapTransport

@[expose] public section

/-! # Single common deletion and the own-direction response -/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapDeletion

section Load

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Cleared own-load relation from the Loewner displacement and the
representative direction. No division by the direction denominator is used. -/
theorem loewner_load_relation (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (t L sigma : ι → R) (Lt d : R)
    (hdisp : ∀ i j,(t j-t i)*Q i j=L j-L i)
    (hsigma : ∀ i,t i*sigma i=L i-Lt)
    (hdir : Lt-d=∑ j,(L j-d)*(Q⁻¹ *ᵥ sigma) j) :
    (1-∑ j,(Q⁻¹ *ᵥ sigma) j) • (Q⁻¹ *ᵥ fun i => L i-d)=
      fun i => t i*(Q⁻¹ *ᵥ sigma) i := by
  let g := Q⁻¹ *ᵥ sigma
  let B := 1-∑ j,g j
  have hQg : Q *ᵥ g=sigma := by
    rw [show g=Q⁻¹ *ᵥ sigma from rfl,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  have hd : Lt-d=∑ j,L j*g j-d*∑ j,g j := by
    calc
      _=∑ j,(L j-d)*g j := hdir
      _=_ := by simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
  have hterm (i j : ι) : Q i j*(t j*g j)=t i*(Q i j*g j)+(L j-L i)*g j := by
    linear_combination (g j)*hdisp i j
  have hvec : Q *ᵥ (fun i => t i*g i)=B • (fun i => L i-d) := by
    funext i
    change (∑ j,Q i j*(t j*g j))=B*(L i-d)
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

/-- A symmetric inverse pairs a residual supported at the deleted
coordinate with the inverse solution at that coordinate. -/
theorem residual_pairing (Q : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K) (hsym : Qᵀ=Q)
    (R u : ι ⊕ Unit → K) (hR : ∀ i,R (Sum.inl i)=0) :
    u ⬝ᵥ (Q⁻¹ *ᵥ R)=(Q⁻¹ *ᵥ u) (Sum.inr ())*R (Sum.inr ()) := by
  rw [WrapTransport.response_transpose Q R u,hsym]
  simp only [dotProduct,Fintype.sum_sum_type,hR,zero_mul,Finset.sum_const_zero,zero_add,Fintype.sum_unique]
  exact mul_comm _ _

/-- If deleting one common coordinate preserves the representative
own direction, its quadratic source moment is unchanged. This is the
single-deletion cancellation needed by the zero-debit damage ledger. -/
theorem single_deletion_moment (Q : Matrix (ι ⊕ Unit) (ι ⊕ Unit) K)
    (hQ : IsUnit Q.det) (hminor : IsUnit Q.toBlocks₁₁.det) (hsym : Qᵀ=Q)
    (t L sigma : ι ⊕ Unit → K) (Lt d : K)
    (hdisp : ∀ i j,(t j-t i)*Q i j=L j-L i)
    (hsigma : ∀ i,t i*sigma i=L i-Lt)
    (hfull : sigma ⬝ᵥ (Q⁻¹ *ᵥ fun i => L i-d)=Lt-d)
    (hdeleted : (fun i => sigma (Sum.inl i)) ⬝ᵥ
      (Q.toBlocks₁₁⁻¹ *ᵥ fun i => L (Sum.inl i)-d)=Lt-d)
    (hB : 1-∑ j,(Q⁻¹ *ᵥ sigma) j≠0) (ht : t (Sum.inr ())≠0) :
    (fun i => L i-d) ⬝ᵥ (Q⁻¹ *ᵥ fun i => L i-d)=
      (fun i => L (Sum.inl i)-d) ⬝ᵥ
        (Q.toBlocks₁₁⁻¹ *ᵥ fun i => L (Sum.inl i)-d) := by
  let Y := fun i => L i-d
  let z := Q⁻¹ *ᵥ Y
  let g := Q⁻¹ *ᵥ sigma
  let B := 1-∑ j,g j
  let w := Sum.elim (Q.toBlocks₁₁⁻¹ *ᵥ fun i => Y (Sum.inl i)) (fun _ : Unit => 0)
  let R := Y-Q *ᵥ w
  have hsolve : Q.toBlocks₁₁ *ᵥ (Q.toBlocks₁₁⁻¹ *ᵥ fun i => Y (Sum.inl i))=
      fun i => Y (Sum.inl i) := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hminor,Matrix.one_mulVec]
  have hR : ∀ i,R (Sum.inl i)=0 := by
    intro i
    dsimp only [R,Pi.sub_apply]
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,
      mul_zero,Finset.sum_const_zero,add_zero]
    change Y (Sum.inl i)-(Q.toBlocks₁₁ *ᵥ (Q.toBlocks₁₁⁻¹ *ᵥ fun i => Y (Sum.inl i))) i=0
    rw [hsolve,sub_self]
  have hres : Q⁻¹ *ᵥ R=z-w := by
    dsimp only [R,z]
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q hQ,Matrix.one_mulVec]
  have hwSigma : sigma ⬝ᵥ w=(fun i => sigma (Sum.inl i)) ⬝ᵥ
      (Q.toBlocks₁₁⁻¹ *ᵥ fun i => Y (Sum.inl i)) := by
    simp only [dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,mul_zero,
      Finset.sum_const_zero,add_zero]
  have hzero : sigma ⬝ᵥ (Q⁻¹ *ᵥ R)=0 := by
    rw [hres,dotProduct_sub,hfull,hwSigma,hdeleted,sub_self]
  have hpair := residual_pairing Q hsym R sigma hR
  have hprod : g (Sum.inr ())*R (Sum.inr ())=0 := hpair.symm.trans hzero
  have hdir : Lt-d=∑ i,(L i-d)*g i := by
    rw [← hfull,WrapTransport.response_transpose Q Y sigma,hsym]
    rfl
  have hload := loewner_load_relation Q hQ t L sigma Lt d hdisp hsigma hdir
  have hlast : B*z (Sum.inr ())=t (Sum.inr ())*g (Sum.inr ()) := congrFun hload (Sum.inr ())
  have hg : g (Sum.inr ())=0 := by
    rcases mul_eq_zero.1 hprod with hg|hr
    · exact hg
    · have hRall : R=0 := by
        funext i
        rcases i with i|i
        · exact hR i
        · cases i; exact hr
      have hz : z=w := by
        rw [hRall,Matrix.mulVec_zero] at hres
        exact sub_eq_zero.1 hres.symm
      have hzlast : z (Sum.inr ())=0 := by rw [hz]; rfl
      have htg : t (Sum.inr ())*g (Sum.inr ())=0 := by rw [← hlast,hzlast,mul_zero]
      exact (mul_eq_zero.1 htg).resolve_left ht
  have hzlast : z (Sum.inr ())=0 := by
    have hh : B*z (Sum.inr ())=0 := by rw [hlast,hg,mul_zero]
    exact (mul_eq_zero.1 hh).resolve_left hB
  have hmoment : Y ⬝ᵥ (z-w)=0 := by
    rw [← hres,residual_pairing Q hsym R Y hR]
    change z (Sum.inr ())*R (Sum.inr ())=0
    rw [hzlast,zero_mul]
  rw [dotProduct_sub] at hmoment
  calc
    _=Y ⬝ᵥ w := sub_eq_zero.1 hmoment
    _=_ := by
      simp only [Y,dotProduct,Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,mul_zero,
        Finset.sum_const_zero,add_zero]

end Deletion

end CatalanCore.Uniform.Content.UFSimple.WrapDeletion
