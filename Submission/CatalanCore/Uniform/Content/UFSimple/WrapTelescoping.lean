module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapCauchy

@[expose] public section

/-! # Telescoping specializations of actual two-pole prefix fibres -/

open Polynomial Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapTelescoping

variable {K : Type*} [Field K] {n : ℕ}

/-- A finite rectangular sum identity; no asymptotic expansion is needed. -/
theorem shifted_sum_difference (f : ℕ → K) (n j : ℕ) :
    (∑ h∈Finset.range j,f (n+h))-(∑ h∈Finset.range j,f h)=
      (∑ k∈Finset.range n,f (j+k))-(∑ k∈Finset.range n,f k) := by
  have hs : (∑ h∈Finset.range n,f h)+(∑ h∈Finset.range j,f (n+h))=
      (∑ h∈Finset.range j,f h)+(∑ h∈Finset.range n,f (j+h)) := by
    rw [← Finset.sum_range_add,← Finset.sum_range_add,Nat.add_comm n j]
  linear_combination hs

/-- At an integer separation, the two-pole cumulative source telescopes
to precisely that many Cauchy terms. -/
theorem finite_shift_identity (x : K) (n j : ℕ) :
    (∑ h∈Finset.range j,(1/(x+((n+h:ℕ):K))-1/(x+(h:K))))=
      ∑ k:Fin n,(1/(x+((j+(k:ℕ):ℕ):K))-1/(x+((k:ℕ):K))) := by
  rw [← Finset.sum_range (n:=n) (fun k : ℕ =>
    (1/(x+((j+k:ℕ):K))-1/(x+(k:K))))]
  simp only [Finset.sum_sub_distrib]
  exact shifted_sum_difference (fun h => 1/(x+(h:K))) n j

noncomputable def potential (poles : Fin n → K) (z : K) : K := ∑ k,1/(z-poles k)
noncomputable def entry (poles : Fin n → K) (x y : K) : K :=
  (potential poles y-potential poles x)/(y-x)
noncomputable def loewner (poles x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => entry poles (x i) (y j)

theorem reciprocal_difference (a x y : K) (hxa : x≠a) (hya : y≠a) (hxy : y≠x) :
    (1/(y-a)-1/(x-a))/(y-x)=-(1/(x-a)*(1/(y-a))) := by
  field_simp [sub_ne_zero.mpr hxa,sub_ne_zero.mpr hya,sub_ne_zero.mpr hxy]
  <;> ring

theorem entry_eq (poles : Fin n → K) (x y : K)
    (hxp : ∀ k,x≠poles k) (hyp : ∀ k,y≠poles k) (hxy : y≠x) :
    entry poles x y=-(∑ k,(1/(x-poles k))*(1/(y-poles k))) := by
  unfold entry potential
  rw [← Finset.sum_sub_distrib (s:=Finset.univ)
    (fun k : Fin n => (1:K)/(y-poles k)) (fun k : Fin n => (1:K)/(x-poles k)),Finset.sum_div]
  simp_rw [reciprocal_difference _ _ _ (hxp _) (hyp _) hxy]
  exact Finset.sum_neg_distrib (s:=Finset.univ) (fun k : Fin n => ((1:K)/(x-poles k))*((1:K)/(y-poles k)))

/-- The specialized prefix block is a product of two square Cauchy matrices. -/
theorem loewner_factor (poles x y : Fin n → K)
    (hxp : ∀ i k,x i≠poles k) (hyp : ∀ i k,y i≠poles k) (hxy : ∀ i j,y j≠x i) :
    loewner poles x y=-(WrapCauchy.matrix x poles*(WrapCauchy.matrix y poles)ᵀ) := by
  apply Matrix.ext; intro i j
  exact entry_eq poles (x i) (y j) (hxp i) (hyp j) (hxy i j)

theorem loewner_det_ne (poles x y : Fin n → K) (hp : Function.Injective poles)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxp : ∀ i k,x i≠poles k) (hyp : ∀ i k,y i≠poles k) (hxy : ∀ i j,y j≠x i) :
    (loewner poles x y).det≠0 := by
  rw [loewner_factor poles x y hxp hyp hxy,Matrix.det_neg,Matrix.det_mul,Matrix.det_transpose]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero (WrapCauchy.det_ne x poles hx hp hxp) (WrapCauchy.det_ne y poles hy hp hyp))

/-- The specialized actual row normalization is a Cauchy interpolation
error on the row nodes. The independent column nodes cancel exactly. -/
theorem row_response (poles x y : Fin n → K) (hp : Function.Injective poles)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxp : ∀ i k,x i≠poles k) (hyp : ∀ i k,y i≠poles k) (hxy : ∀ i j,y j≠x i)
    (t : K) (htp : ∀ k,t≠poles k) (hty : ∀ j,y j≠t) :
    (fun j => entry poles t (y j)) ⬝ᵥ ((loewner poles x y)⁻¹ *ᵥ 1)=
      (fun k => 1/(t-poles k)) ⬝ᵥ ((WrapCauchy.matrix x poles)⁻¹ *ᵥ 1) := by
  let CX := WrapCauchy.matrix x poles
  let CY := WrapCauchy.matrix y poles
  let Q := loewner poles x y
  let v := fun k => 1/(t-poles k)
  let w := Q⁻¹ *ᵥ (1:Fin n→K)
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr (loewner_det_ne poles x y hp hx hy hxp hyp hxy)
  have hCX : IsUnit CX.det := isUnit_iff_ne_zero.mpr (WrapCauchy.det_ne x poles hx hp hxp)
  have hsolve : Q *ᵥ w=1 := by
    rw [show w=Q⁻¹ *ᵥ (1:Fin n→K) from rfl,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  have hfactor : Q=-(CX*CYᵀ) := loewner_factor poles x y hxp hyp hxy
  have hstep : CX *ᵥ (CYᵀ *ᵥ w)=-(1:Fin n→K) := by
    calc
      _=(CX*CYᵀ) *ᵥ w := Matrix.mulVec_mulVec _ _ _
      _=-(Q *ᵥ w) := by rw [hfactor,Matrix.neg_mulVec,neg_neg]
      _=_ := by rw [hsolve]
  have hv : CYᵀ *ᵥ w=-(CX⁻¹ *ᵥ (1:Fin n→K)) := by
    have hh := congrArg (fun u => CX⁻¹ *ᵥ u) hstep
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul CX hCX,Matrix.one_mulVec,Matrix.mulVec_neg] at hh
    exact hh
  have hsigma : (fun j => entry poles t (y j))=-(v ᵥ* CYᵀ) := by
    funext j
    have hh := entry_eq poles t (y j) htp (hyp j) (hty j)
    exact hh
  change (fun j => entry poles t (y j)) ⬝ᵥ w=v ⬝ᵥ (CX⁻¹ *ᵥ 1)
  rw [hsigma,neg_dotProduct,← Matrix.dotProduct_mulVec,hv,dotProduct_neg,neg_neg]

/-- Nonzero normalization at a Cauchy specialization certifies generic
nonvanishing; this statement itself specializes no generic inverse pivot. -/
theorem row_reference_ne (poles x y : Fin n → K) (hp : Function.Injective poles)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxp : ∀ i k,x i≠poles k) (hyp : ∀ i k,y i≠poles k) (hxy : ∀ i j,y j≠x i)
    (t : K) (htp : ∀ k,t≠poles k) (htx : ∀ i,x i≠t) (hty : ∀ j,y j≠t) :
    1-(fun j => entry poles t (y j)) ⬝ᵥ ((loewner poles x y)⁻¹ *ᵥ 1)≠0 := by
  rw [row_response poles x y hp hx hy hxp hyp hxy t htp hty]
  exact WrapCauchy.reference_ne x poles hx hp hxp t htx htp

end CatalanCore.Uniform.Content.UFSimple.WrapTelescoping
