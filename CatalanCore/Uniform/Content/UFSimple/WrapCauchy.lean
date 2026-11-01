module

public import CatalanLambda.Decay.CauchyDetFull
public import CatalanCore.Uniform.Content.UFSimple.WrapDisplacement

@[expose] public section

/-! # Cauchy specialization certificates for generic prefix pivots -/

open Polynomial Matrix Finset
open CatalanLambda.Decay

namespace CatalanCore.Uniform.Content.UFSimple.WrapCauchy

variable {K : Type*} [Field K] {n : ℕ}

noncomputable def matrix (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => 1/(x i-y j)

/-- Actual nonzero Cauchy determinants over any residue coefficient field. -/
theorem det_ne (x y : Fin n → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j,x i≠y j) : (matrix x y).det≠0 := by
  rw [matrix,cauchy_det x y hy hxy]
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j hj
    have hij := Finset.mem_Ioi.mp hj
    exact mul_ne_zero (sub_ne_zero.mpr (fun h => (ne_of_gt hij) (hx h)))
      (sub_ne_zero.mpr (fun h => (ne_of_lt hij) (hy h)))
  · apply Finset.prod_ne_zero_iff.mpr; intro i _
    apply Finset.prod_ne_zero_iff.mpr; intro j _
    exact sub_ne_zero.mpr (hxy i j)

noncomputable def denominator (y : Fin n → K) : K[X] := ∏ j,(Polynomial.X-Polynomial.C (y j))
noncomputable def remainder (y : Fin n → K) (b : Fin n → K) : K[X] :=
  denominator y-∑ j,Polynomial.C (b j)*lagP y j

theorem denominator_degree (y : Fin n → K) : (denominator y).natDegree=n := by
  unfold denominator
  have hh := Polynomial.natDegree_prod_of_monic (f:=fun j : Fin n => (Polynomial.X-Polynomial.C (y j):K[X]))
    Finset.univ (fun j _ => Polynomial.monic_X_sub_C (y j))
  simpa using hh

theorem remainder_degree_le (y : Fin n → K) (b : Fin n → K) : (remainder y b).natDegree≤n := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (denominator_degree y).le
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_le _ _).trans (le_of_lt (lagP_natDegree_lt y j))

theorem remainder_coeff (y : Fin n → K) (b : Fin n → K) : (remainder y b).coeff n=1 := by
  have hz : (∑ j,Polynomial.C (b j)*lagP y j).coeff n=0 := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero; intro j _
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_eq_zero_of_natDegree_lt (lagP_natDegree_lt y j),mul_zero]
  rw [remainder,Polynomial.coeff_sub,hz,sub_zero]
  have hh := (Polynomial.monic_prod_X_sub_C y Finset.univ).coeff_natDegree
  change (denominator y).coeff (denominator y).natDegree=1 at hh
  rwa [denominator_degree y] at hh

/-- Clearing the actual Cauchy denominators gives a monic interpolation error. -/
theorem remainder_eval (y : Fin n → K) (b : Fin n → K) (z : K) (hz : ∀ j,z≠y j) :
    (remainder y b).eval z=(denominator y).eval z*(1-∑ j,b j/(z-y j)) := by
  have hlag (j : Fin n) : (lagP y j).eval z=(denominator y).eval z/(z-y j) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hz j))).mpr
    have he := Finset.mul_prod_erase Finset.univ (fun k => z-y k) (Finset.mem_univ j)
    simpa only [denominator,lagP,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,mul_comm] using he
  unfold remainder
  rw [Polynomial.eval_sub,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  calc
    _=(denominator y).eval z-(denominator y).eval z*(∑ j,b j/(z-y j)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [hlag]
      ring
    _=_ := by ring

/-- Adding a shared virtual node leaves a nonzero reference denominator.
This is the Cauchy specialization used to certify a generic normalization. -/
theorem reference_ne (x y : Fin n → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j,x i≠y j) (t : K) (htx : ∀ i,x i≠t) (hty : ∀ j,t≠y j) :
    1-(fun j => 1/(t-y j)) ⬝ᵥ ((matrix x y)⁻¹ *ᵥ 1)≠0 := by
  classical
  let Q := matrix x y
  let b := Q⁻¹ *ᵥ (1:Fin n→K)
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr (det_ne x y hx hy hxy)
  have hsolve : Q *ᵥ b=1 := by
    rw [show b=Q⁻¹ *ᵥ (1:Fin n→K) from rfl,Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  have hrow (i : Fin n) : ∑ j,b j/(x i-y j)=1 := by
    have hh := congrFun hsolve i
    simpa only [Q,matrix,Matrix.mulVec,dotProduct,Matrix.of_apply,Pi.one_apply,div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  intro h0
  have ht : ∑ j,b j/(t-y j)=1 := by
    have hh := (sub_eq_zero.mp h0).symm
    simpa only [b,Q,dotProduct,div_eq_mul_inv,one_mul,mul_one,mul_comm] using hh
  let z : Fin n ⊕ Unit → K := Sum.elim x (fun _ => t)
  have hzinj : Function.Injective z := by
    intro i j hij
    rcases i with i|i <;> rcases j with j|j
    · exact congrArg Sum.inl (hx hij)
    · exact False.elim (htx i hij)
    · exact False.elim (htx j hij.symm)
    · cases i; cases j; rfl
  have heval : ∀ i,(remainder y b).eval (z i)=0 := by
    intro i
    rcases i with i|i
    · change (remainder y b).eval (x i)=0
      rw [remainder_eval y b (x i) (hxy i),hrow i,sub_self,mul_zero]
    · change (remainder y b).eval t=0
      rw [remainder_eval y b t hty,ht,sub_self,mul_zero]
  have hcard : (remainder y b).natDegree<Fintype.card (Fin n ⊕ Unit) := by
    have hh := remainder_degree_le y b
    simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unique]
    omega
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (remainder y b) hzinj heval hcard
  have hc := congrArg (fun f : K[X] => f.coeff n) hz
  rw [remainder_coeff,Polynomial.coeff_zero] at hc
  exact one_ne_zero hc

end CatalanCore.Uniform.Content.UFSimple.WrapCauchy
