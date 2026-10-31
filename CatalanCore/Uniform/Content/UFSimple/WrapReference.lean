module

public import CatalanCore.Uniform.Content.UFSimple.WrapDisplacement

@[expose] public section

/-! # One reference direction for independent prefix row and column loads -/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapReference

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- At a shared virtual node the two cleared reference directions agree.
The identity stays valid even when a direction denominator vanishes. -/
theorem cross_direction (Q : Matrix ι ι K) (hQ : IsUnit Q.det)
    (x y LR LC sigmaR sigmaC : ι → K) (t Lt : K)
    (hdisp : ∀ i j,(y j-x i)*Q i j=LC j-LR i)
    (hrow : ∀ i,(y i-t)*sigmaR i=LC i-Lt)
    (hcol : ∀ i,(t-x i)*sigmaC i=Lt-LR i) :
    (1-sigmaR ⬝ᵥ (Q⁻¹ *ᵥ 1))*(Lt-LC ⬝ᵥ (Q⁻¹ *ᵥ sigmaC))=
      (Lt-sigmaR ⬝ᵥ (Q⁻¹ *ᵥ LR))*(1-(1:ι→K) ⬝ᵥ (Q⁻¹ *ᵥ sigmaC)) := by
  let B : Matrix ι Unit K := Matrix.of fun i _ => sigmaC i
  let C : Matrix Unit ι K := Matrix.of fun _ j => sigmaR j
  have hAN : Q*Q⁻¹=(1:K) • (1:Matrix ι ι K) := by
    rw [Matrix.mul_nonsing_inv Q hQ,one_smul]
  have hNA : Q⁻¹*Q=(1:K) • (1:Matrix ι ι K) := by
    rw [Matrix.nonsing_inv_mul Q hQ,one_smul]
  have hh := WrapDisplacement.mixed_cleared_schur_displacement Q Q⁻¹ B C
    (0:Matrix Unit Unit K) 1 1 hAN hNA x y LR LC
    (fun _ : Unit => t) (fun _ : Unit => Lt) (fun _ : Unit => t) (fun _ : Unit => Lt)
    (by intro i j; simpa only [one_mul] using hdisp i j)
    (by intro i j; simpa only [one_mul,B,Matrix.of_apply] using hcol i)
    (by intro i j; simpa only [one_mul,C,Matrix.of_apply] using hrow j)
    (by intro i j; simp) () ()
  have hc : ∑ j,(∑ k,LC k*Q⁻¹ k j)*sigmaC j=LC ⬝ᵥ (Q⁻¹ *ᵥ sigmaC) := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hd : ∑ j,(∑ k,Q⁻¹ k j)*sigmaC j=(1:ι→K) ⬝ᵥ (Q⁻¹ *ᵥ sigmaC) := by
    simp only [Matrix.mulVec,dotProduct,Pi.one_apply,one_mul,Finset.sum_mul]
    exact Finset.sum_comm
  simp only [sub_self,mul_zero,zero_mul,one_mul,B,C,Matrix.of_apply] at hh
  rw [hc,hd] at hh
  have he := sub_eq_zero.mp hh.symm
  simpa only [Matrix.mulVec,dotProduct,Pi.one_apply,mul_one] using he

/-- Both actual normalizations consequently give the same direction. -/
theorem direction_eq (Q : Matrix ι ι K) (hQ : IsUnit Q.det)
    (x y LR LC sigmaR sigmaC : ι → K) (t Lt : K)
    (hdisp : ∀ i j,(y j-x i)*Q i j=LC j-LR i)
    (hrow : ∀ i,(y i-t)*sigmaR i=LC i-Lt)
    (hcol : ∀ i,(t-x i)*sigmaC i=Lt-LR i)
    (hR : 1-sigmaR ⬝ᵥ (Q⁻¹ *ᵥ 1)≠0)
    (hC : 1-(1:ι→K) ⬝ᵥ (Q⁻¹ *ᵥ sigmaC)≠0) :
    (Lt-sigmaR ⬝ᵥ (Q⁻¹ *ᵥ LR))/(1-sigmaR ⬝ᵥ (Q⁻¹ *ᵥ 1))=
      (Lt-LC ⬝ᵥ (Q⁻¹ *ᵥ sigmaC))/(1-(1:ι→K) ⬝ᵥ (Q⁻¹ *ᵥ sigmaC)) := by
  apply (div_eq_div_iff hR hC).2
  simpa only [mul_comm] using (cross_direction Q hQ x y LR LC sigmaR sigmaC t Lt hdisp hrow hcol).symm

end CatalanCore.Uniform.Content.UFSimple.WrapReference
