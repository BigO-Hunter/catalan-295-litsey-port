module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapTelescoping

@[expose] public section

/-! # Original two-pole harmonic loads at a prefix Cauchy specialization -/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapHarmonic

variable {K : Type*} [Field K]

noncomputable def cumulative (a : K) (j : ℕ) : K :=
  ∑ h∈range j,((1:K)/(1+(h:K))-1/(1+a+(h:K)))
noncomputable def potential (b : ℕ) (x : K) : K := ∑ k:Fin b,(1:K)/(1+x+(k:ℕ))
noncomputable def load (a : K) (epsilon : Bool) (j : ℕ) : K :=
  (∑ h∈range j,(1:K)/(1+(h:K)))-
    ∑ h∈range (j+if epsilon then 1 else 0),(1:K)/(a+(h:K))
noncomputable def testShift (b : ℕ) (epsilon : Bool) : K :=
  1+(b:K)-(if epsilon then 1 else 0)
noncomputable def poles (b : ℕ) : Fin b → K := fun k => -(((k:ℕ)+1:ℕ):K)

theorem cumulative_integer (b j : ℕ) :
    cumulative (b:K) j=potential b (0:K)-potential b (j:K) := by
  have hh := WrapTelescoping.finite_shift_identity (1:K) b j
  unfold cumulative potential
  simp only [Nat.cast_add,add_zero,← add_assoc,Finset.sum_sub_distrib] at hh ⊢
  linear_combination -hh

/-- Exact original cumulative pole load, with the actual pole-side bit. -/
theorem load_test (b j : ℕ) (epsilon : Bool) :
    load (testShift (K:=K) b epsilon) epsilon j=
      potential b (0:K)-potential b (j:K)-(if epsilon then 1/(b:K) else 0) := by
  cases epsilon
  · simpa only [load,testShift,Bool.false_eq_true,↓reduceIte,sub_zero,Nat.add_zero,
      cumulative,Finset.sum_sub_distrib] using cumulative_integer (K:=K) b j
  · have hh := cumulative_integer (K:=K) b j
    have hs := Finset.sum_range_succ' (fun h : ℕ => (1:K)/((b:K)+(h:K))) j
    have ht : (1:K)+(b:K)-1=(b:K) := by ring
    simp only [load,testShift,↓reduceIte,ht]
    rw [hs]
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at *
    have he : (∑ h∈range j,(1:K)/((b:K)+((h:K)+1)))=
        ∑ h∈range j,(1:K)/(1+(b:K)+(h:K)) := by
      apply Finset.sum_congr rfl; intro h _
      congr 1; ring
    rw [he]
    unfold cumulative at hh
    rw [Finset.sum_sub_distrib] at hh
    linear_combination hh

theorem potential_eq (b j : ℕ) :
    WrapTelescoping.potential (poles (K:=K) b) (j:K)=potential b (j:K) := by
  unfold WrapTelescoping.potential poles potential
  apply Finset.sum_congr rfl; intro k _
  simp only [Nat.cast_add,Nat.cast_one,sub_neg_eq_add]
  congr 1; ring

noncomputable def entry (b : ℕ) (epsilon : Bool) (x y : ℕ) : K :=
  (load (testShift (K:=K) b epsilon) epsilon y-
    load (testShift (K:=K) b epsilon) epsilon x)/((y:K)-(x:K))

/-- The original cumulative-load matrix has the opposite sign to the
potential Loewner helper, on both the core and the virtual border. -/
theorem entry_eq (b x y : ℕ) (epsilon : Bool) :
    entry (K:=K) b epsilon x y=
      -WrapTelescoping.entry (poles b) (x:K) (y:K) := by
  unfold entry WrapTelescoping.entry
  rw [load_test,load_test,potential_eq,potential_eq]
  ring

noncomputable def matrix (b : ℕ) (epsilon : Bool) (x y : Fin b → ℕ) : Matrix (Fin b) (Fin b) K :=
  Matrix.of fun i j => entry b epsilon (x i) (y j)

theorem matrix_neg (b : ℕ) (epsilon : Bool) (x y : Fin b → ℕ) :
    matrix (K:=K) b epsilon x y=
      -WrapTelescoping.loewner (poles b) (fun i => (x i:K)) (fun i => (y i:K)) := by
  apply Matrix.ext; intro i j
  exact entry_eq b (x i) (y j) epsilon

theorem neg_reference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι K) (sigma : ι → K) (hQ : IsUnit Q.det) :
    1-(-sigma) ⬝ᵥ ((-Q)⁻¹ *ᵥ 1)=1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1) := by
  have hi : (-Q)⁻¹=-Q⁻¹ := Matrix.inv_eq_left_inv
    (by rw [neg_mul_neg,Matrix.nonsing_inv_mul Q hQ])
  rw [hi,Matrix.neg_mulVec,neg_dotProduct,dotProduct_neg,neg_neg]

end CatalanCore.Uniform.Content.UFSimple.WrapHarmonic
