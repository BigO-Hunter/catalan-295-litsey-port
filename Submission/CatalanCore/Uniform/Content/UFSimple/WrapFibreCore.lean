module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapFibreIndex

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapFibreCore

variable (p : ℕ) [Fact p.Prime]
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- The actual mixed prefix core before separating its colour fibres. -/
noncomputable def core (q o : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ) :
    Matrix (ι ⊕ β) (ι ⊕ β) (WrapDeform.Extension p) :=
  Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (Sum.elim c xs i) (Sum.elim c ys j))+
    Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix ι ι (WrapDeform.Extension p))) 0 0 0

open WrapFibreIndex

/-- Exact original matrix binding: each colour block, reindexed by its
actual common/balanced fibre, is the whole own-core already proved unit. -/
theorem block_eq (q o k j0 m N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (gamma : ZMod p)
    (H : WrapBalancedResidue.Hyp p q o k j0 gamma.val m N
      (Fintype.card (Balanced p xs gamma)) (rowQuotient p xs gamma) (colQuotient p xs ys gamma)) :
    (core p q o s u c xs ys).submatrix
      (fun i => (equiv p c xs gamma i).1) (fun j => (equiv p c xs gamma j).1)=
        WrapOwnCore.actual H s u (commonQuotient p c gamma) := by
  classical
  apply Matrix.ext; intro i j
  rcases i with i|i <;> rcases j with j|j
  · change WrapDeformedEntry.entry p q o u (c i.1) (c j.1)+
      WrapOwnCore.constants p s*(if i.1=j.1 then 1 else 0)=
        WrapOwnCore.constants p s*(if i=j then 1 else 0)+
          WrapDeformedEntry.entry p q o u (gamma.val+commonQuotient p c gamma i*p)
            (gamma.val+commonQuotient p c gamma j*p)
    rw [common_node p c gamma i,common_node p c gamma j]
    by_cases hij : i=j
    · subst j; simp only [↓reduceIte,mul_one,add_comm]
    · have hv : i.1≠j.1 := fun he => hij (Subtype.ext he)
      simp only [hij,hv,↓reduceIte,mul_zero,add_zero,zero_add]
  · change WrapDeformedEntry.entry p q o u (c i.1) (ys (balancedEquiv p xs gamma j).1)+0=
      WrapDeformedEntry.entry p q o u (gamma.val+commonQuotient p c gamma i*p)
        (gamma.val+colQuotient p xs ys gamma j*p)
    rw [common_node p c gamma i,col_node p xs ys hcol gamma j,add_zero]
  · change WrapDeformedEntry.entry p q o u (xs (balancedEquiv p xs gamma i).1) (c j.1)+0=
      WrapDeformedEntry.entry p q o u (gamma.val+rowQuotient p xs gamma i*p)
        (gamma.val+commonQuotient p c gamma j*p)
    rw [row_node p xs gamma i,common_node p c gamma j,add_zero]
  · change WrapDeformedEntry.entry p q o u (xs (balancedEquiv p xs gamma i).1)
      (ys (balancedEquiv p xs gamma j).1)+0=
        WrapDeformedEntry.entry p q o u (gamma.val+rowQuotient p xs gamma i*p)
          (gamma.val+colQuotient p xs ys gamma j*p)
    rw [row_node p xs gamma i,col_node p xs ys hcol gamma j,add_zero]

/-- A single automatic original quotient bound covers all nodes of a
colour fibre and any original virtual node in that fibre. -/
theorem quotient_cap (gamma N : ℕ) (hg : gamma<N) :
    gamma+((N-1-gamma)/p)*p<N := by
  have hh := Nat.div_mul_le_self (N-1-gamma) p
  omega

theorem le_quotient_cap (gamma N a : ℕ) (ha : gamma+a*p<N) :
    a≤(N-1-gamma)/p := by
  apply (Nat.le_div_iff_mul_le (Fact.out : p.Prime).pos).mpr
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapFibreCore
