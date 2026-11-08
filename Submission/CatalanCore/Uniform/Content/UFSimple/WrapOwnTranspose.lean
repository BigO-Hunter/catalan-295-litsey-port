module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapOwnReference
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapEntryRelation
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnTranspose

variable {p : ℕ} [Fact p.Prime] {q o k j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
variable (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

include H

/-- Swapping the actual balanced row and column families retains all
original arithmetic geometry. It does not assert symmetry of the core. -/
theorem swap : WrapBalancedResidue.Hyp p q o k j0 gamma m N b y x := by
  exact {
    hq0 := H.hq0
    hqp := H.hqp
    hq2 := H.hq2
    hoq := H.hoq
    hk0 := H.hk0
    hk := H.hk
    hg := H.hg
    hroot := H.hroot
    hsize := H.hsize
    hN := H.hN
    hb := H.hb
    hb0 := H.hb0
    hx := H.hy
    hy := H.hx
    hxN := H.hyN
    hyN := H.hxN
    hxy := fun i j => Ne.symm (H.hxy j i)
  }

theorem actual_transpose (s u : GaussLoc p) (c : ι → ℕ) :
    WrapOwnCore.actual (swap H) s u c=(WrapOwnCore.actual H s u c)ᵀ := by
  classical
  apply Matrix.ext; intro i j
  rcases i with i|i <;> rcases j with j|j
  · change WrapOwnCore.constants p s*(if i=j then 1 else 0)+
      WrapDeformedEntry.entry p q o u (gamma+c i*p) (gamma+c j*p)=
        WrapOwnCore.constants p s*(if j=i then 1 else 0)+
          WrapDeformedEntry.entry p q o u (gamma+c j*p) (gamma+c i*p)
    rw [WrapEntryRelation.entry_symm p q o u (gamma+c i*p) (gamma+c j*p)]
    simp only [eq_comm]
  · exact WrapEntryRelation.entry_symm p q o u (gamma+c i*p) (gamma+x j*p)
  · exact WrapEntryRelation.entry_symm p q o u (gamma+y i*p) (gamma+c j*p)
  · exact WrapEntryRelation.entry_symm p q o u (gamma+y i*p) (gamma+x j*p)

noncomputable def colSigma (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
    (u : GaussLoc p) (c : ι → ℕ) (t : ℕ) : ι ⊕ Fin b → WrapDeform.Extension p :=
  Sum.elim (fun i => WrapDeformedEntry.entry p q o u (gamma+c i*p) (gamma+t*p))
    (fun j => WrapDeformedEntry.entry p q o u (gamma+x j*p) (gamma+t*p))

theorem swap_sigma (u : GaussLoc p) (c : ι → ℕ) (t : ℕ) :
    WrapOwnReference.sigma (swap H) u c t=colSigma H u c t := by
  funext i
  rcases i with i|i
  · exact WrapEntryRelation.entry_symm p q o u (gamma+t*p) (gamma+c i*p)
  · exact WrapEntryRelation.entry_symm p q o u (gamma+t*p) (gamma+x i*p)

/-- The actual column normalization is a unit by the swapped actual
row theorem. Both directions are valid for an independently mixed core. -/
theorem column_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J)
    (t : ℕ) (htJ : t≤J) (hxt : ∀ i,x i≠t) (hyt : ∀ j,y j≠t) :
    IsUnit (1-(1:ι ⊕ Fin b → WrapDeform.Extension p) ⬝ᵥ
      ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ colSigma H u c t)) := by
  have hh := WrapOwnReference.unit (swap H) s u hs hu huc c J hJ hc hyJ hxJ t htJ hyt hxt
  rw [actual_transpose H s u c,swap_sigma H u c t] at hh
  rw [WrapTransport.response_transpose] at hh
  simpa only [Matrix.transpose_transpose] using hh

end CatalanCore.Uniform.Content.UFSimple.WrapOwnTranspose
