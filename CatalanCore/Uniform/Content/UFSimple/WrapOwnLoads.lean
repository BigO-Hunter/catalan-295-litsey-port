module

public import CatalanCore.Uniform.Content.UFSimple.WrapOwnTranspose
public import CatalanCore.Uniform.Content.UFSimple.WrapMixedReference

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnLoads

variable {p : ℕ} [Fact p.Prime] {q o k j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
variable (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowCoord (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y) (c : ι → ℕ) : ι ⊕ Fin b → ℕ :=
  Sum.elim c x

def colCoord (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y) (c : ι → ℕ) : ι ⊕ Fin b → ℕ :=
  Sum.elim c y

noncomputable def load (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
    (u : GaussLoc p) (a : ℕ) : WrapDeform.Extension p :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+a*p)

noncomputable def rowLoad (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
    (u : GaussLoc p) (c : ι → ℕ) : ι ⊕ Fin b → WrapDeform.Extension p :=
  fun i => load H u (rowCoord H c i)

noncomputable def colLoad (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
    (u : GaussLoc p) (c : ι → ℕ) : ι ⊕ Fin b → WrapDeform.Extension p :=
  fun i => load H u (colCoord H c i)

noncomputable def direction (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
    (s u : GaussLoc p) (c : ι → ℕ) (t : ℕ) : WrapDeform.Extension p :=
  (load H u t-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ rowLoad H u c))*
    Ring.inverse (1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))

include H

theorem entry_disp (u : GaussLoc p) (a d : ℕ) (ha : gamma+a*p<N) (hd : gamma+d*p<N) :
    ((d:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*
      WrapDeformedEntry.entry p q o u (gamma+a*p) (gamma+d*p)=load H u d-load H u a := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hcol : ((gamma+a*p:ℕ):ZMod p)=((gamma+d*p:ℕ):ZMod p) := by simp
  have hh := WrapEntryRelation.divided_commutator p q o N u hsingle _ _ ha hd hcol
  have hdiv (j : ℕ) : (gamma+j*p)/p=j := by
    rw [Nat.add_mul_div_right _ _ (Fact.out : p.Prime).pos,Nat.div_eq_of_lt H.hg,zero_add]
  rw [hdiv a,hdiv d] at hh
  change ((d:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*
    WrapDeformedEntry.entry p q o u (gamma+a*p) (gamma+d*p)=
      WrapOwnCore.constants p u*(WrapEntryRelation.load p q o (gamma+d*p)-
        WrapEntryRelation.load p q o (gamma+a*p)) at hh
  simpa only [load,mul_sub] using hh

/-- The actual own core has independent original row and column loads,
including its original common-node spectral diagonal. -/
theorem core_disp (s u : GaussLoc p) (c : ι → ℕ) (hc : ∀ i,gamma+c i*p<N)
    (i j : ι ⊕ Fin b) :
    ((colCoord H c j:WrapDeform.Extension p)-(rowCoord H c i:WrapDeform.Extension p))*
      WrapOwnCore.actual H s u c i j=colLoad H u c j-rowLoad H u c i := by
  classical
  rcases i with i|i <;> rcases j with j|j
  · by_cases hij : i=j
    · subst j
      change ((c i:WrapDeform.Extension p)-(c i:WrapDeform.Extension p))*_=load H u (c i)-load H u (c i)
      rw [sub_self,zero_mul,sub_self]
    · change ((c j:WrapDeform.Extension p)-(c i:WrapDeform.Extension p))*
        (WrapOwnCore.constants p s*(if i=j then 1 else 0)+
          WrapDeformedEntry.entry p q o u (gamma+c i*p) (gamma+c j*p))=
            load H u (c j)-load H u (c i)
      rw [if_neg hij,mul_zero,zero_add]
      exact entry_disp H u _ _ (hc i) (hc j)
  · exact entry_disp H u _ _ (hc i) (H.hyN j)
  · exact entry_disp H u _ _ (H.hxN i) (hc j)
  · exact entry_disp H u _ _ (H.hxN i) (H.hyN j)

theorem row_disp (u : GaussLoc p) (c : ι → ℕ) (hc : ∀ i,gamma+c i*p<N)
    (t : ℕ) (ht : gamma+t*p<N) (i : ι ⊕ Fin b) :
    ((colCoord H c i:WrapDeform.Extension p)-(t:WrapDeform.Extension p))*
      WrapOwnReference.sigma H u c t i=colLoad H u c i-load H u t := by
  rcases i with i|i
  · exact entry_disp H u _ _ ht (hc i)
  · exact entry_disp H u _ _ ht (H.hyN i)

theorem col_disp (u : GaussLoc p) (c : ι → ℕ) (hc : ∀ i,gamma+c i*p<N)
    (t : ℕ) (ht : gamma+t*p<N) (i : ι ⊕ Fin b) :
    ((t:WrapDeform.Extension p)-(rowCoord H c i:WrapDeform.Extension p))*
      WrapOwnTranspose.colSigma H u c t i=load H u t-rowLoad H u c i := by
  rcases i with i|i
  · exact entry_disp H u _ _ (hc i) ht
  · exact entry_disp H u _ _ (H.hxN i) ht

/-- Actual unit reference normalizations define one exact integral
own direction, with every displacement and unit supplied by original data. -/
theorem shared_direction (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J)
    (t : ℕ) (htJ : t≤J) (hxt : ∀ i,x i≠t) (hyt : ∀ j,y j≠t) :
    direction H s u c t=
      (load H u t-colLoad H u c ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ WrapOwnTranspose.colSigma H u c t))*
        Ring.inverse (1-(1:ι ⊕ Fin b → WrapDeform.Extension p) ⬝ᵥ
          ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ WrapOwnTranspose.colSigma H u c t)) := by
  have hcN : ∀ i,gamma+c i*p<N := by
    intro i; have := Nat.mul_le_mul_right p (hc i); omega
  have htN : gamma+t*p<N := by have := Nat.mul_le_mul_right p htJ; omega
  unfold direction
  exact WrapMixedReference.unit_direction _
    (WrapOwnCore.unit H s u hs hu huc c J hJ hc hxJ hyJ)
    (fun i => (rowCoord H c i:WrapDeform.Extension p))
    (fun i => (colCoord H c i:WrapDeform.Extension p))
    (rowLoad H u c) (colLoad H u c) (WrapOwnReference.sigma H u c t)
    (WrapOwnTranspose.colSigma H u c t) (t:WrapDeform.Extension p) (load H u t)
    (core_disp H s u c hcN) (row_disp H u c hcN t htN) (col_disp H u c hcN t htN)
    (WrapOwnReference.unit H s u hs hu huc c J hJ hc hxJ hyJ t htJ hxt hyt)
    (WrapOwnTranspose.column_unit H s u hs hu huc c J hJ hc hxJ hyJ t htJ hxt hyt)

/-- The constructed actual row direction annihilates its own response.
The unit hypothesis is already discharged by WrapOwnReference.unit. -/
theorem direction_zero (s u : GaussLoc p) (c : ι → ℕ) (t : ℕ)
    (hB : IsUnit (1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))) :
    (load H u t-direction H s u c t)-WrapOwnReference.sigma H u c t ⬝ᵥ
      ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ (fun i => rowLoad H u c i-direction H s u c t))=0 := by
  have hd : (1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))*
      direction H s u c t=
        load H u t-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ rowLoad H u c) := by
    unfold direction
    calc
      _=(load H u t-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ rowLoad H u c))*
        ((1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))*
          Ring.inverse (1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))) := by ring
      _=_ := by rw [Ring.mul_inverse_cancel _ hB,mul_one]
  have hv : (fun i => rowLoad H u c i-direction H s u c t)=
      rowLoad H u c-direction H s u c t • (1:ι ⊕ Fin b → WrapDeform.Extension p) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hv,Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _=(load H u t-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ rowLoad H u c))-
      (1-WrapOwnReference.sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1))*direction H s u c t := by ring
    _=0 := by rw [hd,sub_self]

end CatalanCore.Uniform.Content.UFSimple.WrapOwnLoads
