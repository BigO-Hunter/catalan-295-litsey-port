module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapRestrict

@[expose] public section

/-! # A singly edited selected colour in the original member source -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapSingle

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Multiplicity one supplies the unique original deleted coordinate
required by the concrete single-colour cancellation theorem. -/
theorem unique_deleted (c : ι → ℕ) (K : Finset ι) (u : ZMod p)
    (h : WrapDamage.multiplicity K (colOf (p:=p) c) u=1) :
    ∃ j,j∈K ∧ colOf (p:=p) c j=u ∧
      ∀ i,i∈K → colOf (p:=p) c i=u → i=j := by
  change (K.filter (fun i => colOf (p:=p) c i=u)).card=1 at h
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp h
  have hm : j∈K.filter (fun i => colOf (p:=p) c i=u) := by rw [hj]; simp
  refine ⟨j,(Finset.mem_filter.mp hm).1,(Finset.mem_filter.mp hm).2,?_⟩
  intro i hi hcol
  have hm' : i∈K.filter (fun i => colOf (p:=p) c i=u) := Finset.mem_filter.mpr ⟨hi,hcol⟩
  rw [hj] at hm'
  exact Finset.mem_singleton.mp hm'

/-- A singly edited colour has exactly the original own fibre minus
its unique deleted coordinate. All other edits are outside this fibre. -/
def fibreEquiv (c : ι → ℕ) (K : Finset ι) (u : ZMod p) (j : ι)
    (hjK : j∈K) (hj : colOf (p:=p) c j=u)
    (hunique : ∀ i,i∈K → colOf (p:=p) c i=u → i=j) :
    {i : WrapKeep.Keep K // colOf (p:=p) (c ∘ Subtype.val) i=u} ≃
      {i : {i : ι // colOf (p:=p) c i=u} // i≠⟨j,hj⟩} where
  toFun i := ⟨⟨i.1.1,i.2⟩,by
    intro h
    have he : i.1.1=j := congrArg Subtype.val h
    exact i.1.2 (he.symm ▸ hjK)⟩
  invFun i := ⟨⟨i.1.1,by
    intro hk
    exact i.2 (Subtype.ext (hunique i.1.1 hk i.1.2))⟩,i.1.2⟩
  left_inv i := rfl
  right_inv i := rfl

/-- The original own-colour moment is literally the own response of
its concrete common fibre. -/
theorem ownMoment_fibre (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (t : ℕ) (d : GaussLoc p) :
    WrapRestrict.ownMoment (Fr:=Fr) c t d=
      WrapOwn.commonOwn (Fr:=Fr)
        (fun i : {i : ι // colOf (p:=p) c i=(t:ZMod p)} => c i.1) t d := by
  let cf := fun i : {i : ι // colOf (p:=p) c i=(t:ZMod p)} => c i.1
  have hD := WrapActual.reference_Dmat_unit D hN c hc
  have he := WrapCredit.common_own_restrict c t d hD
  have hcol : ∀ i,colOf (p:=p) cf i=(t:ZMod p) := fun i => i.2
  have hmat : Dmat cf (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cf)=
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cf).map (algebraMap _ (GaussLoc p)) := by
    apply Matrix.ext; intro i j
    simp only [Dmat,Matrix.of_apply,hcol i,hcol j,↓reduceIte,Matrix.map_apply]
  have hs : sOwn cf t (loewRow p Fr cf t)=
      fun i => algebraMap _ (GaussLoc p) (loewRow p Fr cf t i) := by
    funext i; simp only [sOwn,hcol i,↓reduceIte]
  unfold WrapRestrict.ownMoment WrapOwn.commonOwn
  erw [he,hmat,hs,Matrix.dotProduct_mulVec]

/-- A single edited original colour preserves its source moment when
both full and member own moments vanish in the same reduced direction. -/
theorem moment_eq (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (K : Finset ι) (t : ℕ) (ht : t<N)
    (j : ι) (hjK : j∈K) (hj : colOf (p:=p) c j=(t:ZMod p))
    (hunique : ∀ i,i∈K → colOf (p:=p) c i=(t:ZMod p) → i=j)
    (hnej : c j≠t) (d : GaussLoc p)
    (hfull : res p (WrapRestrict.ownMoment (Fr:=Fr) c t d)=0)
    (hminor : res p (WrapRestrict.ownMoment (Fr:=Fr)
      (c ∘ (Subtype.val : WrapKeep.Keep K → ι)) t d)=0) :
    fibMom c (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c))
      (fun i => ellL p Fr (c i)-d) (t:ZMod p)=
    fibMom (c ∘ (Subtype.val : WrapKeep.Keep K → ι))
      (Dmat (c ∘ (Subtype.val : WrapKeep.Keep K → ι))
        (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ (Subtype.val : WrapKeep.Keep K → ι))))
      (fun i => ellL p Fr (c i.1)-d) (t:ZMod p) := by
  let cf := fun i : {i : ι // colOf (p:=p) c i=(t:ZMod p)} => c i.1
  let jf : {i : ι // colOf (p:=p) c i=(t:ZMod p)} := ⟨j,hj⟩
  let ce := fun i : {i : {i : ι // colOf (p:=p) c i=(t:ZMod p)} // i≠jf} => c i.1.1
  let cK := c ∘ (Subtype.val : WrapKeep.Keep K → ι)
  let E := fibreEquiv c K (t:ZMod p) j hjK hj hunique
  have hF : res p (WrapOwn.commonOwn (Fr:=Fr) cf t d)=0 := by
    rw [← ownMoment_fibre D hN c hc t d]; exact hfull
  have hK : res p (WrapOwn.commonOwn (Fr:=Fr)
      (fun i : {i : WrapKeep.Keep K // colOf (p:=p) cK i=(t:ZMod p)} => cK i.1) t d)=0 := by
    rw [← ownMoment_fibre D hN cK (fun i => hc i.1) t d]; exact hminor
  have hE := WrapOwn.commonOwn_reindex (Fr:=Fr) ce E t d
  have hCE : res p (WrapOwn.commonOwn (Fr:=Fr) ce t d)=0 := by
    rw [← hE]
    exact hK
  have hh := WrapOwn.single_erase_moment D hN cf (fun i => hc i.1) t ht (fun i => i.2)
    jf hnej d hF hCE
  have hr := WrapKeep.response_reindex (Fr:=Fr) ce E d
  erw [WrapCredit.common_moment_restrict c t d (WrapActual.reference_Dmat_unit D hN c hc),
    WrapCredit.common_moment_restrict cK t d (WrapActual.reference_Dmat_unit D hN cK (fun i => hc i.1))]
  exact hh.trans (congrArg (res p) hr.symm)

end CatalanCore.Uniform.Content.UFSimple.WrapSingle
