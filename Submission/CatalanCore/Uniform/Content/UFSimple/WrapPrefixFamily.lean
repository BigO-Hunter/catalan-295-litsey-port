module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPrefixMember

@[expose] public section

open Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixFamily

variable {ι κ χ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq χ]

noncomputable def slots (Jr Jc : Finset κ) := Jr.disjSum Jc
noncomputable def selected (Jr Jc : Finset κ) (rowColour colColour : κ → χ) :=
  (slots Jr Jc).image (Sum.elim rowColour colColour)
noncomputable def rows (Jr : Finset κ) (rowColour : κ → χ) (K : Finset ι) (f : ι → χ) :=
  Jr.filter (fun i => rowColour i∉K.image f)
noncomputable def cols (Jc : Finset κ) (colColour : κ → χ) (K : Finset ι) (f : ι → χ) :=
  Jc.filter (fun i => colColour i∉K.image f)
noncomputable def unedited (Jr Jc : Finset κ) (rowColour colColour : κ → χ) (K : Finset ι) (f : ι → χ) :=
  (slots Jr Jc).filter (fun i => Sum.elim rowColour colColour i∉K.image f)

variable (Jr Jc : Finset κ) (rowColour colColour : κ → χ)
variable (hinj : Function.Injective (Sum.elim rowColour colColour))
variable (f : ι → χ) (d : ℕ)

include hinj in
theorem selected_card : (selected Jr Jc rowColour colColour).card=Jr.card+Jc.card := by
  rw [selected,Finset.card_image_of_injective _ hinj]
  exact Finset.card_disjSum _ _

theorem unedited_card (K : Finset ι) :
    (unedited Jr Jc rowColour colColour K f).card=(rows Jr rowColour K f).card+(cols Jc colColour K f).card := by
  have he : unedited Jr Jc rowColour colColour K f=(rows Jr rowColour K f).disjSum (cols Jc colColour K f) := by
    classical
    apply Finset.ext; intro i
    rcases i with i|i
    · constructor
      · intro hi
        have hh := Finset.mem_filter.mp hi
        apply Finset.inl_mem_disjSum.mpr
        exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mp hh.1,hh.2⟩
      · intro hi
        have hh := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hi)
        exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hh.1,hh.2⟩
    · constructor
      · intro hi
        have hh := Finset.mem_filter.mp hi
        apply Finset.inr_mem_disjSum.mpr
        exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mp hh.1,hh.2⟩
      · intro hi
        have hh := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hi)
        exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mpr hh.1,hh.2⟩
  rw [he,Finset.card_disjSum]

theorem unedited_image (K : Finset ι) :
    (unedited Jr Jc rowColour colColour K f).image (Sum.elim rowColour colColour)=selected Jr Jc rowColour colColour \ K.image f := by
  apply Finset.ext; intro u
  simp only [Finset.mem_image,unedited,Finset.mem_filter,Finset.mem_sdiff,selected]
  constructor
  · rintro ⟨i,⟨hi,hu⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hu⟩
  · rintro ⟨⟨i,hi,rfl⟩,hu⟩
    exact ⟨i,⟨hi,hu⟩,rfl⟩

-- Each edited selected colour costs at most one supported coordinate.
include hinj in
theorem sigma_loss (K : Finset ι) :
    (Jr.card+Jc.card-d)-
      ((WrapDamage.single K f (selected Jr Jc rowColour colColour)).card+
       (WrapDamage.multiple K f (selected Jr Jc rowColour colColour)).card)≤
      (rows Jr rowColour K f).card+(cols Jc colColour K f).card-d := by
  have h := WrapDamage.selected_loss K f (selected Jr Jc rowColour colColour)
  have hc := Finset.card_image_of_injective (unedited Jr Jc rowColour colColour K f) hinj
  rw [unedited_image,unedited_card] at hc
  rw [selected_card Jr Jc rowColour colColour hinj] at h
  change Jr.card+Jc.card-_≤(selected Jr Jc rowColour colColour \ K.image f).card at h
  rw [hc] at h
  omega


-- The original size drop pays the entire source loss.
include hinj in
theorem price_from_source (K : Finset ι) (Ret RetMember : Finset χ) (total : ℕ)
    (hquiet : ∀ gamma,gamma∉K.image f → gamma∈RetMember → gamma∈Ret)
    (hsingle : ∀ gamma,gamma∈WrapDamage.single K f (selected Jr Jc rowColour colColour) → gamma∉RetMember) :
    2*(total-K.card)-(d+WrapCount.gain ((rows Jr rowColour K f).card+(cols Jc colColour K f).card-d) RetMember.card)≤
      2*total-(d+WrapCount.gain (Jr.card+Jc.card-d) Ret.card) := by
  exact WrapDamage.price_from_source K f (selected Jr Jc rowColour colColour) Ret RetMember total d
    (Jr.card+Jc.card-d) _ (sigma_loss Jr Jc rowColour colColour hinj f d K) hquiet hsingle


section Actual
open Polynomial Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments

variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Slot counting and the actual selected-colour union describe the same set. -/
theorem selected_points_eq (Jr Jc : Finset (Fin d)) :
    selected Jr Jc (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))=WrapPrefixMember.selectedPoints H Jr Jc := by
  classical
  apply Finset.ext
  intro gamma
  constructor
  · intro hg
    obtain ⟨i,hi,hig⟩ := mem_image.mp hg
    cases i with
    | inl z => exact mem_union_left _ (mem_image.mpr ⟨z,inl_mem_disjSum.mp hi,hig⟩)
    | inr y => exact mem_union_right _ (mem_image.mpr ⟨y,inr_mem_disjSum.mp hi,hig⟩)
  · intro hg
    rcases mem_union.mp hg with hr|hc
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hr
      exact mem_image.mpr ⟨Sum.inl z,inl_mem_disjSum.mpr hz,rfl⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hc
      exact mem_image.mpr ⟨Sum.inr y,inr_mem_disjSum.mpr hy,rfl⟩

/-- Every original common-deletion member has the full prefix window
price, with exactly zero debit, including an empty surviving selection. -/
theorem window_gle {Fr : Frame} (T : CatalanCore.Uniform.Content.Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (Jr Jc : Finset (Fin d))
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (hJr : ∀ z∈Jr,WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv)
    (K : Finset (Fin r)) :
    let s := algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X
    let u := WrapOriginalEntry.normInv p Fr
    GLE p (2*(r+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d) (WrapPrefixMember.fullRetained H s u).card))
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  classical
  intro s u
  let rowC : Fin d → ZMod p := fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p)
  let colC : Fin d → ZMod p := fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p)
  let f : Fin r → ZMod p := fun i => (i:ZMod p)
  let JrK := rows Jr rowC K f
  let JcK := cols Jc colC K f
  have hs : res p s=(RatFunc.X:RatFunc (ZMod p)) := WrapFrameResidue.spectral p
  have hu : res p u≠0 := WrapFrameResidue.normInv_ne p D
  have huc : WrapConstant.Has p u := WrapFrameResidue.normInv_constant p D
  have hdist : ∀ z y,rowC z≠colC y := by
    intro z y he
    have hh := hinj (show Sum.elim rowC colC (Sum.inl z)=Sum.elim rowC colC (Sum.inr y) from he)
    exact Sum.inl_ne_inr hh
  have hg := WrapPrefixMember.Schur.original_gle H K T D hsq hdist JrK JcK
    (fun z hz => hJr z (mem_filter.mp hz).1)
    (fun y hy => hJc y (mem_filter.mp hy).1)
    (fun z hz => (mem_filter.mp hz).2)
    (fun y hy => (mem_filter.mp hy).2)
  have hpaid := price_from_source Jr Jc rowC colC hinj f d K
    (WrapPrefixMember.fullRetained H s u) (WrapPrefixMember.retained H K s u) (r+n*p+e)
    (WrapPrefixMember.retained_quiet H K s u hs hu huc) (by
      intro gamma hgamma
      apply WrapPrefixMember.single_retained_excluded H K s u hs hu huc Jr Jc hJr hJc gamma
      simpa only [rowC,colC,selected_points_eq H Jr Jc] using hgamma)
  have hk : K.card≤r := by simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ K)
  have hsize : r-K.card+n*p+e=(r+n*p+e)-K.card := by omega
  apply hg.mono
  simpa only [hsize,JrK,JcK,WrapPrefixMember.retained,WrapPrefixMember.fullRetained] using hpaid

end Actual

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixFamily
