module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapMemberWindow

@[expose] public section

/-! # Actual retained-source comparison after common deletion -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMemberWindow.Setup

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable {W : WrapWindow.Window Fr q o r s l p N T} (M : Setup W)
include M

/-- The member direction has the original full window's residue. -/
theorem direction_residue : res p M.direction=res p W.direction := by
  have hh := WrapMember.window_direction W M.deleted M.rep M.hrep M.hrepp M.hunedited
  have he := WrapBalanced.commonLift_eq_core W.D W.hN (fun i:Fin r => (i:ℕ))
    (WrapActual.xs r) (WrapActual.ys r) W.common_bound W.xs_bound W.ys_bound
  dsimp only at hh
  erw [he] at hh
  exact hh

theorem weight_unchanged (u : ZMod p) (hu : u∉WrapMemberCount.edited M.deleted) :
    M.weight u=W.weight u :=
  WrapRestrict.weight_unchanged W M.deleted M.rep M.hrep M.hrepp M.hunedited u hu

theorem own_unchanged (t : ℕ) (hu : (t:ZMod p)∉WrapMemberCount.edited M.deleted) :
    res p (WrapRestrict.ownMoment (Fr:=Fr) M.common t M.direction)=
      res p (WrapRestrict.ownMoment (Fr:=Fr) (fun i:Fin r => (i:ℕ)) t W.direction) := by
  have hh := WrapRestrict.ownMoment_unchanged W.D W.hN (fun i:Fin r => (i:ℕ)) W.common_bound
    M.deleted t hu M.direction W.direction M.direction_residue
  exact hh

/-- Nonvanishing of an original row kill is preserved at untouched colours. -/
theorem row_kill_unchanged (z : Fin (s+1-l))
    (hu : (M.rowBorder z:ZMod p)∉WrapMemberCount.edited M.deleted)
    (hfull : wedgeR W.matrix Fr W.row W.rowBorder W.direction z≠0) :
    wedgeR M.matrix Fr M.row M.rowBorder M.direction z≠0 := by
  have h1 := (WrapMemberCoupling.row_ne_iff (WrapRestrict.windowHyp W)
    (fun i:Fin r => (i:ℕ)) W.common_bound W.direction z).mp hfull
  apply (WrapMemberCoupling.row_ne_iff M.H M.common M.common_bound M.direction z).2
  have hh := M.own_unchanged (M.rowBorder z) hu
  exact fun h0 => h1 (hh.symm.trans h0)

/-- Column wedges may have different unit determinant factors, but their
nonvanishing is preserved at untouched colours. -/
theorem col_kill_unchanged (z : Fin (s+1-l))
    (hu : (M.colBorder z:ZMod p)∉WrapMemberCount.edited M.deleted)
    (hfull : wedgeC W.matrix Fr W.col W.colBorder W.direction z≠0) :
    wedgeC M.matrix Fr M.col M.colBorder M.direction z≠0 := by
  have h1 := (WrapMemberCoupling.col_ne_iff (WrapRestrict.windowHyp W)
    (fun i:Fin r => (i:ℕ)) W.common_bound W.direction z).mp hfull
  apply (WrapMemberCoupling.col_ne_iff M.H M.common M.common_bound M.direction z).2
  have hh := M.own_unchanged (M.colBorder z) hu
  exact fun h0 => h1 (hh.symm.trans h0)

open Classical in
noncomputable def oldRet (_M : Setup W) := retOf W.weight \ (
  W.TC.image (fun z => (W.colBorder z:ZMod p)) ∪ W.TR'.image (fun z => (W.rowBorder z:ZMod p)))

theorem oldRet_count : M.oldRet.card=W.jblock.sJ := W.jblock_count.symm

/-- No untouched colour enlarges the retained source support. -/
theorem retained_quiet (u : ZMod p) (hu : u∉WrapMemberCount.edited M.deleted)
    (hnew : u∈M.retained) : u∈M.oldRet := by
  classical
  have hn := Finset.mem_sdiff.mp hnew
  have hv := (Finset.mem_filter.mp hn.1).2
  have hvOld : W.weight u≠0 := by rw [← M.weight_unchanged u hu]; exact hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvOld⟩,?_⟩
  intro hold
  rcases Finset.mem_union.mp hold with hc|hr
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    have hkeep : z∈M.TC := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      M.col_kill_unchanged z hu (W.kill_col z hz)⟩
    exact hn.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,hkeep,rfl⟩))
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have hkeep : z∈M.TR := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      M.row_kill_unchanged z hu (W.kill_row z (Finset.mem_filter.mp hz).1),hv⟩
    exact hn.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hkeep,rfl⟩))


theorem C0_eq : M.C0=W.C0 := by
  have hh := WrapRestrict.referenceC0_unchanged W M.deleted M.rep M.hrep M.hrepp M.hunedited
  have he := WrapBalanced.commonLift_eq_core W.D W.hN (fun i:Fin r => (i:ℕ))
    (WrapActual.xs r) (WrapActual.ys r) W.common_bound W.xs_bound W.ys_bound
  erw [he] at hh
  exact hh

/-- At surplus nodes the member source uses its original common moment. -/
theorem weight_surplus (t : ℕ) (hlo : r+2*l-1≤t) (hhi : t<r+p) :
    M.weight (t:ZMod p)=res p (algebraMap _ (GaussLoc p) (nL p Fr))*
      (rfH p (wT p q o (t:ZMod p))*(rfH p (red p Fr.norm))⁻¹-M.C0-
        fibMom M.common (Dmat M.common (WrapBalanced.commonLift (p:=p) (Fr:=Fr) M.common))
          (fun i => ellL p Fr (M.common i)-M.direction) (t:ZMod p)) := by
  have hDa := WrapActual.actual_Dmat_unit T W.hqp W.hN W.hsq W.hnorm W.hnorm0
    M.common r s l W.hl W.hls W.hp W.hsize M.common_bound W.xs_bound W.ys_bound
  have hDo := WrapActual.reference_Dmat_unit W.D W.hN M.common M.common_bound
  change WrapWeights.actualV Fr q o M.common r s l W.hl W.hls M.hint M.rep _= _
  rw [WrapWeights.surplus_V_eq M.common r s l M.rep t W.hl W.hls W.hp hlo hhi M.hint
    hDa (by change IsUnit (Dmat M.common M.original.toBlocks₁₁).det; rw [← M.commonCore_eq]; exact hDo)]
  unfold vS7 vDer
  erw [← M.commonCore_eq]
  rfl

theorem full_weight_surplus (t : ℕ) (hlo : r+2*l-1≤t) (hhi : t<r+p) :
    W.weight (t:ZMod p)=res p (algebraMap _ (GaussLoc p) (nL p Fr))*
      (rfH p (wT p q o (t:ZMod p))*(rfH p (red p Fr.norm))⁻¹-W.C0-
        fibMom (fun i:Fin r => (i:ℕ))
          (Dmat (fun i:Fin r => (i:ℕ)) W.original.toBlocks₁₁)
          (fun i:Fin r => ellL p Fr (i:ℕ)-W.direction) (t:ZMod p)) := by
  have he := WrapBalanced.commonLift_eq_core W.D W.hN (fun i:Fin r => (i:ℕ))
    (WrapActual.xs r) (WrapActual.ys r) W.common_bound W.xs_bound W.ys_bound
  have hDa := WrapActual.actual_Dmat_unit T W.hqp W.hN W.hsq W.hnorm W.hnorm0
    (fun i:Fin r => (i:ℕ)) r s l W.hl W.hls W.hp W.hsize W.common_bound W.xs_bound W.ys_bound
  have hDo := WrapActual.reference_Dmat_unit W.D W.hN (fun i:Fin r => (i:ℕ)) W.common_bound
  change WrapWeights.actualV Fr q o (fun i:Fin r => (i:ℕ)) r s l W.hl W.hls W.hint W.t0 _= _
  rw [WrapWeights.surplus_V_eq _ r s l W.t0 t W.hl W.hls W.hp hlo hhi W.hint
    hDa (by erw [← he]; exact hDo)]
  rfl

/-- The selected full own response vanishes in the re-anchored member direction. -/
theorem full_own_zero (t : ℕ) (ht : W.t0≤t ∧ t≤W.tv) (htp : t<r+p) :
    res p (WrapRestrict.ownMoment (Fr:=Fr) (fun i:Fin r => (i:ℕ)) t M.direction)=0 := by
  let co := fun i:Fin r => (i:ℕ)
  let Q := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
  let d := dirOf Fr co Q W.t0 (loewRow p Fr co W.t0)
  have he := WrapBalanced.commonLift_eq_core W.D W.hN co
    (WrapActual.xs r) (WrapActual.ys r) W.common_bound W.xs_bound W.ys_bound
  have hd : res p M.direction=res p d := by
    dsimp only [d,Q]; erw [he]; exact M.direction_residue
  have heq : W.t0+(t-W.t0)=t := Nat.add_sub_of_le ht.1
  have htN : t<N := by have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
  have hT := WrapCell.typeData_window T W.hN W.hsq W.hnorm W.hnorm0 W.hp2 W.ho W.hq0
    r W.t0 (t-W.t0) W.common_bound W.t0_common (by rw [heq]; exact htp)
    (by rw [heq]; exact W.selected_div t ht.1 ht.2) (by rw [heq]; exact htN)
    (W.selected_window t ht.1 ht.2) 0
  dsimp only at hT
  rw [heq] at hT
  have hh := WrapType.own_type_residue_eq co Q
    (WrapActual.reference_Dmat_unit W.D W.hN co W.common_bound)
    W.t0 (loewRow p Fr co W.t0) d _ _ t (loewRow p Fr co t) hT
  have hz := own_dir_zero Fr co Q W.t0 (loewRow p Fr co W.t0)
    (WrapBalanced.commonLift_own_unit W.D W.hN co W.common_bound W.t0 W.t0_bound)
  rw [hz,map_zero] at hh
  change res p (WrapRestrict.ownMoment (Fr:=Fr) co t M.direction)=0
  unfold WrapRestrict.ownMoment
  simp only [map_sub,RingHom.map_dotProduct,Function.comp_def,hd]
  simpa only [map_sub,RingHom.map_dotProduct,Function.comp_def] using hh


/-- A single edited selected colour either has nonzero own coupling or
keeps the original zero source weight. -/
theorem single_weight_zero (t : ℕ) (ht : W.t0≤t ∧ t≤W.tv) (htp : t<r+p)
    (hmult : WrapDamage.multiplicity M.deleted
      (colOf (p:=p) (fun i:Fin r => (i:ℕ))) (t:ZMod p)=1)
    (hown : res p (WrapRestrict.ownMoment (Fr:=Fr) M.common t M.direction)=0) :
    M.weight (t:ZMod p)=0 := by
  let co := fun i:Fin r => (i:ℕ)
  obtain ⟨j,hjK,hj,hunique⟩ := WrapSingle.unique_deleted co M.deleted (t:ZMod p) hmult
  have htN : t<N := by have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
  have hnej : co j≠t := by have := j.2; have := W.t0_common; dsimp [co]; omega
  have hm := WrapSingle.moment_eq W.D W.hN co W.common_bound M.deleted t htN j hjK hj hunique
    hnej M.direction (M.full_own_zero t ht htp) hown
  have hd := WrapKeep.mixed_moment_direction (Fr:=Fr) co co co
    (Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co))
    M.direction W.direction M.direction_residue (t:ZMod p)
  have he := WrapBalanced.commonLift_eq_core W.D W.hN co
    (WrapActual.xs r) (WrapActual.ys r) W.common_bound W.xs_bound W.ys_bound
  change fibMom co _ _ _=fibMom co _ _ _ at hd
  have hlo : r+2*l-1≤t := le_trans W.t0_lower ht.1
  rw [M.weight_surplus t hlo htp,M.C0_eq]
  erw [← hm,hd]
  erw [he]
  erw [← M.full_weight_surplus t hlo htp]
  exact W.weight_zero t (by have := W.hmax; omega) ht.2

/-- A singly edited selected colour cannot survive the member kills. -/
theorem retained_single (u : ZMod p)
    (hu : u∈WrapDamage.single M.deleted (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
      (WrapMemberCount.selected W)) : u∉M.retained := by
  classical
  have hs := (Finset.mem_filter.mp hu).2
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs.1
  intro hr
  have hn := Finset.mem_sdiff.mp hr
  have hv := (Finset.mem_filter.mp hn.1).2
  rcases z with z|z
  · have hz' := (Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hz)).2
    have hcol : WrapMemberCount.colour W (Sum.inl z)=(M.rowBorder z:ZMod p) := rfl
    have hown : res p (WrapRestrict.ownMoment (Fr:=Fr) M.common (M.rowBorder z) M.direction)≠0 := by
      intro h0
      exact hv (M.single_weight_zero (M.rowBorder z) hz' (W.rowBorder_range z).2 hs.2 h0)
    have hw := (WrapMemberCoupling.row_ne_iff M.H M.common M.common_bound M.direction z).2 hown
    have hk : z∈M.TR := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw,hv⟩
    exact hn.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hk,rfl⟩))
  · have hz' := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hz)).2
    have hown : res p (WrapRestrict.ownMoment (Fr:=Fr) M.common (M.colBorder z) M.direction)≠0 := by
      intro h0
      exact hv (M.single_weight_zero (M.colBorder z) hz' (W.colBorder_range z).2 hs.2 h0)
    have hw := (WrapMemberCoupling.col_ne_iff M.H M.common M.common_bound M.direction z).2 hown
    have hk : z∈M.TC := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
    exact hn.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,hk,rfl⟩))

/-- Concrete support enlargement is charged only to multiple selected
edits and edited colours outside the selected set. -/
theorem retained_count : M.retained.card≤M.oldRet.card+
    (WrapDamage.multiple M.deleted (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
      (WrapMemberCount.selected W)).card+
    (WrapDamage.outside M.deleted (colOf (p:=p) (fun i:Fin r => (i:ℕ)))
      (WrapMemberCount.selected W)).card :=
  WrapDamage.retained_count M.deleted _ _ _ _ M.retained_quiet M.retained_single

end CatalanCore.Uniform.Content.UFSimple.WrapMemberWindow.Setup
