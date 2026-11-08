module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapRestrict

@[expose] public section

/-! # Member kill couplings in original common-fibre coordinates -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMemberCoupling

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (H : WrapClosed.Hyp Fr q o r s l p N T)

/-- Every actual surplus row coupling is its original common own moment,
multiplied by the fixed nonzero negative frame norm. -/
theorem row_own (c : ι → ℕ) (hc : ∀ i,c i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let xx := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inr i)
    wedgeR A Fr cr xx d z= -res p (algebraMap _ (GaussLoc p) (nL p Fr))*
      res p (WrapRestrict.ownMoment (Fr:=Fr) c (xx z) d) := by
  intro A cr xx
  rw [WrapCoupling.actual_row_wedge_eq T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound d z]
  let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r)
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
  let j := WrapGeometry.rowSlot s l H.hl H.hls (Sum.inr z)
  have he : Ao.toBlocks₁₁=WrapBalanced.commonLift (p:=p) (Fr:=Fr) c :=
    (WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
      hc H.xs_bound H.ys_bound).symm
  have hload : Ao.toBlocks₂₁ j=loewRow p Fr c (WrapActual.xs r j) := by
    funext i
    exact sLift_row_entry H.D H.hN c (WrapActual.xs r) (WrapActual.ys r) hc H.xs_bound H.ys_bound j i
  have hw := WrapCoupling.row_wedge_res H.D Ao c c (WrapActual.xs r) (WrapActual.ys r)
    hc hc H.xs_bound (fun _ => rfl)
    (WrapEntries.sLift_commutator H.D H.hN c (WrapActual.xs r) (WrapActual.ys r) hc H.xs_bound H.ys_bound)
    (sLift_core_det c (WrapActual.xs r) (WrapActual.ys r) _) d j
  rw [hload,he] at hw
  exact hw

/-- The same original own moment controls the transposed column-axis
row coupling. This avoids assuming symmetry of the actual mixed core. -/
theorem transpose_col_own (c : ι → ℕ) (hc : ∀ i,c i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let yy := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inr i)
    wedgeR Aᵀ Fr cc yy d z= -res p (algebraMap _ (GaussLoc p) (nL p Fr))*
      res p (WrapRestrict.ownMoment (Fr:=Fr) c (yy z) d) := by
  intro A cc yy
  rw [WrapCoupling.actual_col_row_wedge_eq T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound d z]
  let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r)
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
  let j := WrapGeometry.colSlot s l H.hl H.hls (Sum.inr z)
  have he : Ao.toBlocks₁₁=WrapBalanced.commonLift (p:=p) (Fr:=Fr) c :=
    (WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
      hc H.xs_bound H.ys_bound).symm
  have heT : Aoᵀ.toBlocks₁₁=WrapBalanced.commonLift (p:=p) (Fr:=Fr) c := by
    change Ao.toBlocks₁₁ᵀ=_
    rw [he,WrapBalanced.commonLift_symm]
  have hload : Aoᵀ.toBlocks₂₁ j=loewRow p Fr c (WrapActual.ys r j) := by
    funext i
    exact sLift_col_entry H.D H.hN c (WrapActual.xs r) (WrapActual.ys r) hc H.xs_bound H.ys_bound i j
  have hdet : phiP p Aoᵀ.toBlocks₁₁.det≠0 := by
    change phiP p Ao.toBlocks₁₁ᵀ.det≠0
    rw [Matrix.det_transpose]
    exact sLift_core_det c (WrapActual.xs r) (WrapActual.ys r) _
  have hw := WrapCoupling.row_wedge_res H.D Aoᵀ c c (WrapActual.ys r) (WrapActual.xs r)
    hc hc H.ys_bound (fun _ => rfl)
    (WrapResponse.commutator_transpose Ao (rowNode c (WrapActual.xs r)) (colNode c (WrapActual.ys r))
      (WrapEntries.sLift_commutator H.D H.hN c (WrapActual.xs r) (WrapActual.ys r) hc H.xs_bound H.ys_bound))
    hdet d j
  rw [hload,heT] at hw
  exact hw

/-- Actual row kill coupling is nonzero exactly when the original own
moment is nonzero after reduction. -/
theorem row_ne_iff (c : ι → ℕ) (hc : ∀ i,c i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let xx := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inr i)
    wedgeR A Fr cr xx d z≠0 ↔ res p (WrapRestrict.ownMoment (Fr:=Fr) c (xx z) d)≠0 := by
  intro A cr xx
  rw [row_own H c hc d z]
  have hn := ((isUnit_nL H.D).map (res p)).ne_zero
  simp [hn,xx]

/-- Actual column kill coupling has the same nonvanishing criterion;
its extra core determinant is a unit. -/
theorem col_ne_iff (c : ι → ℕ) (hc : ∀ i,c i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let yy := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inr i)
    wedgeC A Fr cc yy d z≠0 ↔ res p (WrapRestrict.ownMoment (Fr:=Fr) c (yy z) d)≠0 := by
  intro A cc yy
  have hdet : phiP p A.toBlocks₁₁.det≠0 := WrapActual.core_primitive T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
  have hn := ((isUnit_nL H.D).map (res p)).ne_zero
  have hrow : wedgeR Aᵀ Fr cc yy d z≠0 ↔
      res p (WrapRestrict.ownMoment (Fr:=Fr) c (yy z) d)≠0 := by
    rw [transpose_col_own H c hc d z]
    simp [hn,yy]
  have hcol : wedgeR Aᵀ Fr cc yy d z≠0 ↔ wedgeC A Fr cc yy d z≠0 := by
    rw [WrapCoupling.wedgeR_transpose]
    simp [hdet]
  exact hcol.symm.trans hrow

end CatalanCore.Uniform.Content.UFSimple.WrapMemberCoupling
