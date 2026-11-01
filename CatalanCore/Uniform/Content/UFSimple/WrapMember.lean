module

public import CatalanCore.Uniform.Content.UFSimple.WrapClosed
public import CatalanCore.Uniform.Content.UFSimple.WrapKeep
public import CatalanCore.Uniform.Content.UFSimple.WrapDamage

@[expose] public section

/-! # Original common-deletion matrices and their Smith prices -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMember

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable (H : WrapClosed.Hyp Fr q o r s l p N T)

/-- A direct original-matrix denominator bound from member-specific
Smith data. No inheritance from the full determinant is assumed. -/
theorem gle_of_data {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → ℕ) (hc : ∀ i,c i<N) {a b : ℕ}
    (D2 : TwoLevelData (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
      (WrapSchur.dividedSchur (WrapActual.reordered c r s l H.hl H.hls
        (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound))) a b) :
    GLE p (2*(Fintype.card ι+s+l)-((s+1-l)+WrapCount.gain a b))
      (FullN Fr c (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  let W := WrapActual.witness_of_data T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c
    r s l H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound D2
  let M := FullN Fr c (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])
  have hs := WrapSource.gle_minor_reindex (M.map (scaleU p))
    (WrapGeometry.rowFullEquiv ι s l H.hl H.hls)
    (WrapGeometry.colFullEquiv ι s l H.hl H.hls) W id id le_rfl
  have hg := gle_submatrix_of_scaleU M id id hs
  have hf : GLE p W.price M.det := by
    simpa only [Nat.sub_self,add_zero,Matrix.submatrix_id_id] using hg
  have he := WrapActual.witness_of_data_price T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c
    r s l H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound D2
  simpa only [W,he,WrapCount.gain] using hf

/-- Exact remaining common size, including the empty member. -/
theorem keep_card (K : Finset (Fin r)) : Fintype.card (WrapKeep.Keep K)=r-K.card := by
  simp only [WrapKeep.Keep,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]

include H

/-- Every common-deletion member has the actual balanced baseline. -/
theorem baseline (K : Finset (Fin r)) :
    GLE p (2*(r-K.card+s+l)-(s+1-l))
      (FullN Fr (fun i : WrapKeep.Keep K => (i.1:ℕ))
        (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hc : ∀ i : WrapKeep.Keep K,(i.1:ℕ)<N := fun i => H.common_bound i.1
  have hh := gle_of_data H (fun i : WrapKeep.Keep K => (i.1:ℕ)) hc
    (TwoLevelData.trivial (phiP p) (Polynomial.C ((p:ℕ):LocRing p)) _)
  simpa only [keep_card,WrapCount.gain,Nat.sub_self,Nat.zero_add,add_zero] using hh

/-- Large common deletions already pay the complete proposed saving
through their two-per-coordinate raw-size reduction. -/
theorem large_deletion (K : Finset (Fin r)) (saving : ℕ)
    (hpaid : saving≤(s+1-l)+2*K.card) :
    GLE p (2*(r+s+l)-saving)
      (FullN Fr (fun i : WrapKeep.Keep K => (i.1:ℕ))
        (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hk : K.card≤r := by simpa using Finset.card_le_univ K
  apply (baseline H K).mono
  have hraw : r-K.card+s+l=r+s+l-K.card := by omega
  rw [hraw]
  exact WrapCount.price_debit_zero (r+s+l) K.card saving (s+1-l) hpaid

omit H

/-- Every pair of untouched selected colours retains the original
joint-window type data, re-anchored at the first chosen untouched node.
The old window representative may itself have been deleted. -/
theorem window_type_data (W : WrapWindow.Window Fr q o r s l p N T)
    (K : Finset (Fin r)) (t1 t2 : ℕ)
    (ht1 : W.t0≤t1 ∧ t1≤W.tv) (ht2 : W.t0≤t2 ∧ t2≤W.tv)
    (hp1 : t1<r+p) (hp2 : t2<r+p)
    (hu1 : (t1:ZMod p)∉K.image (colOf (p:=p) (fun a:Fin r => (a:ℕ))))
    (hu2 : (t2:ZMod p)∉K.image (colOf (p:=p) (fun a:Fin r => (a:ℕ))))
    (C0 : RatFunc (ZMod p)) :
    let c := fun a : WrapKeep.Keep K => (a.1:ℕ)
    let n := (rfH p (red p Fr.norm))⁻¹
    let V := fun u => rfH p (wT p q o u)*n-C0
    TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t1 (loewRow p Fr c t1)
      (-(∑ u : ZMod p,V u*rfH p (u-(t1:ZMod p))⁻¹)) V
      t2 (loewRow p Fr c t2) := by
  intro c n V
  have hbound (t : ℕ) (ht : t<r+p) : t<N := by
    have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
  have hdata (t : ℕ) (ht : W.t0≤t ∧ t≤W.tv) (hp : t<r+p) :
      TypeData Fr (fun a:Fin r => (a:ℕ))
        (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ)))
        W.t0 (loewRow p Fr (fun a:Fin r => (a:ℕ)) W.t0)
        (-(rfH p (cauchyH (wT p q o) ((W.t0:ℕ):ZMod p)))*n) V
        t (loewRow p Fr (fun a:Fin r => (a:ℕ)) t) := by
    have he : W.t0+(t-W.t0)=t := Nat.add_sub_of_le ht.1
    have hh := WrapCell.typeData_window T W.hN W.hsq W.hnorm W.hnorm0 W.hp2 W.ho W.hq0
      r W.t0 (t-W.t0) W.common_bound W.t0_common
      (by rw [he]; exact hp) (by rw [he]; exact W.selected_div t ht.1 ht.2)
      (by rw [he]; exact hbound t hp) (W.selected_window t ht.1 ht.2) C0
    dsimp only at hh
    rw [he] at hh
    exact hh
  have hh := WrapKeep.typeData_reanchor (fun a:Fin r => (a:ℕ))
    (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ)))
    W.t0 t1 t2 _ _ _ _ V (hdata t1 ht1 hp1) (hdata t2 ht2 hp2)
  exact WrapKeep.typeData_unchanged (fun a:Fin r => (a:ℕ)) K t1 t2 hu1 hu2 _ V hh

/-- The member's untouched representative has the same reduced
direction as the original window, even when its old anchor was edited. -/
theorem window_direction (W : WrapWindow.Window Fr q o r s l p N T)
    (K : Finset (Fin r)) (t1 : ℕ) (ht1 : W.t0≤t1 ∧ t1≤W.tv) (hp1 : t1<r+p)
    (hu1 : (t1:ZMod p)∉K.image (colOf (p:=p) (fun a:Fin r => (a:ℕ)))) :
    let c := fun a : WrapKeep.Keep K => (a.1:ℕ)
    let co := fun a : Fin r => (a:ℕ)
    res p (dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t1 (loewRow p Fr c t1))=
      res p (dirOf Fr co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co) W.t0 (loewRow p Fr co W.t0)) := by
  intro c co
  let Qo := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
  let d0 := dirOf Fr co Qo W.t0 (loewRow p Fr co W.t0)
  have htN : t1<N := by have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
  have hD := WrapActual.reference_Dmat_unit W.D W.hN co W.common_bound
  have hDK := WrapActual.reference_Dmat_unit W.D W.hN c (fun i => W.common_bound i.1)
  have hd := WrapKeep.direction_unchanged co K t1 hu1 hD hDK
  change res p (dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t1 (loewRow p Fr c t1))=res p d0
  erw [hd]
  have he : W.t0+(t1-W.t0)=t1 := Nat.add_sub_of_le ht1.1
  have hT := WrapCell.typeData_window T W.hN W.hsq W.hnorm W.hnorm0 W.hp2 W.ho W.hq0
    r W.t0 (t1-W.t0) W.common_bound W.t0_common
    (by rw [he]; exact hp1) (by rw [he]; exact W.selected_div t1 ht1.1 ht1.2)
    (by rw [he]; exact htN) (W.selected_window t1 ht1.1 ht1.2) 0
  dsimp only at hT
  rw [he] at hT
  have hz := own_dir_zero Fr co Qo W.t0 (loewRow p Fr co W.t0)
    (WrapBalanced.commonLift_own_unit W.D W.hN co W.common_bound W.t0 W.t0_bound)
  have hh := WrapType.own_type_residue_eq co Qo hD W.t0 (loewRow p Fr co W.t0) d0
    _ _ t1 (loewRow p Fr co t1) hT
  rw [hz,map_zero] at hh
  exact (WrapBalanced.dirOf_residue co Qo t1 (loewRow p Fr co t1) d0
    (WrapBalanced.commonLift_own_unit W.D W.hN co W.common_bound t1 htN) hh).symm

/-- The step source is constant throughout the original selected window,
so changing its untouched representative does not change this term. -/
theorem window_step_equal (W : WrapWindow.Window Fr q o r s l p N T)
    (t1 t2 : ℕ) (ht1 : W.t0≤t1 ∧ t1≤W.tv) (ht2 : W.t0≤t2 ∧ t2≤W.tv)
    (hp1 : t1<r+p) (hp2 : t2<r+p) : wT p q o (t1:ZMod p)=wT p q o (t2:ZMod p) := by
  have hh (t : ℕ) (ht : W.t0≤t ∧ t≤W.tv) (hp : t<r+p) :
      wT p q o (t:ZMod p)=wT p q o (W.t0:ZMod p) := by
    have he : W.t0+(t-W.t0)=t := Nat.add_sub_of_le ht.1
    have htN : t<N := by have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
    have h := wT_window T W.hN.le W.hsq W.hnorm W.hnorm0 W.ho W.hq0 W.t0 (t-W.t0)
      (by rw [he]; exact htN) (W.selected_window t ht.1 ht.2)
    rwa [he] at h
  exact (hh t1 ht1 hp1).trans (hh t2 ht2 hp2).symm

end CatalanCore.Uniform.Content.UFSimple.WrapMember
